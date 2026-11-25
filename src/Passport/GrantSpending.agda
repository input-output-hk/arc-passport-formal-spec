{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

-- The book is auxiliary accounting obtained by replaying accepted history, not
-- another contract state. It records accepted amounts under each actual issuance;
-- identities retain epoch, generation and issuedAt, not just the reusable map id.
-- observeAttempt re-runs deterministic dispatch at the recorded before-state to
-- distinguish commitment from refusal; a checked trace ties this replay to its
-- observed transition. It cannot admit a call independently of the evaluator.
-- HistoryAgreement supplies only relevant spent-opening agreement at accepted
-- grant calls; initialization and cap preservation are conclusions, not premises.
module Passport.GrantSpending (P : Primitives) where


import Conformance.FullAccount as Model
open import Conformance.FullAccountDeviceSecurity P using (deviceArguments)
open import Conformance.FullAccountBody P
open import Conformance.FullAccountCrypto P
open import Conformance.FullAccountExecution
open import Conformance.FullAccountGrant P
open import Conformance.FullAccountGrantSecurity P
open import Conformance.FullAccountLayouts
open import Data.Bool.Base using (true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_; take; drop; length)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe.Base using (Maybe; just; nothing; fromMaybe)
open import Data.Nat.Base hiding (equal)
open import Data.Nat.ListAction using (sum)
open import Data.Product.Base using (_×_)
open import Data.Unit.Base using (⊤)
open import Passport.GrantEffects P
import Midnight.ContractDSL.Lifecycle as Lifecycle
import Passport.Account as Account
open import Passport.AccountLifecycle P
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.PropositionalEquality using (_≡_)



-- Amounts are newest first. An entry is moved to completed on replacement
-- or revoke-all, so a reused map identifier never resets the older episode's
-- accumulated sum. Revocation and recovery leave its accounting intact.
record Episode : Set where
  constructor episode
  field issuanceIdentity : Issuance
        saltValue : Value
        capValue : ℕ
        amounts : List ℕ

total : Episode → ℕ
total ep = sum (Episode.amounts ep)

episodeKey : Episode → Value
episodeKey ep = Issuance.identifier (Episode.issuanceIdentity ep)

record Book : Set where
  constructor book
  field current completed : List Episode

emptyBook : Book
emptyBook = book [] []

findEpisode : Value → List Episode → Maybe Episode
findEpisode id [] = nothing
findEpisode id (ep ∷ eps) = if equal id (episodeKey ep) then just ep else findEpisode id eps

insertEpisode : Episode → List Episode → List Episode
insertEpisode ep [] = ep ∷ []
insertEpisode ep (old ∷ eps) = if equal (episodeKey ep) (episodeKey old) then ep ∷ eps
  else old ∷ insertEpisode ep eps

charge : Value → ℕ → List Episode → List Episode
charge id amount [] = []
charge id amount (ep ∷ eps) = if equal id (episodeKey ep)
  then record ep { amounts = amount ∷ Episode.amounts ep } ∷ eps
  else ep ∷ charge id amount eps

data AccountingAction : Set where
  issueEpisode : Episode → AccountingAction
  spendAmount : Value → ℕ → AccountingAction
  closeAll : AccountingAction
  noCharge : AccountingAction

remember : Maybe Episode → List Episode → List Episode
remember nothing completed = completed
remember (just old) completed = old ∷ completed

evolve : AccountingAction → Book → Book
evolve (issueEpisode ep) (book current completed) =
  book (insertEpisode ep current) (remember (findEpisode (episodeKey ep) current) completed)
evolve (spendAmount id amount) (book current completed) = book (charge id amount current) completed
evolve closeAll (book current completed) = book [] (current ++ completed)
evolve noCharge b = b

open Model.AccountSemantics P using (Entrypoint; construct; activation; device; grant;
  depositPublic; depositPrivate; submitRecovery; finaliseRecovery; parseGrant)

-- Same source argument split as AccountSecurity.grantAuthorisation.
parseGrantAuth : Curve → Operation → List Value → GrantAuth
parseGrantAuth c withdrawUnshielded xs = parseGrant c (drop 3 xs) none none
parseGrantAuth c _ xs = parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)

observeBody : Operation → List Value → State → AccountingAction
observeBody issueGrant xs after = issueEpisode
  (episode (issuanceOf A.id (fromMaybe none (lookupMap A.id (fields (cell "grants" after)))))
    A.salt (number A.cap) [])
  where module A = IssueArguments xs
observeBody revokeAllGrants xs after = closeAll
observeBody _ _ _ = noCharge

-- Only committed calls are observed. The dispatcher still validates every
-- argument/context/state; the observer neither accepts nor rejects a call.
observeAccepted : Entrypoint → Context → List Value → State → State → AccountingAction
observeAccepted (device c op) ctx xs before after = observeBody op (deviceArguments op xs) after
observeAccepted (grant c op) ctx xs before after with grantId c ctx (parseGrantAuth c op xs) before
... | rejected _ = noCharge
... | accepted id _ _ = spendAmount id (amountOf op (take 3 xs))
observeAccepted _ _ _ _ _ = noCharge

WithinCap : Episode → Set
WithinCap ep = total ep ≤ Episode.capValue ep

BookBounded : Book → Set
BookBounded b = All WithinCap (Book.current b) × All WithinCap (Book.completed b)

-- The map correspondence includes the stored nonce and an actual opening of
-- the sum. The numerical spentPrev guard alone cannot establish this relation.
-- spentCommit is state-independent: state [] is a canonical evaluation state,
-- not an assumption that the account is undeployed or has an empty grants map.
record Opens (ep : Episode) (g : Value) : Set where
  field identityKept : issuanceOf (episodeKey ep) g ≡ Episode.issuanceIdentity ep
        scopeCapKept : number (scopeCap (grantScope g)) ≡ Episode.capValue ep
        nonceKept : grantNonce g ≡ nat (length (Episode.amounts ep))
        spentOpening : Run (spentCommit (Episode.saltValue ep) (total ep)) (state [])
          (grantSpentCommitment g) (state [])

data Corresponds : List Episode → List Value → Set where
  empty : Corresponds [] []
  mapEntry : ∀ {ep g eps entries} → Opens ep g → Corresponds eps entries →
    Corresponds (ep ∷ eps) (tuple (episodeKey ep ∷ g ∷ []) ∷ entries)

record Accounted (b : Book) (s : State) : Set where
  field correspondence : Corresponds (Book.current b) (fields (cell "grants" s))
        bounded : BookBounded b

-- Quantify only over a current episode whose key is the call's computed grant
-- id. The premise relates that episode's historical opening to the presented one.
CallAgreement : Entrypoint → Context → List Value → State → Book → Set
CallAgreement (grant c op) ctx xs s b = ∀ ep →
  findEpisode (episodeKey ep) (Book.current b) ≡ just ep →
  Run (grantId c ctx (parseGrantAuth c op xs)) s (episodeKey ep) s →
  SpentOpeningsAgree (salt (parseGrantAuth c op xs)) (spentPrev (parseGrantAuth c op xs))
    (Episode.saltValue ep) (total ep)
CallAgreement _ _ _ _ _ = Data.Unit.Base.⊤

-- These lookups use the same actual entrypoints/name table as Model.dispatch,
-- AccountSecurity.resolve, OutsiderPreservation.resolve and
-- UnshieldedAccounting.dispatchedAction; there is no additional dispatch policy.
observeSuccessful : Context → RawCall → State → State → Book → Book
observeSuccessful ctx call s t b
  with Model.AccountSemantics.lookupEntrypoint P (name call) (Model.AccountSemantics.entrypoints P)
... | nothing = b
... | just e = evolve (observeAccepted e ctx (arguments call) s t) b

observeAttempt : Context → RawCall → State → Book → Book
observeAttempt ctx call s b with Model.dispatch P ctx call s
... | rejected _ = b
... | accepted _ t _ = observeSuccessful ctx call s t b

AcceptedAgreement : Context → RawCall → State → Book → Set
AcceptedAgreement ctx call s b
  with Model.AccountSemantics.lookupEntrypoint P (name call) (Model.AccountSemantics.entrypoints P)
... | nothing = ⊤
... | just e = CallAgreement e ctx (arguments call) s b

AttemptAgreement : Context → RawCall → State → Book → Set
AttemptAgreement ctx call s b with Model.dispatch P ctx call s
... | rejected _ = ⊤
... | accepted _ _ _ = AcceptedAgreement ctx call s b

module Histories (address : Value) where
  module Runs = Lifecycle.Runs lifecycle address

  runBook : ∀ {s t} → Book → Runs.Trace s t → Book
  runBook b ε = b
  runBook {s} b (Runs.event env call _ _ ◅ rest) =
    runBook (observeAttempt (executionContext address env) (RuntimeCall.request call) s b) rest

  TraceAgreement : ∀ {s t} → Book → Runs.Trace s t → Set
  TraceAgreement b ε = ⊤
  TraceAgreement {s} b (Runs.event env call _ _ ◅ rest) =
    AttemptAgreement (executionContext address env) (RuntimeCall.request call) s b ×
    TraceAgreement (observeAttempt (executionContext address env) (RuntimeCall.request call) s b) rest

  historyBook : ∀ {s} → Runs.History s → Book
  historyBook h = runBook emptyBook (Runs.History.execution h)

  HistoryAgreement : ∀ {s} → Runs.History s → Set
  HistoryAgreement h = TraceAgreement emptyBook (Runs.History.execution h)

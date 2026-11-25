{-# OPTIONS --safe --without-K #-}

-- What a successful grant-authenticated call (FullAccountGrant.grantCall)
-- establishes about its before-state. Each fact is the outcome of an actual
-- evaluator step: a map lookup, a ledger read, an assertion, or a source
-- commitment/verification function run at that state (`Run m s v s`: m
-- answers v and leaves s unchanged). Nothing here asserts that a commitment
-- or signature is sound; SpentOpeningsAgree is the only cryptographic
-- premise, taken by one theorem for one pair of openings. Statements and proof references:
-- Conformance.FullAccountGrantSecurityProperties.

open import Conformance.FullAccountTypes

module Conformance.FullAccountGrantSecurity (P : Primitives) where

open import Conformance.FullAccountBody P
open import Conformance.FullAccountCrypto P
open import Conformance.FullAccountExecution using (Run)
open import Conformance.FullAccountGrant P
open import Conformance.FullAccountLayouts
open import Data.Bool.Base using (if_then_else_; true; false)
open import Data.List.Base using (List; []; _∷_; _++_; take; drop)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base hiding (equal)
open import Data.Product.Base using (Σ; _×_; _,_)
open import Data.Sum.Base using (_⊎_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- The held coin grantCall reads: present only for the shielded withdrawals.
grantCoin : Operation → Context → Value
grantCoin op ctx = if shielded op then heldCoin ctx else none

-- The argument atoms grantCall passes to the grant challenge.
grantChallengeAtoms : Operation → List Value → Value → GrantAuth → Value → Value → List Atom
grantChallengeAtoms op xs coin ga identifier g =
  b32 identifier ∷ u64 (grantIssuedAt g) ∷ grantChallengeArgs op xs coin ga

-- The P-256 origin-hash preimage hashed by authenticateGrant's curve guard.
grantOriginPreimage : GrantAuth → List Atom
grantOriginPreimage ga =
  b32 (pad 32 "midnight:account:grant:origin:v1") ∷ ("Bytes<21>" , at 1 (policy (authorisation ga))) ∷ []

-- authenticateGrant's curve-specific key/policy admission. The P-256 RP
-- commitment is checked against the record's scope after the lookup.
CurvePolicy : Curve → GrantAuth → State → Value → Set
CurvePolicy jubjub ga s scope =
  Run (requireSmallOrderFree (key (authorisation ga)) "grantee key has small order") s tt s
CurvePolicy k256 ga s scope =
  envelope (authorisation ga) ≡ 0 × Run (requireK256Key (key (authorisation ga))) s tt s
CurvePolicy p256 ga s scope =
  persistentHash P (grantOriginPreimage ga) ≡ success (origin ga) ×
  Run (rpCommit (salt ga) (at 0 (policy (authorisation ga)))) s (scopeRPCommitment scope) s

-- An expiry of zero means no expiry.
Unexpired : Context → Value → Set
Unexpired ctx scope =
  number (scopeExpiresAt scope) ≡ 0 ⊎ blockTime ctx < number (scopeExpiresAt scope)

record LiveGrant (c : Curve) (ctx : Context) (ga : GrantAuth) (s : State) (g : Value) : Set where
  field active : grantActive g ≡ bool true
        currentEpoch : lookupCell "device_epoch" (ledger s) ≡ just (grantEpoch g)
        currentGeneration : lookupCell "grant_generation" (ledger s) ≡ just (grantGeneration g)
        unexpired : Unexpired ctx (grantScope g)
        curvePolicy : CurvePolicy c ga s (grantScope g)

-- A zero caller commitment leaves the caller unrestricted; otherwise the call
-- came from a contract whose salted commitment is the scope's.
CallerAdmitted : Context → GrantAuth → State → Value → Set
CallerAdmitted ctx ga s scope =
  scopeCallerCommitment scope ≡ zero32 ⊎
  Σ Value λ address → caller ctx ≡ some (tuple (bool true ∷ address ∷ [])) ×
    Run (callerCommit (salt ga) (some address)) s (scopeCallerCommitment scope) s

-- Recipient kind zero admits any recipient; otherwise kind and pin must match.
RecipientAdmitted : Operation → GrantAuth → List Value → Set
RecipientAdmitted op ga xs = number (recipientKind ga) ≡ 0 ⊎
  (number (recipientKind ga) ≡ thisKind op × pinnedRecipient ga ≡ recipientOf op xs)

-- scopeCheck's guards, in source order. The spent opening binds the
-- caller-supplied spentPrev to the record only through spentCommit's digest.
record ScopeAdmitted (op : Operation) (ctx : Context) (ga : GrantAuth) (xs : List Value)
    (coin : Value) (s : State) (g : Value) (spent : ℕ) : Set where
  field operationAllowed : scopeAllows op (grantScope g) ≡ bool true
        callerAdmitted : CallerAdmitted ctx ga s (grantScope g)
        objectCommitted : Run (objectCommit (salt ga) (if shielded op then at 1 coin else get 0 xs)
          (recipientKind ga) (pinnedRecipient ga) (nat (maxCoinValue ga))) s
          (scopeObjectCommitment (grantScope g)) s
        perCallCap : amountOf op xs ≤ number (scopePerCallCap (grantScope g))
        spentOpened : Run (spentCommit (salt ga) (spentPrev ga)) s (grantSpentCommitment g) s
        cumulativeCap : spentPrev ga + amountOf op xs ≤ number (scopeCap (grantScope g))
        spentTotal : spent ≡ spentPrev ga + amountOf op xs
        spentBound : spent < 2 ^ 128
        recipientAdmitted : RecipientAdmitted op ga xs

-- The shielded-coin guards grantCall runs after scopeCheck.
CoinAdmitted : Operation → GrantAuth → Value → State → Set
CoinAdmitted op ga coin s = shielded op ≡ false ⊎
  (shielded op ≡ true × number (at 2 coin) ≤ maxCoinValue ga ×
   lookupCell "enc_key" (ledger s) ≡ just (encryptionKey ga))

-- settle's record update: nonce and spent commitment replace fields 3 and 4.
settledGrant : Value → ℕ → Value → Value
settledGrant g nonce commitment =
  tuple (take 3 (fields g) ++ (nat nonce ∷ commitment ∷ drop 5 (fields g)))

grantsSettled : State → Value → Value → State
grantsSettled s identifier updated =
  state (insertCell "grants" (tuple (insertMap identifier updated (fields (cell "grants" s)))) (ledger s))

-- settle after its verification: bounded nonce increment, new spent
-- commitment, record insertion, then the round bump reaching `settled`.
record Settlement (ga : GrantAuth) (s : State) (identifier g : Value) (spent : ℕ)
    (settled : State) : Set where
  field nextNonce : suc (number (grantNonce g)) < 2 ^ 64
        commitment : Value
        spentCommitted : Run (spentCommit (salt ga) spent) s commitment s
        roundAdvanced : Run (bump "round" 64)
          (grantsSettled s identifier (settledGrant g (suc (number (grantNonce g))) commitment)) tt settled

-- Everything an accepted grantCall establishes, for any curve and operation.
-- The challenge is the operation challenge; `verified` is the actual
-- curve-specific verification of it (including any envelope/WebAuthn digest).
record GrantCallEvidence (c : Curve) (op : Operation) (ctx : Context) (ga : GrantAuth)
    (xs : List Value) (s : State) : Set where
  constructor grantCallEvidence
  field identifier grantRecord challengeValue : Value
        spent : ℕ
        settled : State
        identified : Run (grantId c ctx ga) s identifier s
        recorded : Run (lookup "grants" identifier) s grantRecord s
        live : LiveGrant c ctx ga s grantRecord
        scoped : ScopeAdmitted op ctx ga xs (grantCoin op ctx) s grantRecord spent
        coinAdmitted : CoinAdmitted op ga (grantCoin op ctx) s
        challenged : Run (challengeAt c true (operationName op) (self ctx) (authorisation ga)
          (grantChallengeAtoms op xs (grantCoin op ctx) ga identifier grantRecord)
          (number (grantNonce grantRecord))) s challengeValue s
        verified : Run (verify c (authorisation ga) challengeValue "invalid grant signature") s tt s
        settlement : Settlement ga s identifier grantRecord spent settled
        withdrawn : Σ Value λ result → Σ State λ after →
          Run (body op ctx xs (grantCoin op ctx) none) settled result after

-- settledGrant's effect on the GrantRecord layout.
record SettledRecord (g : Value) (nonce : ℕ) (commitment updated : Value) : Set where
  field nonceSet : grantNonce updated ≡ nat nonce
        commitmentSet : grantSpentCommitment updated ≡ commitment
        epochKept : grantEpoch updated ≡ grantEpoch g
        generationKept : grantGeneration updated ≡ grantGeneration g
        issuedKept : grantIssuedAt updated ≡ grantIssuedAt g
        windowStartKept : grantWindowStart updated ≡ grantWindowStart g
        windowSpentKept : grantWindowSpent updated ≡ grantWindowSpent g
        activeKept : grantActive updated ≡ grantActive g
        scopeKept : grantScope updated ≡ grantScope g

-- Explicit agreement for one pair of spent-commitment openings: the call's
-- (salt, spentPrev) and a claimed opening of the stored commitment. If both
-- digest to the same value, they are the same opening. This is a premise
-- about that pair only; SHA-256 binding of spentCommit is not proved here.
SpentOpeningsAgree : (callSalt : Value) (callSpent : ℕ) (storedSalt : Value) (storedTotal : ℕ) → Set
SpentOpeningsAgree callSalt callSpent storedSalt storedTotal = ∀ {v s₁ s₂} →
  Run (spentCommit callSalt callSpent) s₁ v s₁ → Run (spentCommit storedSalt storedTotal) s₂ v s₂ →
  callSalt ≡ storedSalt × callSpent ≡ storedTotal

open GrantCallEvidence public

-- The grant-authenticated runtime entrypoints (AccountSemantics.spendOperations).
data Withdrawal : Operation → Set where
  unshieldedWithdrawal : Withdrawal withdrawUnshielded
  shieldedWithdrawal : Withdrawal withdrawShielded
  contractWithdrawal : Withdrawal withdrawToContract

-- The record an accepted withdrawal leaves under its grant id in the final
-- state t: the evidence's record with nonce + 1 and the new spent commitment
-- (Settlement.spentCommitted: spentCommit of the call's salt and new spend).
record GrantFinalState (c : Curve) (op : Operation) (ctx : Context) (ga : GrantAuth)
    (xs : List Value) (s t : State) : Set where
  field callEvidence : GrantCallEvidence c op ctx ga xs s

  settledNonce : ℕ
  settledNonce = suc (number (grantNonce (grantRecord callEvidence)))

  settledCommitment : Value
  settledCommitment = Settlement.commitment (settlement callEvidence)

  settledValue : Value
  settledValue = settledGrant (grantRecord callEvidence) settledNonce settledCommitment

  field storedGrant : lookupMap (identifier callEvidence) (fields (cell "grants" t)) ≡ just settledValue
        storedFields : SettledRecord (grantRecord callEvidence) settledNonce settledCommitment settledValue

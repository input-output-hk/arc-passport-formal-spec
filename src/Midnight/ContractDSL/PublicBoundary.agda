{-# OPTIONS --safe --without-K --guardedness #-}

module Midnight.ContractDSL.PublicBoundary where

open import Data.Bool.Base
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Sum.Properties using (inj₂-injective)
open import Data.Unit.Base
open import Function.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
import Midnight.ContractDSL.AdmissionProperties as Admissions
import Midnight.ContractDSL.Balance as Balance
import Midnight.ContractDSL.BalanceLedger as BL
import Midnight.ContractDSL.Contract as Contracts
import Midnight.ContractDSL.Experiment as Experiments
import Midnight.ContractDSL.Program as Programs
import Midnight.ContractDSL.ObservedExecution as Observed
open import Midnight.ContractDSL.MidnightLedger as Ledger hiding (prepare)
open import Midnight.ContractDSL.MerkleFixture using (initial)
open import Midnight.ContractDSL.Program midnight Assertion hiding (step)
open import Midnight.ContractDSL.ObservedExecution midnight Assertion
open import Midnight.ContractDSL.Smoke using () renaming (readDet to deterministic)

-- Result declassification is fixed per entry, not chosen by the challenge bit.
data Entry : Set where
  silent echo publicEcho publishInput queryInput abortAfter chainGate : Entry

Result : Entry → Set
Result echo = Bool
Result publicEcho = Bool
Result _ = ⊤

bit : Bool → ℕ
bit false = 0
bit true = 1

boundaryContract : Contracts.Contract midnight Assertion
boundaryContract = record
  { self = 0 ; EntryPoint = Entry ; Input = λ _ → Bool × ⊤ ; Result = Result
  ; body = λ _ → λ
      { silent (b , _) → pure tt
      ; echo (b , _) → pure b
      ; publicEcho (b , _) → pure b
      ; publishInput (b , _) → perform (publish (bit b))
      ; queryInput (b , _) → perform (ledger (flagMember b)) >> pure tt
      ; abortAfter (b , _) → perform (publish (bit b)) >> perform (ledger (flagMember b)) >> assert false assertionFailed
      ; chainGate (b , _) → perform (atChain (timeAtLeast 1)) } }

module I = Experiments.Runtime midnight Assertion boundaryContract (λ _ → ⊤) (λ _ _ → tt)
module A = Admissions midnight Assertion boundaryContract

query-input-details : (b : Bool) (s : State) {t : State} {j : Journal} →
  eval (I.body 0 queryInput (b , tt)) s ≡ inj₂ (finished tt t j) →
  t ≡ s × Σ Bool (λ observed →
    Ledger.prepare (flagMember b) s ≡ inj₂ (observed , s) ×
    j ≡ operated (flagMember b) observed ∷ [])
query-input-details false s refl = refl , falseFlag s , refl , refl
query-input-details true s refl = refl , trueFlag s , refl , refl

chain-gate-admitted : (now : ℕ) (s : State) (b : Bool) →
  holds (timeAtLeast 1) now ≡ true →
  I.admit s (I.submit now (I.transaction
    (I.makeCertifiedDraft chainGate (b , tt) I.neutralArtifact s tt s (required (timeAtLeast 1) ∷ []) refl)))
    ≡ (s , I.accepted)
chain-gate-admitted now s b mature = A.Eligible⇒admit
  (I.submit now (I.transaction
    (I.makeCertifiedDraft chainGate (b , tt) I.neutralArtifact s tt s (required (timeAtLeast 1) ∷ []) refl)))
  refl (mature , tt)

chain-gate-required : (now : ℕ) (s : State) (tx : I.Transaction) →
  I.Transaction.entry tx ≡ chainGate → {t : State} →
  I.admit s (I.submit now tx) ≡ (t , I.accepted) →
  holds (timeAtLeast 1) now ≡ true
chain-gate-required now s tx same {t} admitted = proj₁
  (subst (Eligible now) journal-equal (A.accepted-eligible (I.submit now tx) s t admitted))
  where
  journal-equal : journal (I.Transaction.execution tx) ≡ required (timeAtLeast 1) ∷ []
  journal-equal = entry-journal tx same
    where
    entry-journal : (q : I.Transaction) → I.Transaction.entry q ≡ chainGate →
      journal (I.Transaction.execution q) ≡ required (timeAtLeast 1) ∷ []
    entry-journal record { target = target ; entry = chainGate ; input = b , witness
      ; view = view ; execution = run ; certified = cert } refl =
      cong journal (sym (inj₂-injective cert))

simulator-not-binding : ¬ I.CommitmentBinding
simulator-not-binding binding with cong proj₁
  (proj₁ (binding I.neutralArtifact 0 silent (false , tt) (true , tt) false false tt tt))
... | ()

PublicResult : Entry → Set
PublicResult publicEcho = Bool
PublicResult _ = ⊤

disclose : (n : Entry) → Result n → PublicResult n
disclose publicEcho b = b
disclose silent _ = tt
disclose echo _ = tt
disclose publishInput _ = tt
disclose queryInput _ = tt
disclose abortAfter _ = tt
disclose chainGate _ = tt

module O = I.PublicProjection PublicResult disclose

data Action : Set where
  prepare commit : Action

request : Entry → Bool → Action → I.ClientQuery
request n b prepare = I.prepareDraft n (b , tt) I.neutralArtifact
request n b commit = I.submitDraft

publicSystem : Entry → Bool → Protocol unitᴵ (O.PublicAnswer ⇿ Action)
publicSystem n b = O.wrapper (request n b) ∘ᵖ I.services 0 initial

publicResponse : Entry → Bool → Calls unitᴵ O.PublicAnswer
publicResponse n b = step (publicSystem n b) (init (publicSystem n b)) prepare >>=ᶜ λ sr → ret (proj₂ sr)

callerResponse : Entry → Bool → Calls unitᴵ I.ClientAnswer
callerResponse n b = step (I.system 0 initial) (init (I.system 0 initial))
  (I.prepareDraft n (b , tt) I.neutralArtifact) >>=ᶜ λ sr → ret (proj₂ sr)

recipientResponse : Entry → Bool → Calls unitᴵ (Maybe (Σ Entry Result))
recipientResponse n b = callerResponse n b >>=ᶜ λ answer → ret (O.recipientAnswer answer)

private-booleans-distinct : false ≢ true
private-booleans-distinct ()

silent-public-response-equal : publicResponse silent false ≡ publicResponse silent true
silent-public-response-equal = refl

echo-public-response-equal : publicResponse echo false ≡ publicResponse echo true
echo-public-response-equal = refl

recipient-false : recipientResponse echo false ≡ ret (just (echo , false))
recipient-false = refl
recipient-true : recipientResponse echo true ≡ ret (just (echo , true))
recipient-true = refl

public-result-policy-false : publicResponse publicEcho false ≡
  ret (O.prepared publicEcho false (I.claim 0 publicEcho tt I.neutralArtifact []) [])
public-result-policy-false = refl
public-result-policy-true : publicResponse publicEcho true ≡
  ret (O.prepared publicEcho true (I.claim 0 publicEcho tt I.neutralArtifact []) [])
public-result-policy-true = refl

publicTrace : O.PublicAnswer → Trace
publicTrace (O.prepared n r statement observed) = observed
publicTrace (O.failed e observed) = observed
publicTrace (O.provingFailed observed) = observed
publicTrace _ = []

publicationBit : Trace → Maybe Bool
publicationBit [] = nothing
publicationBit (publication 0 ∷ _) = just false
publicationBit (publication 1 ∷ _) = just true
publicationBit (_ ∷ rest) = publicationBit rest

queryBit : Trace → Maybe Bool
queryBit [] = nothing
queryBit (queried (flagMember b) _ ∷ _) = just b
queryBit (_ ∷ rest) = queryBit rest

readPublication : Entry → Bool → Calls unitᴵ (Maybe Bool)
readPublication n b = publicResponse n b >>=ᶜ λ answer → ret (publicationBit (publicTrace answer))
readQuery : Entry → Bool → Calls unitᴵ (Maybe Bool)
readQuery n b = publicResponse n b >>=ᶜ λ answer → ret (queryBit (publicTrace answer))

publication-false-visible : readPublication publishInput false ≡ ret (just false)
publication-false-visible = refl
publication-true-visible : readPublication publishInput true ≡ ret (just true)
publication-true-visible = refl
query-false-visible : readQuery queryInput false ≡ ret (just false)
query-false-visible = refl
query-true-visible : readQuery queryInput true ≡ ret (just true)
query-true-visible = refl

publication-leaks : publicResponse publishInput false ≢ publicResponse publishInput true
publication-leaks ()
query-leaks : publicResponse queryInput false ≢ publicResponse queryInput true
query-leaks ()

abort-projection : (b : Bool) → publicResponse abortAfter b ≡ ret
  (O.failed (assertionError assertionFailed)
    (publication (bit b) ∷ queried (flagMember b) (inj₂ true) ∷ []))
abort-projection false = refl
abort-projection true = refl

abort-publication-survives : (b : Bool) → readPublication abortAfter b ≡ ret (just b)
abort-publication-survives false = refl
abort-publication-survives true = refl
abort-query-survives : (b : Bool) → readQuery abortAfter b ≡ ret (just b)
abort-query-survives false = refl
abort-query-survives true = refl

admissionResponse : Entry → Bool → Calls unitᴵ O.PublicAnswer
admissionResponse n b = step P (init P) prepare >>=ᶜ λ
  { (st , answer) → step P st commit >>=ᶜ λ next → ret (proj₂ next) }
  where P = publicSystem n b

accepted-projection : admissionResponse silent false ≡ ret (O.admitted I.accepted)
accepted-projection = refl
rejected-projection : admissionResponse chainGate false ≡ ret (O.admitted I.rejected)
rejected-projection = refl
no-draft-after-failure : admissionResponse abortAfter true ≡ ret O.absentDraft
no-draft-after-failure = refl

wrongTarget : I.Transaction
wrongTarget = record
  { target = 1 ; entry = silent ; input = false , tt ; view = initial
  ; execution = finished tt initial [] ; certified = refl }

wrong-target-rejected :
  (step (I.system 0 initial) (init (I.system 0 initial))
    (I.sendEnvelope (I.certifiedEnvelope (I.certifiedDraft wrongTarget I.neutralArtifact))) >>=ᶜ λ next →
      ret (O.publicAnswer (proj₂ next))) ≡ ret (O.submitted I.rejected)
wrong-target-rejected = refl

proofFailureResource : Protocol unitᴵ I.ProofIf
proofFailureResource = record { St = ⊤ ; init = tt ; step = λ _ _ → ret (tt , false) }

proof-failure-projection :
  (step (O.wrapper (request publishInput true) ∘ᵖ (I.bridge 0 initial ∘ᵖ proofFailureResource))
    (nothing , initial , tt) prepare >>=ᶜ λ sr → ret (proj₂ sr)) ≡
    ret (O.provingFailed (publication 1 ∷ []))
proof-failure-projection = refl

verificationFailureResource : Protocol unitᴵ I.ProofIf
verificationFailureResource = record
  { St = ⊤ ; init = tt ; step = λ _ → λ
      { (I.certifyRequest p) → ret (tt , true)
      ; (I.verifyRequest p) → ret (tt , false)
      ; I.invalidVerifyRequest → ret (tt , false) } }

verificationFailureSystem : Protocol unitᴵ (O.PublicAnswer ⇿ Action)
verificationFailureSystem =
  O.wrapper (request silent false) ∘ᵖ (I.bridge 0 initial ∘ᵖ verificationFailureResource)

verification-rejection :
  (step verificationFailureSystem (init verificationFailureSystem) prepare >>=ᶜ λ sr →
    step verificationFailureSystem (proj₁ sr) commit >>=ᶜ λ tr → ret (proj₂ tr)) ≡
    ret (O.admitted I.rejected)
verification-rejection = refl

occupiedResponse : Calls unitᴵ O.PublicAnswer
occupiedResponse = step P (init P) prepare >>=ᶜ λ sr →
  step P (proj₁ sr) prepare >>=ᶜ λ tr → ret (proj₂ tr)
  where P = publicSystem silent false

occupied-projection : occupiedResponse ≡ ret O.occupied
occupied-projection = refl

absent-projection : step (publicSystem silent false) (init (publicSystem silent false)) commit ≡
  ret ((nothing , initial , tt) , O.absentDraft)
absent-projection = refl

invalid-envelope-projection :
  (step (I.system 0 initial) (init (I.system 0 initial)) (I.sendEnvelope I.invalidEnvelope) >>=ᶜ λ sr →
    ret (O.publicAnswer (proj₂ sr))) ≡ ret O.transportInvalid
invalid-envelope-projection = refl

module BP = Programs BL.balanceLedger BL.Assertion
module BObserved = Observed BL.balanceLedger BL.Assertion
module BE = Experiments.Runtime BL.balanceLedger BL.Assertion Balance.balanceContract (λ _ → ℕ) (λ _ n → n)
module BO = BE.PublicProjection (λ _ → ⊤) (λ _ _ → tt)

balanceResponse : ℕ → Calls unitᴵ BO.PublicAnswer
balanceResponse amount = step P (init P) tt >>=ᶜ λ sr → ret (proj₂ sr)
  where
  P = BO.wrapper (λ _ → BE.prepareDraft BL.alice amount BE.neutralArtifact) ∘ᵖ BE.services 0 Balance.initial

operation-failure-projection : balanceResponse 11 ≡ ret
  (BO.failed (BP.operationError BL.insufficientFunds)
    (BObserved.queried (BL.transfer BL.alice 11) (inj₁ BL.insufficientFunds) ∷ []))
operation-failure-projection = refl

empty-assertion-projection : balanceResponse 0 ≡ ret (BO.failed (BP.assertionError BL.emptyTransfer) [])
empty-assertion-projection = refl

publicBooleanBoundary : Bool
publicBooleanBoundary = case deterministic (publicResponse silent false) of λ
  { (just (O.prepared silent tt statement [])) → case deterministic (publicResponse silent true) of λ
      { (just (O.prepared silent tt claim′ [])) → true ; _ → false }
  ; _ → false }

privateRecipientBoundary : Bool
privateRecipientBoundary = case deterministic (recipientResponse echo false) of λ
  { (just (just (echo , false))) → case deterministic (recipientResponse echo true) of λ
      { (just (just (echo , true))) → true ; _ → false }
  ; _ → false }

publicationBoundary : Bool
publicationBoundary = case deterministic (readPublication publishInput true) of λ
  { (just (just true)) → case deterministic (readPublication publishInput false) of λ
      { (just (just false)) → true ; _ → false }
  ; _ → false }

queryBoundary : Bool
queryBoundary = case deterministic (readQuery queryInput true) of λ
  { (just (just true)) → case deterministic (readQuery queryInput false) of λ
      { (just (just false)) → true ; _ → false }
  ; _ → false }

abortBoundary : Bool
abortBoundary = case deterministic (readPublication abortAfter true) of λ
  { (just (just true)) → case deterministic (readQuery abortAfter true) of λ
      { (just (just true)) → true ; _ → false }
  ; _ → false }

publicResultBoundary : Bool
publicResultBoundary = case deterministic (publicResponse publicEcho true) of λ
  { (just (O.prepared publicEcho true statement [])) → case deterministic (publicResponse publicEcho false) of λ
      { (just (O.prepared publicEcho false claim′ [])) → true ; _ → false }
  ; _ → false }

admissionBoundary : Bool
admissionBoundary = case deterministic (admissionResponse silent false) of λ
  { (just (O.admitted I.accepted)) → case deterministic (admissionResponse chainGate false) of λ
      { (just (O.admitted I.rejected)) → true ; _ → false }
  ; _ → false }

operationFailureBoundary : Bool
operationFailureBoundary = case deterministic (balanceResponse 11) of λ
  { (just (BO.failed (BP.operationError BL.insufficientFunds) _)) →
      case deterministic (balanceResponse 0) of λ
        { (just (BO.failed (BP.assertionError BL.emptyTransfer) [])) → true ; _ → false }
  ; _ → false }

proofResourceBoundary : Bool
proofResourceBoundary = case deterministic
  (step (O.wrapper (request publishInput true) ∘ᵖ (I.bridge 0 initial ∘ᵖ proofFailureResource))
    (nothing , initial , tt) prepare >>=ᶜ λ sr → ret (proj₂ sr)) of λ
  { (just (O.provingFailed (publication 1 ∷ []))) → case deterministic
      (step verificationFailureSystem (init verificationFailureSystem) prepare >>=ᶜ λ sr →
        step verificationFailureSystem (proj₁ sr) commit >>=ᶜ λ tr → ret (proj₂ tr)) of λ
      { (just (O.admitted I.rejected)) → true ; _ → false }
  ; _ → false }

transportBoundary : Bool
transportBoundary = case deterministic
  (step (I.system 0 initial) (init (I.system 0 initial))
    (I.sendEnvelope (I.certifiedEnvelope (I.certifiedDraft wrongTarget I.neutralArtifact))) >>=ᶜ λ sr →
      ret (O.publicAnswer (proj₂ sr))) of λ
  { (just (O.submitted I.rejected)) → case deterministic
      (step (I.system 0 initial) (init (I.system 0 initial)) (I.sendEnvelope I.invalidEnvelope) >>=ᶜ λ sr →
        ret (O.publicAnswer (proj₂ sr))) of λ
      { (just O.transportInvalid) → true ; _ → false }
  ; _ → false }

draftBoundary : Bool
draftBoundary = case deterministic occupiedResponse of λ
  { (just O.occupied) → case deterministic (admissionResponse abortAfter true) of λ
      { (just O.absentDraft) → case deterministic
          (step (publicSystem silent false) (init (publicSystem silent false)) commit) of λ
          { (just (_ , O.absentDraft)) → true ; _ → false }
      ; _ → false }
  ; _ → false }

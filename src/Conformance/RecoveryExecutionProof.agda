{-# OPTIONS --safe --without-K #-}

open import Conformance.Primitives

-- Implements RecoveryExecution. The shared successful-run facts below expose
-- guards and exact states/journals; RecoveryAuthorityProof reuses those facts
-- for authority preservation and reset without repeating the circuit analysis.
module Conformance.RecoveryExecutionProof (P : Primitives)
  (self : Primitives.Bytes32 P) where

open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base
open import Data.Maybe.Base using (nothing; just)
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Conformance.AccountLedger P
open import Conformance.Custody P self
open import Conformance.Recovery P self
open import Conformance.RecoveryExecutionDefinitions P self
import Passport.AccountRecovery P self as Account
open Account using (module Chain)
open import Midnight.ContractDSL.Program accountLedger Assertion

open Primitives P
open SubmitArgs

------------------------------------------------------------------------
-- Positive recovery execution
------------------------------------------------------------------------

submission-positive : ∀ s a → SubmissionReady s a →
  eval (submitRecovery a) s ≡ inj₂ (finished tt (submissionState s a) (submissionJournal s a))
submission-positive s a ready
  rewrite SubmissionReady.notPending ready | SubmissionReady.epochMatches ready |
    SubmissionReady.nonceMatches ready | SubmissionReady.recoveryNonidentity ready |
    SubmissionReady.recoveryLargeOrder ready | SubmissionReady.successorNonidentity ready |
    SubmissionReady.successorLargeOrder ready | SubmissionReady.replacementNonidentity ready |
    SubmissionReady.replacementLargeOrder ready | SubmissionReady.commitmentFresh ready |
    SubmissionReady.challengeInField ready | SubmissionReady.recoverySignature ready |
    SubmissionReady.successorSignature ready | SubmissionReady.deadlineFits ready |
    SubmissionReady.roundFits ready = refl

finalisation-positive : ∀ s → FinalisationReady s →
  eval (finaliseRecovery corrected) s ≡ inj₂ (finished tt (finalisationState s) (finalisationJournal s))
finalisation-positive s ready
  rewrite FinalisationReady.hasPending ready | FinalisationReady.successorRecoveryNonidentity ready |
    FinalisationReady.successorRecoveryLargeOrder ready | FinalisationReady.epochFits ready |
    FinalisationReady.nonceFits ready | FinalisationReady.roundFits ready = refl

------------------------------------------------------------------------
-- Shared successful-run facts
------------------------------------------------------------------------

submission-details : ∀ {s a result t j} →
  eval (submitRecovery a) s ≡ inj₂ (finished result t j) →
  SubmissionReady s a × t ≡ submissionState s a × j ≡ submissionJournal s a
submission-details {s} {a} eq with not (pending s) in pend
... | false with eq
...   | ()
submission-details {s} {a} eq | true with expectedEpoch a ≡ᵇ deviceEpoch s in epoch
... | false with eq
...   | ()
submission-details {s} {a} eq | true | true with expectedNonce a ≡ᵇ authNonce s in nonce
... | false with eq
...   | ()
submission-details {s} {a} eq | true | true | true
  with not (does (recoveryPk s ≟ᴾ ecMulG 0)) in rni
... | false with eq
...   | ()
submission-details {s} {a} eq | true | true | true | true
  with not (smallOrder (recoveryPk s)) in rlo
... | false with eq
...   | ()
submission-details {s} {a} eq | true | true | true | true | true
  with not (does (successorPk a ≟ᴾ ecMulG 0)) in sni
... | false with eq
...   | ()
submission-details {s} {a} eq | true | true | true | true | true | true
  with not (smallOrder (successorPk a)) in slo
... | false with eq
...   | ()
submission-details {s} {a} eq | true | true | true | true | true | true | true
  with not (does (successorRecoveryPk a ≟ᴾ ecMulG 0)) in nni
... | false with eq
...   | ()
submission-details {s} {a} eq | true | true | true | true | true | true | true | true
  with not (smallOrder (successorRecoveryPk a)) in nlo
... | false with eq
...   | ()
submission-details {s} {a} eq | true | true | true | true | true | true | true | true | true
  with not (does (successorRecoveryPk a ≟ᴾ recoveryPk s)) in fresh
... | false with eq
...   | ()
submission-details {s} {a} eq | true | true | true | true | true | true | true | true | true | true
  with le (submissionChallenge s a) <ᵇ fieldOrder in fieldRoom
... | false with eq
...   | ()
submission-details {s} {a} eq | true | true | true | true | true | true | true | true | true | true | true
  with verifies (sigRRecovery a) (sigSRecovery a) (recoveryPk s) (submissionChallenge s a) in rsig
... | false with eq
...   | ()
submission-details {s} {a} eq | true | true | true | true | true | true | true | true | true | true | true | true
  with verifies (sigRSuccessor a) (sigSSuccessor a) (successorPk a) (submissionChallenge s a) in ssig
... | false with eq
...   | ()
submission-details {s} {a} eq | true | true | true | true | true | true | true | true | true | true | true | true | true
  with nowUpper a + vetoWindow s <ᵇ uint64 in deadline
... | false with eq
...   | ()
submission-details {s} {a} eq | true | true | true | true | true | true | true | true | true | true | true | true | true | true
  with suc (round s) <ᵇ uint64 in roundRoom
... | false with eq
...   | ()
submission-details refl | true | true | true | true | true | true | true | true | true | true | true | true | true | true | true =
  record { notPending = pend ; epochMatches = epoch ; nonceMatches = nonce
         ; recoveryNonidentity = rni ; recoveryLargeOrder = rlo
         ; successorNonidentity = sni ; successorLargeOrder = slo
         ; replacementNonidentity = nni ; replacementLargeOrder = nlo
         ; commitmentFresh = fresh ; challengeInField = fieldRoom
         ; recoverySignature = rsig ; successorSignature = ssig
         ; deadlineFits = deadline ; roundFits = roundRoom } , refl , refl

submission-shape : ∀ {s a result t j} →
  eval (submitRecovery a) s ≡ inj₂ (finished result t j) →
  t ≡ submissionState s a × j ≡ submissionJournal s a
submission-shape {s} {a} ev = proj₂ (submission-details {s = s} {a = a} ev)

finalisation-details : ∀ {s result t j} →
  eval (finaliseRecovery corrected) s ≡ inj₂ (finished result t j) →
  FinalisationReady s × t ≡ finalisationState s × j ≡ finalisationJournal s
finalisation-details {s} eq with pending s in pend
... | false with eq
...   | ()
finalisation-details {s} eq | true with not (does (pendingRecoveryPk s ≟ᴾ ecMulG 0)) in live
... | false with eq
...   | ()
finalisation-details {s} eq | true | true with not (smallOrder (pendingRecoveryPk s)) in order
... | false with eq
...   | ()
finalisation-details {s} eq | true | true | true with suc (deviceEpoch s) <ᵇ uint32 in epoch
... | false with eq
...   | ()
finalisation-details {s} eq | true | true | true | true with suc (authNonce s) <ᵇ uint64 in nonce
... | false with eq
...   | ()
finalisation-details {s} eq | true | true | true | true | true with suc (round s) <ᵇ uint64 in round
... | false with eq
...   | ()
finalisation-details refl | true | true | true | true | true | true =
  record { hasPending = pend ; successorRecoveryNonidentity = live
         ; successorRecoveryLargeOrder = order ; epochFits = epoch
         ; nonceFits = nonce ; roundFits = round } , refl , refl

finalisation-shape : ∀ {s result t j} →
  eval (finaliseRecovery corrected) s ≡ inj₂ (finished result t j) →
  t ≡ finalisationState s × j ≡ finalisationJournal s
finalisation-shape ev = proj₂ (finalisation-details ev)

authorisation-details : ∀ a challenge {s result t j} →
  eval (authorise a challenge) s ≡ inj₂ (finished result t j) →
  deviceEntry self (pk a) (deviceEpoch s) (useCounter a) ∈ᵇ devices s ≡ true ×
  t ≡ authorisationState s a × j ≡ authorisationJournal s a
authorisation-details a challenge {s} eq with not (smallOrder (pk a))
... | false with eq
...   | ()
authorisation-details a challenge {s} eq | true
  with deviceEntry self (pk a) (deviceEpoch s) (useCounter a) ∈ᵇ devices s in known
... | false with eq
...   | ()
authorisation-details a challenge {s} eq | true | true
  with le (challenge (sigR a) (pk a) (authNonce s) (grind a)) <ᵇ fieldOrder
... | false with eq
...   | ()
authorisation-details a challenge {s} eq | true | true | true
  with verifies (sigR a) (sigS a) (pk a) (challenge (sigR a) (pk a) (authNonce s) (grind a))
... | false with eq
...   | ()
authorisation-details a challenge {s} eq | true | true | true | true
  with suc (authNonce s) <ᵇ uint64
... | false with eq
...   | ()
authorisation-details a challenge {s} eq | true | true | true | true | true
  with suc (round s) <ᵇ uint64
... | false with eq
...   | ()
authorisation-details a challenge refl | true | true | true | true | true | true = refl , refl , refl

------------------------------------------------------------------------
-- Admission and deadline conditions
------------------------------------------------------------------------

submission-eligible : ∀ ctx s a → holds (timeAtMost (nowUpper a)) ctx ≡ true →
  Eligible ctx (submissionJournal s a)
submission-eligible ctx s a onTime = onTime , tt

finalisation-eligible : ∀ ctx s → holds (timeAtLeast (pendingNotBefore s)) ctx ≡ true →
  Eligible ctx (finalisationJournal s)
finalisation-eligible ctx s mature = mature , tt

submission-admission : ∀ now s a (ready : SubmissionReady s a) →
  holds (timeAtMost (nowUpper a)) (context 0 now) ≡ true →
  Chain.admission (context 0 now) s
    (Chain.makeTx Account.recoverSubmit a tt 0 s tt (submissionState s a)
      (submissionJournal s a) (submission-positive s a ready)) ≡ (submissionState s a , Chain.accepted)
submission-admission now s a ready onTime =
  Chain.makeTx-admitted Account.recoverSubmit a tt 0 s tt (submissionState s a)
    (submissionJournal s a) (submission-positive s a ready) (context 0 now)
    (submission-eligible (context 0 now) s a onTime) refl

finalisation-admission : ∀ now s (ready : FinalisationReady s) →
  holds (timeAtLeast (pendingNotBefore s)) (context 0 now) ≡ true →
  Chain.admission (context 0 now) s
    (Chain.makeTx Account.recoverFinalise tt tt 0 s tt (finalisationState s)
      (finalisationJournal s) (finalisation-positive s ready)) ≡ (finalisationState s , Chain.accepted)
finalisation-admission now s ready mature =
  Chain.makeTx-admitted Account.recoverFinalise tt tt 0 s tt (finalisationState s)
    (finalisationJournal s) (finalisation-positive s ready) (context 0 now)
    (finalisation-eligible (context 0 now) s mature) refl


submission-deadline : ∀ ctx s a t → replay ctx (submissionJournal s a) s ≡ just t →
  holds (timeAtMost (nowUpper a)) ctx ≡ true
submission-deadline ctx s a t rp = proj₁ (replay-eligible ctx (submissionJournal s a) s rp)

finalisation-deadline : ∀ ctx s t → replay ctx (finalisationJournal s) s ≡ just t →
  holds (timeAtLeast (pendingNotBefore s)) ctx ≡ true
finalisation-deadline ctx s t rp = proj₁ (replay-eligible ctx (finalisationJournal s) s rp)

accepted-submission-deadline : ∀ ctx tx {s t}
  (isSubmission : Chain.Statement.name (Chain.Tx.claim tx) ≡ Account.recoverSubmit) →
  Chain.admission ctx s tx ≡ (t , Chain.accepted) →
  holds (timeAtMost (nowUpper
    (subst Account.Input isSubmission (Chain.Statement.publicInputs (Chain.Tx.claim tx))))) ctx ≡ true
accepted-submission-deadline ctx tx@(Chain.transaction
  (Chain.statement acc Account.recoverSubmit a binding j) proof) {s} refl admitted
  with Chain.accepted-refinement ctx s tx admitted
... | e , (refl , relation) , evaluated with submission-shape {s = s} {a = a} evaluated
...   | shape , refl = proj₁ (Chain.accepted-conditions ctx s tx admitted)

accepted-finalisation-deadline : ∀ ctx tx {s t}
  (isFinalisation : Chain.Statement.name (Chain.Tx.claim tx) ≡ Account.recoverFinalise) →
  Chain.admission ctx s tx ≡ (t , Chain.accepted) →
  holds (timeAtLeast (pendingNotBefore s)) ctx ≡ true
accepted-finalisation-deadline ctx tx@(Chain.transaction
  (Chain.statement acc Account.recoverFinalise tt binding j) proof) {s} refl admitted
  with Chain.accepted-refinement ctx s tx admitted
... | Chain.evidence view tt tt tt opening , relation , evaluated
  with finalisation-shape evaluated
...   | shape , refl = proj₁ (Chain.accepted-conditions ctx s tx admitted)

------------------------------------------------------------------------
-- Cancellation and guard rejection
------------------------------------------------------------------------

cancellationState : State → State
cancellationState s = record s
  { pending = false ; pendingEntry = zero32 ; pendingRecoveryPk = ecMulG 0 ; pendingNotBefore = 0 }

cancellation-shape : ∀ {s result t j} → eval doCancel s ≡ inj₂ (finished result t j) →
  t ≡ cancellationState s
cancellation-shape {s} eq with pending s
... | false with eq
...   | ()
cancellation-shape refl | true = refl

already-pending-rejected : ∀ s a → pending s ≡ true →
  eval (submitRecovery a) s ≡ inj₁ (assertionError alreadyPending)
already-pending-rejected s a pend rewrite pend = refl

stale-epoch-rejected : ∀ s a → pending s ≡ false →
  (expectedEpoch a ≡ᵇ deviceEpoch s) ≡ false →
  eval (submitRecovery a) s ≡ inj₁ (assertionError staleEpoch)
stale-epoch-rejected s a pend stale rewrite pend | stale = refl

stale-nonce-rejected : ∀ s a → pending s ≡ false →
  (expectedEpoch a ≡ᵇ deviceEpoch s) ≡ true → (expectedNonce a ≡ᵇ authNonce s) ≡ false →
  eval (submitRecovery a) s ≡ inj₁ (assertionError staleNonce)
stale-nonce-rejected s a pend epoch stale rewrite pend | epoch | stale = refl

no-pending-finalisation-rejected : ∀ s → pending s ≡ false →
  eval (finaliseRecovery corrected) s ≡ inj₁ (assertionError noPending)
no-pending-finalisation-rejected s pend rewrite pend = refl


gated-cancellation-clears : ∀ {s a result t j} →
  eval (Account.circuit corrected (Account.jubjub Account.recoverCancel) (tt , a)) s
    ≡ inj₂ (finished result t j) →
  pending t ≡ false × pendingEntry t ≡ zero32 × pendingNotBefore t ≡ 0
gated-cancellation-clears {a = a} ev
  with bind-success (authorise a (Account.challengeOf Account.recoverCancel tt)) (λ _ → doCancel) _ ev
... | head , js , headEval , tail , joined with cancellation-shape tail
...   | refl = refl , refl , refl

cancelled-finalisation-rejected : ∀ {s a result t j} →
  eval (Account.circuit corrected (Account.jubjub Account.recoverCancel) (tt , a)) s
    ≡ inj₂ (finished result t j) →
  eval (finaliseRecovery corrected) t ≡ inj₁ (assertionError noPending)
cancelled-finalisation-rejected ev = no-pending-finalisation-rejected _ (proj₁ (gated-cancellation-clears ev))

------------------------------------------------------------------------
-- Recovery composition and ordinary rotation
------------------------------------------------------------------------

recovery-positive : ∀ s a → SubmissionReady s a → FinalisationReady (submissionState s a) →
  Σ State (λ t → Σ Journal (λ submitJournal → Σ Journal (λ finaliseJournal →
    eval (submitRecovery a) s ≡ inj₂ (finished tt (submissionState s a) submitJournal) ×
    eval (finaliseRecovery corrected) (submissionState s a) ≡ inj₂ (finished tt t finaliseJournal) ×
    devices t ≡ deviceEntry self (successorPk a) (suc (deviceEpoch s)) 0 ∷ [] × pending t ≡ false)))
recovery-positive s a submitReady finaliseReady =
  finalisationState (submissionState s a) , submissionJournal s a , finalisationJournal (submissionState s a) ,
  submission-positive s a submitReady , finalisation-positive (submissionState s a) finaliseReady , refl , refl

submission-replay-rejected : ∀ s a →
  eval (submitRecovery a) (submissionState s a) ≡ inj₁ (assertionError alreadyPending)
submission-replay-rejected s a = refl

finalisation-replay-rejected : ∀ s →
  eval (finaliseRecovery corrected) (finalisationState s) ≡ inj₁ (assertionError noPending)
finalisation-replay-rejected s = refl

self-member : ∀ e → e ∈ᵇ (e ∷ []) ≡ true
self-member e with e ≟ᴮ e
... | yes _ = refl
... | no different = Data.Empty.⊥-elim (different refl)

successor-authority : ∀ s a →
  deviceEntry self (successorPk a) (deviceEpoch (finalisationState (submissionState s a))) 0
    ∈ᵇ devices (finalisationState (submissionState s a)) ≡ true
successor-authority s a = self-member _

rotation-positive : ∀ s k a → RotationReady s k a →
  eval (Account.circuit corrected (Account.jubjub Account.rotateEncKey) (k , a)) s ≡
    inj₂ (finished tt (rotationState s k a) (rotationJournal s k a))
rotation-positive s k a ready
  rewrite RotationReady.liveSigner ready | RotationReady.knownSigner ready |
    RotationReady.challengeInField ready | RotationReady.signatureValid ready |
    RotationReady.nonceFits ready | RotationReady.roundFits ready = refl

rotation-admission : ∀ now s k a (ready : RotationReady s k a) →
  Chain.admission (context 0 now) s
    (Chain.makeTx (Account.jubjub Account.rotateEncKey) (k , a) tt 0 s tt (rotationState s k a)
      (rotationJournal s k a) (rotation-positive s k a ready)) ≡ (rotationState s k a , Chain.accepted)
rotation-admission now s k a ready =
  Chain.makeTx-admitted (Account.jubjub Account.rotateEncKey) (k , a) tt 0 s tt
    (rotationState s k a) (rotationJournal s k a) (rotation-positive s k a ready)
    (context 0 now) tt refl

rejection-is-atomic : ∀ ctx s tx {t} → Chain.admission ctx s tx ≡ (t , Chain.rejected) → t ≡ s
rejection-is-atomic ctx s tx = Chain.rejection-atomic ctx s tx (Chain.verified tx)

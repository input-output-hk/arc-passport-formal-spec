{-# OPTIONS --safe --without-K #-}

open import Conformance.Primitives

-- Guard-premised evaluation, admission, provenance and rejection properties.
-- Definitions: RecoveryExecutionDefinitions; proofs: RecoveryExecutionProof.
-- Program.eval constructs a working state/journal; Contract.admit replays the
-- certified journal at the current state and submission time, enforcing deadlines.
-- Assumptions and limits: docs/conformance-recovery.md#checked-formal-scope
-- and #ledger-primitive-boundary (including concrete-width guards).
module Conformance.RecoveryExecution (P : Primitives)
  (self : Primitives.Bytes32 P) where

open import Data.Bool.Base
open import Data.List.Base
open import Data.Maybe.Base using (just)
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

open import Conformance.AccountLedger P
open import Conformance.Custody P self
open import Conformance.Recovery P self
open import Conformance.RecoveryExecutionDefinitions P self
import Passport.AccountRecovery P self as Account
open Account using (module Chain)
import Conformance.RecoveryExecutionProof P self as Proof
open import Midnight.ContractDSL.Program accountLedger Assertion

open Primitives P
open SubmitArgs

positive-submission : ∀ s a → SubmissionReady s a →
  eval (submitRecovery a) s ≡ inj₂ (finished tt (submissionState s a) (submissionJournal s a))
positive-submission = Proof.submission-positive

positive-finalisation : ∀ s → FinalisationReady s →
  eval (finaliseRecovery corrected) s ≡ inj₂ (finished tt (finalisationState s) (finalisationJournal s))
positive-finalisation = Proof.finalisation-positive

positive-recovery : ∀ s a → SubmissionReady s a → FinalisationReady (submissionState s a) →
  Σ State (λ t → Σ Journal (λ submitJournal → Σ Journal (λ finaliseJournal →
    eval (submitRecovery a) s ≡ inj₂ (finished tt (submissionState s a) submitJournal) ×
    eval (finaliseRecovery corrected) (submissionState s a) ≡ inj₂ (finished tt t finaliseJournal) ×
    devices t ≡ deviceEntry self (successorPk a) (suc (deviceEpoch s)) 0 ∷ [] × pending t ≡ false)))
positive-recovery = Proof.recovery-positive

submission-provenance : ∀ {s a result t j} →
  eval (submitRecovery a) s ≡ inj₂ (finished result t j) →
  SubmissionReady s a × t ≡ submissionState s a × j ≡ submissionJournal s a
submission-provenance = Proof.submission-details

finalisation-provenance : ∀ {s result t j} →
  eval (finaliseRecovery corrected) s ≡ inj₂ (finished result t j) →
  t ≡ finalisationState s × j ≡ finalisationJournal s
finalisation-provenance = Proof.finalisation-shape

-- Certified transactions retain their actual build view and successful execution.
-- Admission independently replays against the current state.

submission-commits : ∀ now s a (ready : SubmissionReady s a) →
  holds (timeAtMost (nowUpper a)) now ≡ true →
  Chain.admit s (Chain.submit now
    (submissionTransaction s a (positive-submission s a ready))) ≡ (submissionState s a , Chain.accepted)
submission-commits = Proof.submission-admission

finalisation-commits : ∀ now s (ready : FinalisationReady s) →
  holds (timeAtLeast (pendingNotBefore s)) now ≡ true →
  Chain.admit s (Chain.submit now
    (finalisationTransaction s (positive-finalisation s ready))) ≡ (finalisationState s , Chain.accepted)
finalisation-commits = Proof.finalisation-admission

submission-deadline : ∀ ctx s a t → replay ctx (submissionJournal s a) s ≡ just t →
  holds (timeAtMost (nowUpper a)) ctx ≡ true
submission-deadline = Proof.submission-deadline

finalisation-deadline : ∀ ctx s t → replay ctx (finalisationJournal s) s ≡ just t →
  holds (timeAtLeast (pendingNotBefore s)) ctx ≡ true
finalisation-deadline = Proof.finalisation-deadline

-- Entry equality transports the certified transaction's dependent input.
-- The current admission state can differ from the transaction's build view.
accepted-submission-deadline : ∀ now tx {s t}
  (isSubmission : Chain.Transaction.entry tx ≡ Account.recoverSubmit) →
  Chain.admit s (Chain.submit now tx) ≡ (t , Chain.accepted) →
  holds (timeAtMost (nowUpper
    (subst Account.Input isSubmission (Chain.Transaction.input tx)))) now ≡ true
accepted-submission-deadline = Proof.accepted-submission-deadline

accepted-finalisation-deadline : ∀ now tx {s t}
  (isFinalisation : Chain.Transaction.entry tx ≡ Account.recoverFinalise) →
  Chain.admit s (Chain.submit now tx) ≡ (t , Chain.accepted) →
  holds (timeAtLeast (pendingNotBefore s)) now ≡ true
accepted-finalisation-deadline = Proof.accepted-finalisation-deadline

cancellation-clears : ∀ {s a result t j} →
  eval (Account.circuit corrected (Account.jubjub Account.recoverCancel) (tt , a)) s
    ≡ inj₂ (finished result t j) →
  pending t ≡ false × pendingEntry t ≡ zero32 × pendingNotBefore t ≡ 0
cancellation-clears = Proof.gated-cancellation-clears

cancelled-finalisation-rejected : ∀ {s a result t j} →
  eval (Account.circuit corrected (Account.jubjub Account.recoverCancel) (tt , a)) s
    ≡ inj₂ (finished result t j) →
  eval (finaliseRecovery corrected) t ≡ inj₁ (assertionError noPending)
cancelled-finalisation-rejected = Proof.cancelled-finalisation-rejected

pending-submission-rejected : ∀ s a → pending s ≡ true →
  eval (submitRecovery a) s ≡ inj₁ (assertionError alreadyPending)
pending-submission-rejected = Proof.already-pending-rejected

stale-epoch-rejected : ∀ s a → pending s ≡ false →
  (expectedEpoch a ≡ᵇ deviceEpoch s) ≡ false →
  eval (submitRecovery a) s ≡ inj₁ (assertionError staleEpoch)
stale-epoch-rejected = Proof.stale-epoch-rejected

stale-nonce-rejected : ∀ s a → pending s ≡ false →
  (expectedEpoch a ≡ᵇ deviceEpoch s) ≡ true → (expectedNonce a ≡ᵇ authNonce s) ≡ false →
  eval (submitRecovery a) s ≡ inj₁ (assertionError staleNonce)
stale-nonce-rejected = Proof.stale-nonce-rejected

rejection-is-atomic : ∀ now s tx {t} → Chain.admit s (Chain.submit now tx) ≡ (t , Chain.rejected) → t ≡ s
rejection-is-atomic = Proof.rejection-is-atomic

submission-replay-rejected : ∀ s a →
  eval (submitRecovery a) (submissionState s a) ≡ inj₁ (assertionError alreadyPending)
submission-replay-rejected = Proof.submission-replay-rejected

finalisation-replay-rejected : ∀ s →
  eval (finaliseRecovery corrected) (finalisationState s) ≡ inj₁ (assertionError noPending)
finalisation-replay-rejected = Proof.finalisation-replay-rejected

successor-authority : ∀ s a →
  deviceEntry self (successorPk a) (deviceEpoch (finalisationState (submissionState s a))) 0
    ∈ᵇ devices (finalisationState (submissionState s a)) ≡ true
successor-authority = Proof.successor-authority

positive-rotation : ∀ s k a → RotationReady s k a →
  eval (Account.circuit corrected (Account.jubjub Account.rotateEncKey) (k , a)) s ≡
    inj₂ (finished tt (rotationState s k a) (rotationJournal s k a))
positive-rotation = Proof.rotation-positive

rotation-commits : ∀ now s k a (ready : RotationReady s k a) →
  Chain.admit s (Chain.submit now
    (rotationTransaction s k a (positive-rotation s k a ready))) ≡ (rotationState s k a , Chain.accepted)
rotation-commits = Proof.rotation-admission

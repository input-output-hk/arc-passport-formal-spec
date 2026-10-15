{-# OPTIONS --safe --without-K #-}

open import Conformance.Primitives

-- Definitions: RecoveryExecutionDefinitions contains SubmissionReady,
-- FinalisationReady, RotationReady, and the exact state/journal functions.
-- Proofs: RecoveryExecutionProof; this file presents their explicit types.
-- Reading route: Passport.AccountRecovery.contract, then its unrestricted
-- Chain.Admissions; the circuit bodies and authorisation seam are in
-- Recovery and Custody. Program.eval constructs a working state/journal without
-- enforcing chain deadlines; Protocol.Interpreter.admission verifies
-- the certificate and atomically replays its journal against the current state,
-- checking chain conditions. The makeTx argument slots are explained below.
-- Chain's account identity is 0, so admission uses `context 0 now`.
-- The separate `0` argument to makeTx is the commitment opening.
-- Readiness records expose model guards. RotationReady additionally retains
-- the concrete counterFits premise; the omitted submission post_epoch cast
-- instead remains a prose caveat (conformance-recovery.md#ledger-primitive-boundary).
-- Positive execution requires readiness; admission also requires chain deadlines.
-- Signature equations are checked, but unforgeability, challenge collision
-- resistance, signer ownership and primitive correspondence remain external.
-- Exact journal/state provenance below is for actual account DSL evaluation and
-- Interpreter replay. Concrete circuit correspondence is executable evidence,
-- not a verified compiler/deployment refinement. No grant claim is made.
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

-- makeTx name input tt 0 s tt post journal evidence uses the unit circuit
-- witness, opening 0, build-view/prestate s, and unit result tt. Its final
-- slots give the computed poststate, ordered journal, and evaluation evidence.
-- The separate admission call replays that certificate against current state s.

submission-commits : ∀ now s a (ready : SubmissionReady s a) →
  holds (timeAtMost (nowUpper a)) (context 0 now) ≡ true →
  Chain.admission (context 0 now) s
    (Chain.makeTx Account.recoverSubmit a tt 0 s tt (submissionState s a)
      (submissionJournal s a) (positive-submission s a ready)) ≡ (submissionState s a , Chain.accepted)
submission-commits = Proof.submission-admission

finalisation-commits : ∀ now s (ready : FinalisationReady s) →
  holds (timeAtLeast (pendingNotBefore s)) (context 0 now) ≡ true →
  Chain.admission (context 0 now) s
    (Chain.makeTx Account.recoverFinalise tt tt 0 s tt (finalisationState s)
      (finalisationJournal s) (positive-finalisation s ready)) ≡ (finalisationState s , Chain.accepted)
finalisation-commits = Proof.finalisation-admission

submission-deadline : ∀ ctx s a t → replay ctx (submissionJournal s a) s ≡ just t →
  holds (timeAtMost (nowUpper a)) ctx ≡ true
submission-deadline = Proof.submission-deadline

finalisation-deadline : ∀ ctx s t → replay ctx (finalisationJournal s) s ≡ just t →
  holds (timeAtLeast (pendingNotBefore s)) ctx ≡ true
finalisation-deadline = Proof.finalisation-deadline

-- The claim's publicInputs is the circuit input record; subst transports it
-- to SubmitArgs using isSubmission. Here s is the admission state; the
-- transaction's build view may differ. Neither claim assumes a given journal.
accepted-submission-deadline : ∀ ctx tx {s t}
  (isSubmission : Chain.Statement.name (Chain.Tx.claim tx) ≡ Account.recoverSubmit) →
  Chain.admission ctx s tx ≡ (t , Chain.accepted) →
  holds (timeAtMost (nowUpper
    (subst Account.Input isSubmission (Chain.Statement.publicInputs (Chain.Tx.claim tx))))) ctx ≡ true
accepted-submission-deadline = Proof.accepted-submission-deadline

accepted-finalisation-deadline : ∀ ctx tx {s t}
  (isFinalisation : Chain.Statement.name (Chain.Tx.claim tx) ≡ Account.recoverFinalise) →
  Chain.admission ctx s tx ≡ (t , Chain.accepted) →
  holds (timeAtLeast (pendingNotBefore s)) ctx ≡ true
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

rejection-is-atomic : ∀ ctx s tx {t} → Chain.admission ctx s tx ≡ (t , Chain.rejected) → t ≡ s
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
  Chain.admission (context 0 now) s
    (Chain.makeTx (Account.jubjub Account.rotateEncKey) (k , a) tt 0 s tt (rotationState s k a)
      (rotationJournal s k a) (positive-rotation s k a ready)) ≡ (rotationState s k a , Chain.accepted)
rotation-commits = Proof.rotation-admission

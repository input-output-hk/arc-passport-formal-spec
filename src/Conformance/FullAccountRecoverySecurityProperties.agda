{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

-- Contract-level P5′ obligations, each for one full-account execution: what an
-- accepted recover_submit verified and installed, what an accepted
-- recover_finalise enacted, recover_cancel and recovery publication, and how
-- every entrypoint affects the pending record. A finalise guard alone does not
-- show where a pending record came from. provenance-step and empty-provenance
-- keep every flagged record matched, cell for cell, to the result of some
-- witnessed accepting submission computation; finalise-enacts-submission then
-- equates the enacted record with that one. This is endpoint matching, not a
-- history occurrence or an unchanged-since claim: those are established over
-- deployment-rooted traces in Passport.AccountSecurityProperties. Local source
-- execution only: no ledger adoption, cryptographic law (P is uninterpreted),
-- guardian consent, quorum honesty, or timely cancellation by a live device.
-- Definitions: FullAccountRecoverySecurity; proofs: ...RecoverySecurityProof.
module Conformance.FullAccountRecoverySecurityProperties (P : Primitives) where

import Conformance.FullAccount as Model
open import Conformance.FullAccountBody P using (body; cancelRecovery; publishRecovery; submit; finalise)
open import Conformance.FullAccountRecoverySecurity P
import Conformance.FullAccountRecoverySecurityProof P as Proof
open import Data.Bool.Base using (true; false)
open import Data.List.Base using ([])
open import Data.Nat.Base using (_<_)
open import Data.Product.Base using (∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open Model.AccountSemantics P using (execute)

------------------------------------------------------------------------
-- Submission (I-5′.1)

-- The configured recovery key and the successor key both verified on one
-- digest of the exact request, at the stored epoch and nonce and before the
-- signed time bound; the pending record was then installed.
submit-evidence : ∀ ctx xs {s v t es} → submit ctx xs s ≡ accepted v t es → Submission.Evidence ctx xs s t
submit-evidence = Proof.submit-evidence

submit-refused-while-pending : ∀ ctx xs {s p} → Stores s "pending_recovery" p → flag p ≡ true →
  ∃ λ error → submit ctx xs s ≡ rejected error
submit-refused-while-pending = Proof.submit-refused-while-pending

------------------------------------------------------------------------
-- Finalisation (I-5′.2), verifying no signature

-- The record pending at s, after its veto window, became the device set and
-- recovery key, and the pending record was cleared.
finalise-evidence : ∀ ctx {s v t es} → finalise ctx s ≡ accepted v t es → Finalisation.Evidence ctx s t
finalise-evidence = Proof.finalise-evidence

finalise-refused-without-pending : ∀ ctx {s p} → Stores s "pending_recovery" p → flag p ≡ false →
  ∃ λ error → finalise ctx s ≡ rejected error
finalise-refused-without-pending = Proof.finalise-refused-without-pending

finalise-refused-before-deadline : ∀ ctx {s d} → Stores s "pending_not_before" d → blockTime ctx < number d →
  ∃ λ error → finalise ctx s ≡ rejected error
finalise-refused-before-deadline = Proof.finalise-refused-before-deadline

------------------------------------------------------------------------
-- Device-authorised operation bodies touching recovery

cancel-evidence : ∀ ctx xs coin e {s v t es} → body cancelRecovery ctx xs coin e s ≡ accepted v t es →
  Cancellation s t
cancel-evidence = Proof.cancel-evidence

publish-evidence : ∀ ctx xs coin e {s v t es} → body publishRecovery ctx xs coin e s ≡ accepted v t es →
  Publication.Evidence xs s t
publish-evidence = Proof.publish-evidence

publish-refused-while-pending : ∀ ctx xs coin e {s p} → Stores s "pending_recovery" p → flag p ≡ true →
  ∃ λ error → body publishRecovery ctx xs coin e s ≡ rejected error
publish-refused-while-pending = Proof.publish-refused-while-pending

------------------------------------------------------------------------
-- The pending record across all entrypoints

-- Submission installs; finalisation and cancellation clear; constructor
-- execution initializes the flag to false; other accepted executions keep it.
-- This covers execute's internal enumeration, including grant operations the
-- public dispatcher never exposes. AccountSecurity restricts calls to that table.
pending-effect : ∀ e ctx xs {s v t es} → execute e ctx xs s ≡ accepted v t es → PendingEffect e ctx xs s t
pending-effect = Proof.pending-effect

-- The empty pre-deployment ledger has no pending record.
empty-provenance : PendingProvenance (state [])
empty-provenance = Proof.empty-provenance

provenance-step : ∀ e ctx xs {s v t es} → execute e ctx xs s ≡ accepted v t es →
  PendingProvenance s → PendingProvenance t
provenance-step = Proof.provenance-step

-- Under provenance, finalisation enacts exactly the successor entry, next
-- recovery key and deadline installed by the witnessed submission computation
-- that s's pending record matches.
finalise-enacts-submission : ∀ ctx {s v t es} → PendingProvenance s → finalise ctx s ≡ accepted v t es →
  EnactsSubmission ctx s t
finalise-enacts-submission = Proof.finalise-enacts-submission

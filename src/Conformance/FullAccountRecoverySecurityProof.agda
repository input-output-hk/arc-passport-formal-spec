{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

-- Guard refutations and endpoint provenance. Execution decomposition lives in
-- FullAccountRecoverySecurityStages; all-entrypoint pending frames live in
-- FullAccountRecoverySecurityPendingProof.
module Conformance.FullAccountRecoverySecurityProof (P : Primitives) where

import Conformance.FullAccount as Model
open import Conformance.FullAccountBody P
open import Conformance.FullAccountExecution using (run)
open import Conformance.FullAccountRecoverySecurity P
open import Conformance.FullAccountRecoverySecurityHelpers P
import Conformance.FullAccountRecoverySecurityStages P as Stages
import Conformance.FullAccountRecoverySecurityPendingProof P as PendingProof
open import Data.Bool.Base using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using ([])
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (_<_; _≤_)
open import Data.Nat.Properties using (<⇒≱)
open import Data.Product.Base using (∃)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open Model.AccountSemantics P using (construct; activation; device; grant;
  depositPublic; depositPrivate; submitRecovery; finaliseRecovery; execute)


------------------------------------------------------------------------
-- recover_submit


abstract
  submit-evidence : ∀ ctx xs {s v t es} → submit ctx xs s ≡ accepted v t es → Submission.Evidence ctx xs s t
  submit-evidence ctx xs ok = Stages.SubmitRun.evidence ctx xs (run _ ok)

submit-refused-while-pending : ∀ ctx xs {s p} → Stores s "pending_recovery" p → flag p ≡ true →
  ∃ λ error → submit ctx xs s ≡ rejected error
submit-refused-while-pending ctx xs {s} {p} cell flagged =
  refused (submit ctx xs s) λ ran →
  let evidence = submit-evidence ctx xs {s = s} ran
  in true≢false
    (trans (sym flagged) (trans (cong flag (stores-unique cell (Submission.Evidence.idle evidence)))
      (Submission.Evidence.notPending evidence)))

------------------------------------------------------------------------
-- recover_finalise


abstract
  finalise-evidence : ∀ ctx {s v t es} → finalise ctx s ≡ accepted v t es → Finalisation.Evidence ctx s t
  finalise-evidence ctx ok = Stages.FinaliseRun.evidence ctx (run _ ok)

finalise-refused-without-pending : ∀ ctx {s p} → Stores s "pending_recovery" p → flag p ≡ false →
  ∃ λ error → finalise ctx s ≡ rejected error
finalise-refused-without-pending ctx {s} {p} cell idle =
  refused (finalise ctx s) λ ran →
  let evidence = finalise-evidence ctx {s = s} ran
  in true≢false
    (trans (sym (Finalisation.Evidence.isPending evidence))
      (trans (cong flag (stores-unique (Finalisation.Evidence.pending evidence) cell)) idle))

finalise-refused-before-deadline : ∀ ctx {s d} → Stores s "pending_not_before" d → blockTime ctx < number d →
  ∃ λ error → finalise ctx s ≡ rejected error
finalise-refused-before-deadline ctx {s} {d} cell early =
  refused (finalise ctx s) λ ran →
  let evidence = finalise-evidence ctx {s = s} ran
  in <⇒≱ early
    (subst (λ w → number w ≤ blockTime ctx) (stores-unique (Finalisation.Evidence.deadlineCell evidence) cell)
      (Finalisation.Evidence.windowElapsed evidence))

------------------------------------------------------------------------
-- recover_cancel and publish_recovery_session bodies


cancel-evidence : ∀ ctx xs coin e {s v t es} → body cancelRecovery ctx xs coin e s ≡ accepted v t es →
  Cancellation s t
cancel-evidence ctx xs coin e ok = Stages.OperationRun.cancel-body (run _ ok)

publish-evidence : ∀ ctx xs coin e {s v t es} → body publishRecovery ctx xs coin e s ≡ accepted v t es →
  Publication.Evidence xs s t
publish-evidence ctx xs coin e ok = Stages.OperationRun.publish-body ctx xs coin e (run _ ok)

publish-refused-while-pending : ∀ ctx xs coin e {s p} → Stores s "pending_recovery" p → flag p ≡ true →
  ∃ λ error → body publishRecovery ctx xs coin e s ≡ rejected error
publish-refused-while-pending ctx xs coin e {s} {p} cell flagged =
  refused (body publishRecovery ctx xs coin e s) λ ran →
  let evidence = publish-evidence ctx xs coin e {s = s} ran
  in true≢false
    (trans (sym flagged) (trans (cong flag (stores-unique cell (Publication.Evidence.idle evidence)))
      (Publication.Evidence.notPending evidence)))

------------------------------------------------------------------------
-- Pending-record effect of every entrypoint

pending-effect : ∀ e ctx xs {s v t es} → execute e ctx xs s ≡ accepted v t es → PendingEffect e ctx xs s t
pending-effect = PendingProof.pending-effect

------------------------------------------------------------------------
-- Provenance of the pending record

private
  cleared-provenance : ∀ {t} → Stores t "pending_recovery" (bool false) → PendingProvenance t
  cleared-provenance cleared cell flagged =
    ⊥-elim (true≢false (sym (trans (cong flag (stores-unique cleared cell)) flagged)))

  kept-provenance : ∀ {s t} → SamePending s t → PendingProvenance s → PendingProvenance t
  kept-provenance same prov cell flagged =
    let installed = prov (same-stores-back same (here refl) cell) flagged
    in record
      { submitContext = Installed.submitContext installed
      ; submitArguments = Installed.submitArguments installed
      ; submittedFrom = Installed.submittedFrom installed
      ; installedAt = Installed.installedAt installed
      ; submission = Installed.submission installed
      ; unchanged = same-trans (Installed.unchanged installed) same
      }

  operation-provenance : ∀ op {s t} → OperationEffect op s t → PendingProvenance s → PendingProvenance t
  operation-provenance withdrawUnshielded = kept-provenance
  operation-provenance withdrawShielded = kept-provenance
  operation-provenance withdrawToContract = kept-provenance
  operation-provenance appendInbox = kept-provenance
  operation-provenance rotateEncKey = kept-provenance
  operation-provenance addDevice = kept-provenance
  operation-provenance removeDevice = kept-provenance
  operation-provenance issueGrant = kept-provenance
  operation-provenance revokeGrant = kept-provenance
  operation-provenance revokeAllGrants = kept-provenance
  operation-provenance publishRecovery = kept-provenance
  operation-provenance cancelRecovery cleared _ = cleared-provenance (Cleared.clearsFlag cleared)

empty-provenance : PendingProvenance (state [])
empty-provenance (stored ()) _

provenance-step : ∀ e ctx xs {s v t es} → execute e ctx xs s ≡ accepted v t es →
  PendingProvenance s → PendingProvenance t
provenance-step construct ctx xs {s} ok _ = cleared-provenance (pending-effect construct ctx xs {s = s} ok)
provenance-step submitRecovery ctx xs {s} {t = t} ok _ _ _ = record
  { submitContext = ctx
  ; submitArguments = xs
  ; submittedFrom = s
  ; installedAt = t
  ; submission = submit-evidence ctx xs ok
  ; unchanged = same-refl
  }
provenance-step finaliseRecovery ctx xs {s} ok _ =
  cleared-provenance (Finalisation.Evidence.clearsFlag (finalise-evidence ctx {s = s} ok))
provenance-step (activation c) ctx xs ok = kept-provenance (pending-effect (activation c) ctx xs ok)
provenance-step (device c op) ctx xs ok = operation-provenance op (pending-effect (device c op) ctx xs ok)
provenance-step (grant c op) ctx xs ok = operation-provenance op (pending-effect (grant c op) ctx xs ok)
provenance-step depositPublic ctx xs ok = kept-provenance (pending-effect depositPublic ctx xs ok)
provenance-step depositPrivate ctx xs ok = kept-provenance (pending-effect depositPrivate ctx xs ok)

finalise-enacts-submission : ∀ ctx {s v t es} → PendingProvenance s → finalise ctx s ≡ accepted v t es →
  EnactsSubmission ctx s t
finalise-enacts-submission ctx prov ok = record
  { installation = installed
  ; finalisation = evidence
  ; sameSuccessor = stores-unique (Finalisation.Evidence.successorCell evidence)
      (same-stores (Installed.unchanged installed) (there (here refl))
        (Submission.Evidence.installsEntry (Installed.submission installed)))
  ; sameRecoveryKey = stores-unique (Finalisation.Evidence.recoveryKeyCell evidence)
      (same-stores (Installed.unchanged installed) (there (there (here refl)))
        (Submission.Evidence.installsRecoveryKey (Installed.submission installed)))
  ; sameDeadline = stores-unique (Finalisation.Evidence.deadlineCell evidence)
      (same-stores (Installed.unchanged installed) (there (there (there (here refl))))
        (Submission.Evidence.installsDeadline (Installed.submission installed)))
  }
  where
  evidence = finalise-evidence ctx ok
  installed = prov (Finalisation.Evidence.pending evidence) (Finalisation.Evidence.isPending evidence)

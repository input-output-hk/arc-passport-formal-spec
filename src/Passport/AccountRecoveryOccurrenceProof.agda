{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes using (Primitives; Value)

module Passport.AccountRecoveryOccurrenceProof (P : Primitives) (address : Value) where

open import Data.Bool.Base using (true)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (_+_; _≤_)
open import Data.Maybe.Base using (just)
open import Data.Product using (_,_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import Conformance.FullAccountTypes
import Conformance.FullAccountLayouts
import Midnight.ContractDSL.AdversarialLifecycle as Adversarial
import Midnight.ContractDSL.SymbolicSigning as Signing
import Passport.Account as Account
open import Passport.AccountLifecycle P
open import Passport.AccountRecoveryOccurrence P address
import Passport.AccountSecurity as Security
import Passport.AccountSecurityProof as SecurityProof

private
  module Full = Security P address (λ _ → Signing.attacker)
  module FullProof = SecurityProof P address (λ _ → Signing.attacker)

from-certified : ∀ {s t} {trace : Runs.Trace s t} → Full.SubmittedIn trace → PendingOrigin trace
from-certified (Full.submitted env call answer effects executed resolved installation retained) =
  _ , _ , _ , submitted env call answer effects executed resolved
    S.installsFlag S.installsEntry S.installsRecoveryKey S.installsDeadline retained
  where module S = Recovery.Submission.Evidence installation
from-certified (Full.later x origin) with from-certified origin
... | entry , key , deadline , occurs = entry , key , deadline , later x occurs

pending-origin : ∀ {s p} (h : Runs.History s) → Recovery.Stores s "pending_recovery" p →
  flag p ≡ true → PendingOrigin (Runs.History.execution h)
pending-origin h cell flagged = from-certified (FullProof.pending-origin h cell flagged)

private
  certified-occurrence : ∀ {s t} {trace : Runs.Trace s t} (origin : Full.SubmittedIn trace) →
    let installation = Full.Occurrence.installation (Full.occurrence origin)
        xs = Full.Occurrence.submissionArguments (Full.occurrence origin)
    in Occurrence trace (Recovery.Submission.Evidence.successor installation)
      (Conformance.FullAccountLayouts.SubmitArguments.nextRecoveryKey xs)
      (nat (number (Conformance.FullAccountLayouts.SubmitArguments.nowBound xs) +
        number (Recovery.Submission.Evidence.vetoWindow installation)))
  certified-occurrence (Full.submitted env call answer effects executed resolved installation retained) =
    submitted env call answer effects executed resolved S.installsFlag S.installsEntry
      S.installsRecoveryKey S.installsDeadline retained
    where module S = Recovery.Submission.Evidence installation
  certified-occurrence (Full.later x origin) = later x (certified-occurrence origin)

finalisation-enacts-occurrence : ∀ env (call : RuntimeCall) {before answer effects after} →
  (h : Runs.History before) →
  Semantics.lookupEntrypoint (name (RuntimeCall.request call)) Semantics.entrypoints
    ≡ just Semantics.finaliseRecovery →
  Account.Transition P (executionContext address env) (RuntimeCall.request call) before
    (Account.committed answer effects) after →
  EnactsOccurrence (executionContext address env) (Runs.History.execution h) after
finalisation-enacts-occurrence env call h resolved committed = record
  { successor = _
  ; recoveryKey = _
  ; deadline = _
  ; origin = certified-occurrence E.origin
  ; replacesDevices = subst (λ entry → Recovery.Stores _ "devices" (tuple (entry ∷ [])))
      E.sameSuccessor F.replacesDevices
  ; installsRecoveryKey = subst (Recovery.Stores _ "recovery_pk") E.sameRecoveryKey F.installsRecoveryKey
  ; windowElapsed = subst (λ deadline → number deadline ≤ blockTime (executionContext address env))
      E.sameDeadline F.windowElapsed }
  where
  certificate = FullProof.finalisation-enacts-occurrence env call h resolved committed
  module E = Full.EnactsOccurrence certificate
  module F = Recovery.Finalisation.Evidence E.finalisation

module Joint (S : Signing.Interface 0ℓ)
  (required : State → Environment → RuntimeCall → List (Signing.Model.Token S)) where
  module Histories = Adversarial.Joint lifecycle address S required

  joint-pending-origin : ∀ {s knowledge p} (h : Histories.History (s , knowledge)) →
    Recovery.Stores s "pending_recovery" p → flag p ≡ true →
    PendingOrigin (Histories.contractTrace (Histories.History.execution h))
  joint-pending-origin h = pending-origin (Histories.contractHistory h)

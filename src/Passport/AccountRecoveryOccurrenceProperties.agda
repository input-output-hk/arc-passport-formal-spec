{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes using (Primitives; Value)

-- A pending recovery has an actual submission occurrence in the account's
-- history, with no intervening accepted submit, cancel or finalise. Finalising
-- enacts that occurrence's installed fields after its deadline. This is local
-- source safety, not consent, fairness or ledger adoption. Full guard evidence
-- remains available in AccountSecurityProof.finalisation-enacts-occurrence.
module Passport.AccountRecoveryOccurrenceProperties (P : Primitives) (address : Value) where

open import Data.Bool.Base using (true)
open import Data.List.Base using (List)
open import Data.Maybe.Base using (just)
open import Data.Product using (_,_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Conformance.FullAccountTypes
import Midnight.ContractDSL.AdversarialLifecycle as Adversarial
import Midnight.ContractDSL.SymbolicSigning as Signing
import Passport.Account as Account
open import Passport.AccountLifecycle P
open import Passport.AccountRecoveryOccurrence P address
import Passport.AccountRecoveryOccurrenceProof P address as Proof

pending-origin : ∀ {s p} (h : Runs.History s) → Recovery.Stores s "pending_recovery" p →
  flag p ≡ true → PendingOrigin (Runs.History.execution h)
pending-origin = Proof.pending-origin

finalisation-enacts-occurrence : ∀ env (call : RuntimeCall) {before answer effects after} →
  (h : Runs.History before) →
  Semantics.lookupEntrypoint (name (RuntimeCall.request call)) Semantics.entrypoints
    ≡ just Semantics.finaliseRecovery →
  Account.Transition P (executionContext address env) (RuntimeCall.request call) before
    (Account.committed answer effects) after →
  EnactsOccurrence (executionContext address env) (Runs.History.execution h) after
finalisation-enacts-occurrence = Proof.finalisation-enacts-occurrence

-- Signing and token extraction cannot affect this claim. For the concrete
-- AccountSecurity.Histories, instantiate S with AccountSecurity.Symbolic.interface
-- and required with AccountSecurity.requiredTokens (at the same P/address/ownership).
module Joint (S : Signing.Interface 0ℓ)
  (required : State → Environment → RuntimeCall → List (Signing.Model.Token S)) where
  module Histories = Adversarial.Joint lifecycle address S required
  private module JointProof = Proof.Joint S required

  joint-pending-origin : ∀ {s knowledge p} (h : Histories.History (s , knowledge)) →
    Recovery.Stores s "pending_recovery" p → flag p ≡ true →
    PendingOrigin (Histories.contractTrace (Histories.History.execution h))
  joint-pending-origin = JointProof.joint-pending-origin

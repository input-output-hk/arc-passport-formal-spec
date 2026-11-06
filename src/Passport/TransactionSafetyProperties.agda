{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes
open import Midnight.ContractDSL.SymbolicSigning using (Ownership)
import Conformance.FullAccountSignatureBinding as SignatureBinding

-- Contract-level P11 component, not adoption-level transaction safety.
-- For every committed runtime withdrawal after deployment, dispatch selects the
-- device or grant branch (all three schemes and all three destinations).
-- TransactionSafety.SafeWithdrawal exposes live source authorisation, the actual
-- encoded signed request, and branch-specific safety:
--   device: immediate consumed-credentials refusal, conditional on separation of
--           the actual old/rolled entry digests; no intervening history is covered;
--   grant: intended asset/caller/recipient/coin scope and the historical issuance's
--          cap INCLUDING this spend; later same-issuance symbolic tokens differ
--          under relevant request binding, including zero spends and refusals.
-- HistoryAgreement and SpendAgreement concern spent openings only; IntendedOpening
-- and ScopeAgreement concern policy openings only. None assumes the conclusion.
-- The provenance corollary is ideal symbolic signing: ownership and compromises
-- determine Controlled, and honest issuance requires approved signing. Trace-local
-- exact-request agreement is explicit; no native-signature realization is claimed.
-- Missing for full P11: cryptographic realization, ledger admission/adoption and
-- value/effect preservation, and device replay across arbitrary intervening calls.
module Passport.TransactionSafetyProperties (P : Primitives) (address : Value)
  (ownership : SignatureBinding.Key P → Ownership) where

open import Conformance.FullAccountGrantScope P
open import Data.List.Relation.Unary.All using (All)
open import Data.Product.Base using (_,_)
import Passport.AccountSecurity P address ownership as Security
open import Passport.GrantSpending P
open Histories address
open import Passport.RevocationExclusion P address hiding (module Runs)
open import Passport.TransactionSafety P address ownership
import Passport.TransactionSafetyProof P address ownership as Proof

transaction-safety : ∀ {s t} (h : Runs.History s) (event : CommittedOccurrence s t)
  (policy : IntendedPolicy) → WithdrawalCall event → HistoryAgreement h →
  IntendedOpening h event policy → ScopeAgreement h event policy → SpendAgreement h event policy →
  TransactionSafety h event policy
transaction-safety = Proof.transaction-safety

safe-request-provenance : ∀ {s t knowledge} {event : CommittedOccurrence s t} {policy}
  (joint : Security.Histories.History (s , knowledge))
  (safe : TransactionSafety (Security.Histories.contractHistory joint) event policy) →
  All (Security.Symbolic.Signatures.Available knowledge)
    (Security.requiredTokens s (CommittedOccurrence.environment event) (CommittedOccurrence.call event)) →
  Security.AgreesIn (λ r → r) joint (TransactionSafety.request safe) →
  Security.RequestProvenance (λ r → r) joint (TransactionSafety.request safe)
safe-request-provenance = Proof.safe-request-provenance

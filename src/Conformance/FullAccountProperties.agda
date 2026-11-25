{-# OPTIONS --safe --without-K #-}

-- Source-model facts, not compiled-contract refinement. The grant statements
-- concern the executable guard called by authenticateGrant on its map result;
-- they do not prove that an epoch/generation-advancing transaction occurred.
-- Atomicity and determinism below are structural wrapper consequences.
-- They establish neither circuit-specific invariants nor delayed admission.
module Conformance.FullAccountProperties where

open import Data.Bool.Base
open import Data.Nat.Base hiding (equal)
open import Data.Product.Base
open import Data.Maybe.Base using (just)
import Conformance.FullAccount as Model
import Passport.Account as Account
open import Relation.Binary.PropositionalEquality
open import Conformance.FullAccountTypes
import Conformance.FullAccountProof as Proof
open import Conformance.FullAccountLayouts
import Conformance.FullAccountGrant as Grant

-- An old epoch makes the actual live-record guard reject, even if it reaches
-- an earlier rejection (for example because the record is already revoked).
old-epoch-grant-rejected : ∀ P s g n →
  grantEpoch g ≡ nat n → lookupCell "device_epoch" (ledger s) ≡ just (nat (suc n)) →
  ∃ λ e → Grant.validateGrantRecord P g s ≡ rejected e
old-epoch-grant-rejected = Proof.old-epoch-grant-rejected

-- Likewise for an old generation; a revoked or old-epoch record can fail first.
old-generation-grant-rejected : ∀ P s g n →
  grantGeneration g ≡ nat n → lookupCell "grant_generation" (ledger s) ≡ just (nat (suc n)) →
  ∃ λ e → Grant.validateGrantRecord P g s ≡ rejected e
old-generation-grant-rejected = Proof.old-generation-grant-rejected

-- transaction returns the original state on rejection by construction.
rejection-is-atomic : ∀ P ctx call before e →
  Model.dispatch P ctx call before ≡ rejected e →
  Account.step P ctx call before ≡ (Account.reverted e , before)
rejection-is-atomic = Proof.rejection-is-atomic

-- Transition is an equation of the fixed step function, so its result is unique.
transition-deterministic : ∀ P ctx call before observation₁ observation₂ after₁ after₂ →
  Account.Transition P ctx call before observation₁ after₁ →
  Account.Transition P ctx call before observation₂ after₂ →
  (observation₁ , after₁) ≡ (observation₂ , after₂)
transition-deterministic = Proof.transition-deterministic

{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.Definitions using (DecidableEquality)

-- Theorems concern the finalized-only model in FinalizedLedger. The supplied
-- authorization policy is an assumption, not a cryptographic implementation.
-- Here m ⊖ n is integer-valued subtraction of natural amounts, not truncation.
module Passport.FinalizedLedgerProperties
  (Account Asset TxId : Set)
  (_≟Account_ : DecidableEquality Account)
  (_≟Asset_ : DecidableEquality Asset)
  (_≟Id_ : DecidableEquality TxId) where

open import Data.Integer.Base using (_⊖_; +_)
open import Data.List.Base using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat.Base using (_+_; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary.Decidable using (Dec)
open import Relation.Nullary.Negation using (¬_)

import Passport.FinalizedLedger as Ledger
import Passport.FinalizedLedgerProof as Proof

module L = Ledger Account Asset TxId _≟Account_ _≟Asset_ _≟Id_
module LedgerProof = Proof Account Asset TxId _≟Account_ _≟Asset_ _≟Id_
open L hiding (module Execution)

private
  variable
    s s′ s₁ s₂ : State
    t u : Transaction
    a : Account
    x : Asset
    i : TxId

module Execution
  (Authorized : State → Transaction → Set)
  (authorized? : ∀ s t → Dec (Authorized s t)) where

  open L.Execution Authorized authorized?
  module P = LedgerProof.Execution Authorized authorized?

  ------------------------------------------------------------------------
  -- Admission and rejection
  ------------------------------------------------------------------------

  accepted-valid : finalize s t ≡ accepted s′ → Valid s t
  accepted-valid = P.accepted-valid

  valid-accepted : Valid s t → finalize s t ≡ accepted (apply s t)
  valid-accepted = P.valid-accepted

  invalid-rejected : ¬ Valid s t → finalize s t ≡ rejected s
  invalid-rejected = P.invalid-rejected

  rejected-invalid : finalize s t ≡ rejected s′ → ¬ Valid s t
  rejected-invalid = P.rejected-invalid

  -- Equality includes every balance, the fee pools, and accepted-ID history.
  rejected-state : finalize s t ≡ rejected s′ → s′ ≡ s
  rejected-state = P.rejected-state

  accepted-authorized : finalize s t ≡ accepted s′ → Authorized s t
  accepted-authorized = P.accepted-authorized

  accepted-funded : finalize s t ≡ accepted s′ → ∀ a x → debit t a x ≤ balance s a x
  accepted-funded = P.accepted-funded

  insufficient-rejected : ¬ (debit t a x ≤ balance s a x) → finalize s t ≡ rejected s
  insufficient-rejected = P.insufficient-rejected

  duplicate-rejected : txId t ∈ acceptedIds s → finalize s t ≡ rejected s
  duplicate-rejected = P.duplicate-rejected

  unauthorized-rejected : ¬ Authorized s t → finalize s t ≡ rejected s
  unauthorized-rejected = P.unauthorized-rejected

  ------------------------------------------------------------------------
  -- Exact per-account, per-asset accounting
  ------------------------------------------------------------------------

  accepted-state : finalize s t ≡ accepted s′ → s′ ≡ apply s t
  accepted-state = P.accepted-state

  accepted-accounting : finalize s t ≡ accepted s′ → ∀ a x →
    balance s′ a x + debit t a x ≡ balance s a x + credit t a x
  accepted-accounting = P.accepted-accounting

  accepted-signed-effect : finalize s t ≡ accepted s′ → ∀ a x →
    balance s′ a x ⊖ balance s a x ≡ credit t a x ⊖ debit t a x
  accepted-signed-effect = P.accepted-signed-effect

  accepted-fees : finalize s t ≡ accepted s′ → ∀ x → fees s′ x ≡ fees s x + feeFor t x
  accepted-fees = P.accepted-fees

  accepted-signed-fees : finalize s t ≡ accepted s′ → ∀ x →
    fees s′ x ⊖ fees s x ≡ + feeFor t x
  accepted-signed-fees = P.accepted-signed-fees

  irrelevant-balance : finalize s t ≡ accepted s′ →
    debit t a x ≡ 0 → credit t a x ≡ 0 → balance s′ a x ≡ balance s a x
  irrelevant-balance = P.irrelevant-balance

  irrelevant-fees : finalize s t ≡ accepted s′ → feeFor t x ≡ 0 → fees s′ x ≡ fees s x
  irrelevant-fees = P.irrelevant-fees

  self-transfer-gross-funding : ∀ {s s′} i a x n f →
    finalize s (transaction i (transfer a a x n ∷ []) (fee a x f)) ≡ accepted s′ →
    f + n ≤ balance s a x
  self-transfer-gross-funding = P.self-transfer-gross-funding

  self-transfer-net-fee : ∀ {s s′} i a x n f →
    finalize s (transaction i (transfer a a x n ∷ []) (fee a x f)) ≡ accepted s′ →
    balance s′ a x + f ≡ balance s a x
  self-transfer-net-fee = P.self-transfer-net-fee

  ------------------------------------------------------------------------
  -- Accepted history and replay protection
  ------------------------------------------------------------------------

  accepted-id : finalize s t ≡ accepted s′ → txId t ∈ acceptedIds s′
  accepted-id = P.accepted-id

  accepted-fresh : finalize s t ≡ accepted s′ → ¬ (txId t ∈ acceptedIds s)
  accepted-fresh = P.accepted-fresh

  history-preserves-id : Finalized s s′ → i ∈ acceptedIds s → i ∈ acceptedIds s′
  history-preserves-id = P.history-preserves-id

  accepted-id-persists : finalize s t ≡ accepted s₁ → Finalized s₁ s₂ → txId t ∈ acceptedIds s₂
  accepted-id-persists = P.accepted-id-persists

  -- The later attempt may change every transaction field except its ID.
  historical-no-replay : finalize s t ≡ accepted s₁ → Finalized s₁ s₂ →
    txId u ≡ txId t → finalize s₂ u ≡ rejected s₂
  historical-no-replay = P.historical-no-replay

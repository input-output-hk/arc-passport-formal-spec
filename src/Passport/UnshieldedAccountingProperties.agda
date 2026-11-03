{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

-- Accounting for declared receiveUnshielded/sendUnshielded effects of actual
-- accepted full-account calls. All three device/grant curves are covered.
-- Balances are natural numbers (absent entries are zero); the accepted deposit
-- bound and withdrawal funding guard rule out wrapping and truncated overdrafts.
-- The final map includes authentication, settlement, inbox and round tails.
--
-- History equality: stored balance + all declared sends = all declared receives,
-- separately for every color, from an empty constructor map. Refusals contribute
-- no effects and preserve the entire state. Environments remain unrestricted.
-- These are local source effects, not adopted ledger assets, transaction fees,
-- or a full SnapshotSound result. Definitions: UnshieldedAccounting; proofs:
-- UnshieldedAccountingProof (with purpose-specific neutral-source certificates).
module Passport.UnshieldedAccountingProperties (P : Primitives) where

open import Passport.UnshieldedAccounting
open Passport.UnshieldedAccounting.Semantics P
import Passport.UnshieldedAccountingProof P as Proof
import Conformance.FullAccount as Model
open import Conformance.FullAccountBody P using (withdrawUnshielded)
open Model.AccountSemantics P using (device; grant; depositPublic; checked)
open import Data.Bool.Base using (true; false)
open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base using (_+_; _≤ᵇ_; _<ᵇ_; _^_)
open import Data.Product.Base using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Passport.Account as Account
open import Passport.AccountLifecycle P

accepted-runtime-accounting : ∀ ctx (call : RuntimeCall) {s x t es} →
  Model.dispatch P ctx (RuntimeCall.request call) s ≡ accepted x t es →
  Accounting (dispatchedAction (RuntimeCall.request call)) s es t
accepted-runtime-accounting = Proof.dispatch-accounting

accepted-deposit : ∀ ctx xs s {x t es} → checked depositPublic ctx xs s ≡ accepted x t es →
  balance (get 0 xs) t ≡ balance (get 0 xs) s + number (get 1 xs) ×
  transfers es ≡ received (get 0 xs) (number (get 1 xs)) ∷ [] ×
  (balance (get 0 xs) t <ᵇ 2 ^ 128) ≡ true
accepted-deposit = Proof.accepted-deposit

accepted-device-withdrawal : ∀ c ctx xs s {x t es} →
  checked (device c withdrawUnshielded) ctx xs s ≡ accepted x t es →
  balance (get 0 xs) t + number (get 1 xs) ≡ balance (get 0 xs) s ×
  transfers es ≡ sent (get 0 xs) (number (get 1 xs)) ∷ [] ×
  (number (get 1 xs) ≤ᵇ balance (get 0 xs) s) ≡ true
accepted-device-withdrawal = Proof.accepted-device-withdrawal

accepted-grant-withdrawal : ∀ c ctx xs s {x t es} →
  checked (grant c withdrawUnshielded) ctx xs s ≡ accepted x t es →
  balance (get 0 xs) t + number (get 1 xs) ≡ balance (get 0 xs) s ×
  transfers es ≡ sent (get 0 xs) (number (get 1 xs)) ∷ [] ×
  (number (get 1 xs) ≤ᵇ balance (get 0 xs) s) ≡ true
accepted-grant-withdrawal = Proof.accepted-grant-withdrawal

unrelated-credit : ∀ {color amount s es t} → Accounting (credit color amount) s es t →
  ∀ query → equal query color ≡ false →
  lookupMap query (fields (balanceMap t)) ≡ lookupMap query (fields (balanceMap s))
unrelated-credit = Proof.unrelated-credit

unrelated-debit : ∀ {color amount s es t} → Accounting (debit color amount) s es t →
  ∀ query → equal query color ≡ false →
  lookupMap query (fields (balanceMap t)) ≡ lookupMap query (fields (balanceMap s))
unrelated-debit = Proof.unrelated-debit

other-runtime-unchanged : ∀ ctx (call : RuntimeCall) {s x t es} →
  dispatchedAction (RuntimeCall.request call) ≡ idle →
  Model.dispatch P ctx (RuntimeCall.request call) s ≡ accepted x t es →
  balanceMap t ≡ balanceMap s × transfers es ≡ []
other-runtime-unchanged = Proof.other-runtime-unchanged

refused-preserves-state : ∀ ctx call s {error t} →
  Account.Transition P ctx call s (Account.reverted error) t → t ≡ s
refused-preserves-state = Proof.refused-preserves

constructor-starts-empty : ∀ ctx deployment {x s es} →
  Account.deploy P ctx deployment ≡ accepted x s es → balanceMap s ≡ tuple []
constructor-starts-empty = Proof.deployment-empty

module History (address : Value) where
  open Histories address

  deployment-rooted-accounting : ∀ {s} (history : Runs.History s) → ∀ color →
    balance color s + sentTotal color (historyTransfers history) ≡ receivedTotal color (historyTransfers history)
  deployment-rooted-accounting = Proof.History.history-accounted address

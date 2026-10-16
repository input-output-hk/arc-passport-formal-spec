{-# OPTIONS --safe --without-K #-}

open import Midnight.ContractDSL.Ledger
open import Midnight.ContractDSL.Contract

module Midnight.ContractDSL.AdmissionProperties (L : Semantics) (Assertion : Set)
  (C : Contract L Assertion) where

open import Data.Empty
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open Semantics L
open import Midnight.ContractDSL.Program L Assertion
open Contract C
open Transaction
import Midnight.ContractDSL.Properties L Assertion as Replay

Eligible⇒admit : (now : ℕ) (tx : Transaction) → target tx ≡ self →
  Eligible now (journal (execution tx)) →
  admit now (view tx) tx ≡ (working (execution tx) , accepted)
Eligible⇒admit now tx same eligible with target tx ≟ self
... | no neq = ⊥-elim (neq same)
... | yes _ rewrite Replay.same-view-replay (body (target tx) (entry tx) (input tx)) now
  (certified tx) eligible = refl

accepted-execution : (now : ℕ) (s t : State) (tx : Transaction) →
  admit now s tx ≡ (t , accepted) → target tx ≡ self ×
  eval (body self (entry tx) (input tx)) s ≡
    inj₂ (finished (result (execution tx)) t (journal (execution tx)))
accepted-execution now s t tx eq with target tx ≟ self
accepted-execution now s t tx eq | yes same with replay now (journal (execution tx)) s in replayed | eq
... | just u | refl = same , subst (λ acc → eval (body acc (entry tx) (input tx)) s ≡
    inj₂ (finished (result (execution tx)) u (journal (execution tx)))) same
  (Replay.replay-refinement (body (target tx) (entry tx) (input tx)) now (certified tx) replayed)

rejection-atomic : (now : ℕ) (s t : State) (tx : Transaction) →
  admit now s tx ≡ (t , rejected) → t ≡ s
rejection-atomic now s t tx eq with target tx ≟ self
... | no _ with eq
... | refl = refl
rejection-atomic now s t tx eq | yes _ with replay now (journal (execution tx)) s | eq
... | nothing | refl = refl

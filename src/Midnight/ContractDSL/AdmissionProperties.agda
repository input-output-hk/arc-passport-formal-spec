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
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open Semantics L
open import Midnight.ContractDSL.Program L Assertion
open import Midnight.ContractDSL.Hoare L Assertion
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

-- `I` is an invariant of `C`
Preserves : (State → Set) → Set
Preserves I = ∀ entry input → Hoare I (body self entry input) (onSuccess (I ∘ working))

admit-preserves : {I : State → Set} → Preserves I →
  ∀ {s t v} (now : ℕ) (tx : Transaction) →
  admit now s tx ≡ (t , v) → I s → I t
admit-preserves {I} preserves {s} {t} {accepted} now tx admitted initial =
  subst (onSuccess (λ r → I (working r)))
    (proj₂ (accepted-execution now s t tx admitted))
    (preserves (entry tx) (input tx) s initial)
admit-preserves {I} preserves {s} {t} {rejected} now tx admitted initial =
  subst I (sym (rejection-atomic now s t tx admitted)) initial

admissions-preserve : {I : State → Set} → Preserves I →
  ∀ {s t} → Admissions s t → I s → I t
admissions-preserve preserves done initial = initial
admissions-preserve preserves (next now tx v admitted rest) initial =
  admissions-preserve preserves rest (admit-preserves preserves now tx admitted initial)

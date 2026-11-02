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

module _ (q : Submission) where
  open Submission q renaming (transaction to tx)

  Eligible⇒admit : target tx ≡ self → Eligible now (journal (execution tx)) →
    admit (view tx) q ≡ (working (execution tx) , accepted)
  Eligible⇒admit same eligible with target tx ≟ self
  ... | no neq = ⊥-elim (neq same)
  ... | yes _ rewrite Replay.same-view-replay (body (target tx) (entry tx) (input tx)) now
    (certified tx) eligible = refl

  accepted-execution : (s t : State) →
    admit s q ≡ (t , accepted) → target tx ≡ self ×
    eval (body self (entry tx) (input tx)) s ≡
      inj₂ (finished (result (execution tx)) t (journal (execution tx)))
  accepted-execution s t eq with target tx ≟ self
  accepted-execution s t eq | yes same with replay now (journal (execution tx)) s in replayed | eq
  ... | just u | refl = same , subst (λ acc → eval (body acc (entry tx) (input tx)) s ≡
      inj₂ (finished (result (execution tx)) u (journal (execution tx)))) same
    (Replay.replay-refinement (body (target tx) (entry tx) (input tx)) now (certified tx) replayed)

  rejection-atomic : (s t : State) → admit s q ≡ (t , rejected) → t ≡ s
  rejection-atomic s t eq with target tx ≟ self
  ... | no _ with eq
  ... | refl = refl
  rejection-atomic s t eq | yes _ with replay now (journal (execution tx)) s | eq
  ... | nothing | refl = refl

-- `I` is an invariant of `C`
Preserves : (State → Set) → Set
Preserves I = ∀ entry input → Hoare I (body self entry input) (onSuccess (I ∘ working))

admit-preserves : {I : State → Set} → Preserves I →
  ∀ {s t v} (q : Submission) → admit s q ≡ (t , v) → I s → I t
admit-preserves {I} preserves {s} {t} {accepted} q admitted initial =
  subst (onSuccess (λ r → I (working r)))
    (proj₂ (accepted-execution q s t admitted))
    (preserves (entry tx) (input tx) s initial)
  where open Submission q renaming (transaction to tx)
admit-preserves {I} preserves {s} {t} {rejected} q admitted initial =
  subst I (sym (rejection-atomic q s t admitted)) initial

admissions-preserve : {I : State → Set} → Preserves I →
  ∀ {s t} → Admissions s t → I s → I t
admissions-preserve preserves done initial = initial
admissions-preserve preserves (next q v admitted rest) initial =
  admissions-preserve preserves rest (admit-preserves preserves q admitted initial)

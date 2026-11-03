{-# OPTIONS --safe --without-K #-}

-- Success witnesses for the existing account state-and-journal monad.
-- These helpers inspect its actual evaluator; they introduce no authorization
-- predicate or cryptographic assumption.
module Conformance.FullAccountExecution where

open import Conformance.FullAccountTypes
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List)
open import Data.Product.Base using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record Succeeded {A : Set} (m : M A) (before : State) : Set where
  constructor succeeded
  field answer : A
        after : State
        journal : List Effect
        execution : m before ≡ accepted answer after journal

-- Indexed form for decompositions that must retain the final answer and state.
record Run {A : Set} (m : M A) (before : State) (answer : A) (after : State) : Set where
  constructor run
  field journal : List Effect
        execution : m before ≡ accepted answer after journal

private
  rejected≠accepted : ∀ {A e x t es} → rejected {A} e ≡ accepted x t es → ⊥
  rejected≠accepted ()

  accepted-injective : ∀ {A x y t u es fs} → accepted {A} x t es ≡ accepted y u fs →
    x ≡ y × t ≡ u × es ≡ fs
  accepted-injective refl = refl , refl , refl

bind-success : ∀ {A B} (m : M A) (f : A → M B) (s : State) →
  Succeeded (m >>= f) s →
  Σ (Succeeded m s) (λ prefix →
    Succeeded (f (Succeeded.answer prefix)) (Succeeded.after prefix))
bind-success m f s (succeeded answer after journal execution) with m s in first
... | rejected e = ⊥-elim (rejected≠accepted execution)
bind-success m f s (succeeded answer after journal execution) | accepted x t es
  with f x t in second
... | rejected e = ⊥-elim (rejected≠accepted execution)
... | accepted y u fs = succeeded x t es first , succeeded y u fs second

then : ∀ {A B} (m : M A) {f : A → M B} {s y u} → Run (m >>= f) s y u →
  Σ A λ x → Σ State λ t → Run m s x t × Run (f x) t y u
then m {f} {s} (run es execution) with m s in first
... | rejected e = ⊥-elim (rejected≠accepted execution)
... | accepted x t es₁ with f x t in second
...   | rejected e = ⊥-elim (rejected≠accepted execution)
...   | accepted y′ u′ es₂ with accepted-injective execution
...     | refl , refl , _ = x , t , run es₁ first , run es₂ second

{-# OPTIONS --safe --without-K --guardedness #-}

module Midnight.ContractDSL.PrivacyReplacementExample where

open import Data.Bool.Base
open import Data.Bool.Properties
open import Data.Empty
open import Data.Product.Base
open import Data.Unit.Base
open import Level
open import Relation.Binary.PropositionalEquality

open import Categories.Category.Instance.Sets
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Instance.Sets
open import Categories.Functor.Hom
open import CategoricalCrypto.Standard2
open import Midnight.ContractDSL.PrivacyReplacement

private
  sets : MonoidalCategory (suc 0ℓ) 0ℓ 0ℓ
  sets = record { U = Sets 0ℓ ; monoidal = Product.Sets-Monoidal }

module U = StdUC sets (Hom[ Sets 0ℓ ][-, Bool ])
open U hiding (Channel)

-- A finite deterministic idealization, not a second machine/runtime model.
-- The three values permit observers to distinguish rejection from divergence.
data Observation : Set where
  accept reject diverge : Observation

verdict : Bool → Observation
verdict true = accept
verdict false = reject

isAccepted isRejected isDivergent : Observation → Bool
isAccepted accept = true
isAccepted _ = false
isRejected reject = true
isRejected _ = false
isDivergent diverge = true
isDivergent _ = false

ideal real : Bool ⇒ T₀ Bool (Bool × Bool)
ideal b = b , (b , not b)
real b = not b , (b , not b)

-- Negation changes the adversarial output, not the honest payload.
negation-emulates : real ≤UC ideal
negation-emulates = dummy-complete (not , ≈C⇒≈ᵁ (λ _ → refl))

module R = Transfer.Replacement U.StdSetup real ideal negation-emulates

left right : (Bool × Bool) ⇒ T₀ ℐ.unit Observation
left (b , c) = return (verdict b)
right (b , c) = return (verdict (not c))

module Worlds = R.TwoWorld left right

-- The contexts disagree on general payloads. The ideal invariant makes them
-- agree even when the simulator and the ancilla observer inspect the grade.
ideal-private : (s : Bool → Bool) (W : Set)
  (e : Env (T₀ (W ⊗₀ (Bool ⊗₀ ℐ.unit)) Observation)) →
  run W (left ∙ ideal) (regradeEnv W (s ⊗₁ ℐ.id) e) Env.≈
    run W (right ∙ ideal) (regradeEnv W (s ⊗₁ ℐ.id) e)
ideal-private s W e (w , b) rewrite not-involutive b = refl

real-private : (W : Set)
  (e : Env (T₀ (W ⊗₀ (Bool ⊗₀ ℐ.unit)) Observation)) →
  run W (left ∙ real) e Env.≈ run W (right ∙ real) e
real-private W e =
  Worlds.transfer-private (λ _ _ _ → ⊤) (λ s W e _ → ideal-private s W e) W e tt

correlationObserver : Env (T₀ (⊤ ⊗₀ (Bool ⊗₀ ℐ.unit)) Observation)
correlationObserver ((_ , a , _) , observation) = not (a xor isAccepted observation)

shared-observer-transfer :
  run ⊤ (left ∙ real) correlationObserver Env.≈
    run ⊤ (right ∙ real) correlationObserver
shared-observer-transfer = real-private ⊤ correlationObserver

raw-ideal-correlation : (b : Bool) →
  run ⊤ (left ∙ ideal) correlationObserver (tt , b) ≡ true
raw-ideal-correlation true = refl
raw-ideal-correlation false = refl

real-correlation : (b : Bool) →
  run ⊤ (left ∙ real) correlationObserver (tt , b) ≡ false
real-correlation true = refl
real-correlation false = refl

simulated-ideal-correlation : (b : Bool) →
  run ⊤ (left ∙ ideal)
    (regradeEnv ⊤ (R.simulator ⊗₁ ℐ.id) correlationObserver) (tt , b) ≡ false
simulated-ideal-correlation true = refl
simulated-ideal-correlation false = refl

-- This breaks the ideal relational premise, rather than the UC resource law.
broken : Bool ⇒ T₀ Bool (Bool × Bool)
broken b = b , (b , b)

contexts-sensitive :
  run ⊤ (left ∙ broken) correlationObserver (tt , true) ≢
    run ⊤ (right ∙ broken) correlationObserver (tt , true)
contexts-sensitive ()

rejection-not-divergence : isRejected reject ≢ isRejected diverge
rejection-not-divergence ()

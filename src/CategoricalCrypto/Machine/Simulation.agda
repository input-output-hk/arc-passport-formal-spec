{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- CategoricalCrypto.Machine.Simulation
--
-- Weak simulations between machines, and ℤ-weighted flows over traces:
-- the infrastructure for deriving global (whole-system) properties from
-- local (per-component) ones. A `Sim M N` maps every step of M to a
-- trace of N over a state projection; a flow-preserving simulation
-- transports per-step accounting (`flow`) along whole traces.
------------------------------------------------------------------------

module CategoricalCrypto.Machine.Simulation where

open import Data.Integer
open import Data.Integer.Properties
open import Data.Maybe
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality
open import Tactic.Defaults

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core

private variable A B C D E F : Channel

module _ {M : Machine A B} where
  infixl 5 _++ᵗ_
  _++ᵗ_ : ∀ {s₁ s₂ s₃} → Trace M s₁ s₂ → Trace M s₂ s₃ → Trace M s₁ s₃
  t ++ᵗ []                   = t
  t ++ᵗ (u ∷ʳ⟨ i , o , st ⟩) = (t ++ᵗ u) ∷ʳ⟨ i , o , st ⟩

-- ℤ-valued step weights on a machine's channel
Val : Machine A B → Set
Val M = Channel.inType MC → Maybe (Channel.outType MC) → ℤ
  where MC = Machine.machine-channel M

module _ {M : Machine A B} (v : Val M) where
  flow : ∀ {s s'} → Trace M s s' → ℤ
  flow []                  = 0ℤ
  flow (t ∷ʳ⟨ i , o , _ ⟩) = flow t + v i o

  flow-++ : ∀ {s₁ s₂ s₃} (t : Trace M s₁ s₂) (u : Trace M s₂ s₃)
          → flow (t ++ᵗ u) ≡ flow t + flow u
  flow-++ t []                  = sym (+-identityʳ _)
  flow-++ t (u ∷ʳ⟨ i , o , _ ⟩) =
    trans (cong (_+ v i o) (flow-++ t u)) (+-assoc (flow t) (flow u) (v i o))

record Sim (M : Machine A B) (N : Machine C D) : Set₁ where
  field
    π      : Machine.State M → Machine.State N
    onStep : ∀ {s i o s'} → Machine.stepRel M s i o s' → Trace N (π s) (π s')

  onTrace : ∀ {s s'} → Trace M s s' → Trace N (π s) (π s')
  onTrace []                   = []
  onTrace (t ∷ʳ⟨ _ , _ , st ⟩) = onTrace t ++ᵗ onStep st

  -- each M-step's weight equals the N-flow of its image
  Preserves : Val M → Val N → Set
  Preserves vM vN = ∀ {s i o s'} (st : Machine.stepRel M s i o s') → vM i o ≡ flow vN (onStep st)

  flow-onTrace : ∀ {vM vN} → Preserves vM vN
               → ∀ {s s'} (t : Trace M s s') → flow vN (onTrace t) ≡ flow vM t
  flow-onTrace p []                       = refl
  flow-onTrace {vM} {vN} p (t ∷ʳ⟨ i , o , st ⟩) =
    trans (flow-++ vN (onTrace t) (onStep st))
          (cong₂ _+_ (flow-onTrace p t) (sym (p st)))

open Sim

------------------------------------------------------------------------
-- Composition of simulations
------------------------------------------------------------------------

module _ {M : Machine A B} {N : Machine C D} {P : Machine E F} where
  infixr 9 _∙_
  _∙_ : Sim M N → Sim N P → Sim M P
  π      (S ∙ T) s  = π T (π S s)
  onStep (S ∙ T) st = onTrace T (onStep S st)

  ∙-preserves : ∀ {vM vN vP} (S : Sim M N) (T : Sim N P)
              → Preserves S vM vN → Preserves T vN vP → Preserves (S ∙ T) vM vP
  ∙-preserves S T pS pT st = trans (pS st) (sym (flow-onTrace T pT (onStep S st)))

------------------------------------------------------------------------
-- Basic helpers
------------------------------------------------------------------------

modify-sim : {p : ∀ {m} → C ⊗₀ D ᵀ [ m ]⇒[ m ] A ⊗₀ B ᵀ} {N : Machine A B}
           → Sim (modifyStepRel p N) N
π      modify-sim s  = s
onStep modify-sim st = [] ∷ʳ⟨ _ , _ , st ⟩

module _ {M₁ : Machine A B} {M₂ : Machine C D} where
  open Tensor M₁ M₂ using (CompRel; Step₁; Step₂)

  comp-simˡ : Sim (MkMachine CompRel) M₁
  π      comp-simˡ = proj₁
  onStep comp-simˡ (Step₁ st) = [] ∷ʳ⟨ _ , _ , st ⟩
  onStep comp-simˡ (Step₂ st) = []

  comp-simʳ : Sim (MkMachine CompRel) M₂
  π      comp-simʳ = proj₂
  onStep comp-simʳ (Step₁ st) = []
  onStep comp-simʳ (Step₂ st) = [] ∷ʳ⟨ _ , _ , st ⟩

traceRel-sim : {M : Machine (A ⊗₀ C) (B ⊗₀ C)} → Sim (MkMachine (TraceRel M)) M
π      traceRel-sim s = s
onStep traceRel-sim Trace[ st ]       = [] ∷ʳ⟨ _ , _ , st ⟩
onStep traceRel-sim (st Trace∷ₒ rest) = ([] ∷ʳ⟨ _ , _ , st ⟩) ++ᵗ onStep traceRel-sim rest
onStep traceRel-sim (st Trace∷ᵢ rest) = ([] ∷ʳ⟨ _ , _ , st ⟩) ++ᵗ onStep traceRel-sim rest

------------------------------------------------------------------------
-- Simulation combinators
------------------------------------------------------------------------

module _ {M₁ : Machine A B} {M₂ : Machine C D} where
  ⊗₁-simˡ : Sim (M₁ ⊗₁ M₂) M₁
  π      ⊗₁-simˡ    = proj₁
  onStep ⊗₁-simˡ st = onStep comp-simˡ st

  ⊗₁-simʳ : Sim (M₁ ⊗₁ M₂) M₂
  π      ⊗₁-simʳ    = proj₂
  onStep ⊗₁-simʳ st = onStep comp-simʳ st

module _ {M : Machine (A ⊗₀ C) (B ⊗₀ C)} where
  tr-sim : Sim (tr M) M
  π      tr-sim s  = s
  onStep tr-sim st = onStep traceRel-sim st

module _ {M₁ : Machine B C} {M₂ : Machine A B} where
  private
    p : ∀ {m} → (A ⊗₀ B) ⊗₀ (C ⊗₀ B) ᵀ [ m ]⇒[ m ] (A ⊗₀ B) ⊗₀ (B ⊗₀ C) ᵀ
    p = ⇒-solver

    innerˡ : Sim (modifyStepRel p (M₂ ⊗₁ M₁)) M₂
    π      innerˡ = proj₁
    onStep innerˡ {i = i} {o = o} st =
      onStep ⊗₁-simˡ {i = app {mᵢ = In} p i} {o = map (app {mₒ = Out} p) o} st

    innerʳ : Sim (modifyStepRel p (M₂ ⊗₁ M₁)) M₁
    π      innerʳ = proj₂
    onStep innerʳ {i = i} {o = o} st =
      onStep ⊗₁-simʳ {i = app {mᵢ = In} p i} {o = map (app {mₒ = Out} p) o} st

  ∘-simˡ : Sim (M₁ ∘ M₂) M₂
  π      ∘-simˡ    = proj₁
  onStep ∘-simˡ st = onTrace innerˡ (onStep traceRel-sim st)

  ∘-simʳ : Sim (M₁ ∘ M₂) M₁
  π      ∘-simʳ    = proj₂
  onStep ∘-simʳ st = onTrace innerʳ (onStep traceRel-sim st)

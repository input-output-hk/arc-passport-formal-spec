{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- CategoricalCrypto.Machine.Simulation
--
-- Weak simulations between machines: a `Sim M N` maps every step of M to a
-- trace of N over a state projection, and there is one for each of the
-- library's wiring combinators, projecting a composite to a component.
-- `Preserves S vM vN` says `S` transports per-step accounting, so it carries
-- the weight of a whole M-trace to the weight of its N-image
-- (`flow-onTrace`) — the route from global (whole-system) properties to
-- local (per-component) ones.
------------------------------------------------------------------------

module CategoricalCrypto.Machine.Simulation where

open import Data.Integer using (_+_)
open import Data.Maybe
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Machine.Cascade
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Core.Ext
open import CategoricalCrypto.Machine.Valuation

private variable A B C D E F : Channel

record Sim (M : Machine A B) (N : Machine C D) : Set₁ where
  field
    π      : Machine.State M → Machine.State N
    onStep : ∀ {s i o s'} → Machine.stepRel M s i o s' → Trace N (π s) (π s')

  onTrace : ∀ {s s'} → Trace M s s' → Trace N (π s) (π s')
  onTrace []                   = []
  onTrace (t ∷ʳ⟨ _ , _ , st ⟩) = onTrace t ++ᵗ onStep st

open Sim

-- each M-step's weight equals the N-flow of its image
record Preserves {M : Machine A B} {N : Machine C D} (S : Sim M N)
                 (vM : Val (A ⊗ᵀ B)) (vN : Val (C ⊗ᵀ D)) : Set where
  field
    preserves : ∀ {s i o s'} (st : Machine.stepRel M s i o s')
              → vM i o ≡ flow vN (onStep S st)

open Preserves public

flow-onTrace : {M : Machine A B} {N : Machine C D} {S : Sim M N}
               {vM : Val (A ⊗ᵀ B)} {vN : Val (C ⊗ᵀ D)} → Preserves S vM vN
             → ∀ {s s'} (t : Trace M s s') → flow vN (onTrace S t) ≡ flow vM t
flow-onTrace p []                             = refl
flow-onTrace {S = S} {vN = vN} p (t ∷ʳ⟨ _ , _ , st ⟩) =
  trans (flow-++ vN (onTrace S t) (onStep S st))
        (cong₂ _+_ (flow-onTrace p t) (sym (preserves p st)))

module _ {M : Machine A B} {N : Machine C D} {S : Sim M N} where
  preserves-cong : {v v' : Val (A ⊗ᵀ B)} {w w' : Val (C ⊗ᵀ D)}
                 → (∀ i o → v i o ≡ v' i o) → (∀ i o → w i o ≡ w' i o)
                 → Preserves S v w → Preserves S v' w'
  preserves (preserves-cong hv hw p) st =
    trans (sym (hv _ _)) (trans (preserves p st) (flow-cong hw (onStep S st)))

  -- weights that vanish all along the image vanish at the source
  sim-neutral : {μM : MVal (A ⊗ᵀ B)} {μN : MVal (C ⊗ᵀ D)}
              → Preserves S (netVal μM) (netVal μN) → Neutral N μN → Neutral M μM
  absorbs (sim-neutral p n) st = trans (preserves p st) (flow-neutral n (onStep S st))

------------------------------------------------------------------------
-- Composition of simulations
------------------------------------------------------------------------

module _ {M : Machine A B} {N : Machine C D} {P : Machine E F} where
  infixr 9 _∙_
  _∙_ : Sim M N → Sim N P → Sim M P
  π      (S ∙ T) s  = π T (π S s)
  onStep (S ∙ T) st = onTrace T (onStep S st)

  ∙-preserves : {S : Sim M N} {T : Sim N P} {vM : Val (A ⊗ᵀ B)} {vN : Val (C ⊗ᵀ D)}
                {vP : Val (E ⊗ᵀ F)}
              → Preserves S vM vN → Preserves T vN vP → Preserves (S ∙ T) vM vP
  preserves (∙-preserves {S = S} pS pT) st =
    trans (preserves pS st) (sym (flow-onTrace pT (onStep S st)))

------------------------------------------------------------------------
-- Simulation combinators
------------------------------------------------------------------------

-- the simulation of a machine by itself: a step is its own one-step trace
idSim : {M : Machine A B} → Sim M M
π      idSim s  = s
onStep idSim st = [] ∷ʳ⟨ _ , _ , st ⟩

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

  ⊗₁-simˡ : Sim (M₁ ⊗₁ M₂) M₁
  π      ⊗₁-simˡ    = proj₁
  onStep ⊗₁-simˡ st = onStep comp-simˡ st

  ⊗₁-simʳ : Sim (M₁ ⊗₁ M₂) M₂
  π      ⊗₁-simʳ    = proj₂
  onStep ⊗₁-simʳ st = onStep comp-simʳ st

traceRel-sim : {M : Machine (A ⊗₀ C) (B ⊗₀ C)} → Sim (MkMachine (TraceRel M)) M
π      traceRel-sim s = s
onStep traceRel-sim Trace[ st ]       = [] ∷ʳ⟨ _ , _ , st ⟩
onStep traceRel-sim (st Trace∷ₒ rest) = ([] ∷ʳ⟨ _ , _ , st ⟩) ++ᵗ onStep traceRel-sim rest
onStep traceRel-sim (st Trace∷ᵢ rest) = ([] ∷ʳ⟨ _ , _ , st ⟩) ++ᵗ onStep traceRel-sim rest

module _ {M : Machine (A ⊗₀ C) (B ⊗₀ C)} where
  tr-sim : Sim (tr M) M
  π      tr-sim s  = s
  onStep tr-sim st = onStep traceRel-sim st

module _ {M₁ : Machine B C} {M₂ : Machine A B} where
  -- the machine `_∘_` traces over: each node of a composite step's cascade is
  -- one of its steps, i.e. a `M₂ ⊗₁ M₁` step at reshuffled messages
  ∘-core : Machine (A ⊗₀ B) (C ⊗₀ B)
  ∘-core = modifyStepRel ∘-reshuffle (M₂ ⊗₁ M₁)

  ∘-coreˡ : Sim ∘-core M₂
  π      ∘-coreˡ = proj₁
  onStep ∘-coreˡ {i = i} {o = o} st =
    onStep ⊗₁-simˡ {i = app {mᵢ = In} ∘-reshuffle i}
                   {o = map (app {mₒ = Out} ∘-reshuffle) o} st

  ∘-coreʳ : Sim ∘-core M₁
  π      ∘-coreʳ = proj₂
  onStep ∘-coreʳ {i = i} {o = o} st =
    onStep ⊗₁-simʳ {i = app {mᵢ = In} ∘-reshuffle i}
                   {o = map (app {mₒ = Out} ∘-reshuffle) o} st

  ∘-simˡ : Sim (M₁ ∘ M₂) M₂
  π      ∘-simˡ    = proj₁
  onStep ∘-simˡ st = onTrace ∘-coreˡ (onStep traceRel-sim st)

  ∘-simʳ : Sim (M₁ ∘ M₂) M₁
  π      ∘-simʳ    = proj₂
  onStep ∘-simʳ st = onTrace ∘-coreʳ (onStep traceRel-sim st)

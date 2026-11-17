{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

------------------------------------------------------------------------
-- CategoricalCrypto.Machine.Wiring
--
-- Flow through the library's combinators at *structured* weights. A machine
-- boundary weighs its domain messages by one `MVal` and its codomain messages
-- by another (`bdryᵥ`), and every combinator relates such weights in one fixed
-- way: `_∘_` shares the weight of the wire it hides, `_⊗₁_` weighs each factor
-- on its own. At weights in that form the translation equations of the
-- combinators' baked reshuffles hold by `refl` per summand, so callers supply
-- only the `Neutral` facts. Nothing is lost: every `MVal` on a tensor channel
-- is `≗ᵥ` to a structured one, and `neutral-cong`/`preserves-cong` transport
-- these results to it.
------------------------------------------------------------------------

module CategoricalCrypto.Machine.Wiring where

open import Data.Integer using (ℤ; 0ℤ; _+_; _-_)
open import Data.Integer.Properties
open import Data.Maybe
open import Data.Sum using (inj₁; inj₂)
open import Data.Sum.Properties
open import Relation.Binary.PropositionalEquality
open import Tactic.Defaults

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Cascade
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Core.Ext
open import CategoricalCrypto.Machine.Simulation
open import CategoricalCrypto.Machine.Valuation

open Machine
open Sim

private variable A B C D E F : Channel

------------------------------------------------------------------------
-- The reshuffles, per summand
------------------------------------------------------------------------

opaque
  unfolding _⊗₀_ destruct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc ⊗-right-intro
            ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine

  -- `_⊗₁_`'s baked reshuffle is the middle-four interchange
  ⊗₁ᵥ-pulls : {μ : MVal A} {ν : MVal B} {ξ : MVal C} {ζ : MVal D}
            → bdryᵥ (μ ⊗ᵥ ξ) (ν ⊗ᵥ ζ)
            ≗ᵥ pull (⊗₁-msg {A} {B} {C} {D}) (bdryᵥ μ ν ⊗ᵥ bdryᵥ ξ ζ)
  ⊗₁ᵥ-pulls In  (inj₁ (inj₁ _)) = refl
  ⊗₁ᵥ-pulls In  (inj₁ (inj₂ _)) = refl
  ⊗₁ᵥ-pulls In  (inj₂ (inj₁ _)) = refl
  ⊗₁ᵥ-pulls In  (inj₂ (inj₂ _)) = refl
  ⊗₁ᵥ-pulls Out (inj₁ (inj₁ _)) = refl
  ⊗₁ᵥ-pulls Out (inj₁ (inj₂ _)) = refl
  ⊗₁ᵥ-pulls Out (inj₂ (inj₁ _)) = refl
  ⊗₁ᵥ-pulls Out (inj₂ (inj₂ _)) = refl

  -- `tr` exposes the hidden wire on both the domain and the codomain side
  trᵥ-pulls : {μ : MVal A} {ν : MVal B} {ξ : MVal C}
            → bdryᵥ μ ν ≗ᵥ pull (tr-msg {A} {B} {C}) (bdryᵥ (μ ⊗ᵥ ξ) (ν ⊗ᵥ ξ))
  trᵥ-pulls In  (inj₁ _) = refl
  trᵥ-pulls In  (inj₂ _) = refl
  trᵥ-pulls Out (inj₁ _) = refl
  trᵥ-pulls Out (inj₂ _) = refl

  -- `_∘_` reshuffles the traced tensor, then `_⊗₁_` interchanges it
  ∘ᵥ-pulls : {μ : MVal A} {ν : MVal B} {ξ : MVal C}
           → bdryᵥ (μ ⊗ᵥ ν) (ξ ⊗ᵥ ν)
           ≗ᵥ pull (∘-msg {A} {B} {C}) (bdryᵥ μ ν ⊗ᵥ bdryᵥ ν ξ)
  ∘ᵥ-pulls In  (inj₁ (inj₁ _)) = refl
  ∘ᵥ-pulls In  (inj₁ (inj₂ _)) = refl
  ∘ᵥ-pulls In  (inj₂ (inj₁ _)) = refl
  ∘ᵥ-pulls In  (inj₂ (inj₂ _)) = refl
  ∘ᵥ-pulls Out (inj₁ (inj₁ _)) = refl
  ∘ᵥ-pulls Out (inj₁ (inj₂ _)) = refl
  ∘ᵥ-pulls Out (inj₂ (inj₁ _)) = refl
  ∘ᵥ-pulls Out (inj₂ (inj₂ _)) = refl

  -- the hidden wire's two ends weigh the same because they are the same `ξ`
  hiddenᵥ-out : {μ : MVal A} {ν : MVal B} {ξ : MVal C} (c : Channel.outType C)
              → bdryᵥ (μ ⊗ᵥ ξ) (ν ⊗ᵥ ξ) Out ((L⊗ ϵ) ⊗R ↑ₒ c)
              ≡ bdryᵥ (μ ⊗ᵥ ξ) (ν ⊗ᵥ ξ) In (L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹ ↑ᵢ c)
  hiddenᵥ-out _ = refl

  hiddenᵥ-in : {μ : MVal A} {ν : MVal B} {ξ : MVal C} (c : Channel.inType C)
             → bdryᵥ (μ ⊗ᵥ ξ) (ν ⊗ᵥ ξ) Out (L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹ ↑ₒ c)
             ≡ bdryᵥ (μ ⊗ᵥ ξ) (ν ⊗ᵥ ξ) In ((L⊗ ϵ) ⊗R ↑ᵢ c)
  hiddenᵥ-in _ = refl

------------------------------------------------------------------------
-- Flow through the cores: the tensor and the cascade
------------------------------------------------------------------------

module _ {M₁ : Machine A B} {M₂ : Machine C D}
         (κ₁ : MVal (A ⊗ᵀ B)) (κ₂ : MVal (C ⊗ᵀ D)) where
  open Tensor M₁ M₂ using (Step₁; Step₂)

  -- A tensor step is one component's step at an embedded message, so the weight
  -- of the projected-away component must vanish: it is that component's
  -- `netVal`, and the component is `Neutral`.
  comp-preservesˡ : Neutral M₂ κ₂
                  → Preserves (comp-simˡ {M₁ = M₁} {M₂}) (netVal (κ₁ ⊗ᵥ κ₂)) (netVal κ₁)
  preserves (comp-preservesˡ n₂) (Step₁ {m} {m'} st) =
    trans (sym (⊗ᵥ-netˡ κ₁ κ₂ m m')) (sym (+-identityˡ _))
  preserves (comp-preservesˡ n₂) (Step₂ {m} {m'} st) =
    trans (sym (⊗ᵥ-netʳ κ₁ κ₂ m m')) (absorbs n₂ st)

  comp-preservesʳ : Neutral M₁ κ₁
                  → Preserves (comp-simʳ {M₁ = M₁} {M₂}) (netVal (κ₁ ⊗ᵥ κ₂)) (netVal κ₂)
  preserves (comp-preservesʳ n₁) (Step₁ {m} {m'} st) =
    trans (sym (⊗ᵥ-netˡ κ₁ κ₂ m m')) (absorbs n₁ st)
  preserves (comp-preservesʳ n₁) (Step₂ {m} {m'} st) =
    trans (sym (⊗ᵥ-netʳ κ₁ κ₂ m m')) (sym (+-identityˡ _))

module _ {M : Machine (A ⊗₀ C) (B ⊗₀ C)} {μ : MVal A} {ν : MVal B} {ξ : MVal C} where
  private
    κ : MVal ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ C))
    κ = bdryᵥ (μ ⊗ᵥ ξ) (ν ⊗ᵥ ξ)

    -- the head node emits the weight the trailing cascade consumes, so the two
    -- weights telescope to that of the whole step
    join : ∀ {s s' s''} {i oₕ} (st : stepRel M s i (just oₕ) s')
             (t : Trace M s' s'') (b c : ℤ) → κ Out oₕ ≡ b → b - c ≡ flow (netVal κ) t
         → κ In i - c ≡ flow (netVal κ) (([] ∷ʳ⟨ i , just oₕ , st ⟩) ++ᵗ t)
    join {i = i} {oₕ} st t b c h ih =
      trans (trans (sym (+-minus-telescope (κ In i) (κ Out oₕ) c))
                   (cong (λ z → (κ In i - κ Out oₕ) + (z - c)) h))
        (trans (cong₂ _+_ (sym (+-identityˡ (κ In i - κ Out oₕ))) ih)
               (sym (flow-++ (netVal κ) ([] ∷ʳ⟨ i , just oₕ , st ⟩) t)))

    cascade : ∀ {s i o s'} (t : TraceRel M s i o s')
            → netVal κ i o ≡ flow (netVal κ) (onStep traceRel-sim t)
    cascade Trace[ st ] = sym (+-identityˡ _)
    cascade (_Trace∷ₒ_ {outC = c} {outMₘ = o} st rest) =
      join st (onStep traceRel-sim rest) (κ In (L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹ ↑ᵢ c))
           (maybe′ (κ Out) 0ℤ o) (hiddenᵥ-out {μ = μ} {ν} {ξ} c) (cascade rest)
    cascade (_Trace∷ᵢ_ {inC = c} {outMₘ = o} st rest) =
      join st (onStep traceRel-sim rest) (κ In ((L⊗ ϵ) ⊗R ↑ᵢ c))
           (maybe′ (κ Out) 0ℤ o) (hiddenᵥ-in {μ = μ} {ν} {ξ} c) (cascade rest)

  -- the cascade's nodes telescope to the weight of the whole step, since the
  -- hidden wire's two ends carry the same weight
  traceRelᵥ-preserves : Preserves (traceRel-sim {M = M}) (netVal κ) (netVal κ)
  preserves traceRelᵥ-preserves = cascade

  -- `tr`'s two `modifyStepRel` layers translate a step's messages into the
  -- cascade's
  trᵥ-preserves : Preserves (tr-sim {M = M}) (netVal (bdryᵥ μ ν)) (netVal κ)
  preserves trᵥ-preserves {i = i} {o = o} st =
    trans (trans (netVal-cong (trᵥ-pulls {μ = μ} {ν} {ξ}) i o)
                 (netVal-pull² (tr-cod {A} {B} {C}) (tr-dom {A} {B} {C}) κ i o))
          (cascade st)

------------------------------------------------------------------------
-- Per-combinator flow, with only the `Neutral` side left to the caller
------------------------------------------------------------------------

module _ {M₁ : Machine A B} {M₂ : Machine C D}
         {μ : MVal A} {ν : MVal B} {ξ : MVal C} {ζ : MVal D} where
  private
    ω : MVal ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ D))
    ω = bdryᵥ (μ ⊗ᵥ ξ) (ν ⊗ᵥ ζ)

    ωC : MVal ((A ⊗ᵀ B) ⊗₀ (C ⊗ᵀ D))
    ωC = bdryᵥ μ ν ⊗ᵥ bdryᵥ ξ ζ

    at : ∀ i o → netVal ω i o
              ≡ netVal ωC (app {mᵢ = In} (⊗₁-msg {A} {B} {C} {D}) i)
                          (map (app {mᵢ = Out} (⊗₁-msg {A} {B} {C} {D})) o)
    at i o = trans (netVal-cong (⊗₁ᵥ-pulls {μ = μ} {ν} {ξ} {ζ}) i o)
                   (netVal-pull (⊗₁-msg {A} {B} {C} {D}) ωC i o)

  ⊗₁ᵥ-preservesˡ : Neutral M₂ (bdryᵥ ξ ζ)
                 → Preserves (⊗₁-simˡ {M₁ = M₁} {M₂}) (netVal ω) (netVal (bdryᵥ μ ν))
  preserves (⊗₁ᵥ-preservesˡ n₂) {i = i} {o = o} st =
    trans (at i o)
          (preserves (comp-preservesˡ {M₁ = M₁} {M₂} (bdryᵥ μ ν) (bdryᵥ ξ ζ) n₂) st)

  ⊗₁ᵥ-preservesʳ : Neutral M₁ (bdryᵥ μ ν)
                 → Preserves (⊗₁-simʳ {M₁ = M₁} {M₂}) (netVal ω) (netVal (bdryᵥ ξ ζ))
  preserves (⊗₁ᵥ-preservesʳ n₁) {i = i} {o = o} st =
    trans (at i o)
          (preserves (comp-preservesʳ {M₁ = M₁} {M₂} (bdryᵥ μ ν) (bdryᵥ ξ ζ) n₁) st)

  ⊗₁ᵥ-neutral : Neutral M₁ (bdryᵥ μ ν) → Neutral M₂ (bdryᵥ ξ ζ) → Neutral (M₁ ⊗₁ M₂) ω
  ⊗₁ᵥ-neutral n₁ n₂ = sim-neutral (⊗₁ᵥ-preservesˡ n₂) n₁

module _ {M₁ : Machine B C} {M₂ : Machine A B}
         {μ : MVal A} {ξ : MVal C} (ν : MVal B) where
  private
    κN : MVal ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))
    κN = bdryᵥ (μ ⊗ᵥ ν) (ξ ⊗ᵥ ν)

    κC : MVal ((A ⊗ᵀ B) ⊗₀ (B ⊗ᵀ C))
    κC = bdryᵥ μ ν ⊗ᵥ bdryᵥ ν ξ

    at : ∀ i o → netVal κN i o
              ≡ netVal κC (app {mᵢ = In} (⊗₁-msg {A} {B} {B} {C})
                               (app {mᵢ = In} (∘-reshuffle {A} {B} {C}) i))
                          (map (app {mᵢ = Out} (⊗₁-msg {A} {B} {B} {C}))
                               (map (app {mᵢ = Out} (∘-reshuffle {A} {B} {C})) o))
    at i o = trans (netVal-cong (∘ᵥ-pulls {μ = μ} {ν} {ξ}) i o)
                   (netVal-pull² (∘-reshuffle {A} {B} {C}) (⊗₁-msg {A} {B} {B} {C}) κC i o)

    -- `_∘_` traces over `M₂ ⊗₁ M₁`, so the tensor's left factor is `M₂`
    coreˡ : Neutral M₁ (bdryᵥ ν ξ)
          → Preserves (∘-coreˡ {M₁ = M₁} {M₂}) (netVal κN) (netVal (bdryᵥ μ ν))
    preserves (coreˡ n₁) {i = i} {o = o} st =
      trans (at i o)
            (preserves (comp-preservesˡ {M₁ = M₂} {M₁} (bdryᵥ μ ν) (bdryᵥ ν ξ) n₁) st)

    coreʳ : Neutral M₂ (bdryᵥ μ ν)
          → Preserves (∘-coreʳ {M₁ = M₁} {M₂}) (netVal κN) (netVal (bdryᵥ ν ξ))
    preserves (coreʳ n₂) {i = i} {o = o} st =
      trans (at i o)
            (preserves (comp-preservesʳ {M₁ = M₂} {M₁} (bdryᵥ μ ν) (bdryᵥ ν ξ) n₂) st)

  -- A composite step is a cascade of steps of `M₂ ⊗₁ M₁`: its weight
  -- telescopes over the cascade (`trᵥ-preserves`), and each node contributes
  -- only through the component projected to (`comp-preserves`).
  ∘ᵥ-preservesˡ : Neutral M₁ (bdryᵥ ν ξ)
                → Preserves (∘-simˡ {M₁ = M₁} {M₂})
                            (netVal (bdryᵥ μ ξ)) (netVal (bdryᵥ μ ν))
  preserves (∘ᵥ-preservesˡ n₁) {i = i} {o = o} st =
    trans (preserves (trᵥ-preserves {μ = μ} {ν = ξ} {ξ = ν}) {i = i} {o = o} st)
          (sym (flow-onTrace (coreˡ n₁) (onStep traceRel-sim st)))

  ∘ᵥ-preservesʳ : Neutral M₂ (bdryᵥ μ ν)
                → Preserves (∘-simʳ {M₁ = M₁} {M₂})
                            (netVal (bdryᵥ μ ξ)) (netVal (bdryᵥ ν ξ))
  preserves (∘ᵥ-preservesʳ n₂) {i = i} {o = o} st =
    trans (preserves (trᵥ-preserves {μ = μ} {ν = ξ} {ξ = ν}) {i = i} {o = o} st)
          (sym (flow-onTrace (coreʳ n₂) (onStep traceRel-sim st)))

  ∘ᵥ-neutral : Neutral M₁ (bdryᵥ ν ξ) → Neutral M₂ (bdryᵥ μ ν)
             → Neutral (M₁ ∘ M₂) (bdryᵥ μ ξ)
  ∘ᵥ-neutral n₁ n₂ = sim-neutral (∘ᵥ-preservesˡ n₁) n₂

------------------------------------------------------------------------
-- The stateless rewiring machines
--
-- `id` and the associators are `TotalFunctionMachine'`s over `⇒-solver` terms,
-- re-elaborated here at the same generic shape the library solves them at (see
-- `CategoricalCrypto.Machine.Cascade`).
------------------------------------------------------------------------

tfm-msg : A [ In ]⇒[ In ] B → B [ Out ]⇒[ Out ] A → A ⊗ᵀ B [ In ]⇒[ Out ] A ⊗ᵀ B
tfm-msg p q = ⊗-combine (p ⇒ₜ ⇒-negate-transpose-right)
                        (⇒-transpose-left-negate-right ⇒ₜ q) ⇒ₜ ⊗-sym

-- where the machine sends a message: its step relation is
-- `just (tfm-app i) ≡ o`, so it is both total and functional
tfm-app : (p : A [ In ]⇒[ In ] B) (q : B [ Out ]⇒[ Out ] A)
        → Msg (TotalFunctionMachine' p q) In → Msg (TotalFunctionMachine' p q) Out
tfm-app p q = app (tfm-msg p q)

tfm-det : (p : A [ In ]⇒[ In ] B) (q : B [ Out ]⇒[ Out ] A) → ∀ {s s' i o}
        → stepRel (TotalFunctionMachine' p q) s i o s' → o ≡ just (tfm-app p q i)
tfm-det _ _ = sym

opaque
  unfolding _⊗₀_ ⊗-sym ⊗-combine

  tfm-app-inj : (p : A [ In ]⇒[ In ] B) (q : B [ Out ]⇒[ Out ] A)
              → (∀ {x y} → app p x ≡ app p y → x ≡ y)
              → (∀ {x y} → app q x ≡ app q y → x ≡ y)
              → ∀ {x y} → tfm-app p q x ≡ tfm-app p q y → x ≡ y
  tfm-app-inj _ _ f _ {inj₁ _} {inj₁ _} e = cong inj₁ (f (inj₂-injective e))
  tfm-app-inj _ _ _ _ {inj₁ _} {inj₂ _} ()
  tfm-app-inj _ _ _ _ {inj₂ _} {inj₁ _} ()
  tfm-app-inj _ _ _ g {inj₂ _} {inj₂ _} e = cong inj₂ (g (inj₁-injective e))

tfm-neutral : (p : A [ In ]⇒[ In ] B) (q : B [ Out ]⇒[ Out ] A) {μ : MVal (A ⊗ᵀ B)}
            → (∀ i → μ Out (tfm-app p q i) ≡ μ In i)
            → Neutral (TotalFunctionMachine' p q) μ
tfm-neutral p q h = neutral-fwd (λ i → just (tfm-app p q i)) sym h

-- The solver terms `id` and the associators are built from, re-elaborated at the
-- generic shape the library solves them at: instantiating those is definitional,
-- re-running the solver on an instantiated shape is not.
module Sid {X : Channel} where
  fwd : X [ In ]⇒[ In ] X
  fwd = ⇒-solver

  bwd : X [ Out ]⇒[ Out ] X
  bwd = ⇒-solver

module Sassoc {X Y Z : Channel} where
  fwd : (X ⊗₀ Y) ⊗₀ Z [ In ]⇒[ In ] X ⊗₀ (Y ⊗₀ Z)
  fwd = ⇒-solver

  bwd : X ⊗₀ (Y ⊗₀ Z) [ Out ]⇒[ Out ] (X ⊗₀ Y) ⊗₀ Z
  bwd = ⇒-solver

  fwd⃖ : X ⊗₀ (Y ⊗₀ Z) [ In ]⇒[ In ] (X ⊗₀ Y) ⊗₀ Z
  fwd⃖ = ⇒-solver

  bwd⃖ : (X ⊗₀ Y) ⊗₀ Z [ Out ]⇒[ Out ] X ⊗₀ (Y ⊗₀ Z)
  bwd⃖ = ⇒-solver

opaque
  unfolding _⊗₀_ destruct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc ⊗-right-intro
            ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine

  idᵥ-neutral : {μ : MVal A} → Neutral id (bdryᵥ μ μ)
  idᵥ-neutral {A} {μ} = tfm-neutral Sid.fwd Sid.bwd {μ = bdryᵥ μ μ} go
    where go : ∀ i → bdryᵥ μ μ Out (app (tfm-msg (Sid.fwd {A}) Sid.bwd) i)
                   ≡ bdryᵥ μ μ In i
          go (inj₁ _) = refl
          go (inj₂ _) = refl

  ⊗-assocᵥ-neutral : {μ : MVal A} {ν : MVal B} {ξ : MVal C}
                   → Neutral ⊗-assoc (bdryᵥ ((μ ⊗ᵥ ν) ⊗ᵥ ξ) (μ ⊗ᵥ (ν ⊗ᵥ ξ)))
  ⊗-assocᵥ-neutral {A} {B} {C} {μ} {ν} {ξ} =
    tfm-neutral Sassoc.fwd Sassoc.bwd {μ = ω} go
    where ω : MVal (((A ⊗₀ B) ⊗₀ C) ⊗ᵀ (A ⊗₀ (B ⊗₀ C)))
          ω = bdryᵥ ((μ ⊗ᵥ ν) ⊗ᵥ ξ) (μ ⊗ᵥ (ν ⊗ᵥ ξ))
          go : ∀ i → ω Out (app (tfm-msg (Sassoc.fwd {A} {B} {C}) Sassoc.bwd) i)
                   ≡ ω In i
          go (inj₁ (inj₁ (inj₁ _))) = refl
          go (inj₁ (inj₁ (inj₂ _))) = refl
          go (inj₁ (inj₂ _))        = refl
          go (inj₂ (inj₁ _))        = refl
          go (inj₂ (inj₂ (inj₁ _))) = refl
          go (inj₂ (inj₂ (inj₂ _))) = refl

  ⊗-assoc⃖ᵥ-neutral : {μ : MVal A} {ν : MVal B} {ξ : MVal C}
                    → Neutral ⊗-assoc⃖ (bdryᵥ (μ ⊗ᵥ (ν ⊗ᵥ ξ)) ((μ ⊗ᵥ ν) ⊗ᵥ ξ))
  ⊗-assoc⃖ᵥ-neutral {A} {B} {C} {μ} {ν} {ξ} =
    tfm-neutral Sassoc.fwd⃖ Sassoc.bwd⃖ {μ = ω} go
    where ω : MVal ((A ⊗₀ (B ⊗₀ C)) ⊗ᵀ ((A ⊗₀ B) ⊗₀ C))
          ω = bdryᵥ (μ ⊗ᵥ (ν ⊗ᵥ ξ)) ((μ ⊗ᵥ ν) ⊗ᵥ ξ)
          go : ∀ i → ω Out (app (tfm-msg (Sassoc.fwd⃖ {A} {B} {C}) Sassoc.bwd⃖) i)
                   ≡ ω In i
          go (inj₁ (inj₁ _))        = refl
          go (inj₁ (inj₂ (inj₁ _))) = refl
          go (inj₁ (inj₂ (inj₂ _))) = refl
          go (inj₂ (inj₁ (inj₁ _))) = refl
          go (inj₂ (inj₁ (inj₂ _))) = refl
          go (inj₂ (inj₂ _))        = refl

  -- the unitors are the base cases of `mergeᴹ`/`splitᴹ`-style rewirings
  unitorᵥ-neutral : {μ : MVal A}
                  → Neutral (TotalFunctionMachine' ⊗-left-neutral ⊗-left-intro)
                            (bdryᵥ (0ᵥ {I} ⊗ᵥ μ) μ)
  unitorᵥ-neutral {A} {μ} = tfm-neutral ⊗-left-neutral ⊗-left-intro {μ = ω} go
    where ω : MVal ((I ⊗₀ A) ⊗ᵀ A)
          ω = bdryᵥ (0ᵥ {I} ⊗ᵥ μ) μ
          t : (I ⊗₀ A) ⊗ᵀ A [ In ]⇒[ Out ] (I ⊗₀ A) ⊗ᵀ A
          t = tfm-msg ⊗-left-neutral ⊗-left-intro
          go : ∀ i → ω Out (app t i) ≡ ω In i
          go (inj₁ (inj₁ ()))
          go (inj₁ (inj₂ _)) = refl
          go (inj₂ _)        = refl

  unitorᵥ⁻¹-neutral : {μ : MVal A}
                    → Neutral (TotalFunctionMachine' ⊗-left-intro ⊗-left-neutral)
                              (bdryᵥ μ (0ᵥ {I} ⊗ᵥ μ))
  unitorᵥ⁻¹-neutral {A} {μ} = tfm-neutral ⊗-left-intro ⊗-left-neutral {μ = ω} go
    where ω : MVal (A ⊗ᵀ (I ⊗₀ A))
          ω = bdryᵥ μ (0ᵥ {I} ⊗ᵥ μ)
          t : A ⊗ᵀ (I ⊗₀ A) [ In ]⇒[ Out ] A ⊗ᵀ (I ⊗₀ A)
          t = tfm-msg ⊗-left-intro ⊗-left-neutral
          go : ∀ i → ω Out (app t i) ≡ ω In i
          go (inj₁ _)        = refl
          go (inj₂ (inj₁ ()))
          go (inj₂ (inj₂ _)) = refl

------------------------------------------------------------------------
-- Chaining links
--
-- A chain of simulations and its flow-preservation proof have the same
-- shape, so they are built together: each link records the weights it
-- transports, and `_∙ᶠ_` composes both halves at once.
------------------------------------------------------------------------

record SimFlow (M : Machine A B) (N : Machine C D)
               (μ : MVal (A ⊗ᵀ B)) (ν : MVal (C ⊗ᵀ D)) : Set₁ where
  constructor mkSF
  field
    sim   : Sim M N
    flowᶠ : Preserves sim (netVal μ) (netVal ν)

open SimFlow public

idᶠ : {M : Machine A B} {μ : MVal (A ⊗ᵀ B)} → SimFlow M M μ μ
sim idᶠ = idSim
preserves (flowᶠ idᶠ) _ = sym (+-identityˡ _)

infixr 9 _∙ᶠ_
_∙ᶠ_ : {M : Machine A B} {N : Machine C D} {P : Machine E F}
       {μ : MVal (A ⊗ᵀ B)} {ν : MVal (C ⊗ᵀ D)} {ξ : MVal (E ⊗ᵀ F)}
     → SimFlow M N μ ν → SimFlow N P ν ξ → SimFlow M P μ ξ
sim   (S ∙ᶠ T) = sim S ∙ sim T
flowᶠ (S ∙ᶠ T) = ∙-preserves (flowᶠ S) (flowᶠ T)

module _ {M₁ : Machine B C} {M₂ : Machine A B} {μ : MVal A} {ξ : MVal C} where
  ∘ᶠˡ : (ν : MVal B) → Neutral M₁ (bdryᵥ ν ξ)
      → SimFlow (M₁ ∘ M₂) M₂ (bdryᵥ μ ξ) (bdryᵥ μ ν)
  ∘ᶠˡ ν n₁ = mkSF ∘-simˡ (∘ᵥ-preservesˡ {μ = μ} {ξ} ν n₁)

  ∘ᶠʳ : (ν : MVal B) → Neutral M₂ (bdryᵥ μ ν)
      → SimFlow (M₁ ∘ M₂) M₁ (bdryᵥ μ ξ) (bdryᵥ ν ξ)
  ∘ᶠʳ ν n₂ = mkSF ∘-simʳ (∘ᵥ-preservesʳ {μ = μ} {ξ} ν n₂)

module _ {M₁ : Machine A B} {M₂ : Machine C D}
         {μ : MVal A} {ν : MVal B} {ξ : MVal C} {ζ : MVal D} where
  ⊗₁ᶠˡ : Neutral M₂ (bdryᵥ ξ ζ)
       → SimFlow (M₁ ⊗₁ M₂) M₁ (bdryᵥ (μ ⊗ᵥ ξ) (ν ⊗ᵥ ζ)) (bdryᵥ μ ν)
  ⊗₁ᶠˡ n₂ = mkSF ⊗₁-simˡ (⊗₁ᵥ-preservesˡ {μ = μ} {ν} {ξ} {ζ} n₂)

  ⊗₁ᶠʳ : Neutral M₁ (bdryᵥ μ ν)
       → SimFlow (M₁ ⊗₁ M₂) M₂ (bdryᵥ (μ ⊗ᵥ ξ) (ν ⊗ᵥ ζ)) (bdryᵥ ξ ζ)
  ⊗₁ᶠʳ n₁ = mkSF ⊗₁-simʳ (⊗₁ᵥ-preservesʳ {μ = μ} {ν} {ξ} {ζ} n₁)

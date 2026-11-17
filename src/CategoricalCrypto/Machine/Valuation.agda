{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- CategoricalCrypto.Machine.Valuation
--
-- ℤ-weighted accounting on a machine's channel. A `Val C` weighs a whole
-- step — the message it consumes together with the one it may emit — and
-- `flow` sums that over a trace. A `MVal C` weighs single messages, and
-- induces the weight a step *absorbs* (`netVal`): what came in, minus what
-- went out. `pull` transports an `MVal` back along a deterministic channel
-- morphism and `_≗ᵥ_` compares `MVal`s pointwise; `netVal` is natural for
-- both (`netVal-pull`, `netVal-cong`), which is what lets a weight be moved
-- across the message translations the library's combinators bake in. A
-- machine is `Neutral` when every one of its steps absorbs nothing.
------------------------------------------------------------------------

module CategoricalCrypto.Machine.Valuation where

open import Data.Integer hiding (-_)
open import Data.Integer.Properties
open import Data.Maybe
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Core.Ext

-- a step's weight: it consumes one message and emits at most one
Val : Channel → Set
Val C = Channel.inType C → Maybe (Channel.outType C) → ℤ

-- a single message's weight
MVal : Channel → Set
MVal C = ∀ m → modeType m C → ℤ

private variable A B C D E : Channel

module _ {M : Machine A B} (v : Val (A ⊗ᵀ B)) where
  flow : ∀ {s s'} → Trace M s s' → ℤ
  flow []                  = 0ℤ
  flow (t ∷ʳ⟨ i , o , _ ⟩) = flow t + v i o

  flow-++ : ∀ {s₁ s₂ s₃} (t : Trace M s₁ s₂) (u : Trace M s₂ s₃)
          → flow (t ++ᵗ u) ≡ flow t + flow u
  flow-++ t []                  = sym (+-identityʳ _)
  flow-++ t (u ∷ʳ⟨ i , o , _ ⟩) =
    trans (cong (_+ v i o) (flow-++ t u)) (+-assoc (flow t) (flow u) (v i o))

module _ {M : Machine A B} {v w : Val (A ⊗ᵀ B)} (p : ∀ i o → v i o ≡ w i o) where
  flow-cong : ∀ {s s'} (t : Trace M s s') → flow v t ≡ flow w t
  flow-cong []                  = refl
  flow-cong (t ∷ʳ⟨ i , o , _ ⟩) = cong₂ _+_ (flow-cong t) (p i o)

------------------------------------------------------------------------
-- Message weights
------------------------------------------------------------------------

infix 4 _≗ᵥ_
_≗ᵥ_ : MVal C → MVal C → Set
μ ≗ᵥ ν = ∀ m x → μ m x ≡ ν m x

-- a weight transported back along a deterministic channel morphism
pull : (∀ {m} → C [ m ]⇒[ m ] D) → MVal D → MVal C
pull t μ m x = μ m (app {mᵢ = m} {mₒ = m} t x)

netVal : MVal C → Val C
netVal μ i o = μ In i - maybe′ (μ Out) 0ℤ o

netVal-cong : {μ ν : MVal C} → μ ≗ᵥ ν → ∀ i o → netVal μ i o ≡ netVal ν i o
netVal-cong h i nothing  = cong (_- 0ℤ) (h In i)
netVal-cong h i (just x) = cong₂ _-_ (h In i) (h Out x)

netVal-in : {μ : MVal C} → (∀ x → μ Out x ≡ 0ℤ) → ∀ i o → netVal μ i o ≡ μ In i
netVal-in         h i nothing  = +-identityʳ _
netVal-in {μ = μ} h i (just x) = trans (cong (μ In i -_) (h x)) (+-identityʳ _)

-- translating a step's messages leaves the weight it absorbs alone
netVal-pull : (t : ∀ {m} → C [ m ]⇒[ m ] D) (μ : MVal D)
            → ∀ i o → netVal (pull t μ) i o
                    ≡ netVal μ (app {mᵢ = In} t i) (map (app {mᵢ = Out} t) o)
netVal-pull t μ i nothing  = refl
netVal-pull t μ i (just _) = refl

-- … and through two layers, as a doubly wrapped step relation nests them
netVal-pull² : (t : ∀ {m} → C [ m ]⇒[ m ] D) (u : ∀ {m} → D [ m ]⇒[ m ] E) (μ : MVal E)
             → ∀ i o → netVal (pull (t ⇒ₜ u) μ) i o
                     ≡ netVal μ (app {mᵢ = In} u (app {mᵢ = In} t i))
                                (map (app {mᵢ = Out} u) (map (app {mᵢ = Out} t) o))
netVal-pull² t u μ i nothing  = refl
netVal-pull² t u μ i (just _) = refl

------------------------------------------------------------------------
-- Weight combinators
------------------------------------------------------------------------

0ᵥ : MVal C
0ᵥ _ _ = 0ℤ

infixr 9 _⊗ᵥ_
_⊗ᵥ_ : MVal C → MVal D → MVal (C ⊗₀ D)
(μ ⊗ᵥ ν) m x = Sum.[ μ m , ν m ] (destruct-⊗ {m = m} x)

infix 10 _ᵀᵥ
_ᵀᵥ : MVal C → MVal (C ᵀ)
(μ ᵀᵥ) Out = μ In
(μ ᵀᵥ) In  = μ Out

-- a machine boundary's weight: `μ` on the domain, `ν` on the codomain
bdryᵥ : MVal A → MVal B → MVal (A ⊗ᵀ B)
bdryᵥ μ ν = μ ⊗ᵥ (ν ᵀᵥ)

Zeroᵥ : MVal C → Set
Zeroᵥ μ = μ ≗ᵥ 0ᵥ

-- a weight that vanishes on the messages of one mode; `netVal` counts only
-- what a step consumed as soon as `Zeroᵥ[ Out ]` holds (`netVal-in`)
Zeroᵥ[_] : Mode → MVal C → Set
Zeroᵥ[ m ] μ = ∀ x → μ m x ≡ 0ℤ

0ᵥ-zero : Zeroᵥ (0ᵥ {C})
0ᵥ-zero _ _ = refl

-- the weights stay explicit: at a fixed mode `μ` cannot be recovered from
-- `Zeroᵥ[ m ] μ` by unification
⊗ᵥ-zeroᵐ : {m : Mode} (μ : MVal C) (ν : MVal D)
         → Zeroᵥ[ m ] μ → Zeroᵥ[ m ] ν → Zeroᵥ[ m ] (μ ⊗ᵥ ν)
⊗ᵥ-zeroᵐ {C} {D} {m} μ ν hμ hν x = go (destruct-⊗ {C} {D} {m} x)
  where go : (y : modeType m C ⊎ modeType m D) → Sum.[ μ m , ν m ] y ≡ 0ℤ
        go (inj₁ y) = hμ y
        go (inj₂ y) = hν y

⊗ᵥ-zero : {μ : MVal C} {ν : MVal D} → Zeroᵥ μ → Zeroᵥ ν → Zeroᵥ (μ ⊗ᵥ ν)
⊗ᵥ-zero {μ = μ} {ν} hμ hν m = ⊗ᵥ-zeroᵐ μ ν (hμ m) (hν m)

ᵀᵥ-zero : {μ : MVal C} → Zeroᵥ μ → Zeroᵥ (μ ᵀᵥ)
ᵀᵥ-zero h Out = h In
ᵀᵥ-zero h In  = h Out

bdryᵥ-zero : {μ : MVal A} {ν : MVal B} → Zeroᵥ μ → Zeroᵥ ν → Zeroᵥ (bdryᵥ μ ν)
bdryᵥ-zero hμ hν = ⊗ᵥ-zero hμ (ᵀᵥ-zero hν)

-- a boundary weighs no outgoing message when neither does its domain, nor
-- its codomain an incoming one
bdryᵥ-out : (μ : MVal A) (ν : MVal B) → Zeroᵥ[ Out ] μ → Zeroᵥ[ In ] ν
          → Zeroᵥ[ Out ] (bdryᵥ μ ν)
bdryᵥ-out μ ν = ⊗ᵥ-zeroᵐ μ (ν ᵀᵥ)

opaque
  unfolding _⊗₀_ destruct-⊗ ⊗-right-intro ⊗-sym

  -- a summand's weight is the tensor's weight at the embedded message
  ⊗ᵥ-inˡ : {μ : MVal C} {ν : MVal D} → μ ≗ᵥ pull (ϵ ⊗R ↑) (μ ⊗ᵥ ν)
  ⊗ᵥ-inˡ In  _ = refl
  ⊗ᵥ-inˡ Out _ = refl

  ⊗ᵥ-inʳ : {μ : MVal C} {ν : MVal D} → ν ≗ᵥ pull (L⊗ ϵ ↑) (μ ⊗ᵥ ν)
  ⊗ᵥ-inʳ In  _ = refl
  ⊗ᵥ-inʳ Out _ = refl

⊗ᵥ-netˡ : (μ : MVal C) (ν : MVal D) → ∀ i o
        → netVal μ i o ≡ netVal (μ ⊗ᵥ ν) (app {mᵢ = In} (ϵ ⊗R ↑) i)
                                         (map (app {mᵢ = Out} (ϵ ⊗R ↑)) o)
⊗ᵥ-netˡ μ ν i o =
  trans (netVal-cong (⊗ᵥ-inˡ {μ = μ} {ν}) i o) (netVal-pull (ϵ ⊗R ↑) (μ ⊗ᵥ ν) i o)

⊗ᵥ-netʳ : (μ : MVal C) (ν : MVal D) → ∀ i o
        → netVal ν i o ≡ netVal (μ ⊗ᵥ ν) (app {mᵢ = In} (L⊗ ϵ ↑) i)
                                         (map (app {mᵢ = Out} (L⊗ ϵ ↑)) o)
⊗ᵥ-netʳ μ ν i o =
  trans (netVal-cong (⊗ᵥ-inʳ {μ = μ} {ν}) i o) (netVal-pull (L⊗ ϵ ↑) (μ ⊗ᵥ ν) i o)

------------------------------------------------------------------------
-- Value-neutral machines
------------------------------------------------------------------------

record Neutral (M : Machine A B) (μ : MVal (A ⊗ᵀ B)) : Set where
  field absorbs : ∀ {s i o s'} → Machine.stepRel M s i o s' → netVal μ i o ≡ 0ℤ

open Neutral public

neutral-cong : {M : Machine A B} {μ ν : MVal (A ⊗ᵀ B)}
             → μ ≗ᵥ ν → Neutral M μ → Neutral M ν
absorbs (neutral-cong h n) {i = i} {o = o} st =
  trans (sym (netVal-cong h i o)) (absorbs n st)

flow-neutral : {M : Machine A B} {μ : MVal (A ⊗ᵀ B)} → Neutral M μ
             → ∀ {s s'} (t : Trace M s s') → flow (netVal μ) t ≡ 0ℤ
flow-neutral n []                   = refl
flow-neutral n (t ∷ʳ⟨ _ , _ , st ⟩) = cong₂ _+_ (flow-neutral n t) (absorbs n st)

zero-neutral : {M : Machine A B} {μ : MVal (A ⊗ᵀ B)} → Zeroᵥ μ → Neutral M μ
absorbs (zero-neutral h) {i = i} {o = nothing} _ = cong (_- 0ℤ) (h In i)
absorbs (zero-neutral h) {i = i} {o = just x}  _ = cong₂ _-_ (h In i) (h Out x)

-- a machine none of whose wires carry weight absorbs nothing
zeroᵥ-neutral : {M : Machine A B} {μ : MVal A} {ν : MVal B}
              → Zeroᵥ μ → Zeroᵥ ν → Neutral M (bdryᵥ μ ν)
zeroᵥ-neutral hμ hν = zero-neutral (bdryᵥ-zero hμ hν)

-- a machine forwarding its input through `f` absorbs nothing as long as `f`
-- preserves weights
neutral-fwd : {M : Machine A B} {μ : MVal (A ⊗ᵀ B)}
              (f : Channel.inType (A ⊗ᵀ B) → Maybe (Channel.outType (A ⊗ᵀ B)))
            → (∀ {s i o s'} → Machine.stepRel M s i o s' → o ≡ f i)
            → (∀ i → maybe′ (μ Out) 0ℤ (f i) ≡ μ In i)
            → Neutral M μ
absorbs (neutral-fwd {μ = μ} f det h) {i = i} st =
  trans (cong (λ o → μ In i - maybe′ (μ Out) 0ℤ o) (det st))
        (trans (cong (μ In i -_) (h i)) (+-inverseʳ (μ In i)))

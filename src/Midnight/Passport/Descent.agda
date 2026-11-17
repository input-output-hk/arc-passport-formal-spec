{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

------------------------------------------------------------------------
-- Midnight.Passport.Descent
--
-- Descending into a wiring term. A `Path f h` addresses the subterm `h` of
-- `f`; `descend` reads it as a simulation of `⟦ h ⟧ by ⟦ f ⟧`, one block of
-- links per node, and `descendᶠ` pairs that simulation with the flow it
-- preserves, given that every box *off* the path moves no value
-- (`NeutralOn` for a subterm, `NeutralExcept` along a path). Since
-- `⟦ f ⊗ʷ g ⟧` rewires before and after running the factors, a `⊗ʷ` node
-- costs three links where a `∘ʷ` node costs one.
--
-- The wire lists a node tensors over are passed explicitly to the weight
-- combinators: letting Agda invert `?nl ++ ?nr` through the rewiring nest
-- exhausts the heap.
------------------------------------------------------------------------

module Midnight.Passport.Descent where

open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (refl)

open import CategoricalCrypto.Channel.Core hiding (_⊗₀_)
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Simulation
open import CategoricalCrypto.Machine.Valuation
open import CategoricalCrypto.Machine.Wiring

open import Midnight.Passport.Semantics

open HA

module Descend {cm : ChannelModel} (mm : MachineModel cm) where
  open MachineModel mm

  private variable
    n m k n' m' nl ml nr mr : ObjTerm
    h : WTerm n' m'

  data Path : WTerm n m → WTerm n' m' → Set where
    here : {f : WTerm n m} → Path f f
    ∘ˡ   : {f : WTerm m k} {g : WTerm n m} → Path f h → Path (f ∘ʷ g) h
    ∘ʳ   : {f : WTerm m k} {g : WTerm n m} → Path g h → Path (f ∘ʷ g) h
    ⊗ˡ   : {f : WTerm nl ml} {g : WTerm nr mr} → Path f h → Path (f ⊗ʷ g) h
    ⊗ʳ   : {f : WTerm nl ml} {g : WTerm nr mr} → Path g h → Path (f ⊗ʷ g) h

  -- `∘-simˡ` projects to the factor that runs first, `∘-simʳ` to the other
  descend : {f : WTerm n m} → Path f h → Sim ⟦ f ⟧ ⟦ h ⟧
  descend here   = idSim
  descend (∘ˡ p) = ∘-simʳ ∙ descend p
  descend (∘ʳ p) = ∘-simˡ ∙ descend p
  descend (⊗ˡ p) = ∘-simˡ ∙ ∘-simʳ ∙ ⊗₁-simˡ ∙ descend p
  descend (⊗ʳ p) = ∘-simˡ ∙ ∘-simʳ ∙ ⊗₁-simʳ ∙ descend p

module Descendᵥ {cm : ChannelModel} (mm : MachineModel cm)
                (w : ∀ c → MVal (ChannelModel.channelSemantics cm c)) where
  open MachineModel mm
  open Descend mm

  private variable n m n' m' : ObjTerm

  wiresᵥ : ∀ xs → MVal ⟦ xs ⟧₀
  wiresᵥ []       = 0ᵥ
  wiresᵥ (x ∷ xs) = w x ⊗ᵥ wiresᵥ xs

  wiresᵥ-zeroᵐ : ∀ {m} xs → (∀ c → Zeroᵥ[ m ] (w c)) → Zeroᵥ[ m ] (wiresᵥ xs)
  wiresᵥ-zeroᵐ []       _ _ = refl
  wiresᵥ-zeroᵐ (c ∷ xs) h   = ⊗ᵥ-zeroᵐ (w c) (wiresᵥ xs) (h c) (wiresᵥ-zeroᵐ xs h)

  mergeᵥ : ∀ xs ys → Neutral (mergeᴹ channelSemantics xs ys)
                             (bdryᵥ (wiresᵥ xs ⊗ᵥ wiresᵥ ys) (wiresᵥ (xs ++ ys)))
  mergeᵥ []       ys = unitorᵥ-neutral
  mergeᵥ (x ∷ xs) ys =
    ∘ᵥ-neutral (w x ⊗ᵥ (wiresᵥ xs ⊗ᵥ wiresᵥ ys))
      (⊗₁ᵥ-neutral idᵥ-neutral (mergeᵥ xs ys)) ⊗-assocᵥ-neutral

  splitᵥ : ∀ xs ys → Neutral (splitᴹ channelSemantics xs ys)
                             (bdryᵥ (wiresᵥ (xs ++ ys)) (wiresᵥ xs ⊗ᵥ wiresᵥ ys))
  splitᵥ []       ys = unitorᵥ⁻¹-neutral
  splitᵥ (x ∷ xs) ys =
    ∘ᵥ-neutral (w x ⊗ᵥ (wiresᵥ xs ⊗ᵥ wiresᵥ ys))
      ⊗-assoc⃖ᵥ-neutral (⊗₁ᵥ-neutral idᵥ-neutral (splitᵥ xs ys))

------------------------------------------------------------------------
-- Value-neutrality, by induction on a term
------------------------------------------------------------------------

  -- what it takes for a term to move no value: nothing of the wiring, one
  -- obligation per box
  NeutralOn : WTerm n m → Set
  NeutralOn {n} {m} (boxʷ b) = Neutral ⟦ boxʷ b ⟧ (bdryᵥ (wiresᵥ n) (wiresᵥ m))
  NeutralOn idʷ              = ⊤
  NeutralOn (f ∘ʷ g)         = NeutralOn f × NeutralOn g
  NeutralOn (f ⊗ʷ g)         = NeutralOn f × NeutralOn g

  neutralʷ : (f : WTerm n m) → NeutralOn f
           → Neutral ⟦ f ⟧ (bdryᵥ (wiresᵥ n) (wiresᵥ m))
  neutralʷ (boxʷ b) h = h
  neutralʷ idʷ      _ = idᵥ-neutral
  neutralʷ (_∘ʷ_ {m = mid} f g) (hf , hg) =
    ∘ᵥ-neutral (wiresᵥ mid) (neutralʷ f hf) (neutralʷ g hg)
  neutralʷ (_⊗ʷ_ {nl = nl} {ml = ml} {nr = nr} {mr = mr} f g) (hf , hg) =
    ∘ᵥ-neutral (wiresᵥ ml ⊗ᵥ wiresᵥ mr) (mergeᵥ ml mr)
      (∘ᵥ-neutral (wiresᵥ nl ⊗ᵥ wiresᵥ nr)
        (⊗₁ᵥ-neutral (neutralʷ f hf) (neutralʷ g hg)) (splitᵥ nl nr))

------------------------------------------------------------------------
-- The flow along a path
------------------------------------------------------------------------

  NeutralExcept : {f : WTerm n m} {h : WTerm n' m'} → Path f h → Set
  NeutralExcept here           = ⊤
  NeutralExcept (∘ˡ {g = g} p) = NeutralOn g × NeutralExcept p
  NeutralExcept (∘ʳ {f = f} p) = NeutralOn f × NeutralExcept p
  NeutralExcept (⊗ˡ {g = g} p) = NeutralOn g × NeutralExcept p
  NeutralExcept (⊗ʳ {f = f} p) = NeutralOn f × NeutralExcept p

  -- the same descent as `descend`, carrying the weights each link transports
  descendᶠ : {f : WTerm n m} {h : WTerm n' m'} (p : Path f h) → NeutralExcept p
           → SimFlow ⟦ f ⟧ ⟦ h ⟧ (bdryᵥ (wiresᵥ n) (wiresᵥ m))
                                 (bdryᵥ (wiresᵥ n') (wiresᵥ m'))
  descendᶠ here _ = idᶠ
  descendᶠ (∘ˡ {m = mid} {g = g} p) (hg , hs) =
    ∘ᶠʳ (wiresᵥ mid) (neutralʷ g hg) ∙ᶠ descendᶠ p hs
  descendᶠ (∘ʳ {m = mid} {f = f} p) (hf , hs) =
    ∘ᶠˡ (wiresᵥ mid) (neutralʷ f hf) ∙ᶠ descendᶠ p hs
  descendᶠ (⊗ˡ {nl = nl} {ml = ml} {nr = nr} {mr = mr} {g = g} p) (hg , hs) =
       ∘ᶠˡ (wiresᵥ ml ⊗ᵥ wiresᵥ mr) (mergeᵥ ml mr)
    ∙ᶠ ∘ᶠʳ (wiresᵥ nl ⊗ᵥ wiresᵥ nr) (splitᵥ nl nr)
    ∙ᶠ ⊗₁ᶠˡ (neutralʷ g hg)
    ∙ᶠ descendᶠ p hs
  descendᶠ (⊗ʳ {nl = nl} {ml = ml} {nr = nr} {mr = mr} {f = f} p) (hf , hs) =
       ∘ᶠˡ (wiresᵥ ml ⊗ᵥ wiresᵥ mr) (mergeᵥ ml mr)
    ∙ᶠ ∘ᶠʳ (wiresᵥ nl ⊗ᵥ wiresᵥ nr) (splitᵥ nl nr)
    ∙ᶠ ⊗₁ᶠʳ (neutralʷ f hf)
    ∙ᶠ descendᶠ p hs

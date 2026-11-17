{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

------------------------------------------------------------------------
-- Midnight.Passport.Flow
--
-- The architecture, seen as a flow-preserving simulation of the account
-- custody contract: `acPath` locates the contract in the architecture term,
-- `simAC` is the descent along it, and `flowAC` shows that descent moves
-- exactly the value the step did. Only the CHAIN wire carries value
-- (`wireᵥ`), so every box off the path is value-`Neutral` and the wiring
-- machines merely relabel.
--
-- Everything here is generic in the `ChannelModel`: elaborating it at the
-- concrete model of `Midnight.Passport.Properties` exhausts the heap.
------------------------------------------------------------------------

module Midnight.Passport.Flow where

open import Data.Empty using (⊥)
open import Data.Integer using (ℤ; 0ℤ)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CategoricalCrypto.Channel.Core hiding (_⊗₀_)
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Simulation
open import CategoricalCrypto.Machine.Valuation
open import CategoricalCrypto.Machine.Wiring

open import Midnight.Passport.Descent
open import Midnight.Passport.Semantics

open HA

module _ {cm : ChannelModel} (mm : MachineModel cm) where
  open MachineModel mm using (⟦architecture⟧; ⟦accountCustody⟧)
  open Descend mm

  -- past the passport key, into layer 2 and down to its third factor
  acPath : Path architectureᶜ (boxʷ accountCustody)
  acPath = ∘ʳ (∘ˡ (⊗ʳ (⊗ʳ (⊗ˡ here))))

  simAC : Sim ⟦architecture⟧ ⟦accountCustody⟧
  simAC = descend acPath

------------------------------------------------------------------------
-- Where the value is
------------------------------------------------------------------------

module _ {cm : ChannelModel} (mm : MachineModel cm)
         (txv : modeType In (ChannelModel.⟦CHAIN⟧ cm) → ℤ) where
  open MachineModel mm

  chainᵥ : MVal (channelSemantics CHAIN)
  chainᵥ In  x = txv x
  chainᵥ Out _ = 0ℤ

  -- only the CHAIN wire carries value …
  wireᵥ : ∀ c → MVal (channelSemantics c)
  wireᵥ CHAIN = chainᵥ
  wireᵥ _     = 0ᵥ

  -- … and only into a step
  wireᵥ-out : ∀ c → Zeroᵥ[ Out ] (wireᵥ c)
  wireᵥ-out TBD            _ = refl
  wireᵥ-out TBD-SYNC       _ = refl
  wireᵥ-out RECOVERY-P5    _ = refl
  wireᵥ-out READ-STATE     _ = refl
  wireᵥ-out JUBJUB-SCHNORR _ = refl
  wireᵥ-out STATE          _ = refl
  wireᵥ-out WITNESS-IPC    _ = refl
  wireᵥ-out CHAIN          _ = refl
  wireᵥ-out User           _ = refl

  open Descendᵥ mm wireᵥ

  NoCHAIN : ObjTerm → Set
  NoCHAIN []           = ⊤
  NoCHAIN (CHAIN ∷ _)  = ⊥
  NoCHAIN (_ ∷ xs)     = NoCHAIN xs

  wiresᵥ-out : ∀ xs → Zeroᵥ[ Out ] (wiresᵥ xs)
  wiresᵥ-out xs = wiresᵥ-zeroᵐ xs wireᵥ-out

  wiresᵥ-zero : ∀ xs → NoCHAIN xs → Zeroᵥ (wiresᵥ xs)
  wiresᵥ-zero []                     _ = 0ᵥ-zero
  wiresᵥ-zero (TBD ∷ xs)             p = ⊗ᵥ-zero 0ᵥ-zero (wiresᵥ-zero xs p)
  wiresᵥ-zero (TBD-SYNC ∷ xs)        p = ⊗ᵥ-zero 0ᵥ-zero (wiresᵥ-zero xs p)
  wiresᵥ-zero (RECOVERY-P5 ∷ xs)     p = ⊗ᵥ-zero 0ᵥ-zero (wiresᵥ-zero xs p)
  wiresᵥ-zero (READ-STATE ∷ xs)      p = ⊗ᵥ-zero 0ᵥ-zero (wiresᵥ-zero xs p)
  wiresᵥ-zero (JUBJUB-SCHNORR ∷ xs)  p = ⊗ᵥ-zero 0ᵥ-zero (wiresᵥ-zero xs p)
  wiresᵥ-zero (STATE ∷ xs)           p = ⊗ᵥ-zero 0ᵥ-zero (wiresᵥ-zero xs p)
  wiresᵥ-zero (WITNESS-IPC ∷ xs)     p = ⊗ᵥ-zero 0ᵥ-zero (wiresᵥ-zero xs p)
  wiresᵥ-zero (User ∷ xs)            p = ⊗ᵥ-zero 0ᵥ-zero (wiresᵥ-zero xs p)

  -- a machine wired only to CHAIN-free channels absorbs nothing
  boxᵥ-neutral : ∀ X Y {M : Machine ⟦ X ⟧₀ ⟦ Y ⟧₀} → NoCHAIN X → NoCHAIN Y
               → Neutral M (bdryᵥ (wiresᵥ X) (wiresᵥ Y))
  boxᵥ-neutral X Y p q = zeroᵥ-neutral (wiresᵥ-zero X p) (wiresᵥ-zero Y q)

------------------------------------------------------------------------
-- From the system boundary to the contract
------------------------------------------------------------------------

  μ⊤ : MVal (⟦ Var CHAIN ⟧₀ ⊗ᵀ ⟦ Var User ⟧₀)
  μ⊤ = bdryᵥ (wiresᵥ (Var CHAIN)) (wiresᵥ (Var User))

  μᴬ : MVal (⟦ Var TBD ⊗₀ Var TBD ⊗₀ Var CHAIN ⟧₀ ⊗ᵀ ⟦ Var JUBJUB-SCHNORR ⟧₀)
  μᴬ = bdryᵥ (wiresᵥ (Var TBD ⊗₀ Var TBD ⊗₀ Var CHAIN))
             (wiresᵥ (Var JUBJUB-SCHNORR))

  -- a step of either machine absorbs exactly the value it took in: nothing
  -- goes out weighed, and the codomain is CHAIN-free
  μ⊤-out : Zeroᵥ[ Out ] μ⊤
  μ⊤-out = bdryᵥ-out (wiresᵥ (Var CHAIN)) (wiresᵥ (Var User))
                     (wiresᵥ-out (Var CHAIN)) (wiresᵥ-zero (Var User) tt In)

  μᴬ-out : Zeroᵥ[ Out ] μᴬ
  μᴬ-out = bdryᵥ-out (wiresᵥ (Var TBD ⊗₀ Var TBD ⊗₀ Var CHAIN))
                     (wiresᵥ (Var JUBJUB-SCHNORR))
                     (wiresᵥ-out (Var TBD ⊗₀ Var TBD ⊗₀ Var CHAIN))
                     (wiresᵥ-zero (Var JUBJUB-SCHNORR) tt In)

  -- the boxes off `acPath`: the passport key answers on `User`, layer 1
  -- threads CHAIN through an `idʷ` leg, and no other box touches CHAIN
  flowAC : Preserves (simAC mm) (netVal μ⊤) (netVal μᴬ)
  flowAC = flowᶠ (descendᶠ (acPath mm)
    ( boxᵥ-neutral (Var RECOVERY-P5 ⊗₀ Var READ-STATE ⊗₀ Var JUBJUB-SCHNORR
                        ⊗₀ Var STATE ⊗₀ Var WITNESS-IPC) (Var User) tt tt
    , ( boxᵥ-neutral unit (Var TBD) tt tt
      , boxᵥ-neutral unit (Var TBD) tt tt
      , tt
      , boxᵥ-neutral unit (Var TBD-SYNC) tt tt )
    , boxᵥ-neutral unit (Var RECOVERY-P5) tt tt
    , boxᵥ-neutral unit (Var READ-STATE) tt tt
    , ( boxᵥ-neutral (Var TBD-SYNC) (Var STATE) tt tt
      , boxᵥ-neutral unit (Var WITNESS-IPC) tt tt )
    , tt ))

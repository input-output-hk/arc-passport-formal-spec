{-# OPTIONS --safe --without-K --guardedness #-}

module Midnight.ContractDSL.Observation where

open import Data.Bool.Base
open import Data.Empty
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Rational.Base
import Data.Rational.Properties as ℚP
import Data.Rational.Properties.Ext as ℚExt
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.GamePlaying.Partial
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy using (Strat)
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Setoid

private variable X Y : Set

-- Hidden states may differ while the same coins couple their public answers.
data Coupled (R : X → Y → Set) : Calls unitᴵ X → Calls unitᴵ Y → Set where
  returned : {x : X} {y : Y} → R x y → Coupled R (ret x) (ret y)
  flipped : {μ : Dist-ℚ Bool} {f : Bool → Calls unitᴵ X} {g : Bool → Calls unitᴵ Y} →
    (∀ b → Coupled R (f b) (g b)) → Coupled R (coin μ f) (coin μ g)
  diverged : Coupled R dead dead

coupled-read : {R : X → Y → Set} {t : Calls unitᴵ X} {u : Calls unitᴵ Y} → Coupled R t u →
  (F : X → ℚ) (G : Y → ℚ) → (∀ x y → R x y → F x ≡ G y) → E⊥ (evalC t) F ≡ E⊥ (evalC u) G
coupled-read (returned {x} {y} r) F G h =
  trans (E⊥-return x F) (trans (h x y r) (sym (E⊥-return y G)))
coupled-read (flipped {μ} {f} {g} h) F G eq =
  trans (E-bind μ (λ b → evalC (f b)) (maybeℚ F))
    (trans (lookupᴰℚ-cong-P (entries μ) (λ b → coupled-read (h b) F G eq))
      (sym (E-bind μ (λ b → evalC (g b)) (maybeℚ G))))
coupled-read diverged F G h = refl

partial-extensionality : {μ ν : Dist⊥ X} →
  (∀ G → E⊥ μ G ≡ E⊥ ν G) → μ ≈Mℚ ν
partial-extensionality {X = X} {μ = μ} {ν} eq F =
  trans (recenter μ) (trans (cong (_+ F nothing) (eq difference)) (sym (recenter ν)))
  where
  difference : X → ℚ
  difference x = F (just x) - F nothing
  recenter : (ρ : Dist⊥ X) → E ρ F ≡ E⊥ ρ difference + F nothing
  recenter ρ = trans (lookupᴰℚ-cong-P (entries ρ) λ
    { nothing → sym (ℚP.+-identityˡ (F nothing))
    ; (just x) → sym (ℚExt.−-+-cancel (F (just x)) (F nothing)) })
    (E-+const ρ (maybeℚ difference) (F nothing))

module Relational {B : Iface} (P Q : Protocol unitᴵ B) (R : St P → St Q → Set) where
  Answers : St P × Pos B → St Q × Pos B → Set
  Answers (s , a) (t , b) = R s t × a ≡ b

  observations :
    (∀ s t → R s t → ∀ q → Coupled Answers (step P s q) (step Q t q)) →
    (s : St P) (t : St Q) → R s t → (d : Strat (Neg B) (Pos B)) →
    runFrom P s d ≈Mℚ runFrom Q t d
  observations coupled s t r d = partial-extensionality
    {μ = runFrom P s d} {ν = runFrom Q t d} λ G →
    runWith⊥-bisim (kernel P) (kernel Q) R
      (λ s t r q F F′ h → coupled-read (coupled s t r q) F F′
        (λ { (s′ , a) (t′ , b) (r′ , eq) → h (s′ , a) (t′ , b) r′ eq })) d s t r G

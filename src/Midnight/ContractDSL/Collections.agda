{-# OPTIONS --safe --without-K #-}

module Midnight.ContractDSL.Collections where

open import Class.DecEq
open import Data.Bool hiding (_≟_)
open import Data.List hiding (lookup)
import Data.List.Membership.DecPropositional as Membership
open import Data.Maybe
open import Data.Product
open import Relation.Nullary
open import Function

private variable X K V : Set

member : ⦃ _ : DecEq X ⦄ → X → List X → Bool
member x xs = ⌊ Membership._∈?_ _≟_ x xs ⌋

insert : ⦃ _ : DecEq X ⦄ → X → List X → List X
insert x xs = case member x xs of λ where
  true  → xs
  false → x ∷ xs

remove : ⦃ _ : DecEq X ⦄ → X → List X → List X
remove x = filter (¬? ∘ (_≟ x))

lookup : ⦃ _ : DecEq K ⦄ → K → List (K × V) → Maybe V
lookup k xs = Data.Maybe.map proj₂ (find (λ entry → k ≟ proj₁ entry) xs)

update : ⦃ _ : DecEq K ⦄ → K → V → List (K × V) → List (K × V)
update k v [] = (k , v) ∷ []
update k v ((j , w) ∷ xs) = case k ≟ j of λ where
  (yes _) → (k , v) ∷ xs
  (no  _) → (j , w) ∷ update k v xs

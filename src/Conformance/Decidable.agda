{-# OPTIONS --safe --without-K #-}

module Conformance.Decidable where

open import Data.Maybe.Base using (Maybe; just)
open import Data.Maybe.Properties using (just-injective)
open import Function.Bundles using (mk↣)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (via-injection)

-- Decidable equality transported along an encoding with a partial left inverse; the
-- inverse law is typically `λ _ → refl` per constructor, so large enumerations and
-- records get decidable equality in linear rather than quadratic size.
via : {A C : Set} (to : A → C) (from : C → Maybe A) → (∀ a → from (to a) ≡ just a) →
  DecidableEquality C → DecidableEquality A
via to from back = via-injection (mk↣ {to = to} λ {a a′} eq → just-injective (trans (sym (back a)) (trans (cong from eq) (back a′))))

{-# OPTIONS --safe --without-K #-}

open import Midnight.ContractDSL.Storage

module Midnight.ContractDSL.Storage.Properties (A : Atoms) (S : Types.Schema A) where

open import Axiom.UniquenessOfIdentityProofs
open import Class.DecEq
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open Types A
open Schema S
open Lens

get-after-put : (f : Field) (v : El (code f)) (s : State) →
  get (lens f) (put (lens f) v s) ≡ v
get-after-put f v s with f ≟ f
... | yes eq rewrite Decidable⇒UIP.≡-irrelevant _≟_ eq refl = refl
... | no neq = ⊥-elim (neq refl)

put-back-get : (f : Field) (s : State) (g : Field) →
  put (lens f) (get (lens f) s) s g ≡ s g
put-back-get f s g with f ≟ g
... | yes refl = refl
... | no _ = refl

other-field-unchanged : (f g : Field) → f ≢ g → (v : El (code f)) (s : State) →
  get (lens g) (put (lens f) v s) ≡ get (lens g) s
other-field-unchanged f g neq v s with f ≟ g
... | yes eq = ⊥-elim (neq eq)
... | no _ = refl

last-put-wins : (f : Field) (first last : El (code f)) (s : State) (g : Field) →
  put (lens f) last (put (lens f) first s) g ≡ put (lens f) last s g
last-put-wins f first last s g with f ≟ g
... | yes refl = refl
... | no neq = other-field-unchanged f g neq first s


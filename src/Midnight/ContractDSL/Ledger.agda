{-# OPTIONS --safe --without-K #-}

module Midnight.ContractDSL.Ledger where

open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Class.DecEq

record Semantics : Set₁ where
  field State Kind : Set
        Op Res Failure : Kind → Set
        prepare : {k : Kind} → Op k → State → Failure k ⊎ (Res k × State)
        ⦃ DecEq-Res ⦄ : {k : Kind} → DecEq (Res k)

module Execution (L : Semantics) where
  open Semantics L

  validate : {k : Kind} → Op k → Res k → Failure k ⊎ (Res k × State) → Maybe State
  validate o x (inj₁ err) = nothing
  validate o x (inj₂ (y , t)) with x ≟ y
  ... | yes _ = just t
  ... | no _ = nothing

  -- Recompute the operation in the current state, requiring its recorded result.
  apply : {k : Kind} → Op k → Res k → State → Maybe State
  apply o r s = validate o r (prepare o s)

{-# OPTIONS --safe --without-K #-}

module Midnight.ContractDSL.Merkle where

open import Data.Bool.Base
open import Data.List.Base
open import Data.Nat.Base
open import Data.Nat.Properties using (_≟_)
open import Data.Product.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Midnight.ContractDSL.MidnightLedger
open import Midnight.ContractDSL.Program midnight Assertion
open import Midnight.ContractDSL.SymbolicDigest

-- Natural-valued symbols for Field inputs: no arithmetic or encoding claim.
-- The circuit accepts arbitrary values and arbitrary untrusted path witnesses.
FieldValue : Set
FieldValue = ℕ

record Sibling : Set where
  constructor sibling
  field onLeft : Bool
        digestValue : Digest
open Sibling public

record Path : Set where
  constructor path
  field leaf : FieldValue
        siblings : List Sibling
open Path public

foldPath : Digest → List Sibling → Digest
foldPath r [] = r
foldPath r (sibling false t ∷ ts) = foldPath (merkleBranch r t) ts
foldPath r (sibling true t ∷ ts) = foldPath (merkleBranch t r) ts

pathRoot : Path → Digest
pathRoot p = foldPath (merkleLeaf (leaf p)) (siblings p)

-- Manual correspondence: keeping-data-private.md#making-use-of-merkle-trees.
checkSecure : FieldValue → Path → Program ⊤
checkSecure item p = do
  assert ⌊ leaf p ≟ item ⌋ assertionFailed
  ok ← perform (ledger (checkRoot (pathRoot p)))
  assert ok assertionFailed

checkInsecure : (FieldValue → Bool) → FieldValue → Path → Bool → Program ⊤
checkInsecure classify item p mask = do
  checkSecure item p
  ok ← perform (ledger (flagMember (classify item xor mask)))
  assert ok assertionFailed

data Variant : Set where
  secure insecure : Variant

executionProgram : (FieldValue → Bool) → Variant → FieldValue → Path → Bool → Program ⊤
executionProgram classify secure item p mask = checkSecure item p
executionProgram classify insecure item p mask = checkInsecure classify item p mask

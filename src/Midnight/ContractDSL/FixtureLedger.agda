{-# OPTIONS --safe --without-K #-}

module Midnight.ContractDSL.FixtureLedger where

open import Data.Bool.Base
open import Data.Nat.Base

open import Midnight.ContractDSL.MidnightLedger
open import Midnight.ContractDSL.SymbolicDigest

fixtureRoot : Digest
fixtureRoot = padRoot 8 2
  (merkleBranch (merkleBranch (merkleLeaf 1) (merkleLeaf 2))
                (merkleBranch (merkleLeaf 3) (merkleLeaf 4)))

fixtureState : Bool → Digest → ℕ → ℕ → State
fixtureState l a v r = state l a v r fixtureRoot true true

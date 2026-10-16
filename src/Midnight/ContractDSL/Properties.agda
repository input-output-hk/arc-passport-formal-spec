{-# OPTIONS --safe --without-K #-}

open import Midnight.ContractDSL.Ledger

module Midnight.ContractDSL.Properties (L : Semantics) (Assertion : Set) where

open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (ℕ)
open import Data.Sum.Base using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Midnight.ContractDSL.Program L Assertion
import Midnight.ContractDSL.ReplayProof L Assertion as Proof

open Semantics L

private variable A : Set

-- Replaying a successful program's journal preserves its result and journal on re-evaluation.
replay-refinement : (p : Program A) (now : ℕ) {s₀ s t₀ t : State} {a : A} {j : Journal} →
  eval p s₀ ≡ inj₂ (finished a t₀ j) → replay now j s ≡ just t →
  eval p s ≡ inj₂ (finished a t j)
replay-refinement = Proof.replay-refinement

-- A successful evaluation replays on its initial view when its time conditions hold.
same-view-replay : (p : Program A) (now : ℕ) {s t : State} {a : A} {j : Journal} →
  eval p s ≡ inj₂ (finished a t j) → Eligible now j → replay now j s ≡ just t
same-view-replay = Proof.same-view-replay

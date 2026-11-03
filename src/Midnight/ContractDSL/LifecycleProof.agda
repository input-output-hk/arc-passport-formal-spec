{-# OPTIONS --safe --without-K #-}

module Midnight.ContractDSL.LifecycleProof where

open import Level
open import Midnight.ContractDSL.Lifecycle
open import Relation.Binary.Construct.Closure.ReflexiveTransitive

module Proofs {ℓ p} (L : Lifecycle ℓ) (identity : Lifecycle.Identity L)
  (Invariant : Lifecycle.State L → Set p) where
  open Lifecycle L
  open Runs L identity

  trace-invariant :
    (∀ {s t} → Step s t → Invariant s → Invariant t) →
    ∀ {s t} → Trace s t → Invariant s → Invariant t
  trace-invariant preserved ε initial = initial
  trace-invariant preserved (step ◅ rest) initial =
    trace-invariant preserved rest (preserved step initial)

  history-invariant :
    (∀ env d outcome s → Deploy identity env d outcome s → Invariant s) →
    (∀ {s t} → Step s t → Invariant s → Invariant t) →
    ∀ {s} → History s → Invariant s
  history-invariant initialized preserved h = trace-invariant preserved
    (History.execution h)
    (initialized (History.deploymentEnvironment h) (History.deployment h)
      (History.deploymentOutcome h) (History.initial h) (History.initialized h))

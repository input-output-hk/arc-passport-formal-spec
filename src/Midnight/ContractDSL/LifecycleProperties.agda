{-# OPTIONS --safe --without-K #-}

-- Generic induction rules, not established invariants of any particular contract.
-- Both the predicate and its deployment/step preservation obligations are inputs;
-- no instance discharges them here, and they are not P5′/P11 proofs.
-- Scope: docs/conformance-testing-plan.md#deployment-rooted-local-histories.
module Midnight.ContractDSL.LifecycleProperties where

open import Level
open import Midnight.ContractDSL.Lifecycle
import Midnight.ContractDSL.LifecycleProof as Proof

module Properties {ℓ p} (L : Lifecycle ℓ) (identity : Lifecycle.Identity L)
  (Invariant : Lifecycle.State L → Set p) where
  open Lifecycle L
  open Runs L identity
  module P = Proof.Proofs L identity Invariant

  -- A predicate preserved by every labelled step persists along any finite trace.
  trace-invariant :
    (∀ {s t} → Step s t → Invariant s → Invariant t) →
    ∀ {s t} → Trace s t → Invariant s → Invariant t
  trace-invariant = P.trace-invariant

  -- Establishment for every Deploy witness plus step preservation gives an invariant.
  history-invariant :
    (∀ env d outcome s → Deploy identity env d outcome s → Invariant s) →
    (∀ {s t} → Step s t → Invariant s → Invariant t) →
    ∀ {s} → History s → Invariant s
  history-invariant = P.history-invariant

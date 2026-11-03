{-# OPTIONS --safe --without-K #-}

-- Deployment-rooted relational histories, independent of a contract language/VM.
-- Deploy selects roots and records an instance-defined creation observation as
-- its Outcome. Calling those roots successful, and excluding failed creation,
-- is the supplied relation's responsibility, not a generic constraint on Outcome.
-- Invoke may include refused attempts; neither relation must be deterministic.
-- One identity indexes each history; no environment or security policy is chosen.
-- Finite local histories only, not ledger admission/adoption, infinite executions
-- or leakage; scope: docs/conformance-testing-plan.md#deployment-rooted-local-histories.
module Midnight.ContractDSL.Lifecycle where

open import Level
open import Relation.Binary.Construct.Closure.ReflexiveTransitive

record Lifecycle (ℓ : Level) : Set (suc ℓ) where
  field Identity DeploymentEnvironment Environment Deployment Call State Outcome : Set ℓ
        Deploy : Identity → DeploymentEnvironment → Deployment → Outcome → State → Set ℓ
        Invoke : Identity → Environment → Call → State → Outcome → State → Set ℓ

module Runs {ℓ} (L : Lifecycle ℓ) (identity : Lifecycle.Identity L) where
  open Lifecycle L

  -- Labels retain attempted calls and their outcomes, including refusal when
  -- the supplied Invoke relation represents it. No observer projection is implied.
  record Step (before after : State) : Set ℓ where
    constructor event
    field environment : Environment
          call : Call
          outcome : Outcome
          executed : Invoke identity environment call before outcome after

  Trace : State → State → Set ℓ
  Trace = Star Step

  record History (final : State) : Set ℓ where
    constructor rooted
    field deploymentEnvironment : DeploymentEnvironment
          deployment : Deployment
          deploymentOutcome : Outcome
          initial : State
          initialized : Deploy identity deploymentEnvironment deployment deploymentOutcome initial
          execution : Trace initial final

  -- Extension preserves the original deployment witness. Runtime labels have
  -- type Call, not Deployment; semantic restrictions on Call belong to L.
  extend : ∀ {s t} → History s → Trace s t → History t
  extend h trace = let open History h in
    rooted deploymentEnvironment deployment deploymentOutcome initial initialized (execution ◅◅ trace)

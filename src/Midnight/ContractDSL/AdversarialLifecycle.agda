{-# OPTIONS --safe --without-K #-}

-- Deployment-rooted Lifecycle histories interleaved with symbolic signing events
-- (Midnight.ContractDSL.SymbolicSigning). Joint state pairs contract state with
-- signing knowledge; each step is an actual signing Transition or an actual
-- Invoke, and leaves the other component unchanged. Events interleave in any
-- order, without clock or fairness constraints. Deployment is not a step.
--
-- `required before environment call` lists the signature tokens that must
-- already be available to construct that attempted call from contract state
-- `before` (signed requests may bind nonces or keys stored there). It is an
-- interpretation boundary, not an acceptance or authorization predicate: each
-- instance must justify it, and a call carrying invalid signatures may require
-- no token at all. Nothing here extracts tokens from concrete signature bytes
-- or proves that accepted calls are authorized. Invocation consults neither
-- live contract authority nor the outcome, so refused attempts remain steps,
-- and using a token never consumes it.
-- Statements: Midnight.ContractDSL.AdversarialLifecycleProperties.
-- Scope: docs/conformance-testing-plan.md#symbolic-signing-and-adversarial-histories.
module Midnight.ContractDSL.AdversarialLifecycle where

open import Data.List.Base using (List)
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive

open import Midnight.ContractDSL.Lifecycle
import Midnight.ContractDSL.SymbolicSigning as Signing

module Joint {ℓ} (L : Lifecycle ℓ) (identity : Lifecycle.Identity L)
  (S : Signing.Interface ℓ)
  (required : Lifecycle.State L → Lifecycle.Environment L → Lifecycle.Call L →
    List (Signing.Model.Token S)) where
  open Lifecycle L
  module Contract = Runs L identity
  module Signatures = Signing.Model S

  JointState : Set ℓ
  JointState = State × Signatures.State

  data Step : JointState → JointState → Set ℓ where
    signing : ∀ {contract before after} →
      Signatures.Transition before after →
      Step (contract , before) (contract , after)
    invocation : ∀ {before after knowledge} environment call outcome →
      All (Signatures.Available knowledge) (required before environment call) →
      Invoke identity environment call before outcome after →
      Step (before , knowledge) (after , knowledge)

  Trace : JointState → JointState → Set ℓ
  Trace = Star Step

  -- Rooted in an original contract deployment and the empty signing state.
  record History (final : JointState) : Set ℓ where
    constructor rooted
    field deploymentEnvironment : DeploymentEnvironment
          deployment : Deployment
          deploymentOutcome : Outcome
          initial : State
          initialized : Deploy identity deploymentEnvironment deployment deploymentOutcome initial
          execution : Trace (initial , Signatures.initial) final

  extend : ∀ {s t} → History s → Trace s t → History t
  extend h trace = let open History h in
    rooted deploymentEnvironment deployment deploymentOutcome initial initialized (execution ◅◅ trace)

  -- Projections keep one component's steps, unchanged and in order, and drop
  -- the other's. Joint steps therefore cannot alter account semantics or
  -- introduce signing knowledge without a signing Transition.
  contractTrace : ∀ {s t} → Trace s t → Contract.Trace (proj₁ s) (proj₁ t)
  contractTrace ε = ε
  contractTrace (signing _ ◅ rest) = contractTrace rest
  contractTrace (invocation environment call outcome _ executed ◅ rest) =
    Contract.event environment call outcome executed ◅ contractTrace rest

  signingTrace : ∀ {s t} → Trace s t → Signatures.Trace (proj₂ s) (proj₂ t)
  signingTrace ε = ε
  signingTrace (signing x ◅ rest) = x ◅ signingTrace rest
  signingTrace (invocation _ _ _ _ _ ◅ rest) = signingTrace rest

  -- The account history keeps the joint history's own deployment witness.
  contractHistory : ∀ {final} → History final → Contract.History (proj₁ final)
  contractHistory h = let open History h in
    Contract.rooted deploymentEnvironment deployment deploymentOutcome initial initialized
      (contractTrace execution)

  signingHistory : ∀ {final} → History final →
    Signatures.Trace Signatures.initial (proj₂ final)
  signingHistory h = signingTrace (History.execution h)

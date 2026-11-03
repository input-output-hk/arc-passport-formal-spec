{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes using (Primitives)

-- Finite local source-execution histories for the full account: not ledger
-- admission or adoption, infinite executions, leakage, or P5′/P11 results.
-- Scope and limits: docs/conformance-testing-plan.md#deployment-rooted-local-histories.
-- P is an arbitrary primitive backend, with no cryptographic laws assumed.
-- Environment supplies time/caller/coin independently at every attempt; the
-- fixed history identity supplies Context.self and is not caller-controlled.
module Passport.AccountLifecycle (P : Primitives) where

open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)
import Data.List.Membership.DecPropositional as Membership
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (Σ; _×_; _,_)
import Data.String as String
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Level using (0ℓ)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (yes; no)

open import Conformance.FullAccountTypes
import Conformance.FullAccount as Model
import Midnight.ContractDSL.Lifecycle as Generic
import Passport.Account as Account

record Environment : Set where
  constructor environment
  field time : ℕ
        callerValue witnessedCoin : Value

executionContext : Value → Environment → Context
executionContext address env = context address (Environment.time env)
  (Environment.callerValue env) (Environment.witnessedCoin env)

-- Runtime boundary. Conformance.FullAccount.runtimeNames P is the name projection
-- of AccountSemantics.runtimeEntrypoints. The constructor entry is not in that
-- list: AccountSemantics.entrypoints prepends it separately, and no runtime
-- entry's literal name is "constructor". So constructor calls, unknown names and
-- the dispatcher's "unknown runtime circuit" refusal never label a step. Every
-- refusal a known runtime entrypoint can produce is retained as a reverted step:
-- decoding refusals from circuit-argument (including ABI overflow), runtime-context,
-- held-coin and ledger-state validation, and assertion, bounds or primitiveFailure
-- refusals from the circuit body or its primitives.
record RuntimeCall : Set where
  constructor runtimeCall
  field request : RawCall
        runtime : name request ∈ Model.runtimeNames P

-- This checks the entrypoint-name boundary only; all other validation stays in
-- the existing dispatcher, with its existing refusal observations.
decodeRuntime : RawCall → Maybe RuntimeCall
decodeRuntime call with Membership._∈?_ String._≟_ (name call) (Model.runtimeNames P)
... | no _ = nothing
... | yes runtime = just (runtimeCall call runtime)

DeploymentSucceeded : Value → Environment → Account.Deployment → Account.Observation → State → Set
DeploymentSucceeded address env d (Account.committed value effects) s =
  Account.deploy P (executionContext address env) d ≡ accepted value s effects
DeploymentSucceeded address env d (Account.reverted error) s = ⊥

-- Invocation is the existing full-state Account.Transition relation, at the
-- context formed from the history identity and the step environment.
lifecycle : Generic.Lifecycle 0ℓ
lifecycle = record
  { Identity = Value
  ; DeploymentEnvironment = Environment
  ; Environment = Environment
  ; Deployment = Account.Deployment
  ; Call = RuntimeCall
  ; State = State
  ; Outcome = Account.Observation
  ; Deploy = DeploymentSucceeded
  ; Invoke = λ address env call →
      Account.Transition P (executionContext address env) (RuntimeCall.request call)
  }

-- Failed deployment yields an error, never a rooted history.
start : (address : Value) → Environment → Account.Deployment →
  Error ⊎ Σ State (Generic.Runs.History lifecycle address)
start address env d with Account.deploy P (executionContext address env) d in deployed
... | rejected error = inj₁ error
... | accepted value s effects = inj₂
  (s , Generic.Runs.rooted env d (Account.committed value effects) s deployed ε)

-- Executable trace construction keeps refusals and the original state on them.
-- Attach the resulting trace to a rooted history with Generic.Runs.extend.
run : (address : Value) (s : State) → List (Environment × RuntimeCall) →
  Σ State (Generic.Runs.Trace lifecycle address s)
run address s [] = s , ε
run address s ((env , call) ∷ calls)
  with Account.step P (executionContext address env) (RuntimeCall.request call) s in executed
... | observation , next with run address next calls
...   | final , trace =
  final , Generic.Runs.event env call observation (Account.transition executed) ◅ trace

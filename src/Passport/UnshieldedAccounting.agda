{-# OPTIONS --safe --without-K #-}

-- Local declared-effect accounting, not ledger adoption, fee accounting or
-- SnapshotSound. Missing balance-map entries denote zero. Runtime histories
-- are the actual dispatcher histories of AccountLifecycle, rooted at deployment.
module Passport.UnshieldedAccounting where

open import Conformance.FullAccountTypes
open import Data.Bool.Base using (true; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Maybe.Base using (nothing; just)
open import Data.Nat.Base using (ℕ; _+_; _∸_; _≤ᵇ_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Conformance.FullAccount as Model
import Conformance.FullAccountBody as Body
import Midnight.ContractDSL.Lifecycle as Generic
import Passport.Account as Account
import Passport.AccountLifecycle as Lifecycle
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)

balanceMap : State → Value
balanceMap = cell "unshielded_balances"

balanceOf : Value → Value → ℕ
balanceOf color balances with lookupMap color (fields balances)
... | nothing = 0
... | just v = number v

balance : Value → State → ℕ
balance color s = balanceOf color (balanceMap s)

data Transfer : Set where
  received sent : Value → ℕ → Transfer

transfers : List Effect → List Transfer
transfers [] = []
transfers (receiveUnshielded color amount ∷ es) = received color amount ∷ transfers es
transfers (sendUnshielded color amount recipient ∷ es) = sent color amount ∷ transfers es
transfers (_ ∷ es) = transfers es

amountFor : Value → Value → ℕ → ℕ
amountFor query color amount = if equal query color then amount else 0

receivedTotal sentTotal : Value → List Transfer → ℕ
receivedTotal color [] = 0
receivedTotal color (received c a ∷ es) = amountFor color c a + receivedTotal color es
receivedTotal color (_ ∷ es) = receivedTotal color es
sentTotal color [] = 0
sentTotal color (sent c a ∷ es) = amountFor color c a + sentTotal color es
sentTotal color (_ ∷ es) = sentTotal color es

data Action : Set where
  idle : Action
  credit debit : Value → ℕ → Action

actionTransfers : Action → List Transfer
actionTransfers idle = []
actionTransfers (credit color amount) = received color amount ∷ []
actionTransfers (debit color amount) = sent color amount ∷ []

updatedMap : Action → State → Value
updatedMap idle s = balanceMap s
updatedMap (credit color amount) s = tuple
  (insertMap color (nat (balance color s + amount)) (fields (balanceMap s)))
updatedMap (debit color amount) s = tuple
  (insertMap color (nat (balance color s ∸ amount)) (fields (balanceMap s)))

Funded : Action → State → Set
Funded idle s = true ≡ true
Funded (credit color amount) s = true ≡ true
Funded (debit color amount) s = (amount ≤ᵇ balance color s) ≡ true

record Accounting (action : Action) (before : State) (effects : List Effect) (after : State) : Set where
  constructor accounting
  field declared : transfers effects ≡ actionTransfers action
        updated : balanceMap after ≡ updatedMap action before
        funded : Funded action before

Conserved : State → List Transfer → State → Set
Conserved before effects after = ∀ color →
  balance color after + sentTotal color effects ≡ balance color before + receivedTotal color effects

module Semantics (P : Primitives) where
  open Model.AccountSemantics P
  open Body P using (withdrawUnshielded)

  action : Entrypoint → List Value → Action
  action depositPublic xs = credit (get 0 xs) (number (get 1 xs))
  action (device _ withdrawUnshielded) xs = debit (get 0 xs) (number (get 1 xs))
  action (grant _ withdrawUnshielded) xs = debit (get 0 xs) (number (get 1 xs))
  action _ xs = idle

  dispatchedAction : RawCall → Action
  dispatchedAction call with lookupEntrypoint (name call) entrypoints
  ... | nothing = idle
  ... | just e = action e (arguments call)

  module Histories (address : Value) where
    open Lifecycle P
    module Runs = Generic.Runs lifecycle address

    observationTransfers : Account.Observation → List Transfer
    observationTransfers (Account.committed _ es) = transfers es
    observationTransfers (Account.reverted _) = []

    traceTransfers : ∀ {s t} → Runs.Trace s t → List Transfer
    traceTransfers ε = []
    traceTransfers (step ◅ rest) = observationTransfers (Runs.Step.outcome step) ++ traceTransfers rest

    historyTransfers : ∀ {s} → Runs.History s → List Transfer
    historyTransfers h = observationTransfers (Runs.History.deploymentOutcome h) ++ traceTransfers (Runs.History.execution h)

    -- Constructor public effects are empty; refused attempts contribute none.
    HistoryAccounted : ∀ {s} → Runs.History s → Set
    HistoryAccounted {s} h = ∀ color →
      balance color s + sentTotal color (historyTransfers h) ≡ receivedTotal color (historyTransfers h)

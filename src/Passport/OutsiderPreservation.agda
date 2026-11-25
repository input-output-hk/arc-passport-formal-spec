{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes using (Primitives; Value)

-- Restricted local preservation, not NonGriefability or execution availability.
-- Outsider means a permissionless deposit or an actually refused runtime attempt;
-- it does not mean every call made by an identity without an enrolled device.
-- Successful bootstrap and permissionless recovery finalisation are deliberately
-- outside the class: both legitimately install authority without a device signature.
module Passport.OutsiderPreservation (P : Primitives) (address : Value) where

open import Conformance.FullAccountTypes
import Conformance.FullAccount as Model
open import Data.Bool.Base using (false; true)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (ℕ; suc; _+_; _<ᵇ_; _^_)
open import Data.String.Base using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Midnight.ContractDSL.Lifecycle as Generic
import Passport.Account as Account
open import Passport.AccountLifecycle P

module Semantics = Model.AccountSemantics P
module Runs = Generic.Runs lifecycle address
open Semantics using (Entrypoint; depositPublic; depositPrivate)

-- Exactly AccountSemantics.dispatch's lookupEntrypoint/name/entrypoints lookup.
-- AccountSecurity.resolve and UnshieldedAccounting.Semantics.dispatchedAction
-- apply that same lookup directly to the raw RuntimeCall.request.
resolve : RuntimeCall → Data.Maybe.Base.Maybe Entrypoint
resolve call = Semantics.lookupEntrypoint (name (RuntimeCall.request call)) Semantics.entrypoints

-- Classification uses dispatcher names and observed refusal, never a preservation
-- premise. An accepted unregistered-device call is NOT silently classified here.
data OutsiderAction (call : RuntimeCall) : Account.Observation → Set where
  publicDeposit : ∀ {v es} → resolve call ≡ just depositPublic →
    OutsiderAction call (Account.committed v es)
  privateDeposit : ∀ {v es} → resolve call ≡ just depositPrivate →
    OutsiderAction call (Account.committed v es)
  refused : ∀ e → OutsiderAction call (Account.reverted e)

data OutsiderTrace : State → State → Set where
  idle : ∀ {s} → OutsiderTrace s s
  attempt : ∀ {s u t} → (step : Runs.Step s u) →
    OutsiderAction (Runs.Step.call step) (Runs.Step.outcome step) →
    OutsiderTrace u t → OutsiderTrace s t

-- These are exactly the cells that either successful deposit may write.
-- The frame below protects every other cell, including future unrelated cells.
record Protected (k : String) : Set where
  constructor protected
  field notBalance : stringEqual k "unshielded_balances" ≡ false
        notRound : stringEqual k "round" ≡ false
        notInbox : stringEqual k "inbox" ≡ false
        notInboxCount : stringEqual k "inbox_count" ≡ false

Frame : State → State → Set
Frame before after = ∀ k → Protected k →
  lookupCell k (ledger after) ≡ lookupCell k (ledger before)

-- Selected recovery resources are the published key/session/coefficients/wrap,
-- the pending proposal and veto deadline, plus the encryption key. Their bytes
-- are preserved, not their decryptability, proving access or usefulness at a time.
resources : List String
resources = "devices" ∷ "device_epoch" ∷ "device_count" ∷ "auth_nonce" ∷
  "grants" ∷ "grant_generation" ∷ "boot" ∷ "booted" ∷ "enc_key" ∷
  "recovery_pk" ∷ "recovery_session" ∷ "recovery_phi" ∷ "recovery_phi_len" ∷
  "recovery_wrap" ∷ "recovery_version" ∷ "pending_recovery" ∷ "pending_entry" ∷
  "pending_recovery_pk" ∷ "pending_not_before" ∷ "veto_window" ∷ []

ResourcesPreserved : State → State → Set
ResourcesPreserved before after = ∀ {k} → k ∈ resources →
  lookupCell k (ledger after) ≡ lookupCell k (ledger before)

Enrolled : Value → State → Set
Enrolled entry s = member entry (fields (cell "devices" s)) ≡ true

successfulDeposits : ∀ {s t} → OutsiderTrace s t → ℕ
successfulDeposits idle = 0
successfulDeposits (attempt _ (publicDeposit _) rest) = suc (successfulDeposits rest)
successfulDeposits (attempt _ (privateDeposit _) rest) = suc (successfulDeposits rest)
successfulDeposits (attempt _ (refused _) rest) = successfulDeposits rest

roundValue : State → ℕ
roundValue s = number (cell "round" s)

RoundFits : State → Set
RoundFits s = (roundValue s <ᵇ 2 ^ 64) ≡ true

-- Each accepted deposit consumes exactly one round, even a zero-value deposit;
-- refusals consume none in this local transaction model. Thus, from round r,
-- d accepted deposits require r + d < 2^64. Inbox capacity is independently
-- Uint64 and a credited public balance is Uint128. These are not cost bounds:
-- no fee, proof, witness, time, fairness or transaction-admission model is added.
RoundCost : ∀ {s t} → OutsiderTrace s t → Set
RoundCost {s} {t} trace = roundValue t ≡ successfulDeposits trace + roundValue s

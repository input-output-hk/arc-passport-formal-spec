{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

-- Authority confinement for local source-runtime withdrawals, not asset
-- recoverability, admission on a ledger, availability or global non-griefability.
-- Statements and proof references: Passport.GrantConfinementProperties.
module Passport.GrantConfinement (P : Primitives) (address : Value) where

import Conformance.FullAccount as Model
open import Conformance.FullAccountBody P
open import Conformance.FullAccountGrant P
open import Conformance.FullAccountGrantSecurity P
open import Conformance.FullAccountLayouts using (grantNonce)
open import Data.Bool.Base using (false; true)
open import Data.List.Base using (List; []; _∷_; take)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe.Base using (Maybe; just)
open import Data.Nat.Base using (suc)
open import Data.String.Base using (String)
import Midnight.ContractDSL.Lifecycle as Generic
import Passport.Account as Account
open import Passport.AccountLifecycle P
open import Passport.GrantEffects P
open import Passport.GrantSpending P using (parseGrantAuth)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Semantics = Model.AccountSemantics P
module Runs = Generic.Runs lifecycle address

-- These five cells may change: settlement updates grants and round; custody
-- debits public balances, and shielded change can append to the inbox.
record Protected (k : String) : Set where
  constructor protected
  field notGrants : stringEqual k "grants" ≡ false
        notRound : stringEqual k "round" ≡ false
        notBalance : stringEqual k "unshielded_balances" ≡ false
        notInbox : stringEqual k "inbox" ≡ false
        notInboxCount : stringEqual k "inbox_count" ≡ false

Frame : State → State → Set
Frame before after = ∀ k → Protected k →
  lookupCell k (ledger after) ≡ lookupCell k (ledger before)

-- Exact stored bytes and counters, including pending recovery state. Neither
-- decryptability of recovery material nor usefulness of inbox entries is claimed.
authorityCells : List String
authorityCells = "devices" ∷ "device_epoch" ∷ "device_count" ∷ "auth_nonce" ∷
  "grant_generation" ∷ "boot" ∷ "booted" ∷ "enc_key" ∷
  "recovery_pk" ∷ "recovery_session" ∷ "recovery_phi" ∷ "recovery_phi_len" ∷
  "recovery_wrap" ∷ "recovery_version" ∷ "pending_recovery" ∷ "pending_entry" ∷
  "pending_recovery_pk" ∷ "pending_not_before" ∷ "veto_window" ∷ []

AuthorityPreserved : State → State → Set
AuthorityPreserved before after = ∀ {k} → k ∈ authorityCells →
  lookupCell k (ledger after) ≡ lookupCell k (ledger before)

Enrolled : Value → State → Set
Enrolled entry s = member entry (fields (cell "devices" s)) ≡ true

-- mutation fixes the complete grants-map insertion. ownFields preserves the
-- scope (including expiry, caps, pins and read authority), issuance epoch/gen/
-- issuedAt, active flag and reserved window fields; only nonce and spent change.
-- The spent commitment is of spentPrev + amount, as recorded by mutation's
-- ScopeAdmitted.spentTotal and Settlement.spentCommitted. No hash-binding or
-- signature-ownership premise is needed for these source-derived frame facts.
record Confinement (c : Curve) (op : Operation) (ctx : Context) (ga : GrantAuth)
    (xs : List Value) (before after : State) : Set where
  field mutation : SpendMutation c op ctx ga xs before after
        authorityFrame : Frame before after
  module M = SpendMutation mutation
  module E = GrantCallEvidence M.evidence
  field ownFields : SettledRecord E.grantRecord (suc (number (grantNonce E.grantRecord)))
          (Settlement.commitment E.settlement) M.settledValue
        ownStored : lookupMap E.identifier (fields (cell "grants" after)) ≡ just M.settledValue
        otherGrant : ∀ other → equal other E.identifier ≡ false →
          lookupMap other (fields (cell "grants" after)) ≡ lookupMap other (fields (cell "grants" before))

resolve : RuntimeCall → Maybe Semantics.Entrypoint
resolve call = Semantics.lookupEntrypoint (name (RuntimeCall.request call)) Semantics.entrypoints

stepContext : ∀ {s t} → Runs.Step s t → Context
stepContext step = executionContext address (Runs.Step.environment step)

stepArguments : ∀ {s t} → Runs.Step s t → List Value
stepArguments step = arguments (RuntimeCall.request (Runs.Step.call step))

RuntimeConfinement : ∀ {s t} → Runs.Step s t → Curve → Operation → Set
RuntimeConfinement {s} {t} step c op = Confinement c op (stepContext step)
  (parseGrantAuth c op (stepArguments step)) (take 3 (stepArguments step)) s t

-- Refusals can be to any runtime entrypoint; they commit no intermediate writes.
-- Successful actions are exactly the three grant-withdrawal classes, all curves.
data GrantAction (call : RuntimeCall) : Account.Observation → Set where
  grantWithdrawal : ∀ {v es} c op → Withdrawal op → resolve call ≡ just (Semantics.grant c op) →
    GrantAction call (Account.committed v es)
  refused : ∀ e → GrantAction call (Account.reverted e)

data GrantTrace : State → State → Set where
  idle : ∀ {s} → GrantTrace s s
  attempt : ∀ {s u t} → (step : Runs.Step s u) →
    GrantAction (Runs.Step.call step) (Runs.Step.outcome step) → GrantTrace u t → GrantTrace s t

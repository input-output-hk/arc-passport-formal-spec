{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes using (Primitives; Value)

-- Trace occurrence, not endpoint matching: an accepted submission installs the
-- named fields, and only refusals or pending-preserving ordinary calls follow.
-- Guard certificates remain in AccountSecurity; proofs and advertised claims:
-- AccountRecoveryOccurrenceProof and AccountRecoveryOccurrenceProperties.
module Passport.AccountRecoveryOccurrence (P : Primitives) (address : Value) where

open import Data.Bool.Base using (true)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (_≤_)
open import Data.Product using (Σ)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

import Conformance.FullAccount as Model
open import Conformance.FullAccountBody P using (cancelRecovery)
import Conformance.FullAccountRecoverySecurity as RecoverySecurity
open import Conformance.FullAccountTypes
import Midnight.ContractDSL.Lifecycle as Generic
import Passport.Account as Account
open import Passport.AccountLifecycle P

module Semantics = Model.AccountSemantics P
open Semantics using (Entrypoint; activation; device; grant; depositPublic;
  depositPrivate; submitRecovery; finaliseRecovery)
module Recovery = RecoverySecurity P
module Runs = Generic.Runs lifecycle address

-- These entrypoints cannot submit, cancel or finalise a pending record.
data Ordinary : Entrypoint → Set where
  ordinaryActivation : ∀ c → Ordinary (activation c)
  ordinaryDevice : ∀ c op → op ≢ cancelRecovery → Ordinary (device c op)
  ordinaryGrant : ∀ c op → op ≢ cancelRecovery → Ordinary (grant c op)
  ordinaryUnshieldedDeposit : Ordinary depositPublic
  ordinaryShieldedDeposit : Ordinary depositPrivate

data Retains {s t : State} : Runs.Step s t → Set where
  refused : ∀ {env call error executed} → t ≡ s →
    Retains (Runs.event env call (Account.reverted error) executed)
  ordinary : ∀ {env call answer effects executed} e →
    Semantics.lookupEntrypoint (name (RuntimeCall.request call)) Semantics.entrypoints ≡ just e →
    Ordinary e → Recovery.SamePending s t →
    Retains (Runs.event env call (Account.committed answer effects) executed)

data Retained : ∀ {s t} → Runs.Trace s t → Set where
  done : ∀ {s} → Retained {s} {s} ε
  kept : ∀ {s m t} {x : Runs.Step s m} {rest : Runs.Trace m t} →
    Retains x → Retained rest → Retained (x ◅ rest)

-- The indices name the installed fields once. The event is the actual source
-- transition in this trace; retaining its suffix excludes cancel/resubmit even
-- if a later record would have equal fields.
data Occurrence : ∀ {s t} → Runs.Trace s t → Value → Value → Value → Set where
  submitted : ∀ {s m t entry key deadline} env call answer effects
    (executed : Account.Transition P (executionContext address env) (RuntimeCall.request call) s
      (Account.committed answer effects) m) {rest : Runs.Trace m t} →
    Semantics.lookupEntrypoint (name (RuntimeCall.request call)) Semantics.entrypoints
      ≡ just submitRecovery →
    Recovery.Stores m "pending_recovery" (bool true) →
    Recovery.Stores m "pending_entry" entry →
    Recovery.Stores m "pending_recovery_pk" key →
    Recovery.Stores m "pending_not_before" deadline →
    Retained rest →
    Occurrence (Runs.event env call (Account.committed answer effects) executed ◅ rest) entry key deadline
  later : ∀ {s m t entry key deadline} (x : Runs.Step s m) {rest : Runs.Trace m t} →
    Occurrence rest entry key deadline → Occurrence (x ◅ rest) entry key deadline

PendingOrigin : ∀ {s t} → Runs.Trace s t → Set
PendingOrigin trace = Σ Value λ entry → Σ Value λ key → Σ Value λ deadline →
  Occurrence trace entry key deadline

record EnactsOccurrence (ctx : Context) {s t} (trace : Runs.Trace s t) (after : State) : Set where
  field successor recoveryKey deadline : Value
        origin : Occurrence trace successor recoveryKey deadline
        replacesDevices : Recovery.Stores after "devices" (tuple (successor ∷ []))
        installsRecoveryKey : Recovery.Stores after "recovery_pk" recoveryKey
        windowElapsed : number deadline ≤ blockTime ctx

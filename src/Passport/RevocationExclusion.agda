{-# OPTIONS --safe --without-K #-}

-- Definitions for runtime revocation/recovery exclusion.
-- Advertised claims: RevocationExclusionProperties; proofs: RevocationExclusionProof.
-- Histories are local to one deployment, not ledger adoption.
open import Conformance.FullAccountTypes using (Primitives; Value)

module Passport.RevocationExclusion (P : Primitives) (address : Value) where

open import Conformance.FullAccountTypes
open import Conformance.FullAccountBody P
open import Conformance.FullAccountDeviceSecurity P using (deviceArguments; deviceAuth)
open import Data.Bool.Base using (true)
open import Data.Sum.Base using (_⊎_)
import Conformance.FullAccount as Model
open import Conformance.FullAccountExecution
open import Conformance.FullAccountLayouts
open import Conformance.FullAccountCrypto P using (Auth; counter; entryAt)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; _≤_; _<_)
open import Data.Product.Base using (_×_)
open import Data.String.Base using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (_◅_)
import Midnight.ContractDSL.Lifecycle as Generic
open import Passport.AccountLifecycle P hiding (environment)
import Passport.Account as Account
import Passport.GrantEffects as GrantEffects

module Runs = Generic.Runs lifecycle address
module Runtime = Model.AccountSemantics P
module Effects = GrantEffects P

-- The actual source entrypoint table, without signing or ownership parameters.
resolve : RawCall → Maybe Runtime.Entrypoint
resolve request = Runtime.lookupEntrypoint (name request) Runtime.entrypoints

callArguments : RuntimeCall → List Value
callArguments call = arguments (RuntimeCall.request call)

callAuth : Curve → Operation → RuntimeCall → Auth
callAuth c op call = deviceAuth c op (callArguments call)

nextAuthCounter : Curve → Operation → RuntimeCall → ℕ
nextAuthCounter c op call = Data.Nat.Base.suc (counter (callAuth c op call))

callIdentifier : Operation → RuntimeCall → Value
callIdentifier op call = get 0 (deviceArguments op (callArguments call))


counterValue : String → State → ℕ
counterValue label s = number (cell label s)

record CountersAdvance (s t : State) : Set where
  field nonce : counterValue "auth_nonce" s ≤ counterValue "auth_nonce" t
        epoch : counterValue "device_epoch" s ≤ counterValue "device_epoch" t
        generation : counterValue "grant_generation" s ≤ counterValue "grant_generation" t


-- Occurrences retain an actual committed runtime transition, never just an
-- endpoint record that could have been cleared and subsequently reinstalled.
record CommittedOccurrence (s t : State) : Set where
  constructor occurrence
  field environment : Environment
        call : RuntimeCall
        answer : Value
        effects : List Effect
        executed : Account.Transition P (executionContext address environment)
          (RuntimeCall.request call) s (Account.committed answer effects) t

occurrenceContext : ∀ {s t} → CommittedOccurrence s t → Context
occurrenceContext event = executionContext address (CommittedOccurrence.environment event)

occurrenceArguments : ∀ {s t} → CommittedOccurrence s t → List Value
occurrenceArguments event = callArguments (CommittedOccurrence.call event)

occurrenceAuth : ∀ {s t} → Curve → Operation → CommittedOccurrence s t → Auth
occurrenceAuth c op event = callAuth c op (CommittedOccurrence.call event)

Resolved : ∀ {s t} → CommittedOccurrence s t → Runtime.Entrypoint → Set
Resolved event entrypoint = resolve (RuntimeCall.request (CommittedOccurrence.call event)) ≡ just entrypoint

recoverySuccessor : ∀ {s t} → CommittedOccurrence s t → Value
recoverySuccessor {s} event = cell "pending_entry" s

revocationIdentifier : ∀ {s t} → CommittedOccurrence s t → Value
revocationIdentifier event = callIdentifier revokeGrant (CommittedOccurrence.call event)

issuedIdentifier : ∀ {s t} → CommittedOccurrence s t → Value
issuedIdentifier event = callIdentifier issueGrant (CommittedOccurrence.call event)

-- Observe the installed record; a committed issue proves the lookup succeeds.
observedGrant : Value → State → Value
observedGrant identifier s with lookupMap identifier (fields (cell "grants" s))
... | just g = g
... | nothing = none

issuedIdentity : ∀ {s t} → CommittedOccurrence s t → Effects.Issuance
issuedIdentity {t = t} event = Effects.issuanceOf (issuedIdentifier event)
  (observedGrant (issuedIdentifier event) t)

-- These four boundaries are source operations at a particular invocation, not
-- equality of endpoint sets. In particular addDevice accepts raw digest bytes.
data EntryIntroduction (entry : Value) (s : State) (env : Environment) (call : RuntimeCall) : Set where
  bootstrapped : ∀ c →
    resolve (RuntimeCall.request call) ≡ just (Runtime.activation c) →
    Run (entryAt c address (Runtime.parseActivation c (callArguments call))
      (counterValue "device_epoch" s) 0) s entry s → EntryIntroduction entry s env call
  rolled : ∀ c op →
    resolve (RuntimeCall.request call) ≡ just (Runtime.device c op) →
    Run (entryAt c address (callAuth c op call) (counterValue "device_epoch" s)
      (nextAuthCounter c op call)) s entry s →
    EntryIntroduction entry s env call
  enrolled : ∀ c →
    resolve (RuntimeCall.request call) ≡ just (Runtime.device c addDevice) →
    callIdentifier addDevice call ≡ entry →
    EntryIntroduction entry s env call
  recoveredSuccessor : resolve (RuntimeCall.request call) ≡ just Runtime.finaliseRecovery →
    cell "pending_entry" s ≡ entry → EntryIntroduction entry s env call

data IntroducedIn (entry : Value) : ∀ {s t} → Runs.Trace s t → Set where
  here : ∀ {s t u env call x es} {trace : Runs.Trace t u}
    {executed : Account.Transition P (executionContext address env) (RuntimeCall.request call)
      s (Account.committed x es) t} →
    EntryIntroduction entry s env call →
    IntroducedIn entry (Runs.event env call (Account.committed x es) executed ◅ trace)
  introducedLater : ∀ {s t u} {step : Runs.Step s t} {trace : Runs.Trace t u} →
    IntroducedIn entry trace → IntroducedIn entry (step ◅ trace)

-- A query-scoped separation premise: this one protected opening does not equal
-- the installed successor digest or a digest actually inserted subsequently.
-- Raw addDevice enrolment of the protected opening, successor reuse of the
-- protected key, compromised-device rolling to it, and relevant hash collisions
-- invalidate this premise. No universal digest injectivity is required.
-- entryAt reads no ledger cells and changes no state; arbitrary evaluation
-- states below express separation of this opening, not an authority premise.
record RelevantEntrySeparation (c : Curve) (a : Auth) (epoch : ℕ)
    (successor : Value) {s t : State} (trace : Runs.Trace s t) : Set where
  field successorSeparated : ∀ {state entry} →
          Run (entryAt c address a epoch (counter a)) state entry state → entry ≢ successor
        insertionsSeparated : ∀ {state entry inserted} →
          Run (entryAt c address a epoch (counter a)) state entry state →
          IntroducedIn inserted trace → entry ≢ inserted

-- Disabled means absent or inactive; it does not forbid authorized reissuance.
GrantDisabled : Value → State → Set
GrantDisabled identifier s = ∀ g →
  lookupMap identifier (fields (cell "grants" s)) ≡ just g → grantActive g ≢ bool true

-- A matching issue at an actual committed trace position, never record equality.
data ReissuedIn (identifier : Value) : ∀ {s t} → Runs.Trace s t → Set where
  issuedHere : ∀ {s t u env call x es c} {trace : Runs.Trace t u}
    {executed : Account.Transition P (executionContext address env) (RuntimeCall.request call)
      s (Account.committed x es) t} →
    resolve (RuntimeCall.request call) ≡ just (Runtime.device c issueGrant) →
    callIdentifier issueGrant call ≡ identifier →
    ReissuedIn identifier (Runs.event env call (Account.committed x es) executed ◅ trace)
  issuedLater : ∀ {s t u} {step : Runs.Step s t} {trace : Runs.Trace t u} →
    ReissuedIn identifier trace → ReissuedIn identifier (step ◅ trace)


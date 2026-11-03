{-# OPTIONS --safe --without-K #-}

-- Local full-account histories, not ledger adoption. Counters are observations
-- of the actual ledger cells; no monotonicity or authorization is assumed.
open import Conformance.FullAccountTypes using (Primitives; Value)

module Passport.RevocationExclusion (P : Primitives) (address : Value) where

open import Conformance.FullAccountTypes
open import Conformance.FullAccountBody P
open import Conformance.FullAccountDeviceSecurity P
open import Conformance.FullAccountRecoverySecurity P
open import Data.Bool.Base using (true)
open import Data.Sum.Base using (_⊎_)
open import Midnight.ContractDSL.SymbolicSigning using (attacker)
import Passport.AccountSecurity as Security
open import Conformance.FullAccountExecution
open import Conformance.FullAccountLayouts
open import Conformance.FullAccountCrypto P using (Auth; counter; entryAt)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (just)
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
-- Only source-guard extraction is used. Its symbolic ownership parameter is
-- irrelevant here; no token availability or authorization law is a premise.
module Source = Security P address (λ _ → attacker)

-- These four boundaries are source operations at a particular invocation, not
-- equality of endpoint sets. In particular addDevice accepts raw digest bytes.
data EntryIntroduction (entry : Value) (s : State) (env : Environment) (call : RuntimeCall) : Set where
  bootstrapped : ∀ c →
    Source.resolve (RuntimeCall.request call) ≡ just (Source.Semantics.activation c) →
    Run (entryAt c address (Source.Semantics.parseActivation c (arguments (RuntimeCall.request call)))
      (counterValue "device_epoch" s) 0) s entry s → EntryIntroduction entry s env call
  rolled : ∀ c op →
    Source.resolve (RuntimeCall.request call) ≡ just (Source.Semantics.device c op) →
    Run (entryAt c address (deviceAuth c op (arguments (RuntimeCall.request call)))
      (counterValue "device_epoch" s)
      (Data.Nat.Base.suc (counter (deviceAuth c op (arguments (RuntimeCall.request call)))))) s entry s →
    EntryIntroduction entry s env call
  enrolled : ∀ c →
    Source.resolve (RuntimeCall.request call) ≡ just (Source.Semantics.device c addDevice) →
    get 0 (deviceArguments addDevice (arguments (RuntimeCall.request call))) ≡ entry →
    EntryIntroduction entry s env call
  recoveredSuccessor : Source.resolve (RuntimeCall.request call) ≡ just Source.Semantics.finaliseRecovery →
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
record RelevantEntrySeparation (c : Curve) (a : Auth) (epoch : ℕ)
    (successor : Value) {s t : State} (trace : Runs.Trace s t) : Set where
  field successorSeparated : ∀ {state entry} →
          Run (entryAt c address a epoch (counter a)) state entry state → entry ≢ successor
        insertionsSeparated : ∀ {state entry inserted} →
          Run (entryAt c address a epoch (counter a)) state entry state →
          IntroducedIn inserted trace → entry ≢ inserted

-- The boundary includes the deployment-rooted history and the committed
-- dispatcher occurrence. Guard evidence is extracted from this source path.
record RecoveryBoundary (s recovered : State) : Set where
  field history : Runs.History s
        event : CommittedOccurrence s recovered
        finaliseResolved : Source.resolve (RuntimeCall.request (CommittedOccurrence.call event)) ≡
          just Source.Semantics.finaliseRecovery
        evidence : Finalisation.Evidence
          (executionContext address (CommittedOccurrence.environment event)) s recovered

record DeviceBoundary (c : Curve) (op : Operation) (s after : State) : Set where
  field history : Runs.History s
        event : CommittedOccurrence s after
        deviceResolved : Source.resolve (RuntimeCall.request (CommittedOccurrence.call event)) ≡
          just (Source.Semantics.device c op)
        evidence : DeviceCall c op
          (executionContext address (CommittedOccurrence.environment event))
          (arguments (RuntimeCall.request (CommittedOccurrence.call event))) s
          (CommittedOccurrence.answer event) after

GrantDisabled : Value → State → Set
GrantDisabled identifier s = ∀ g →
  lookupMap identifier (fields (cell "grants" s)) ≡ just g → grantActive g ≢ bool true

data ReissuedIn (identifier : Value) : ∀ {s t} → Runs.Trace s t → Set where
  issuedHere : ∀ {s t u env call x es c} {trace : Runs.Trace t u}
    {executed : Account.Transition P (executionContext address env) (RuntimeCall.request call)
      s (Account.committed x es) t} →
    Source.Dispatched (Source.Semantics.device c issueGrant) env call s x t es →
    IssueArguments.id (deviceArguments issueGrant (arguments (RuntimeCall.request call))) ≡ identifier →
    ReissuedIn identifier (Runs.event env call (Account.committed x es) executed ◅ trace)
  issuedLater : ∀ {s t u} {step : Runs.Step s t} {trace : Runs.Trace t u} →
    ReissuedIn identifier trace → ReissuedIn identifier (step ◅ trace)

revokedIdentifier : ∀ {c s t} → DeviceBoundary c revokeGrant s t → Value
revokedIdentifier boundary = get 0 (deviceArguments revokeGrant
  (arguments (RuntimeCall.request (CommittedOccurrence.call (DeviceBoundary.event boundary)))))

module Effects = GrantEffects P

record IssueBoundary (c : Curve) (s t : State) : Set where
  field device : DeviceBoundary c issueGrant s t
        issued : Effects.IssueResult
          (deviceArguments issueGrant
            (arguments (RuntimeCall.request (CommittedOccurrence.call (DeviceBoundary.event device)))))
          (DeviceCall.authorisedState (DeviceBoundary.evidence device)) t

issueIdentity : ∀ {c s t} → IssueBoundary c s t → Effects.Issuance
issueIdentity issued = Effects.issuanceOf
  (IssueArguments.id (deviceArguments issueGrant
    (arguments (RuntimeCall.request (CommittedOccurrence.call (DeviceBoundary.event (IssueBoundary.device issued)))))))
  (Effects.issuedRecord (IssueBoundary.issued issued))

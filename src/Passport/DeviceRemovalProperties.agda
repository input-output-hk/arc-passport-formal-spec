{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes using (Primitives; Value)

-- Source-history exclusion for ordinary remove_device, at the literal-entry
-- boundary. Start with DeviceRemoval.Removal (guards and effect), then
-- RevocationExclusion.CommittedOccurrence / Resolved / IntroducedIn (history).
-- Proofs: DeviceRemovalProof; source: FullAccountBody.body removeDevice and
-- FullAccount.AccountSemantics.callerEntryAfter / deviceCall.
-- No digest injectivity, signature security, or absence conclusion is assumed.
-- Later rolling, activation, raw add_device enrolment, or recovery installation
-- of this entry invalidate noIntroduction. Other openings of the same key may
-- remain live; the caller's current opening is consumed by authorisation first.
-- This is neither a permanent-key ban nor ledger adoption.
module Passport.DeviceRemovalProperties (P : Primitives) (address : Value) where

open import Conformance.FullAccountTypes
open import Conformance.FullAccountBody P using (removeDevice)
open import Conformance.FullAccountCrypto P using (entryAt; counter)
open import Conformance.FullAccountExecution using (Run)
open import Data.Bool.Base using (true; false)
open import Data.Empty using (⊥)
open import Passport.DeviceRemoval P address
import Passport.DeviceRemovalProof as Implementation
open import Passport.RevocationExclusion P address
open import Relation.Binary.PropositionalEquality using (_≡_)

module Proof = Implementation P address

-- Successful execution supplies target membership, inequality from the rolled
-- caller, count > 1, exact removal and decrement, and strict count decrease.
removal-evidence : ∀ {c s t} → Runs.History s →
  (event : CommittedOccurrence s t) → Resolved event (Runtime.device c removeDevice) → Removal c event
removal-evidence = Proof.removal-evidence

-- Even if the final entry is byte-for-byte equal to the removed one, membership
-- requires an actual introducing occurrence, not just endpoint equality.
removed-device-origin : ∀ {c s removed later} → Runs.History s →
  (event : CommittedOccurrence s removed) → Resolved event (Runtime.device c removeDevice) →
  (trace : Runs.Trace removed later) → member (removedEntry event) (fields (cell "devices" later)) ≡ true →
  IntroducedIn (removedEntry event) trace
removed-device-origin = Proof.removed-device-origin

-- The trace may contain accepted calls and reverted attempts. NoIntroduction
-- is entry-specific: key reuse and collisions count if they recreate its value.
removed-device-absent : ∀ {c s removed later} → Runs.History s →
  (event : CommittedOccurrence s removed) → Resolved event (Runtime.device c removeDevice) →
  (trace : Runs.Trace removed later) → (IntroducedIn (removedEntry event) trace → ⊥) →
  member (removedEntry event) (fields (cell "devices" later)) ≡ false
removed-device-absent = Proof.removed-device-absent

-- Only this opening is excluded: the proposed caller's source entryAt at the
-- later epoch/presented counter must compute the removed entry. No assumption
-- forbids another pre-enrolled counter or a different opening of the same key.
removed-device-call-excluded : ∀ {ownerCurve s removed later c op after} → Runs.History s →
  (removal : CommittedOccurrence s removed) → Resolved removal (Runtime.device ownerCurve removeDevice) →
  (trace : Runs.Trace removed later) → (IntroducedIn (removedEntry removal) trace → ⊥) →
  (device : CommittedOccurrence later after) → Resolved device (Runtime.device c op) →
  Run (entryAt c address (occurrenceAuth c op device) (counterValue "device_epoch" later)
    (counter (occurrenceAuth c op device))) later (removedEntry removal) later → ⊥
removed-device-call-excluded = Proof.removed-device-call-excluded

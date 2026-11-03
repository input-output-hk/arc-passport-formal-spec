{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes using (Primitives; Value)

-- History-level local exclusion for the actual full-account dispatcher.
-- Revoked identifiers may be issued again and old keys may be enrolled again:
-- these are actual authorization boundaries, not counterexamples hidden by
-- endpoint equality. Device exclusion needs separation for the relevant opening
-- against the installed successor and actual subsequent insertion occurrences.
-- No fairness, consent, cryptographic security or ledger adoption is proved.
module Passport.RevocationExclusionProperties (P : Primitives) (address : Value) where

open import Conformance.FullAccountTypes
open import Conformance.FullAccountBody P
open import Conformance.FullAccountDeviceSecurity P
open import Conformance.FullAccountGrantSecurity P
open import Conformance.FullAccountLayouts
open import Conformance.FullAccountExecution
open import Conformance.FullAccountGrant P
open import Data.Maybe.Base using (just)
open import Data.Bool.Base using (true)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_<_; _≤_)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Conformance.FullAccountRecoverySecurity as Recovery
open import Passport.AccountLifecycle P
open import Passport.RevocationExclusion P address
import Passport.RevocationExclusionProof as Implementation

module R = Recovery P
module Proof = Implementation P address

-- Derived from source increments/frames; neither monotone time nor a counter
-- invariant is an input. Every reverted runtime attempt is retained.
history-counters : ∀ {s t} → Runs.History s → Runs.Trace s t → CountersAdvance s t
history-counters = Proof.rooted-counters

stale-epoch-excluded : ∀ {s t c ctx ga g} → Runs.History s → Runs.Trace s t →
  number (grantEpoch g) < counterValue "device_epoch" s → LiveGrant c ctx ga t g → ⊥
stale-epoch-excluded = Proof.rooted-stale-epoch-excluded

stale-generation-excluded : ∀ {s t c ctx ga g} → Runs.History s → Runs.Trace s t →
  number (grantGeneration g) < counterValue "grant_generation" s → LiveGrant c ctx ga t g → ⊥
stale-generation-excluded = Proof.rooted-stale-generation-excluded

post-recovery-epoch : ∀ {s recovered later} → RecoveryBoundary s recovered →
  Runs.Trace recovered later → counterValue "device_epoch" s < counterValue "device_epoch" later
post-recovery-epoch = Proof.runtime-post-recovery-epoch

post-device-nonce : ∀ {c op s t later} → DeviceBoundary c op s t →
  Runs.Trace t later → counterValue "auth_nonce" s < counterValue "auth_nonce" later
post-device-nonce = Proof.runtime-post-device-nonce

-- In particular a pre-recovery key has no retained membership merely because
-- it was previously enrolled. Any later membership is the installed successor
-- or has an actual later source insertion (activation, rolling, or addDevice).
post-recovery-device-origin : ∀ {s recovered later entry} →
  (boundary : RecoveryBoundary s recovered) → (trace : Runs.Trace recovered later) →
  member entry (fields (cell "devices" later)) ≡ true →
  (entry ≡ R.Finalisation.Evidence.successor (RecoveryBoundary.evidence boundary)) ⊎ IntroducedIn entry trace
post-recovery-device-origin = Proof.runtime-post-recovery-device-origin

-- This premise excludes only the protected opening's matches to those real
-- insertion events. Re-enrolling it, making it the recovery successor, or
-- compromising a rolling authority so that its successor matches, invalidates
-- the premise. It is not an assumption that accepted calls are authorized.
protected-device-excluded : ∀ {s recovered later c op after} →
  (recovery : RecoveryBoundary s recovered) → (trace : Runs.Trace recovered later) →
  (device : DeviceBoundary c op later after) →
  RelevantEntrySeparation c
    (deviceAuth c op (arguments (RuntimeCall.request (CommittedOccurrence.call (DeviceBoundary.event device)))))
    (counterValue "device_epoch" later)
    (R.Finalisation.Evidence.successor (RecoveryBoundary.evidence recovery)) trace → ⊥
protected-device-excluded = Proof.runtime-protected-device-excluded

post-revoke-all-generation : ∀ {c s t later} → DeviceBoundary c revokeAllGrants s t →
  Runs.Trace t later → counterValue "grant_generation" s < counterValue "grant_generation" later
post-revoke-all-generation = Proof.post-revoke-all-generation

-- Inactivity/absence is invariant until an actual device-authenticated issue
-- of this identifier. Equality of a later record with an earlier record is
-- never used as evidence that an issuance occurrence happened.
revoked-grant-excluded : ∀ {c s revoked later}
  (boundary : DeviceBoundary c revokeGrant s revoked) (trace : Runs.Trace revoked later) →
  (ReissuedIn (revokedIdentifier boundary) trace → ⊥) → GrantDisabled (revokedIdentifier boundary) later
revoked-grant-excluded = Proof.revoked-grant-excluded

-- This denies the source grantCall itself, so also any validated runtime
-- dispatcher call reaching that evaluator. grantId is the real computed id.
revoked-grant-call-excluded : ∀ {ownerCurve s revoked later c op ctx ga xs x after}
  (boundary : DeviceBoundary ownerCurve revokeGrant s revoked) (trace : Runs.Trace revoked later) →
  (ReissuedIn (revokedIdentifier boundary) trace → ⊥) →
  Run (grantId c ctx ga) later (revokedIdentifier boundary) later →
  Run (grantCall c op ctx ga xs) later x after → ⊥
revoked-grant-call-excluded {c = c} {op} {ctx} {ga} {xs} =
  Proof.revoked-grant-call-excluded {c = c} {op = op} {ctx = ctx} {ga = ga} {xs = xs}

-- Every later issuance has a strictly later source auth_nonce, even across
-- revocations, generation resets and recoveries. The full per-issuance identity
-- is GrantEffects.Issuance: identifier, epoch, generation and issuedAt.
issue-nonces-strict : ∀ {c₁ c₂ s first later final} →
  (issued₁ : IssueBoundary c₁ s first) → Runs.Trace first later →
  (issued₂ : IssueBoundary c₂ later final) →
  number (Effects.Issuance.issuedAt (issueIdentity issued₁)) <
    number (Effects.Issuance.issuedAt (issueIdentity issued₂))
issue-nonces-strict = Proof.issue-nonces-strict

-- Constructors for the occurrence boundaries derive the guard evidence from
-- the committed actual dispatcher path, not an accepted-call authorization law.
recovery-boundary : ∀ {s recovered} → (history : Runs.History s) →
  (event : CommittedOccurrence s recovered) →
  Source.resolve (RuntimeCall.request (CommittedOccurrence.call event)) ≡ just Source.Semantics.finaliseRecovery →
  RecoveryBoundary s recovered
recovery-boundary = Proof.recovery-boundary

device-boundary : ∀ {c op s t} → Runs.History s →
  (event : CommittedOccurrence s t) →
  Source.resolve (RuntimeCall.request (CommittedOccurrence.call event)) ≡ just (Source.Semantics.device c op) →
  DeviceBoundary c op s t
device-boundary = Proof.device-boundary

issue-boundary : ∀ {c s t} → DeviceBoundary c issueGrant s t → IssueBoundary c s t
issue-boundary = Proof.issue-boundary

post-recovery-old-grant-excluded : ∀ {s recovered later c ctx ga g} →
  (boundary : RecoveryBoundary s recovered) → Runs.Trace recovered later →
  number (grantEpoch g) ≤ counterValue "device_epoch" s → LiveGrant c ctx ga later g → ⊥
post-recovery-old-grant-excluded = Proof.post-recovery-old-grant-excluded

post-revoke-all-old-grant-excluded : ∀ {ownerCurve s revoked later c ctx ga g} →
  (boundary : DeviceBoundary ownerCurve revokeAllGrants s revoked) → Runs.Trace revoked later →
  number (grantGeneration g) ≤ counterValue "grant_generation" s → LiveGrant c ctx ga later g → ⊥
post-revoke-all-old-grant-excluded = Proof.post-revoke-all-old-grant-excluded

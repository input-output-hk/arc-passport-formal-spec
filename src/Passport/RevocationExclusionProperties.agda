{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes using (Primitives; Value)

-- Runtime-history revocation/recovery exclusion for one deployed account.
-- Definitions: RevocationExclusion. Proofs and source-guard extraction:
-- RevocationExclusionProof. Every occurrence below is an actual committed
-- dispatcher transition; Resolved uses the source entrypoint table.
-- Reissuance and re-enrolment are legitimate, explicitly tracked boundaries.
-- No fairness, consent, cryptographic security or ledger adoption is proved.
module Passport.RevocationExclusionProperties (P : Primitives) (address : Value) where

open import Conformance.FullAccountTypes
open import Conformance.FullAccountBody P using (issueGrant; revokeGrant; revokeAllGrants)
open import Conformance.FullAccountGrantSecurity P using (LiveGrant)
open import Conformance.FullAccountLayouts using (grantEpoch; grantGeneration)
open import Conformance.FullAccountExecution using (Run)
open import Conformance.FullAccountGrant P using (grantId; grantCall)
open import Data.Bool.Base using (true)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_<_; _≤_)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Passport.RevocationExclusion P address
import Passport.RevocationExclusionProof as Implementation

module Proof = Implementation P address

-- Grant exclusion -----------------------------------------------------------

-- No source-live grant whose epoch was already stale at the earlier state.
stale-epoch-excluded : ∀ {s t c ctx ga g} → Runs.History s → Runs.Trace s t →
  number (grantEpoch g) < counterValue "device_epoch" s → LiveGrant c ctx ga t g → ⊥
stale-epoch-excluded = Proof.rooted-stale-epoch-excluded

-- No source-live grant whose generation was already stale at the earlier state.
stale-generation-excluded : ∀ {s t c ctx ga g} → Runs.History s → Runs.Trace s t →
  number (grantGeneration g) < counterValue "grant_generation" s → LiveGrant c ctx ga t g → ⊥
stale-generation-excluded = Proof.rooted-stale-generation-excluded

-- Recovery excludes all grants from its old epoch, throughout the later trace.
post-recovery-old-grant-excluded : ∀ {s recovered later c ctx ga g} →
  Runs.History s → (event : CommittedOccurrence s recovered) → Resolved event Runtime.finaliseRecovery →
  Runs.Trace recovered later → number (grantEpoch g) ≤ counterValue "device_epoch" s →
  LiveGrant c ctx ga later g → ⊥
post-recovery-old-grant-excluded = Proof.occurrence-post-recovery-old-grant-excluded

-- Revoking all grants excludes their old generation throughout the later trace.
post-revoke-all-old-grant-excluded : ∀ {ownerCurve s revoked later c ctx ga g} →
  Runs.History s → (event : CommittedOccurrence s revoked) →
  Resolved event (Runtime.device ownerCurve revokeAllGrants) → Runs.Trace revoked later →
  number (grantGeneration g) ≤ counterValue "grant_generation" s → LiveGrant c ctx ga later g → ⊥
post-revoke-all-old-grant-excluded = Proof.occurrence-post-revoke-all-old-grant-excluded

-- The revoked identifier stays absent/inactive unless the trace actually
-- contains a new authorized issue for it; endpoint record equality is not used.
revoked-grant-excluded : ∀ {c s revoked later} → Runs.History s →
  (event : CommittedOccurrence s revoked) → Resolved event (Runtime.device c revokeGrant) →
  (trace : Runs.Trace revoked later) → (ReissuedIn (revocationIdentifier event) trace → ⊥) →
  GrantDisabled (revocationIdentifier event) later
revoked-grant-excluded = Proof.occurrence-revoked-grant-excluded

-- The real source grantCall cannot succeed for that computed identifier before
-- reissuance, so neither can a validated runtime call reaching that evaluator.
revoked-grant-call-excluded : ∀ {ownerCurve s revoked later c op ctx ga xs x after} →
  Runs.History s → (event : CommittedOccurrence s revoked) →
  Resolved event (Runtime.device ownerCurve revokeGrant) → (trace : Runs.Trace revoked later) →
  (ReissuedIn (revocationIdentifier event) trace → ⊥) →
  Run (grantId c ctx ga) later (revocationIdentifier event) later →
  Run (grantCall c op ctx ga xs) later x after → ⊥
revoked-grant-call-excluded {c = c} {op} {ctx} {ga} {xs} =
  Proof.occurrence-revoked-grant-call-excluded {c = c} {op = op} {ctx = ctx} {ga = ga} {xs = xs}

-- Device exclusion and actual introduction provenance ----------------------

-- A later member is the installed recovery successor or has an actual later
-- introduction: activation, authority rolling, explicit enrolment, or recovery.
post-recovery-device-origin : ∀ {s recovered later entry} → Runs.History s →
  (event : CommittedOccurrence s recovered) → Resolved event Runtime.finaliseRecovery →
  (trace : Runs.Trace recovered later) → member entry (fields (cell "devices" later)) ≡ true →
  (entry ≡ recoverySuccessor event) ⊎ IntroducedIn entry trace
post-recovery-device-origin = Proof.occurrence-post-recovery-device-origin

-- This one opening must differ from the successor and actual later inserted
-- entries. Re-enrolling it, successor reuse, compromised rolling to it, or a
-- relevant collision invalidates separation; accepted-call authorization is
-- not an assumption. In particular no unconditional old-key exclusion is made.
protected-device-excluded : ∀ {s recovered later c op after} → Runs.History s →
  (recovery : CommittedOccurrence s recovered) → Resolved recovery Runtime.finaliseRecovery →
  (trace : Runs.Trace recovered later) →
  (device : CommittedOccurrence later after) → Resolved device (Runtime.device c op) →
  RelevantEntrySeparation c (occurrenceAuth c op device) (counterValue "device_epoch" later)
    (recoverySuccessor recovery) trace → ⊥
protected-device-excluded = Proof.occurrence-protected-device-excluded

-- Source-derived counter and issuance facts ---------------------------------

-- Every reverted attempt is retained; monotone time/counters are not premises.
history-counters : ∀ {s t} → Runs.History s → Runs.Trace s t → CountersAdvance s t
history-counters = Proof.rooted-counters

-- Finalising recovery strictly advances the epoch, which never decreases later.
post-recovery-epoch : ∀ {s recovered later} → Runs.History s →
  (event : CommittedOccurrence s recovered) → Resolved event Runtime.finaliseRecovery →
  Runs.Trace recovered later → counterValue "device_epoch" s < counterValue "device_epoch" later
post-recovery-epoch = Proof.occurrence-post-recovery-epoch

-- Every committed device call strictly advances the nonce, including at bounds.
post-device-nonce : ∀ {c op s t later} → Runs.History s →
  (event : CommittedOccurrence s t) → Resolved event (Runtime.device c op) →
  Runs.Trace t later → counterValue "auth_nonce" s < counterValue "auth_nonce" later
post-device-nonce = Proof.occurrence-post-device-nonce

-- Revoking all grants strictly advances generation, which never decreases later.
post-revoke-all-generation : ∀ {c s t later} → Runs.History s →
  (event : CommittedOccurrence s t) → Resolved event (Runtime.device c revokeAllGrants) →
  Runs.Trace t later → counterValue "grant_generation" s < counterValue "grant_generation" later
post-revoke-all-generation = Proof.occurrence-post-revoke-all-generation

-- Actual installed issuance records have strictly ordered issuedAt nonces,
-- even across revocations/recoveries. Their shared GrantEffects.Issuance identity
-- includes identifier, epoch, generation, and issuedAt, not only the grant id.
issue-nonces-strict : ∀ {c₁ c₂ s first later final} → Runs.History s →
  (issued₁ : CommittedOccurrence s first) → Resolved issued₁ (Runtime.device c₁ issueGrant) →
  Runs.Trace first later →
  (issued₂ : CommittedOccurrence later final) → Resolved issued₂ (Runtime.device c₂ issueGrant) →
  number (Effects.Issuance.issuedAt (issuedIdentity issued₁)) <
    number (Effects.Issuance.issuedAt (issuedIdentity issued₂))
issue-nonces-strict = Proof.occurrence-issue-nonces-strict

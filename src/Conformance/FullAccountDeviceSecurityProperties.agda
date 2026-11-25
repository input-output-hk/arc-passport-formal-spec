{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

-- Device-authorisation security of the actual full-account evaluator: what a
-- successful authorise, deviceCall or activate run establishes, which cells the
-- device-operation bodies may write, and the replay boundary. These are local
-- contract-execution facts, not ledger admission or adoption. Signature meaning
-- and symbolic provenance: Conformance.FullAccountSignatureBindingProperties.
-- Definitions: Conformance.FullAccountDeviceSecurity;
-- proofs: Conformance.FullAccountDeviceSecurityProof.
module Conformance.FullAccountDeviceSecurityProperties (P : Primitives) where

open import Conformance.FullAccount using (module AccountSemantics)
open import Conformance.FullAccountBody P using (body; activate)
open import Conformance.FullAccountCrypto P using (authorise)
open import Conformance.FullAccountDeviceSecurity P
import Conformance.FullAccountDeviceSecurityProof as DeviceSecurityProof
open import Conformance.FullAccountExecution using (Run)
open import Data.Bool.Base using (true; false)
open import Data.List.Base using ([])
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe.Base using (just)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)

private
  module Proof = DeviceSecurityProof P

open AccountSemantics P using (deviceCall)

------------------------------------------------------------------------
-- Successful device authorisation

-- Every curve: the presented key passed its key guard; the entry entryAt derives
-- for this account, the stored epoch and the presented counter was live; the
-- actual verify accepted h; that entry was replaced by the next counter's entry;
-- auth_nonce and round were bumped; no other cell changed.
authorise-evidence : ∀ c ctx a h {before next after} → Run (authorise c ctx a h) before next after →
  Authorisation c ctx a h before next after
authorise-evidence = Proof.authorise-evidence

-- Every curve and operation: the verified challenge is challengeAt over the
-- operation atoms of the decoded arguments, this account's address and the
-- stored auth_nonce; authorise ran from the before state and the body from its
-- result; the committed state carries the advanced auth_nonce and round.
device-call-evidence : ∀ c op ctx xs {before result after} →
  Run (deviceCall c op ctx xs) before result after → DeviceCall c op ctx xs before result after
device-call-evidence = Proof.device-call-evidence

-- Device bodies write only the cells bodyWrites lists for their operation.
body-frame : ∀ k op ctx args coin callerEntry →
  All (λ label → stringEqual k label ≡ false) (bodyWrites op) →
  Preserves k (body op ctx args coin callerEntry)
body-frame = Proof.body-frame

-- The used entry leaves the device set unless the next counter's entry is the
-- same value (which would need entryAt to hash two distinct preimages alike).
-- Bodies such as add_device may later insert any entry their arguments name.
entry-consumed : ∀ {c ctx a h before next after} (authorised : Authorisation c ctx a h before next after) →
  equal (Authorisation.current authorised) next ≡ false →
  member (Authorisation.current authorised) (fields (cell "devices" after)) ≡ false
entry-consumed = Proof.entry-consumed

------------------------------------------------------------------------
-- Activation: the bootstrap boundary

-- Activation opens the boot commitment with the presented key and salt (no
-- signature), installs the epoch's counter-0 entry, sets booted and clears boot.
activation-evidence : ∀ c ctx a salt {before result after} →
  Run (activate c ctx a salt) before result after → Activation c ctx a salt before after
activation-evidence = Proof.activation-evidence

-- Once booted is set, activation is refused.
activation-once : ∀ c ctx a salt {before result after} →
  lookupCell "booted" (ledger before) ≡ just (bool true) → ¬ Run (activate c ctx a salt) before result after
activation-once = Proof.activation-once

-- Without a stored device entry no device-authorised call succeeds; in
-- particular none succeeds in the constructor's state.
device-call-needs-device : ∀ c op ctx xs {before result after} → cell "devices" before ≡ tuple [] →
  ¬ Run (deviceCall c op ctx xs) before result after
device-call-needs-device = Proof.device-call-needs-device

no-device-call-at-deployment : ∀ c op ctx xs boot encryption recovery wrap window {result after} →
  ¬ Run (deviceCall c op ctx xs) (initialState boot encryption recovery wrap window) result after
no-device-call-at-deployment = Proof.no-device-call-at-deployment

------------------------------------------------------------------------
-- Replay boundary

-- All device operations except addDevice/removeDevice have this body frame:
-- withdrawals (all three forms), appendInbox, rotateEncKey, issueGrant,
-- revokeGrant, revokeAllGrants, publishRecovery and cancelRecovery.
-- The separation premise concerns the actual hashed entries, not just counters.
-- No hash injectivity or signature-security assumption discharges it here.
-- From the first successful source run, its old entry remains absent in the
-- final state, so a verbatim repeat cannot pass live-membership authorisation.
exact-device-replay-refused : ∀ c op ctx xs {s y t}
  (first : Run (deviceCall c op ctx xs) s y t) →
  All (λ label → stringEqual "devices" label ≡ false) (bodyWrites op) →
  equal (Authorisation.current (DeviceCall.authorised (device-call-evidence c op ctx xs first)))
    (DeviceCall.rolledEntry (device-call-evidence c op ctx xs first)) ≡ false →
  ∀ {result after} → ¬ Run (deviceCall c op ctx xs) t result after
exact-device-replay-refused = Proof.exact-device-replay-refused

-- Stronger boundary: at that final state no authorisation with the same
-- account address and decoded authentication arguments succeeds, even for a
-- different challenge or context's other fields. No intervening call is covered.
consumed-credentials-refused : ∀ c op {ctx xs s y t}
  (first : DeviceCall c op ctx xs s y t) →
  All (λ label → stringEqual "devices" label ≡ false) (bodyWrites op) →
  equal (Authorisation.current (DeviceCall.authorised first)) (DeviceCall.rolledEntry first) ≡ false →
  ∀ {ctx′ a h next u} → self ctx′ ≡ self ctx → a ≡ deviceAuth c op xs →
  ¬ Authorisation c ctx′ a h t next u
consumed-credentials-refused = Proof.consumed-credentials-refused

-- Same curve and operation, different account or stored nonce: the two
-- challenges hash distinct typed preimages, so equal challenge values exhibit a
-- persistentHash collision. This does not say a signature cannot be presented
-- again; whether it verifies a different challenge is the signature scheme's
-- (and digest construction's) concern, see FullAccountSignatureBinding.
challenge-collision : ∀ c op {ctx₁ ctx₂ xs₁ xs₂ s₁ s₂ y₁ y₂ u₁ u₂}
  (first : DeviceCall c op ctx₁ xs₁ s₁ y₁ u₁) (second : DeviceCall c op ctx₂ xs₂ s₂ y₂ u₂) →
  self ctx₁ ≢ self ctx₂ ⊎ number (DeviceCall.nonce first) ≢ number (DeviceCall.nonce second) →
  DeviceCall.challengeValue first ≡ DeviceCall.challengeValue second → Collision
challenge-collision = Proof.challenge-collision

-- A device call made from the state another committed reads the advanced nonce,
-- so equal challenges again exhibit a collision.
immediate-replay-collision : ∀ c op {ctx₁ ctx₂ xs₁ xs₂ s y₁ t y₂ u}
  (first : DeviceCall c op ctx₁ xs₁ s y₁ t) (second : DeviceCall c op ctx₂ xs₂ t y₂ u) →
  DeviceCall.challengeValue first ≡ DeviceCall.challengeValue second → Collision
immediate-replay-collision = Proof.immediate-replay-collision

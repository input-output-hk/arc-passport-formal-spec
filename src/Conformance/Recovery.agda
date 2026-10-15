{-# OPTIONS --safe --without-K #-}

open import Conformance.Primitives

-- Device lifecycle, encryption-key rotation and recovery circuits of `account.compact`,
-- source-reviewed at Passport `d315208` (:1004-1039, :2559-2920), unchanged from
-- the executed `5d12798` reference; see docs/recovery-specification.md#reference-versions-and-evidence.
-- Guards follow the implementation's assert order. The seam-gated circuits appear as
-- their `do_*` chips; Passport.AccountRecovery puts the seam in
-- front. Chain-time asserts are `atChain` requirements, so a time-guard failure is a
-- refusal at admission rather than a build failure. The recovery-session payload
-- (phi, wrap) is carried opaquely, with every guard on it kept.
-- `disclose` is Program's no-op source marker, not information-flow enforcement.
module Conformance.Recovery (P : Primitives) (self : Primitives.Bytes32 P) where

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Unit.Base
open import Relation.Nullary

open import Conformance.AccountLedger P
open import Conformance.Custody P self

open Primitives P

open import Midnight.ContractDSL.Program accountLedger Assertion

doAddDevice : Bytes32 → Program ⊤
doAddDevice newEntry = do
  e ← disclose newEntry
  present ← perform (ledger (deviceMember e))
  assert (not present) entryPresent
  perform (ledger (insertDevice e))
  n ← perform (ledger readDeviceCount)
  perform (ledger (writeDeviceCount (suc n)))

-- `pk`/`uc` are the authorising device's; its post-roll entry may not be removed.
doRemoveDevice : Bytes32 → Point → ℕ → Program ⊤
doRemoveDevice entry pk uc = do
  e ← disclose entry
  epoch ← perform (ledger readEpoch)
  n ← perform (ledger readDeviceCount)
  assert (1 <ᵇ n) lastDevice
  callerEntry ← disclose (deviceEntry self pk epoch (suc uc))
  assert (not (does (e ≟ᴮ callerEntry))) authorisingDevice
  present ← perform (ledger (deviceMember e))
  assert present unknownDevice
  perform (ledger (removeDevice e))
  perform (ledger (writeDeviceCount (pred n)))

doRotateEncKey : Bytes32 → Program ⊤
doRotateEncKey newKey = do
  k ← disclose newKey
  perform (ledger (setEncKey k))

record PublishArgs : Set where
  constructor publishArgs
  field newRecoveryPk : Point
        sessionNonce : Bytes32
        phi : Phi
        phiLen : ℕ
        wrap : Bytes64

doPublish : PublishArgs → Program ⊤
doPublish (publishArgs pk′ n (φ₁ , φ₂ , φ₃ , φ₄) len w) = do
  pend ← perform (ledger readPending)
  assert (not pend) recoveryPending
  assert (1 ≤ᵇ len) phiEmpty
  assert (len ≤ᵇ 4) phiLength
  assert ((2 ≤ᵇ len) ∨ (φ₂ ≡ᵇ 0)) phiSlot2
  assert ((3 ≤ᵇ len) ∨ (φ₃ ≡ᵇ 0)) phiSlot3
  assert ((4 ≤ᵇ len) ∨ (φ₄ ≡ᵇ 0)) phiSlot4
  assert (not (does (n ≟ᴮ zero32))) sessionZero
  stored ← perform (ledger readSession)
  assert (not (does (n ≟ᴮ stored))) sessionReused
  current ← perform (ledger readRecoveryPk)
  assert (not (does (pk′ ≟ᴾ current))) commitmentReused
  requireLive pk′
  pk″ ← disclose pk′
  n′ ← disclose n
  φ₁′ ← disclose φ₁
  φ₂′ ← disclose φ₂
  φ₃′ ← disclose φ₃
  φ₄′ ← disclose φ₄
  len′ ← disclose len
  w′ ← disclose w
  perform (ledger (writeRecoveryPk pk″))
  perform (ledger (writeSession n′))
  perform (ledger (insertPhi1 φ₁′))
  perform (ledger (insertPhi2 φ₂′))
  perform (ledger (insertPhi3 φ₃′))
  perform (ledger (insertPhi4 φ₄′))
  perform (ledger (writePhiLen len′))
  perform (ledger (writeWrap w′))

-- The source's ecMul(pending_recovery_pk, 0) reads the key even though its
-- group-theoretic result is the canonical identity. That equality belongs to
-- concrete curve correspondence, not the abstract Primitives record.
clearPending : Program ⊤
clearPending = do
  perform (ledger (writePending false))
  perform (ledger (writePendingEntry zero32))
  _ ← perform (ledger readPendingRecoveryPk)
  perform (ledger (writePendingRecoveryPk (ecMulG 0)))
  perform (ledger (writeNotBefore 0))

-- No deadline check: cancellation stays possible until finalisation wins.
doCancel : Program ⊤
doCancel = do
  pend ← perform (ledger readPending)
  assert pend noPending
  clearPending

record SubmitArgs : Set where
  constructor submitArgs
  field successorPk successorRecoveryPk : Point
        expectedEpoch expectedNonce nowUpper : ℕ
        sigRRecovery : Point
        sigSRecovery : ℕ
        sigRSuccessor : Point
        sigSSuccessor grindNonce : ℕ

-- The natural-number model does not enforce the source's post_epoch Uint<32>
-- cast. At epoch uint32 - 1 submission can overflow before finalisation ever
-- runs; see docs/conformance-recovery.md#ledger-primitive-boundary.
submitRecovery : SubmitArgs → Program ⊤
submitRecovery (submitArgs q q′ e₀ n₀ u Rr sr Rs ss g) = do
  pend ← perform (ledger readPending)
  assert (not pend) alreadyPending
  epoch ← perform (ledger readEpoch)
  assert (e₀ ≡ᵇ epoch) staleEpoch
  nonce ← perform (ledger readNonce)
  assert (n₀ ≡ᵇ nonce) staleNonce
  rpk ← perform (ledger readRecoveryPk)
  requireLive rpk
  requireLive q
  requireLive q′
  assert (not (does (q′ ≟ᴾ rpk))) commitmentReused
  let c = challengeSubmit self rpk Rr q Rs q′ (suc epoch) nonce u g
  asField c
  assert (verifies Rr sr rpk c) invalidRecoverySignature
  assert (verifies Rs ss q c) invalidSuccessorSignature
  u₁ ← disclose u
  perform (atChain (timeAtMost u₁))
  perform (ledger (writePending true))
  entry ← disclose (deviceEntry self q (suc epoch) 0)
  q″ ← disclose q′
  u₂ ← disclose u
  perform (ledger (writePendingEntry entry))
  perform (ledger (writePendingRecoveryPk q″))
  window ← perform (ledger readVetoWindow)
  perform (ledger (writeNotBefore (u₂ + window)))
  bumpRound

-- Corrected set replacement is an intended specification, not a claim that
-- the stamped-map repair physically clears its retained historical entries.
install : Finalisation → Bytes32 → Program ⊤
install sourceShaped e = do
  perform (ledger (insertDevice e))
  perform (ledger (writeDeviceCount 1))
install corrected e = do
  perform (ledger resetDevices)
  perform (ledger (insertDevice e))
  perform (ledger (writeDeviceCount 1))

-- Permissionless; installs the successor according to the `Finalisation` variant.
finaliseRecovery : Finalisation → Program ⊤
finaliseRecovery f = do
  pend ← perform (ledger readPending)
  assert pend noPending
  notBefore ← perform (ledger readNotBefore)
  perform (atChain (timeAtLeast notBefore))
  pk ← perform (ledger readPendingRecoveryPk)
  requireLive pk
  epoch ← perform (ledger readEpoch)
  perform (ledger (writeEpoch (suc epoch)))
  entry ← perform (ledger readPendingEntry)
  install f entry
  pk′ ← perform (ledger readPendingRecoveryPk)
  perform (ledger (writeRecoveryPk pk′))
  perform (ledger (writePhiLen 0))
  clearPending
  bumpNonce
  bumpRound

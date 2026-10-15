{-# OPTIONS --safe --without-K #-}

open import Conformance.Primitives

-- The jubjub authorisation seam (`require_authorised_with_jubjub`), the key guard
-- `require_live_jubjub_point`, and unshielded custody (`deposit_unshielded`,
-- `do_withdraw_unshielded`) of `account.compact`, in the implementation's assert order so
-- failure kinds and journal prefixes line up. `Assertion` names every assert the model's
-- circuits share; `errorCode` is the harness's rendering of the abort message.
module Conformance.Custody (P : Primitives) (self : Primitives.Bytes32 P) where

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.String.Base using (String)
open import Data.Unit.Base
open import Relation.Nullary

open import Conformance.AccountLedger P

open Primitives P

data Assertion : Set where
  smallOrderKey unknownDevice invalidSignature noBalance insufficientBalance : Assertion
  entryPresent lastDevice authorisingDevice : Assertion
  recoveryPending phiEmpty phiLength phiSlot2 phiSlot3 phiSlot4 sessionZero sessionReused : Assertion
  commitmentReused identityKey smallOrderRecoveryKey : Assertion
  alreadyPending staleEpoch staleNonce invalidRecoverySignature invalidSuccessorSignature noPending : Assertion
  -- Not an assert: the abort of `challenge as Field` (see `asField`).
  challengeRange : Assertion

open import Midnight.ContractDSL.Program accountLedger Assertion

errorCode : Error → String
errorCode (operationError overflow) = "overflow"
errorCode (operationError absent) = "absent"
errorCode (assertionError smallOrderKey) = "smallOrderKey"
errorCode (assertionError unknownDevice) = "unknownDevice"
errorCode (assertionError invalidSignature) = "invalidSignature"
errorCode (assertionError noBalance) = "noBalance"
errorCode (assertionError insufficientBalance) = "insufficientBalance"
errorCode (assertionError entryPresent) = "entryPresent"
errorCode (assertionError lastDevice) = "lastDevice"
errorCode (assertionError authorisingDevice) = "authorisingDevice"
errorCode (assertionError recoveryPending) = "recoveryPending"
errorCode (assertionError phiEmpty) = "phiEmpty"
errorCode (assertionError phiLength) = "phiLength"
errorCode (assertionError phiSlot2) = "phiSlot2"
errorCode (assertionError phiSlot3) = "phiSlot3"
errorCode (assertionError phiSlot4) = "phiSlot4"
errorCode (assertionError sessionZero) = "sessionZero"
errorCode (assertionError sessionReused) = "sessionReused"
errorCode (assertionError commitmentReused) = "commitmentReused"
errorCode (assertionError identityKey) = "identityKey"
errorCode (assertionError smallOrderRecoveryKey) = "smallOrderRecoveryKey"
errorCode (assertionError alreadyPending) = "alreadyPending"
errorCode (assertionError staleEpoch) = "staleEpoch"
errorCode (assertionError staleNonce) = "staleNonce"
errorCode (assertionError invalidRecoverySignature) = "invalidRecoverySignature"
errorCode (assertionError invalidSuccessorSignature) = "invalidSuccessorSignature"
errorCode (assertionError noPending) = "noPending"
errorCode (assertionError challengeRange) = "challengeRange"

-- The trailing arguments of every `_with_jubjub` circuit.
record Authorisation : Set where
  constructor authorisation
  field pk : Point
        useCounter : ℕ
        sigR : Point
        sigS grind : ℕ
open Authorisation public

-- A circuit's challenge as a function of `(sig_r, pk, auth_nonce, grind_nonce)`.
Challenge : Set
Challenge = Point → Point → ℕ → ℕ → Bytes32

-- s·G = R + c·pk, with c the little-endian reading of the challenge.
verifies : Point → ℕ → Point → Bytes32 → Bool
verifies R s pk h = does (ecMulG s ≟ᴾ ecAdd R (ecMul pk (le h)))

-- [8]X = O exactly when X has small order.
smallOrder : Point → Bool
smallOrder x = does (ecMul x 8 ≟ᴾ ecMulG 0)

-- `challenge as Field` aborts above the field modulus: a challenge nobody ground, e.g. one
-- recomputed over arguments changed after signing.
asField : Bytes32 → Program ⊤
asField h = assert (le h <ᵇ fieldOrder) challengeRange


bumpNonce : Program ⊤
bumpNonce = do
  n ← perform (ledger readNonce)
  perform (ledger (writeNonce (suc n)))

bumpRound : Program ⊤
bumpRound = do
  n ← perform (ledger readRound)
  perform (ledger (writeRound (suc n)))

credit : Bytes32 → ℕ → Program ⊤
credit c a = do
  present ← perform (ledger (balanceMember c))
  (if present
    then (do
      n ← perform (ledger (readBalance c))
      perform (ledger (writeBalance c (n + a))))
    else perform (ledger (writeBalance c a)))

-- The challenge reads auth_nonce before the seam runs.
authorise : Authorisation → Challenge → Program ⊤
authorise (authorisation pk uc R s g) challenge = do
  nonce ← perform (ledger readNonce)
  assert (not (smallOrder pk)) smallOrderKey
  epoch ← perform (ledger readEpoch)
  let entry = deviceEntry self pk epoch uc
  known ← perform (ledger (deviceMember entry))
  assert known unknownDevice
  perform (ledger (removeDevice entry))
  perform (ledger (insertDevice (deviceEntry self pk epoch (suc uc))))
  let h = challenge R pk nonce g
  asField h
  assert (verifies R s pk h) invalidSignature
  bumpNonce
  bumpRound

requireLive : Point → Program ⊤
requireLive x = do
  assert (not (does (x ≟ᴾ ecMulG 0))) identityKey
  assert (not (smallOrder x)) smallOrderRecoveryKey

deposit : Bytes32 → ℕ → Program ⊤
deposit c a = do
  credit c a
  bumpRound

doWithdraw : Bytes32 → ℕ → Program ⊤
doWithdraw c a = do
  present ← perform (ledger (balanceMember c))
  assert present noBalance
  bal ← perform (ledger (readBalance c))
  assert (a ≤ᵇ bal) insufficientBalance
  perform (ledger (writeBalance c (bal ∸ a)))

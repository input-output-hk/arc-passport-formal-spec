{-# OPTIONS --safe --without-K #-}

open import Conformance.Primitives

module Conformance.RecoveryExecutionDefinitions (P : Primitives)
  (self : Primitives.Bytes32 P) where

open import Data.Bool.Base
open import Data.List.Base
open import Data.Nat.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Conformance.AccountLedger P
open import Conformance.Custody P self
open import Conformance.Recovery P self
open import Midnight.ContractDSL.Program accountLedger Assertion

open Primitives P
open SubmitArgs

submissionChallenge : State → SubmitArgs → Bytes32
submissionChallenge s a = challengeSubmit self (recoveryPk s) (sigRRecovery a)
  (successorPk a) (sigRSuccessor a) (successorRecoveryPk a)
  (suc (deviceEpoch s)) (authNonce s) (nowUpper a) (grindNonce a)

submissionState : State → SubmitArgs → State
submissionState s a = record s
  { round = suc (round s) ; pending = true
  ; pendingEntry = deviceEntry self (successorPk a) (suc (deviceEpoch s)) 0
  ; pendingRecoveryPk = successorRecoveryPk a
  ; pendingNotBefore = nowUpper a + vetoWindow s }

submissionJournal : State → SubmitArgs → Journal
submissionJournal s a = operated readPending (pending s) ∷ operated readEpoch (deviceEpoch s) ∷
  operated readNonce (authNonce s) ∷ operated readRecoveryPk (recoveryPk s) ∷
  required (timeAtMost (nowUpper a)) ∷ operated (writePending true) tt ∷
  operated (writePendingEntry (deviceEntry self (successorPk a) (suc (deviceEpoch s)) 0)) tt ∷
  operated (writePendingRecoveryPk (successorRecoveryPk a)) tt ∷
  operated readVetoWindow (vetoWindow s) ∷
  operated (writeNotBefore (nowUpper a + vetoWindow s)) tt ∷
  operated readRound (round s) ∷ operated (writeRound (suc (round s))) tt ∷ []

record SubmissionReady (s : State) (a : SubmitArgs) : Set where
  field notPending : not (pending s) ≡ true
        epochMatches : (expectedEpoch a ≡ᵇ deviceEpoch s) ≡ true
        nonceMatches : (expectedNonce a ≡ᵇ authNonce s) ≡ true
        recoveryNonidentity : not (does (recoveryPk s ≟ᴾ ecMulG 0)) ≡ true
        recoveryLargeOrder : not (smallOrder (recoveryPk s)) ≡ true
        successorNonidentity : not (does (successorPk a ≟ᴾ ecMulG 0)) ≡ true
        successorLargeOrder : not (smallOrder (successorPk a)) ≡ true
        replacementNonidentity : not (does (successorRecoveryPk a ≟ᴾ ecMulG 0)) ≡ true
        replacementLargeOrder : not (smallOrder (successorRecoveryPk a)) ≡ true
        commitmentFresh : not (does (successorRecoveryPk a ≟ᴾ recoveryPk s)) ≡ true
        challengeInField : (le (submissionChallenge s a) <ᵇ fieldOrder) ≡ true
        recoverySignature : verifies (sigRRecovery a) (sigSRecovery a) (recoveryPk s)
          (submissionChallenge s a) ≡ true
        successorSignature : verifies (sigRSuccessor a) (sigSSuccessor a) (successorPk a)
          (submissionChallenge s a) ≡ true
        deadlineFits : (nowUpper a + vetoWindow s <ᵇ uint64) ≡ true
        roundFits : (suc (round s) <ᵇ uint64) ≡ true

finalisationState : State → State
finalisationState s = record s
  { round = suc (round s) ; authNonce = suc (authNonce s)
  ; deviceEpoch = suc (deviceEpoch s) ; deviceCount = 1 ; devices = pendingEntry s ∷ []
  ; recoveryPk = pendingRecoveryPk s ; phiLen = 0 ; pending = false
  ; pendingEntry = zero32 ; pendingRecoveryPk = ecMulG 0 ; pendingNotBefore = 0 }

finalisationJournal : State → Journal
finalisationJournal s = operated readPending (pending s) ∷
  operated readNotBefore (pendingNotBefore s) ∷ required (timeAtLeast (pendingNotBefore s)) ∷
  operated readPendingRecoveryPk (pendingRecoveryPk s) ∷
  operated readEpoch (deviceEpoch s) ∷ operated (writeEpoch (suc (deviceEpoch s))) tt ∷
  operated readPendingEntry (pendingEntry s) ∷ operated resetDevices tt ∷
  operated (insertDevice (pendingEntry s)) tt ∷ operated (writeDeviceCount 1) tt ∷
  operated readPendingRecoveryPk (pendingRecoveryPk s) ∷
  operated (writeRecoveryPk (pendingRecoveryPk s)) tt ∷ operated (writePhiLen 0) tt ∷
  operated (writePending false) tt ∷ operated (writePendingEntry zero32) tt ∷
  operated readPendingRecoveryPk (pendingRecoveryPk s) ∷
  operated (writePendingRecoveryPk (ecMulG 0)) tt ∷ operated (writeNotBefore 0) tt ∷
  operated readNonce (authNonce s) ∷ operated (writeNonce (suc (authNonce s))) tt ∷
  operated readRound (round s) ∷ operated (writeRound (suc (round s))) tt ∷ []

record FinalisationReady (s : State) : Set where
  field hasPending : pending s ≡ true
        successorRecoveryNonidentity : not (does (pendingRecoveryPk s ≟ᴾ ecMulG 0)) ≡ true
        successorRecoveryLargeOrder : not (smallOrder (pendingRecoveryPk s)) ≡ true
        epochFits : (suc (deviceEpoch s) <ᵇ uint32) ≡ true
        nonceFits : (suc (authNonce s) <ᵇ uint64) ≡ true
        roundFits : (suc (round s) <ᵇ uint64) ≡ true


authorisationState : State → Authorisation → State
authorisationState s a = record s
  { authNonce = suc (authNonce s) ; round = suc (round s)
  ; devices = insertSet (deviceEntry self (pk a) (deviceEpoch s) (suc (useCounter a)))
      (removeSet (deviceEntry self (pk a) (deviceEpoch s) (useCounter a)) (devices s)) }

authorisationJournal : State → Authorisation → Journal
authorisationJournal s a = operated readNonce (authNonce s) ∷ operated readEpoch (deviceEpoch s) ∷
  operated (deviceMember (deviceEntry self (pk a) (deviceEpoch s) (useCounter a))) true ∷
  operated (removeDevice (deviceEntry self (pk a) (deviceEpoch s) (useCounter a))) tt ∷
  operated (insertDevice (deviceEntry self (pk a) (deviceEpoch s) (suc (useCounter a)))) tt ∷
  operated readNonce (authNonce s) ∷ operated (writeNonce (suc (authNonce s))) tt ∷
  operated readRound (round s) ∷ operated (writeRound (suc (round s))) tt ∷ []

rotationChallenge : State → Bytes32 → Authorisation → Bytes32
rotationChallenge s k a = challengeRotateEncKey self (sigR a) (pk a) k (authNonce s) (grind a)

rotationState : State → Bytes32 → Authorisation → State
rotationState s k a = record (authorisationState s a) { encKey = k }

rotationJournal : State → Bytes32 → Authorisation → Journal
rotationJournal s k a = authorisationJournal s a ++ operated (setEncKey k) tt ∷ []

record RotationReady (s : State) (k : Bytes32) (a : Authorisation) : Set where
  field liveSigner : not (smallOrder (pk a)) ≡ true
        knownSigner : deviceEntry self (pk a) (deviceEpoch s) (useCounter a) ∈ᵇ devices s ≡ true
        challengeInField : (le (rotationChallenge s k a) <ᵇ fieldOrder) ≡ true
        signatureValid : verifies (sigR a) (sigS a) (pk a) (rotationChallenge s k a) ≡ true
        nonceFits : (suc (authNonce s) <ᵇ uint64) ≡ true
        roundFits : (suc (round s) <ᵇ uint64) ≡ true
        -- The current model increments the use counter over naturals; this
        -- extra concrete-width precondition is not a model-enforced assertion.
        counterFits : (suc (useCounter a) <ᵇ uint64) ≡ true

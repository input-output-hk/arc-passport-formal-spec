{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

-- Recovery facts of contracts/account.compact at Passport fc19e471536f, read
-- off accepted runs of the actual full-account evaluator (FullAccountBody and
-- FullAccount.AccountSemantics): recover_submit's recovery authority, successor
-- proof of possession and pending installation; the permissionless finalisation
-- enacting that pending record; device-authorised cancellation and recovery
-- publication; and how every entrypoint affects the pending record.
--
-- These are local source-execution facts from an arbitrary before-state, not
-- ledger adoption. Primitives P is uninterpreted: hash, key-validation and
-- Schnorr checks appear as accepted runs of the source functions, with no
-- cryptographic law assumed. Nothing here certifies guardian consent, an honest
-- recovery quorum, fairness or that any recovery or cancellation is ever made.
-- Statements: FullAccountRecoverySecurityProperties.
module Conformance.FullAccountRecoverySecurity (P : Primitives) where

import Conformance.FullAccount as Model
open import Conformance.FullAccountBody P
open import Conformance.FullAccountCrypto P
open import Conformance.FullAccountExecution using (Run)
open import Conformance.FullAccountLayouts
open import Conformance.FullAccountSignatureBinding P using (recoverySubmitTag; submitChallenge; submitPreimage)
open import Data.Bool.Base using (true; false)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base hiding (equal)
open import Data.String.Base using (String)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_)

open Model.AccountSemantics P using (Entrypoint; construct; activation; device; grant;
  depositPublic; depositPrivate; submitRecovery; finaliseRecovery)

------------------------------------------------------------------------
-- Observed states
--
-- `Run m s x s` (FullAccountExecution): the actual source computation m, run
-- from s, returns x and leaves the ledger unchanged. Below it records the
-- source's hashing, key-validation and signature checks.

-- Ledger cell k of s holds v, exactly as the source `read` observes it.
record Stores (s : State) (k : String) (v : Value) : Set where
  constructor stored
  field observed : lookupCell k (ledger s) ≡ just v

-- t agrees with s on every ledger cell outside `written`.
record Frames (written : List String) (s t : State) : Set where
  constructor framed
  field unwritten : ∀ k → k ∉ written → lookupCell k (ledger t) ≡ lookupCell k (ledger s)

-- The pending recovery record: flag, successor device entry, next recovery
-- key and the end of its veto window.
pendingCells : List String
pendingCells = "pending_recovery" ∷ "pending_entry" ∷ "pending_recovery_pk" ∷ "pending_not_before" ∷ []

record SamePending (s t : State) : Set where
  constructor samePending
  field pendingKept : ∀ k → k ∈ pendingCells → lookupCell k (ledger t) ≡ lookupCell k (ledger s)

------------------------------------------------------------------------
-- recover_submit

-- The successor authority submit enrols: its Jubjub key at use counter 0.
successorAuthority : List Value → Auth
successorAuthority xs = auth (SubmitArguments.successorKey xs) 0 none none 0 0 none none none

-- An accepted recover_submit with argument vector xs from s to t. All checks
-- observe s: submit writes nothing before its final installation block.
module Submission (ctx : Context) (xs : List Value) where
  open SubmitArguments xs

  record Evidence (s t : State) : Set where
    field
      pendingFlag storedEpoch storedNonce recoveryKey : Value
      -- No recovery is pending, and the signed epoch and nonce are current.
      idle : Stores s "pending_recovery" pendingFlag
      notPending : flag pendingFlag ≡ false
      epochCell : Stores s "device_epoch" storedEpoch
      signedEpoch : number epoch ≡ number storedEpoch
      nonceCell : Stores s "auth_nonce" storedNonce
      signedNonce : number authNonce ≡ number storedNonce
      -- The configured recovery authority, and the source key checks.
      recoveryKeyCell : Stores s "recovery_pk" recoveryKey
      recoveryKeyValid : Run (requireRecoveryKey recoveryKey) s tt s
      successorKeyValid : Run (requireRecoveryKey successorKey) s tt s
      nextKeyValid : Run (requireRecoveryKey nextRecoveryKey) s tt s
      freshRecoveryKey : equal nextRecoveryKey recoveryKey ≡ false
      epochBound : (suc (number storedEpoch) <ᵇ 2 ^ 32) ≡ true
      -- Recovery authority and successor sign one digest of the exact request:
      -- account, both keys and commitments, next recovery key, next epoch,
      -- current nonce, time bound and grind nonce.
      domain digest : Value
      domainHash : Run (hashTag recoverySubmitTag) s domain s
      challengeHash : Run (hash (submitPreimage domain
        (submitChallenge (self ctx) recoveryKey xs (suc (number storedEpoch)) (number storedNonce)))) s digest s
      recoverySignature : Run (schnorr recoveryKey recoveryR recoveryS digest "invalid recovery signature") s tt s
      successorSignature :
        Run (schnorr successorKey successorR successorS digest "invalid successor co-signature") s tt s
      notPast : blockTime ctx ≤ number nowBound
      -- Installation: the successor's entry for the next epoch, the next
      -- recovery key, and a deadline one veto window after the time bound.
      successor vetoWindow : Value
      successorEntry :
        Run (entryAt jubjub (self ctx) (successorAuthority xs) (suc (number storedEpoch)) 0) s successor s
      windowCell : Stores s "veto_window" vetoWindow
      installsFlag : Stores t "pending_recovery" (bool true)
      installsEntry : Stores t "pending_entry" successor
      installsRecoveryKey : Stores t "pending_recovery_pk" nextRecoveryKey
      installsDeadline : Stores t "pending_not_before" (nat (number nowBound + number vetoWindow))
      frame : Frames (pendingCells ++ "round" ∷ []) s t

------------------------------------------------------------------------
-- recover_finalise: permissionless enactment, verifying no signature

finaliseWrites : List String
finaliseWrites = "device_epoch" ∷ "devices" ∷ "device_count" ∷ "recovery_pk" ∷
  "recovery_phi_len" ∷ "auth_nonce" ∷ "round" ∷ pendingCells

module Finalisation (ctx : Context) where
  record Evidence (s t : State) : Set where
    field
      pendingFlag deadline successor recoveryKey storedEpoch storedNonce clearedKey : Value
      -- A pending record whose veto window has ended at this block time.
      pending : Stores s "pending_recovery" pendingFlag
      isPending : flag pendingFlag ≡ true
      deadlineCell : Stores s "pending_not_before" deadline
      windowElapsed : number deadline ≤ blockTime ctx
      successorCell : Stores s "pending_entry" successor
      recoveryKeyCell : Stores s "pending_recovery_pk" recoveryKey
      recoveryKeyValid : Run (requireRecoveryKey recoveryKey) s tt s
      epochCell : Stores s "device_epoch" storedEpoch
      nonceCell : Stores s "auth_nonce" storedNonce
      -- Enactment: the pending successor alone, the pending recovery key, a
      -- new epoch and nonce.
      advancesEpoch : Stores t "device_epoch" (nat (suc (number storedEpoch)))
      replacesDevices : Stores t "devices" (tuple (successor ∷ []))
      resetsDeviceCount : Stores t "device_count" (nat 1)
      installsRecoveryKey : Stores t "recovery_pk" recoveryKey
      clearsPhi : Stores t "recovery_phi_len" (nat 0)
      advancesNonce : Stores t "auth_nonce" (nat (suc (number storedNonce)))
      -- The pending record is cleared.
      clearsFlag : Stores t "pending_recovery" (bool false)
      clearsEntry : Stores t "pending_entry" zero32
      clearedKeyValue : ecMul P jubjub recoveryKey 0 ≡ success clearedKey
      clearsKey : Stores t "pending_recovery_pk" clearedKey
      clearsDeadline : Stores t "pending_not_before" (nat 0)
      frame : Frames finaliseWrites s t

------------------------------------------------------------------------
-- recover_cancel and publish_recovery_session operation bodies, which
-- device authorisation precedes (FullAccount.AccountSemantics.deviceCall)

record Cancellation (s t : State) : Set where
  field
    pendingFlag recoveryKey clearedKey : Value
    pending : Stores s "pending_recovery" pendingFlag
    isPending : flag pendingFlag ≡ true
    recoveryKeyCell : Stores s "pending_recovery_pk" recoveryKey
    clearedKeyValue : ecMul P jubjub recoveryKey 0 ≡ success clearedKey
    clearsFlag : Stores t "pending_recovery" (bool false)
    clearsEntry : Stores t "pending_entry" zero32
    clearsKey : Stores t "pending_recovery_pk" clearedKey
    clearsDeadline : Stores t "pending_not_before" (nat 0)
    frame : Frames pendingCells s t

publishWrites : List String
publishWrites = "recovery_pk" ∷ "recovery_session" ∷ "recovery_phi" ∷ "recovery_phi_len" ∷
  "recovery_wrap" ∷ "recovery_version" ∷ []

-- Publication replaces the configured recovery authority; argument layout
-- [recovery_pk, session_nonce, phi1..phi4, phi_len, wrap] (FullAccountBody).
module Publication (xs : List Value) where
  record Evidence (s t : State) : Set where
    field
      pendingFlag session oldRecoveryKey : Value
      idle : Stores s "pending_recovery" pendingFlag
      notPending : flag pendingFlag ≡ false
      sessionCell : Stores s "recovery_session" session
      freshSession : equal (get 1 xs) session ≡ false
      recoveryKeyCell : Stores s "recovery_pk" oldRecoveryKey
      freshRecoveryKey : equal (get 0 xs) oldRecoveryKey ≡ false
      newKeyValid : Run (requireRecoveryKey (get 0 xs)) s tt s
      installsRecoveryKey : Stores t "recovery_pk" (get 0 xs)
      installsSession : Stores t "recovery_session" (get 1 xs)
      frame : Frames publishWrites s t

------------------------------------------------------------------------
-- The pending record across entrypoints

-- A record pending when the call began is cleared.
record Cleared (s t : State) : Set where
  field
    pendingFlag : Value
    wasPending : Stores s "pending_recovery" pendingFlag
    isPending : flag pendingFlag ≡ true
    clearsFlag : Stores t "pending_recovery" (bool false)

-- Device- and grant-authorised calls run an operation body; only recover_cancel
-- touches the pending record.
OperationEffect : Operation → State → State → Set
OperationEffect cancelRecovery s t = Cleared s t
OperationEffect _ s t = SamePending s t

-- How an accepted execution of each entrypoint, from s to t, affects the
-- pending record: only submission installs one.
PendingEffect : Entrypoint → Context → List Value → State → State → Set
PendingEffect construct ctx xs s t = Stores t "pending_recovery" (bool false)
PendingEffect submitRecovery ctx xs s t = Submission.Evidence ctx xs s t
PendingEffect finaliseRecovery ctx xs s t = Finalisation.Evidence ctx s t
PendingEffect (device c op) ctx xs s t = OperationEffect op s t
PendingEffect (grant c op) ctx xs s t = OperationEffect op s t
PendingEffect (activation c) ctx xs s t = SamePending s t
PendingEffect depositPublic ctx xs s t = SamePending s t
PendingEffect depositPrivate ctx xs s t = SamePending s t

-- A witnessed accepting recover_submit computation, from submittedFrom to
-- installedAt, whose installed pending cells equal those of s. This is endpoint
-- matching only: it records neither that the submission occurred in a given
-- history nor that the record stayed unchanged in between (an equal record may
-- recur after cancellation and resubmission). Trace-indexed occurrence is
-- established at the lifecycle layer (Passport.AccountSecurityProperties).
record Installed (s : State) : Set where
  field
    submitContext : Context
    submitArguments : List Value
    submittedFrom installedAt : State
    submission : Submission.Evidence submitContext submitArguments submittedFrom installedAt
    unchanged : SamePending installedAt s

-- Every flagged pending record of s matches the record installed by some
-- accepting submission computation. provenance-step and empty-provenance
-- (FullAccountRecoverySecurityProperties) maintain this along executions.
PendingProvenance : State → Set
PendingProvenance s = ∀ {p} → Stores s "pending_recovery" p → flag p ≡ true → Installed s

-- A finalisation from s to t enacts the successor, recovery key and deadline
-- installed by the witnessed submission computation that s's record matches.
record EnactsSubmission (ctx : Context) (s t : State) : Set where
  field
    installation : Installed s
    finalisation : Finalisation.Evidence ctx s t
    sameSuccessor : Finalisation.Evidence.successor finalisation ≡
      Submission.Evidence.successor (Installed.submission installation)
    sameRecoveryKey : Finalisation.Evidence.recoveryKey finalisation ≡
      SubmitArguments.nextRecoveryKey (Installed.submitArguments installation)
    sameDeadline : Finalisation.Evidence.deadline finalisation ≡
      nat (number (SubmitArguments.nowBound (Installed.submitArguments installation)) +
        number (Submission.Evidence.vetoWindow (Installed.submission installation)))

{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

-- Opaque recovery execution stages; public statements stay in RecoverySecurityProperties.
module Conformance.FullAccountRecoverySecurityStages (P : Primitives) where

open import Conformance.FullAccountBody P
open import Conformance.FullAccountCrypto P
open import Conformance.FullAccountExecution using (Run) renaming (then to split)
open import Conformance.FullAccountLayouts
open import Conformance.FullAccountRecoverySecurity P
open import Conformance.FullAccountRecoverySecurityHelpers P
open import Conformance.FullAccountSignatureBinding P using (recoverySubmitTag; submitChallenge; submitPreimage)
open import Data.Bool.Base using (true; false; not)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Nat.Base hiding (equal)
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (tt)

module SubmitRun (ctx : Context) (xs : List Value) where
  open SubmitArguments xs

  private
    installation : ℕ → M Value
    installation postEpoch = do
      write "pending_recovery" (bool true)
      successor ← entry jubjub ctx (successorAuthority xs) postEpoch 0
      write "pending_entry" successor
      write "pending_recovery_pk" nextRecoveryKey
      window ← readCount "veto_window"
      writeCount "pending_not_before" 64 (number nowBound + window)
      bump "round" 64
      return unit

    signatures : ℕ → Value → Value → M Value
    signatures postEpoch digest pk = do
      schnorr pk recoveryR recoveryS digest "invalid recovery signature"
      schnorr successorKey successorR successorS digest "invalid successor co-signature"
      past ← readTimeGreater ctx (number nowBound)
      assert (not past) "now bound is in the past"
      installation postEpoch

    signing : ℕ → Value → Value → ℕ → M Value
    signing postEpoch addr pk nonce = do
      domain ← hashTag recoverySubmitTag
      digest ← hash (submitPreimage domain (submitChallenge addr pk xs postEpoch nonce))
      verifyingPk ← read "recovery_pk"
      signatures postEpoch digest verifyingPk

    record InstalledCells (postEpoch : ℕ) (s t : State) : Set where
      field
        successor window : Value
        successorEntry : Run (entryAt jubjub (self ctx) (successorAuthority xs) postEpoch 0) s successor s
        windowCell : Stores s "veto_window" window
        flagStored : Stores t "pending_recovery" (bool true)
        entryStored : Stores t "pending_entry" successor
        keyStored : Stores t "pending_recovery_pk" nextRecoveryKey
        deadlineStored : Stores t "pending_not_before" (nat (number nowBound + number window))
        frame : Frames (pendingCells ++ "round" ∷ []) s t

    record Ready (s : State) (v : Value) (t : State) : Set where
      field
        storedEpoch : Value
        complete : InstalledCells (suc (number storedEpoch)) s t → Submission.Evidence ctx xs s t
        remaining : Run (installation (suc (number storedEpoch))) s v t

    abstract
      install : ∀ postEpoch {s v t} → Run (installation postEpoch) s v t → InstalledCells postEpoch s t
      install postEpoch {s} r₀ =
        step-write "pending_recovery" (bool true) r₀ λ flagStored f₁ r₁ →
        step-entry ctx (successorAuthority xs) postEpoch 0 r₁ λ successor successorEntry r₂ →
        step-write "pending_entry" successor r₂ λ entryStored f₂ r₃ →
        step-write "pending_recovery_pk" nextRecoveryKey r₃ λ keyStored f₃ r₄ →
        step-readCount "veto_window"
          {f = λ window → writeCount "pending_not_before" 64 (number nowBound + window) >> (bump "round" 64 >> return unit)}
          r₄ λ window windowCell r₅ →
        step-writeCount "pending_not_before" 64 (number nowBound + number window) r₅ λ _ deadlineStored f₄ r₆ →
        step-bump "round" 64 r₆ λ _ _ _ _ f₅ r₇ →
        finish r₇ (InstalledCells postEpoch s) record
          { successor = successor
          ; window = window
          ; successorEntry = successorEntry s
          ; windowCell = stores-frames-back (frames-then f₁ (frames-then f₂ f₃)) windowCell (absent _)
          ; flagStored = stores-frames (frames-then f₂ (frames-then f₃ (frames-then f₄ f₅))) flagStored (absent _)
          ; entryStored = stores-frames (frames-then f₃ (frames-then f₄ f₅)) entryStored (absent _)
          ; keyStored = stores-frames (frames-then f₄ f₅) keyStored (absent _)
          ; deadlineStored = stores-frames f₅ deadlineStored (absent _)
          ; frame = frames-then f₁ (frames-then f₂ (frames-then f₃ (frames-then f₄ f₅)))
          }

      prefix : ∀ {s v t} → Run (submit ctx xs) s v t → Ready s v t
      prefix {s} r₀ =
        step-read "pending_recovery" r₀ λ pending idle r₁ →
        step-assert (not (flag pending)) "recovery already pending" r₁ λ free r₂ →
        step-readCount "device_epoch" r₂ λ storedEpoch epochCell r₃ →
        step-assert (number epoch ≡ᵇ number storedEpoch) "stale epoch" r₃ λ signedEpoch r₄ →
        step-readCount "auth_nonce" r₄ λ storedNonce nonceCell r₅ →
        step-assert (number authNonce ≡ᵇ number storedNonce) "stale authorisation nonce" r₅ λ signedNonce r₆ →
        step-read "recovery_pk" r₆ λ pk pkCell r₇ →
        step-pure (requireRecoveryKey pk) (pure-requireRecoveryKey pk) r₇ λ _ pkValid r₈ →
        step-pure (requireRecoveryKey successorKey) (pure-requireRecoveryKey successorKey) r₈ λ _ successorValid r₉ →
        step-pure (requireRecoveryKey nextRecoveryKey) (pure-requireRecoveryKey nextRecoveryKey) r₉ λ _ nextValid r₁₀ →
        step-assert (not (equal nextRecoveryKey pk)) "recovery commitment reused"
          (read-known "recovery_pk" pkCell r₁₀) λ reused r₁₁ →
        step-cast "device_epoch" 32 (suc (number storedEpoch))
          (readCount-known "device_epoch" epochCell r₁₁) λ epochBound r₁₂ →
        step-pure (hashTag recoverySubmitTag) pure-hash
          (readCount-known "auth_nonce" {f = signing (suc (number storedEpoch)) (self ctx) pk} nonceCell
            (read-known "recovery_pk"
              {f = λ signingPk → readCount "auth_nonce" >>= signing (suc (number storedEpoch)) (self ctx) signingPk}
              pkCell (step-readSelf ctx (λ _ → read "recovery_pk")
                {g = λ addr signingPk → readCount "auth_nonce" >>= signing (suc (number storedEpoch)) addr signingPk} r₁₂)))
          λ domain domainHash r₁₃ →
        step-hash r₁₃ λ digest challengeHash r₁₄ →
        step-pure (schnorr pk recoveryR recoveryS digest "invalid recovery signature")
          (pure-schnorr pk recoveryR recoveryS digest "invalid recovery signature")
          (read-known "recovery_pk" {f = signatures (suc (number storedEpoch)) digest} pkCell r₁₄)
          λ _ recoverySignature r₁₅ →
        step-pure (schnorr successorKey successorR successorS digest "invalid successor co-signature")
          (pure-schnorr successorKey successorR successorS digest "invalid successor co-signature") r₁₅
          λ _ successorSignature r₁₆ →
        step-assert (not (number nowBound <ᵇ blockTime ctx)) "now bound is in the past"
          (step-past ctx (number nowBound) (λ past → assert (not past) "now bound is in the past")
            {g = λ _ _ → installation (suc (number storedEpoch))} r₁₆)
          λ notPast r₁₇ → record
          { storedEpoch = storedEpoch
          ; remaining = r₁₇
          ; complete = λ cells → record
            { pendingFlag = pending
            ; storedEpoch = storedEpoch
            ; storedNonce = storedNonce
            ; recoveryKey = pk
            ; idle = idle
            ; notPending = not-true (flag pending) free
            ; epochCell = epochCell
            ; signedEpoch = ≡ᵇ-true (number epoch) (number storedEpoch) signedEpoch
            ; nonceCell = nonceCell
            ; signedNonce = ≡ᵇ-true (number authNonce) (number storedNonce) signedNonce
            ; recoveryKeyCell = pkCell
            ; recoveryKeyValid = pkValid
            ; successorKeyValid = successorValid
            ; nextKeyValid = nextValid
            ; freshRecoveryKey = not-true (equal nextRecoveryKey pk) reused
            ; epochBound = epochBound
            ; domain = domain
            ; digest = digest
            ; domainHash = domainHash
            ; challengeHash = challengeHash
            ; recoverySignature = recoverySignature
            ; successorSignature = successorSignature
            ; notPast = <ᵇ-false (number nowBound) (blockTime ctx) (not-true (number nowBound <ᵇ blockTime ctx) notPast)
            ; successor = InstalledCells.successor cells
            ; vetoWindow = InstalledCells.window cells
            ; successorEntry = InstalledCells.successorEntry cells
            ; windowCell = InstalledCells.windowCell cells
            ; installsFlag = InstalledCells.flagStored cells
            ; installsEntry = InstalledCells.entryStored cells
            ; installsRecoveryKey = InstalledCells.keyStored cells
            ; installsDeadline = InstalledCells.deadlineStored cells
            ; frame = InstalledCells.frame cells
            }
          }

  evidence : ∀ {s v t} → Run (submit ctx xs) s v t → Submission.Evidence ctx xs s t
  evidence r = Ready.complete ready (install (suc (number (Ready.storedEpoch ready))) (Ready.remaining ready))
    where ready = prefix r

module FinaliseRun (ctx : Context) where
  private
    clearing : Value → M Value
    clearing pk = do
      o ← lift (ecMul P jubjub pk 0)
      write "pending_recovery_pk" o
      write "pending_not_before" (nat 0)
      bump "auth_nonce" 64
      bump "round" 64
      return unit

    installing : Value → M Value
    installing pk = do
      write "recovery_pk" pk
      write "recovery_phi_len" (nat 0)
      write "pending_recovery" (bool false)
      write "pending_entry" zero32
      clearingPk ← read "pending_recovery_pk"
      clearing clearingPk

    enacting : M Value
    enacting = do
      pk ← read "pending_recovery_pk"
      requireRecoveryKey pk
      bump "device_epoch" 32
      clear "devices"
      successor ← read "pending_entry"
      include "devices" successor
      write "device_count" (nat 1)
      installingPk ← read "pending_recovery_pk"
      installing installingPk

  evidence : ∀ {s v t} → Run (finalise ctx) s v t → Finalisation.Evidence ctx s t
  evidence {s} r₀ =
    step-read "pending_recovery" r₀ λ pending pendingCell r₁ →
    step-assert (flag pending) "no recovery pending" r₁ λ isPending r₂ →
    step-readCount "pending_not_before" r₂ λ deadline deadlineCell r₃ →
    step-assert (not (blockTime ctx <ᵇ number deadline)) "veto window still open"
      (step-early ctx (number deadline) (λ early → assert (not early) "veto window still open")
        {g = λ _ _ → enacting} r₃)
      λ notEarly r₄ →
    step-read "pending_recovery_pk" r₄ λ pk pkCell r₅ →
    step-pure (requireRecoveryKey pk) (pure-requireRecoveryKey pk) r₅ λ _ pkValid r₆ →
    step-bump "device_epoch" 32 r₆ λ storedEpoch epochCell _ epochStored f₁ r₇ →
    step-clear "devices" r₇ λ emptied f₂ r₈ →
    step-read "pending_entry" r₈ λ successor successorRead r₉ →
    step-include "devices" successor r₉ λ includedSuccessor f₃ r₁₀ →
    step-write "device_count" (nat 1) r₁₀ λ countStored f₄ r₁₁ →
    step-write "recovery_pk" pk
      (read-known "pending_recovery_pk" {f = installing}
        (stores-frames (frames-then f₁ (frames-then f₂ (frames-then f₃ f₄))) pkCell (absent _)) r₁₁)
      λ keyStored f₅ r₁₂ →
    step-write "recovery_phi_len" (nat 0) r₁₂ λ phiStored f₆ r₁₃ →
    step-write "pending_recovery" (bool false) r₁₃ λ flagStored f₇ r₁₄ →
    step-write "pending_entry" zero32 r₁₄ λ entryStored f₈ r₁₅ →
    step-lift (ecMul P jubjub pk 0)
      (read-known "pending_recovery_pk" {f = clearing}
        (stores-frames (frames-then f₁ (frames-then f₂ (frames-then f₃ (frames-then f₄
          (frames-then f₅ (frames-then f₆ (frames-then f₇ f₈))))))) pkCell (absent _)) r₁₅)
      λ clearedKey clearedKeyValue r₁₆ →
    step-write "pending_recovery_pk" clearedKey r₁₆ λ clearedStored f₉ r₁₇ →
    step-write "pending_not_before" (nat 0) r₁₇ λ deadlineStored f₁₀ r₁₈ →
    step-bump "auth_nonce" 64 r₁₈ λ storedNonce nonceRead _ nonceStored f₁₁ r₁₉ →
    step-bump "round" 64 r₁₉ λ _ _ _ _ f₁₂ r₂₀ →
    let F₁₂ = f₁₂
        F₁₁ = frames-then f₁₁ F₁₂
        F₁₀ = frames-then f₁₀ F₁₁
        F₉ = frames-then f₉ F₁₀
        F₈ = frames-then f₈ F₉
        F₇ = frames-then f₇ F₈
        F₆ = frames-then f₆ F₇
        F₅ = frames-then f₅ F₆
        F₄ = frames-then f₄ F₅
        F₃ = frames-then f₃ F₄
        F₂ = frames-then f₂ F₃
        F₁ = frames-then f₁ F₂
    in finish r₂₀ (Finalisation.Evidence ctx s) record
      { pendingFlag = pending
      ; deadline = deadline
      ; successor = successor
      ; recoveryKey = pk
      ; storedEpoch = storedEpoch
      ; storedNonce = storedNonce
      ; clearedKey = clearedKey
      ; pending = pendingCell
      ; isPending = isPending
      ; deadlineCell = deadlineCell
      ; windowElapsed = <ᵇ-false (blockTime ctx) (number deadline) (not-true (blockTime ctx <ᵇ number deadline) notEarly)
      ; successorCell = stores-frames-back (frames-then f₁ f₂) successorRead (absent _)
      ; recoveryKeyCell = pkCell
      ; recoveryKeyValid = pkValid
      ; epochCell = epochCell
      ; nonceCell = stores-frames-back (frames-then f₁ (frames-then f₂ (frames-then f₃ (frames-then f₄
          (frames-then f₅ (frames-then f₆ (frames-then f₇ (frames-then f₈ (frames-then f₉ f₁₀)))))))))
          nonceRead (absent _)
      ; advancesEpoch = stores-frames F₂ epochStored (absent _)
      ; replacesDevices = stores-frames F₄ (include-empty emptied includedSuccessor) (absent _)
      ; resetsDeviceCount = stores-frames F₅ countStored (absent _)
      ; installsRecoveryKey = stores-frames F₆ keyStored (absent _)
      ; clearsPhi = stores-frames F₇ phiStored (absent _)
      ; advancesNonce = stores-frames F₁₂ nonceStored (absent _)
      ; clearsFlag = stores-frames F₈ flagStored (absent _)
      ; clearsEntry = stores-frames F₉ entryStored (absent _)
      ; clearedKeyValue = clearedKeyValue
      ; clearsKey = stores-frames F₁₀ clearedStored (absent _)
      ; clearsDeadline = stores-frames F₁₁ deadlineStored (absent _)
      ; frame = frames-weaken _ F₁
      }

module OperationRun where
  cancel-run : ∀ {s x t} → Run cancel s x t → Cancellation s t
  cancel-run {s} r₀ =
    step-read "pending_recovery" r₀ λ pending pendingCell r₁ →
    step-assert (flag pending) "no recovery pending" r₁ λ isPending r₂ →
    step-write "pending_recovery" (bool false) r₂ λ flagStored f₁ r₃ →
    step-write "pending_entry" zero32 r₃ λ entryStored f₂ r₄ →
    step-read "pending_recovery_pk" r₄ λ pk pkRead r₅ →
    step-lift (ecMul P jubjub pk 0) r₅ λ clearedKey clearedKeyValue r₆ →
    step-write "pending_recovery_pk" clearedKey r₆ λ keyStored f₃ r₇ →
    write-last "pending_not_before" (nat 0) r₇ λ deadlineStored f₄ → record
      { pendingFlag = pending
      ; recoveryKey = pk
      ; clearedKey = clearedKey
      ; pending = pendingCell
      ; isPending = isPending
      ; recoveryKeyCell = stores-frames-back (frames-then f₁ f₂) pkRead (absent _)
      ; clearedKeyValue = clearedKeyValue
      ; clearsFlag = stores-frames (frames-then f₂ (frames-then f₃ f₄)) flagStored (absent _)
      ; clearsEntry = stores-frames (frames-then f₃ f₄) entryStored (absent _)
      ; clearsKey = stores-frames f₄ keyStored (absent _)
      ; clearsDeadline = deadlineStored
      ; frame = frames-then f₁ (frames-then f₂ (frames-then f₃ f₄))
      }

  -- body cancelRecovery is `cancel >> return unit`, whatever its other arguments.
  cancel-body : ∀ {s v t} → Run (cancel >> return unit) s v t → Cancellation s t
  cancel-body r with split cancel {λ _ → return unit} r
  ... | _ , t₁ , cancelled , returned = finish returned (Cancellation _) (cancel-run cancelled)

  publish-run : ∀ xs {s x t} → Run (publish xs) s x t → Publication.Evidence xs s t
  publish-run xs {s} r₀ =
    step-read "pending_recovery" r₀ λ pending idle r₁ →
    step-assert (not (flag pending)) "recovery pending; cancel first" r₁ λ free r₂ →
    step-assert (1 ≤ᵇ number (get 6 xs)) "phi must not be empty" r₂ λ _ r₃ →
    step-assert (number (get 6 xs) ≤ᵇ 4) "phi length out of range" r₃ λ _ r₄ →
    step-if (number (get 6 xs) <ᵇ 2) (pure-assert (number (get 3 xs) ≡ᵇ 0) "unused phi slot 2 not zero")
      (pure-return tt) r₄ λ r₅ →
    step-if (number (get 6 xs) <ᵇ 3) (pure-assert (number (get 4 xs) ≡ᵇ 0) "unused phi slot 3 not zero")
      (pure-return tt) r₅ λ r₆ →
    step-if (number (get 6 xs) <ᵇ 4) (pure-assert (number (get 5 xs) ≡ᵇ 0) "unused phi slot 4 not zero")
      (pure-return tt) r₆ λ r₇ →
    step-assert (not (equal (get 1 xs) zero32)) "session nonce is zero" r₇ λ _ r₈ →
    step-read "recovery_session" r₈ λ session sessionCell r₉ →
    step-assert (not (equal (get 1 xs) session)) "session nonce reused" r₉ λ sessionFresh r₁₀ →
    step-read "recovery_pk" r₁₀ λ oldKey keyCell r₁₁ →
    step-assert (not (equal (get 0 xs) oldKey)) "recovery commitment reused" r₁₁ λ keyFresh r₁₂ →
    step-pure (requireRecoveryKey (get 0 xs)) (pure-requireRecoveryKey (get 0 xs)) r₁₂ λ _ newValid r₁₃ →
    step-write "recovery_pk" (get 0 xs) r₁₃ λ keyStored f₁ r₁₄ →
    step-write "recovery_session" (get 1 xs) r₁₄ λ sessionStored f₂ r₁₅ →
    step-insert "recovery_phi" (nat 1) (get 2 xs) r₁₅ λ f₃ r₁₆ →
    step-insert "recovery_phi" (nat 2) (get 3 xs) r₁₆ λ f₄ r₁₇ →
    step-insert "recovery_phi" (nat 3) (get 4 xs) r₁₇ λ f₅ r₁₈ →
    step-insert "recovery_phi" (nat 4) (get 5 xs) r₁₈ λ f₆ r₁₉ →
    step-write "recovery_phi_len" (get 6 xs) r₁₉ λ _ f₇ r₂₀ →
    step-write "recovery_wrap" (get 7 xs) r₂₀ λ _ f₈ r₂₁ →
    write-last "recovery_version" (nat 1) r₂₁ λ _ f₉ →
    let F₃ = frames-then f₃ (frames-then f₄ (frames-then f₅ (frames-then f₆ (frames-then f₇
          (frames-then f₈ f₉)))))
    in record
      { pendingFlag = pending
      ; session = session
      ; oldRecoveryKey = oldKey
      ; idle = idle
      ; notPending = not-true (flag pending) free
      ; sessionCell = sessionCell
      ; freshSession = not-true (equal (get 1 xs) session) sessionFresh
      ; recoveryKeyCell = keyCell
      ; freshRecoveryKey = not-true (equal (get 0 xs) oldKey) keyFresh
      ; newKeyValid = newValid
      ; installsRecoveryKey = stores-frames (frames-then f₂ F₃) keyStored (absent _)
      ; installsSession = stores-frames F₃ sessionStored (absent _)
      ; frame = frames-weaken _ (frames-then f₁ (frames-then f₂ F₃))
      }

  publish-body : ∀ ctx xs coin e {s v t} → Run (body publishRecovery ctx xs coin e) s v t →
    Publication.Evidence xs s t
  publish-body ctx xs coin e r with split (publish xs) {λ _ → return unit} r
  ... | _ , t₁ , published , returned = finish returned (Publication.Evidence xs _) (publish-run xs published)

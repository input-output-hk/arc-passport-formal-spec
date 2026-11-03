{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

module Passport.GrantEffectsProof (P : Primitives) where


import Conformance.FullAccount as Model
import Conformance.FullAccountDeviceSecurity P as DeviceSpec
open DeviceSpec using (DeviceCall; Authorisation; Activation)
open import Conformance.FullAccountBody P
open import Conformance.FullAccountCrypto P
open import Conformance.FullAccountExecution using (Run; run; then)
open import Conformance.FullAccountGrant P
open import Conformance.FullAccountGrantSecurity P
open import Conformance.FullAccountLayouts
import Conformance.FullAccountDeviceSecurityProof P as Device
import Conformance.FullAccountGrantSecurityProof P as Grant
import Conformance.FullAccountSignatureBindingProof P as Binding
open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_; take)
import Data.List.Relation.Unary.All as All
open import Data.Maybe.Base using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat.Base hiding (equal)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Passport.GrantEffects P
open import Relation.Binary.PropositionalEquality
private
  Stable : ∀ {A : Set} → M A → Set
  Stable m = ∀ {s v t} → Run m s v t → t ≡ s

  stable-bind : ∀ {A B : Set} {m : M A} {f : A → M B} → Stable m →
    (∀ x → Stable (f x)) → Stable (m >>= f)
  stable-bind {m = m} first rest r with then m r
  ... | x , _ , ran , tail = trans (rest x tail) (first ran)

  stable-if : ∀ {A : Set} b {m n : M A} → Stable m → Stable n → Stable (if b then m else n)
  stable-if true first second = first
  stable-if false first second = second

  stable-return : ∀ {A : Set} (x : A) → Stable (return x)
  stable-return x r = proj₂ (Device.return-run x r)

  stable-read : ∀ k → Stable (read k)
  stable-read k r = proj₂ (Device.read-run k r)

  stable-assert : ∀ b message → Stable (assert b message)
  stable-assert b message r = proj₂ (Device.assert-run b message r)

  stable-pure : ∀ {A : Set} {m : M A} → Binding.Pure m → Stable m
  stable-pure p (run _ executed) = Binding.pure-preserves p executed

  step : ∀ {A B R : Set} (m : M A) {f : A → M B} → Stable m → ∀ {s v t} →
    Run (m >>= f) s v t → (∀ x → Run m s x s → Run (f x) s v t → R) → R
  step m {f} stable r k with then m {f = f} r
  ... | x , _ , first , rest with stable first
  ... | refl = k x first rest

  step-assert : ∀ {B R : Set} b message {f : ⊤ → M B} {s v t} →
    Run (assert b message >>= f) s v t → (Run (f tt) s v t → R) → R
  step-assert b message r k = step (assert b message) (stable-assert b message) r λ _ _ tail → k tail

  previousCheck : List Value → Bool → M ⊤
  previousCheck xs present = if present then (do
    old ← lookup "grants" (IssueArguments.id xs)
    if flag (grantActive old) then (do
      epoch ← read "device_epoch"
      if equal (grantEpoch old) epoch then (do
        generation ← read "grant_generation"
        assert (not (equal (grantGeneration old) generation)) "grant already active")
        else return tt)
      else return tt) else return tt

  previous-stable : ∀ xs present → Stable (previousCheck xs present)
  previous-stable xs present = stable-if present
    (stable-bind (Device.lookup-run "grants" (IssueArguments.id xs)) λ old →
      stable-if (flag (grantActive old))
        (stable-bind (stable-read "device_epoch") λ epoch →
          stable-if (equal (grantEpoch old) epoch)
            (stable-bind (stable-read "grant_generation") λ generation →
              stable-assert (not (equal (grantGeneration old) generation)) "grant already active")
            (stable-return tt))
        (stable-return tt))
    (stable-return tt)

  issue-with : ∀ xs caller′ {s v t} → Run (Device.issueWith xs caller′) s v t → IssueResult xs s t
  issue-with xs caller′ {s} r =
    step (memberMap "grants" A.id) (Device.memberMap-run "grants" A.id) r λ present _ r₁ →
    step (previousCheck xs present) (previous-stable xs present) r₁ λ _ _ r₂ →
    step-assert (spend ∨ readFlag) "empty scope" r₂ λ r₃ →
    step-assert (spend ∨ not (Device.isSome′ caller′)) "read-only grant cannot restrict caller" r₃ λ r₄ →
    step-assert (not (flag A.withdrawShielded ∨ flag A.withdrawToContract) ∨ readFlag)
      "shielded spend requires read" r₄ λ r₅ →
    step-assert (number A.perCallCap ≤ᵇ number A.cap) "per-call cap above cap" r₅ λ r₆ →
    step-assert (not spend ∨ (0 <ᵇ number A.cap)) "spend without cap" r₆ λ r₇ →
    step-assert (not spend ∨ (number A.perCallCap ≤ᵇ number A.maxCoinValue)) "coin bound below per-call cap" r₇ λ r₈ →
    step-assert (not readFlag ∨ not (equal A.readKeyHash zero32)) "read without delegate key" r₈ λ r₉ →
    step-assert ((number A.windowLength ≡ᵇ 0) ∧ (number A.windowCap ≡ᵇ 0)) "window bounds reserved" r₉ λ r₁₀ →
    step-assert (spend ∨ (equal A.color zero32 ∧ (number A.recipientKind ≡ᵇ 0) ∧ equal A.recipient zero32 ∧
      (number A.maxCoinValue ≡ᵇ 0) ∧ (number A.perCallCap ≡ᵇ 0) ∧ (number A.cap ≡ᵇ 0)))
      "read-only grant carries object fields" r₁₀ λ r₁₁ →
    step (read "device_epoch") (stable-read "device_epoch") r₁₁ λ epoch epochRead r₁₂ →
    step (read "grant_generation") (stable-read "grant_generation") r₁₂ λ generation generationRead r₁₃ →
    step (read "auth_nonce") (stable-read "auth_nonce") r₁₃ λ issued issuedRead r₁₄ →
    step (spentCommit A.salt 0) (stable-pure (Device.spentCommit-pure A.salt 0)) r₁₄ λ spent spentRun r₁₅ →
    step (objectCommit A.salt A.color A.recipientKind A.recipient A.maxCoinValue)
      (stable-pure (Device.objectCommit-pure A.salt A.color A.recipientKind A.recipient A.maxCoinValue)) r₁₅
      λ object _ r₁₆ →
    step (rpCommit A.salt A.rpIdHash) (stable-pure (Device.rpCommit-pure A.salt A.rpIdHash)) r₁₆ λ rp _ r₁₇ →
    step (callerCommit A.salt caller′) (stable-pure (Device.callerCommit-pure A.salt caller′)) r₁₇ λ caller _ inserted →
    record
      { epoch = epoch ; generation = generation ; issued = issued ; spent = spent
      ; object = object ; rp = rp ; caller = caller
      ; epochRead = proj₁ (Device.read-run "device_epoch" epochRead)
      ; generationRead = proj₁ (Device.read-run "grant_generation" generationRead)
      ; issuedRead = proj₁ (Device.read-run "auth_nonce" issuedRead)
      ; zeroOpening = spentRun
      ; installed = trans (cong (cell "grants") (Device.insert-run "grants" A.id
          (issueRecord xs epoch generation issued spent object rp caller) inserted))
          (Device.cell-insert-same "grants" _ (ledger s)) }
    where
    module A = IssueArguments xs
    spend = flag A.withdrawUnshielded ∨ flag A.withdrawShielded ∨ flag A.withdrawToContract
    readFlag = flag A.readFlag

issue-result : ∀ xs {s v t} → Run (issue xs) s v t → IssueResult xs s t
issue-result xs r with get 16 xs
... | none = issue-with xs none r
... | some v = issue-with xs (some v) r
... | tuple (bool b ∷ v ∷ []) = issue-with xs (tuple (bool b ∷ v ∷ [])) r
... | nat n = issue-with xs (nat n) r
... | bool b = issue-with xs (bool b) r
... | bytes bs = issue-with xs (bytes bs) r
... | tuple [] = issue-with xs (tuple []) r
... | tuple (nat n ∷ vs) = issue-with xs (tuple (nat n ∷ vs)) r
... | tuple (bytes bs ∷ vs) = issue-with xs (tuple (bytes bs ∷ vs)) r
... | tuple (tuple vs ∷ ws) = issue-with xs (tuple (tuple vs ∷ ws)) r
... | tuple (none ∷ vs) = issue-with xs (tuple (none ∷ vs)) r
... | tuple (some v ∷ vs) = issue-with xs (tuple (some v ∷ vs)) r
... | tuple (bool b ∷ []) = issue-with xs (tuple (bool b ∷ [])) r
... | tuple (bool b ∷ v ∷ w ∷ vs) = issue-with xs (tuple (bool b ∷ v ∷ w ∷ vs)) r

lookup-found : ∀ label id {s v t} → Run (lookup label id) s v t →
  lookupMap id (fields (cell label s)) ≡ just v
lookup-found label id {s} (run _ executed) with lookupMap id (fields (cell label s))
... | nothing with executed
... | ()
lookup-found label id (run _ refl) | just _ = refl

private
  flag-true : ∀ v → flag v ≡ true → v ≡ bool true
  flag-true (bool true) _ = refl
  flag-true (bool false) ()
  flag-true (nat _) ()
  flag-true (bytes _) ()
  flag-true (tuple _) ()
  flag-true none ()
  flag-true (some _) ()

revoke-result : ∀ id {s v t} → Run (revoke id) s v t → RevokeResult id s t
revoke-result id {s} r =
  step (memberMap "grants" id) (Device.memberMap-run "grants" id) r λ present _ r₁ →
  step-assert present "unknown grant" r₁ λ r₂ →
  step (lookup "grants" id) (Device.lookup-run "grants" id) r₂ λ old found r₃ →
  step (assert (flag (grantActive old)) "grant not live")
    (stable-assert (flag (grantActive old)) "grant not live") r₃ λ _ active inserted → record
      { old = old ; recorded = lookup-found "grants" id found
      ; active = flag-true (grantActive old) (proj₁ (Device.assert-run (flag (grantActive old)) "grant not live" active))
      ; installed = trans (cong (cell "grants") (Device.insert-run "grants" id (revokedRecord old) inserted))
          (Device.cell-insert-same "grants" _ (ledger s)) }

cell-frame : ∀ k s t → lookupCell k (ledger t) ≡ lookupCell k (ledger s) → cell k t ≡ cell k s
cell-frame k s t frame = trans (view t) (trans (cong value frame) (sym (view s)))
  where
  value : Data.Maybe.Base.Maybe Value → Value
  value nothing = none
  value (just v) = v
  view : ∀ s → cell k s ≡ value (lookupCell k (ledger s))
  view s with lookupCell k (ledger s)
  ... | nothing = refl
  ... | just _ = refl

settled-map : ∀ {ga s id g spent t} (S : Settlement ga s id g spent t) →
  cell "grants" t ≡ tuple (insertMap id
    (settledGrant g (suc (number (grantNonce g))) (Settlement.commitment S)) (fields (cell "grants" s)))
settled-map {s = s} {id} {g} {t = t} S with Device.bump-run "round" 64 (Settlement.roundAdvanced S)
... | previous , _ , _ , stateEq =
  trans (cong (cell "grants") stateEq)
    (trans (cell-frame "grants" inserted advanced
      (Device.lookup-insert-other "grants" "round" (nat (suc (number previous))) (ledger inserted) refl))
      (Device.cell-insert-same "grants" _ (ledger s)))
  where
  inserted = grantsSettled s id (settledGrant g (suc (number (grantNonce g))) (Settlement.commitment S))
  advanced = state (insertCell "round" (nat (suc (number previous))) (ledger inserted))

private
  mutation-from : ∀ {c op ctx ga xs s t} (E : GrantCallEvidence c op ctx ga xs s) →
    lookupCell "grants" (ledger t) ≡ lookupCell "grants" (ledger (GrantCallEvidence.settled E)) →
    SpendMutation c op ctx ga xs s t
  mutation-from {t = t} E frame = record
    { evidence = E
    ; installed = trans (cell-frame "grants" (GrantCallEvidence.settled E) t frame)
        (settled-map (GrantCallEvidence.settlement E)) }

spend-mutation : ∀ c op ctx ga xs → Withdrawal op → ∀ {s v t} →
  Run (grantCall c op ctx ga xs) s v t → SpendMutation c op ctx ga xs s t
spend-mutation c op ctx ga xs withdrawal {s} {t = t} r
  with then (if shielded op then held ctx (get 1 xs) else return none) r
... | coin , _ , coinRun , r₁ with Grant.coin-run op ctx xs coinRun
... | refl , refl with then (authenticateGrant c ctx ga) r₁
... | (id , g) , _ , authenticated , r₂ with Grant.authenticate-run c ctx ga authenticated
... | refl , identified , recorded , live with then (scopeCheck op ctx ga xs (grantCoin op ctx) g) r₂
... | spent , _ , scopedRun , r₃ with Grant.scope-run op ctx ga xs (grantCoin op ctx) g scopedRun
... | refl , scoped with then (Grant.coinCheck op ga (grantCoin op ctx)) r₃
... | _ , _ , coinGuard , r₄ with Grant.coinCheck-run op ga (grantCoin op ctx) coinGuard
... | refl , coinAdmitted with then (challenge c true (operationName op) ctx (authorisation ga)
  (grantChallengeAtoms op xs (grantCoin op ctx) ga id g) (number (grantNonce g))) r₄
... | h , _ , challengeRun , r₅ with Grant.challenge-run c true (operationName op) ctx (authorisation ga)
  (grantChallengeAtoms op xs (grantCoin op ctx) ga id g) (number (grantNonce g)) challengeRun
... | challenged , refl with then (settle c ga id g h spent) r₅
... | _ , settled , settleRun , r₆ with Grant.settle-run c ga id g h spent settleRun
... | verified , settlement with then (body op ctx xs (grantCoin op ctx) none) r₆
... | result , afterBody , bodyRun , tailRun with withdrawal
... | unshieldedWithdrawal = mutation-from
  (grantCallEvidence id g h spent settled identified recorded live scoped coinAdmitted challenged verified
    settlement (result , afterBody , bodyRun))
  (trans (Grant.unshielded-tail result tailRun)
    (Device.body-frame "grants" withdrawUnshielded ctx xs (grantCoin withdrawUnshielded ctx) none
      (refl All.∷ All.[]) bodyRun))
... | shieldedWithdrawal = mutation-from
  (grantCallEvidence id g h spent settled identified recorded live scoped coinAdmitted challenged verified
    settlement (result , afterBody , bodyRun))
  (trans (Grant.change-tail (flag (at 0 result)) (changeEntry ga) result refl refl tailRun)
    (Device.body-frame "grants" withdrawShielded ctx xs (grantCoin withdrawShielded ctx) none All.[] bodyRun))
... | contractWithdrawal = mutation-from
  (grantCallEvidence id g h spent settled identified recorded live scoped coinAdmitted challenged verified
    settlement (result , afterBody , bodyRun))
  (trans (Grant.change-tail (flag (at 0 (at 1 result))) (changeEntry ga) result refl refl tailRun)
    (Device.body-frame "grants" withdrawToContract ctx xs (grantCoin withdrawToContract ctx) none All.[] bodyRun))

private
  body-kept : ∀ op → All.All (λ k → stringEqual "grants" k ≡ false) (DeviceSpec.bodyWrites op) →
    ∀ ctx xs coin entry {s v t} → Run (body op ctx xs coin entry) s v t → cell "grants" t ≡ cell "grants" s
  body-kept op outside ctx xs coin entry {s} {t = t} r =
    cell-frame "grants" s t (Device.body-frame "grants" op ctx xs coin entry outside r)

  clear-body : ∀ ctx xs coin entry {s v t} → Run (body revokeAllGrants ctx xs coin entry) s v t →
    cell "grants" t ≡ tuple []
  clear-body ctx xs coin entry r with then (bump "grant_generation" 32 >> clear "grants") r
  ... | _ , afterClear , first , returned with Device.return-run unit returned
  ... | refl , refl with then (bump "grant_generation" 32) first
  ... | _ , source , _ , clearedRun with Device.clear-run "grants" clearedRun
  ... | refl = Device.cell-insert-same "grants" (tuple []) (ledger source)

  issue-body : ∀ ctx xs coin entry {s v t} → Run (body issueGrant ctx xs coin entry) s v t → IssueResult xs s t
  issue-body ctx xs coin entry r with then (issue xs) r
  ... | _ , _ , first , returned with Device.return-run unit returned
  ... | refl , refl = issue-result xs first

  revoke-body : ∀ ctx xs coin entry {s v t} → Run (body revokeGrant ctx xs coin entry) s v t →
    RevokeResult (get 0 xs) s t
  revoke-body ctx xs coin entry r with then (revoke (get 0 xs)) r
  ... | _ , _ , first , returned with Device.return-run unit returned
  ... | refl , refl = revoke-result (get 0 xs) first

body-effect : ∀ op ctx xs coin entry {before source v after} →
  cell "grants" source ≡ cell "grants" before →
  Run (body op ctx xs coin entry) source v after → GrantEffect before after
body-effect withdrawUnshielded ctx xs coin entry frame r =
  kept (trans (body-kept withdrawUnshielded (refl All.∷ All.[]) ctx xs coin entry r) frame)
body-effect withdrawShielded ctx xs coin entry frame r =
  kept (trans (body-kept withdrawShielded All.[] ctx xs coin entry r) frame)
body-effect withdrawToContract ctx xs coin entry frame r =
  kept (trans (body-kept withdrawToContract All.[] ctx xs coin entry r) frame)
body-effect appendInbox ctx xs coin entry frame r =
  kept (trans (body-kept appendInbox (refl All.∷ refl All.∷ All.[]) ctx xs coin entry r) frame)
body-effect rotateEncKey ctx xs coin entry frame r =
  kept (trans (body-kept rotateEncKey (refl All.∷ All.[]) ctx xs coin entry r) frame)
body-effect addDevice ctx xs coin entry frame r =
  kept (trans (body-kept addDevice (refl All.∷ refl All.∷ All.[]) ctx xs coin entry r) frame)
body-effect removeDevice ctx xs coin entry frame r =
  kept (trans (body-kept removeDevice (refl All.∷ refl All.∷ All.[]) ctx xs coin entry r) frame)
body-effect issueGrant ctx xs coin entry {source = source} frame r =
  grantIssued xs source frame (issue-body ctx xs coin entry r)
body-effect revokeGrant ctx xs coin entry {source = source} frame r =
  grantRevoked (get 0 xs) source frame (revoke-body ctx xs coin entry r)
body-effect revokeAllGrants ctx xs coin entry frame r = cleared (clear-body ctx xs coin entry r)
body-effect publishRecovery ctx xs coin entry frame r = kept (trans
  (body-kept publishRecovery (refl All.∷ refl All.∷ refl All.∷ refl All.∷ refl All.∷ refl All.∷ All.[])
    ctx xs coin entry r) frame)
body-effect cancelRecovery ctx xs coin entry frame r = kept (trans
  (body-kept cancelRecovery (refl All.∷ refl All.∷ refl All.∷ refl All.∷ All.[]) ctx xs coin entry r) frame)

device-effect : ∀ c op ctx xs {s v t} →
  Run (Model.AccountSemantics.deviceCall P c op ctx xs) s v t → GrantEffect s t
device-effect c op ctx xs {s} r = body-effect op ctx
  (DeviceSpec.deviceArguments op xs)
  (DeviceSpec.deviceCoin op ctx) (DeviceCall.callerEntry D)
  (cell-frame "grants" s (DeviceCall.authorisedState D)
    (Authorisation.unchanged (DeviceCall.authorised D) "grants" refl refl refl)) (DeviceCall.bodyRun D)
  where D = Device.device-call-evidence c op ctx xs r

private
  credit-frame : ∀ color amount → DeviceSpec.Preserves "grants" (credit color amount)
  credit-frame color amount =
    Device.preserves-bind (Device.memberMap-preserves "unshielded_balances" color) λ present →
    Device.if-preserves present
      (Device.preserves-bind (Device.lookup-preserves "unshielded_balances" color) λ old →
       Device.preserves-bind (Device.cast-preserves "unshielded_balances" 128 (number old + amount)) λ n →
       Device.insert-preserves "unshielded_balances" color (nat n) refl)
      (Device.insert-preserves "unshielded_balances" color (nat amount) refl)

  receive-frame : ∀ ctx coin → DeviceSpec.Preserves "grants" (receiveCoin ctx coin)
  receive-frame ctx coin =
    Device.preserves-bind (Device.readSelf-preserves ctx) λ address →
    Device.preserves-bind (Device.createCoin-preserves coin (tuple (bool false ∷ address ∷ []))) λ _ →
    Device.emit-preserves (receiveShielded coin)

  public-frame : ∀ ctx xs → DeviceSpec.Preserves "grants"
    (Model.AccountSemantics.execute P Model.AccountSemantics.depositPublic ctx xs)
  public-frame ctx xs =
    Device.preserves-bind (Device.emit-preserves (receiveUnshielded (get 0 xs) (number (get 1 xs)))) λ _ →
    Device.preserves-bind (credit-frame (get 0 xs) (number (get 1 xs))) λ _ →
    Device.preserves-bind (Device.bump-preserves "round" 64 refl) λ _ → Device.return-preserves unit

  private-frame : ∀ ctx xs → DeviceSpec.Preserves "grants"
    (Model.AccountSemantics.execute P Model.AccountSemantics.depositPrivate ctx xs)
  private-frame ctx xs =
    Device.preserves-bind (receive-frame ctx (get 0 xs)) λ _ →
    Device.preserves-bind (Device.inboxAppend-preserves (get 1 xs) refl refl) λ _ →
    Device.preserves-bind (Device.bump-preserves "round" 64 refl) λ _ → Device.return-preserves unit

  time-less-frame : ∀ ctx n → DeviceSpec.Preserves "grants" (readTimeLess ctx n)
  time-less-frame ctx n = Device.preserves-bind (Device.emit-preserves (contextRead "blockTimeLessThan" (nat n))) λ _ →
    Device.return-preserves (blockTime ctx <ᵇ n)

  time-greater-frame : ∀ ctx n → DeviceSpec.Preserves "grants" (readTimeGreater ctx n)
  time-greater-frame ctx n = Device.preserves-bind (Device.emit-preserves (contextRead "blockTimeGreaterThan" (nat n))) λ _ →
    Device.return-preserves (n <ᵇ blockTime ctx)

  submit-frame : ∀ ctx xs → DeviceSpec.Preserves "grants" (submit ctx xs)
  submit-frame ctx xs =
    Device.preserves-bind (Device.read-preserves "pending_recovery") λ pending →
    Device.preserves-bind (Device.assert-preserves (not (flag pending)) "recovery already pending") λ _ →
    Device.preserves-bind (Device.readCount-preserves "device_epoch") λ epoch →
    Device.preserves-bind (Device.assert-preserves (number A.epoch ≡ᵇ epoch) "stale epoch") λ _ →
    Device.preserves-bind (Device.readCount-preserves "auth_nonce") λ nonce →
    Device.preserves-bind (Device.assert-preserves (number A.authNonce ≡ᵇ nonce) "stale authorisation nonce") λ _ →
    Device.preserves-bind (Device.read-preserves "recovery_pk") λ pk →
    Device.preserves-bind (Device.pure-preserves (Device.requireRecoveryKey-pure pk)) λ _ →
    Device.preserves-bind (Device.pure-preserves (Device.requireRecoveryKey-pure A.successorKey)) λ _ →
    Device.preserves-bind (Device.pure-preserves (Device.requireRecoveryKey-pure A.nextRecoveryKey)) λ _ →
    Device.preserves-bind (Device.read-preserves "recovery_pk") λ currentPk →
    Device.preserves-bind (Device.assert-preserves (not (equal A.nextRecoveryKey currentPk)) "recovery commitment reused") λ _ →
    Device.preserves-bind (Device.readCount-preserves "device_epoch") λ currentEpoch →
    Device.preserves-bind (Device.cast-preserves "device_epoch" 32 (suc currentEpoch)) λ postEpoch →
    Device.preserves-bind (Device.readSelf-preserves ctx) λ addr →
    Device.preserves-bind (Device.read-preserves "recovery_pk") λ signingPk →
    Device.preserves-bind (Device.readCount-preserves "auth_nonce") λ signingNonce →
    Device.preserves-bind (Device.pure-preserves (Binding.hashTag-pure "midnight:account:recovery:submit:v1")) λ dst →
    Device.preserves-bind (Device.pure-preserves (Binding.hash-pure
      (b32 dst ∷ contract addr ∷ jub signingPk ∷ jub A.recoveryR ∷ jub A.successorKey ∷ jub A.successorR ∷
       jub A.nextRecoveryKey ∷ u32 (nat postEpoch) ∷ u64 (nat signingNonce) ∷ u64 A.nowBound ∷ u64 A.grindNonce ∷ []))) λ h →
    Device.preserves-bind (Device.read-preserves "recovery_pk") λ verifyingPk →
    Device.preserves-bind (Device.unchanged-preserves λ r →
      Binding.schnorr-preserves verifyingPk A.recoveryR A.recoveryS h "invalid recovery signature" (Run.execution r)) λ _ →
    Device.preserves-bind (Device.unchanged-preserves λ r →
      Binding.schnorr-preserves A.successorKey A.successorR A.successorS h "invalid successor co-signature" (Run.execution r)) λ _ →
    Device.preserves-bind (time-greater-frame ctx (number A.nowBound)) λ past →
    Device.preserves-bind (Device.assert-preserves (not past) "now bound is in the past") λ _ →
    Device.preserves-bind (Device.write-preserves "pending_recovery" (bool true) refl) λ _ →
    Device.preserves-bind
      (Device.preserves-bind (Device.readSelf-preserves ctx) λ addr →
        Device.pure-preserves (Device.entryAt-pure jubjub addr
          (auth A.successorKey 0 none none 0 0 none none none) postEpoch 0)) λ successor →
    Device.preserves-bind (Device.write-preserves "pending_entry" successor refl) λ _ →
    Device.preserves-bind (Device.write-preserves "pending_recovery_pk" A.nextRecoveryKey refl) λ _ →
    Device.preserves-bind (Device.readCount-preserves "veto_window") λ window →
    Device.preserves-bind (Device.writeCount-preserves "pending_not_before" 64 (number A.nowBound + window) refl) λ _ →
    Device.preserves-bind (Device.bump-preserves "round" 64 refl) λ _ →
    Device.return-preserves unit
    where module A = SubmitArguments xs

  finalise-frame : ∀ ctx → DeviceSpec.Preserves "grants" (finalise ctx)
  finalise-frame ctx =
    Device.preserves-bind (Device.read-preserves "pending_recovery") λ pending →
    Device.preserves-bind (Device.assert-preserves (flag pending) "no recovery pending") λ _ →
    Device.preserves-bind (Device.readCount-preserves "pending_not_before") λ deadline →
    Device.preserves-bind (time-less-frame ctx deadline) λ early →
    Device.preserves-bind (Device.assert-preserves (not early) "veto window still open") λ _ →
    Device.preserves-bind (Device.read-preserves "pending_recovery_pk") λ pk →
    Device.preserves-bind (Device.pure-preserves (Device.requireRecoveryKey-pure pk)) λ _ →
    Device.preserves-bind (Device.bump-preserves "device_epoch" 32 refl) λ _ →
    Device.preserves-bind (Device.clear-preserves "devices" refl) λ _ →
    Device.preserves-bind (Device.read-preserves "pending_entry") λ successor →
    Device.preserves-bind (Device.include-preserves "devices" successor refl) λ _ →
    Device.preserves-bind (Device.write-preserves "device_count" (nat 1) refl) λ _ →
    Device.preserves-bind (Device.read-preserves "pending_recovery_pk") λ installingPk →
    Device.preserves-bind (Device.write-preserves "recovery_pk" installingPk refl) λ _ →
    Device.preserves-bind (Device.write-preserves "recovery_phi_len" (nat 0) refl) λ _ →
    Device.preserves-bind (Device.write-preserves "pending_recovery" (bool false) refl) λ _ →
    Device.preserves-bind (Device.write-preserves "pending_entry" zero32 refl) λ _ →
    Device.preserves-bind (Device.read-preserves "pending_recovery_pk") λ clearingPk →
    Device.preserves-bind (Device.lift-preserves (ecMul P jubjub clearingPk 0)) λ o →
    Device.preserves-bind (Device.write-preserves "pending_recovery_pk" o refl) λ _ →
    Device.preserves-bind (Device.write-preserves "pending_not_before" (nat 0) refl) λ _ →
    Device.preserves-bind (Device.bump-preserves "auth_nonce" 64 refl) λ _ →
    Device.preserves-bind (Device.bump-preserves "round" 64 refl) λ _ →
    Device.return-preserves unit

execute-effect : ∀ {e} → RuntimeEntrypoint e → ∀ ctx xs {s v t} →
  Run (Model.AccountSemantics.execute P e ctx xs) s v t → GrantEffect s t
execute-effect (activationEntry c) ctx xs {s} {t = t} r = kept
  (cell-frame "grants" s t (Activation.unchanged
    (Device.activation-evidence c ctx (Model.AccountSemantics.parseActivation P c xs) (get 1 xs) r)
    "grants" refl refl refl refl refl))
execute-effect (deviceEntry c op) ctx xs r = device-effect c op ctx xs r
execute-effect (grantEntry c withdrawUnshielded w) ctx xs r = grantSpent c withdrawUnshielded ctx
  (Model.AccountSemantics.parseGrant P c (Data.List.Base.drop 3 xs) none none) (take 3 xs) w
  (spend-mutation c withdrawUnshielded ctx
    (Model.AccountSemantics.parseGrant P c (Data.List.Base.drop 3 xs) none none) (take 3 xs) w r)
execute-effect (grantEntry c withdrawShielded w) ctx xs r = grantSpent c withdrawShielded ctx
  (Model.AccountSemantics.parseGrant P c (Data.List.Base.drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) w
  (spend-mutation c withdrawShielded ctx
    (Model.AccountSemantics.parseGrant P c (Data.List.Base.drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) w r)
execute-effect (grantEntry c withdrawToContract w) ctx xs r = grantSpent c withdrawToContract ctx
  (Model.AccountSemantics.parseGrant P c (Data.List.Base.drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) w
  (spend-mutation c withdrawToContract ctx
    (Model.AccountSemantics.parseGrant P c (Data.List.Base.drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) w r)
execute-effect (grantEntry c appendInbox ()) ctx xs r
execute-effect (grantEntry c rotateEncKey ()) ctx xs r
execute-effect (grantEntry c addDevice ()) ctx xs r
execute-effect (grantEntry c removeDevice ()) ctx xs r
execute-effect (grantEntry c issueGrant ()) ctx xs r
execute-effect (grantEntry c revokeGrant ()) ctx xs r
execute-effect (grantEntry c revokeAllGrants ()) ctx xs r
execute-effect (grantEntry c publishRecovery ()) ctx xs r
execute-effect (grantEntry c cancelRecovery ()) ctx xs r
execute-effect publicDepositEntry ctx xs {s} {t = t} r = kept (cell-frame "grants" s t (public-frame ctx xs r))
execute-effect privateDepositEntry ctx xs {s} {t = t} r = kept (cell-frame "grants" s t (private-frame ctx xs r))
execute-effect submissionEntry ctx xs {s} {t = t} r = kept (cell-frame "grants" s t (submit-frame ctx xs r))
execute-effect finalisationEntry ctx xs {s} {t = t} r = kept (cell-frame "grants" s t (finalise-frame ctx r))

issue-body-result : ∀ ctx xs coin entry {s v t} →
  Run (body issueGrant ctx xs coin entry) s v t → IssueResult xs s t
issue-body-result = issue-body

revoke-body-result : ∀ ctx xs coin entry {s v t} →
  Run (body revokeGrant ctx xs coin entry) s v t → RevokeResult (get 0 xs) s t
revoke-body-result = revoke-body

clear-body-result : ∀ ctx xs coin entry {s v t} →
  Run (body revokeAllGrants ctx xs coin entry) s v t → cell "grants" t ≡ tuple []
clear-body-result = clear-body

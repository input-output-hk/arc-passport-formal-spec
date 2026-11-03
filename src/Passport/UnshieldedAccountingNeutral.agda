{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

-- Purpose-specific certificates for source computations which neither touch the
-- unshielded balance map nor declare an unshielded transfer. Both facts inspect
-- the actual state-and-journal evaluator, including its successful tails.
module Passport.UnshieldedAccountingNeutral (P : Primitives) where

open import Passport.UnshieldedAccounting
open import Conformance.FullAccountBody P
open import Conformance.FullAccountCrypto P
open import Conformance.FullAccountGrant P
open import Conformance.FullAccountLayouts
import Conformance.FullAccountDeviceSecurityProof P as Device
import Conformance.FullAccountSignatureBindingProof P as Binding
open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; take; drop)
open import Data.List.Properties using (++-identityʳ)
open import Data.Maybe.Base using (nothing; just)
open import Data.Nat.Base hiding (equal)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality hiding (inspect)

record Quiet {A : Set} (m : M A) : Set where
  field inspect : ∀ {s x t es} → m s ≡ accepted x t es → balanceMap t ≡ balanceMap s × transfers es ≡ []
open Quiet public

transfers-++ : ∀ es fs → transfers (es ++ fs) ≡ transfers es ++ transfers fs
transfers-++ [] fs = refl
transfers-++ (receiveUnshielded c a ∷ es) fs = cong (received c a ∷_) (transfers-++ es fs)
transfers-++ (sendUnshielded c a r ∷ es) fs = cong (sent c a ∷_) (transfers-++ es fs)
transfers-++ (readCell k v ∷ es) fs = transfers-++ es fs
transfers-++ (writeCell k v ∷ es) fs = transfers-++ es fs
transfers-++ (mapMember k v b ∷ es) fs = transfers-++ es fs
transfers-++ (mapLookup k v w ∷ es) fs = transfers-++ es fs
transfers-++ (mapInsert k v w ∷ es) fs = transfers-++ es fs
transfers-++ (setMember k v b ∷ es) fs = transfers-++ es fs
transfers-++ (setInsert k v ∷ es) fs = transfers-++ es fs
transfers-++ (setRemove k v ∷ es) fs = transfers-++ es fs
transfers-++ (reset k ∷ es) fs = transfers-++ es fs
transfers-++ (contextRead k v ∷ es) fs = transfers-++ es fs
transfers-++ (witness k v w ∷ es) fs = transfers-++ es fs
transfers-++ (receiveShielded c ∷ es) fs = transfers-++ es fs
transfers-++ (consumeShielded c r ∷ es) fs = transfers-++ es fs
transfers-++ (createShielded c r cm ∷ es) fs = transfers-++ es fs

rejected≢accepted : ∀ {A : Set} {error x t es} → rejected {A} error ≡ accepted x t es → ⊥
rejected≢accepted ()

bind : ∀ {A B : Set} {m : M A} {f : A → M B} → Quiet m → (∀ x → Quiet (f x)) → Quiet (m >>= f)
inspect (bind {m = m} {f} first rest) {s} execution with m s in prefix
... | rejected _ = ⊥-elim (rejected≢accepted execution)
inspect (bind {m = m} {f} first rest) {s} execution | accepted x t es with f x t in suffix
... | rejected _ = ⊥-elim (rejected≢accepted execution)
... | accepted y u fs with execution
...   | refl = trans (proj₁ (inspect (rest x) suffix)) (proj₁ (inspect first prefix)) ,
  trans (transfers-++ es fs) (cong₂ _++_ (proj₂ (inspect first prefix)) (proj₂ (inspect (rest x) suffix)))

branch : ∀ {A : Set} b {m n : M A} → Quiet m → Quiet n → Quiet (if b then m else n)
branch true yes no = yes
branch false yes no = no

pure : ∀ {A : Set} {m : M A} → Binding.Pure m → Quiet m
inspect (pure (Binding.pure (failure _) runs)) {s} execution with trans (sym (runs s)) execution
... | ()
inspect (pure (Binding.pure (success _) runs)) {s} execution with trans (sym (runs s)) execution
... | refl = refl , refl

ret : ∀ {A : Set} (x : A) → Quiet (return x)
inspect (ret x) refl = refl , refl

lifted : ∀ {A : Set} r → Quiet {A} (lift r)
lifted r = pure (Binding.lift-pure r)

guard : ∀ b message → Quiet (assert b message)
guard b message = pure (Binding.assert-pure b message)

bounded : ∀ label bits n → Quiet (cast label bits n)
inspect (bounded label bits n) execution with n <ᵇ 2 ^ bits
inspect (bounded label bits n) refl | true = refl , refl
inspect (bounded label bits n) () | false

observed : ∀ k → Quiet (read k)
inspect (observed k) {s} execution with lookupCell k (ledger s)
inspect (observed k) () | nothing
inspect (observed k) refl | just _ = refl , refl

counted : ∀ k → Quiet (readCount k)
counted k = bind (observed k) λ v → ret (number v)

membered : ∀ label k → Quiet (memberMap label k)
inspect (membered label k) refl = refl , refl

looked : ∀ label k → Quiet (lookup label k)
inspect (looked label k) {s} execution with lookupMap k (fields (cell label s))
inspect (looked label k) () | nothing
inspect (looked label k) refl | just _ = refl , refl

setMembered : ∀ label k → Quiet (has label k)
inspect (setMembered label k) refl = refl , refl

cell-other : ∀ label v s → stringEqual "unshielded_balances" label ≡ false →
  balanceMap (state (insertCell label v (ledger s))) ≡ balanceMap s
cell-other label v s different with lookupCell "unshielded_balances" (ledger s) in found
... | nothing rewrite Device.lookup-insert-other "unshielded_balances" label v (ledger s) different | found = refl
... | just w rewrite Device.lookup-insert-other "unshielded_balances" label v (ledger s) different | found = refl

written : ∀ label v → stringEqual "unshielded_balances" label ≡ false → Quiet (write label v)
inspect (written label v different) {s} refl = cell-other label v s different , refl

inserted : ∀ label k v → stringEqual "unshielded_balances" label ≡ false → Quiet (insert label k v)
inspect (inserted label k v different) {s} refl = cell-other label _ s different , refl

included : ∀ label k → stringEqual "unshielded_balances" label ≡ false → Quiet (include label k)
inspect (included label k different) {s} refl = cell-other label _ s different , refl

excluded : ∀ label k → stringEqual "unshielded_balances" label ≡ false → Quiet (exclude label k)
inspect (excluded label k different) {s} refl = cell-other label _ s different , refl

cleared : ∀ label → stringEqual "unshielded_balances" label ≡ false → Quiet (clear label)
inspect (cleared label different) {s} refl = cell-other label _ s different , refl

write-count : ∀ label bits n → stringEqual "unshielded_balances" label ≡ false → Quiet (writeCount label bits n)
write-count label bits n different = bind (bounded label bits n) λ v → written label (nat v) different

bumped : ∀ label bits → stringEqual "unshielded_balances" label ≡ false → Quiet (bump label bits)
bumped label bits different = bind (counted label) λ n → write-count label bits (suc n) different

emitted : ∀ e → transfers (e ∷ []) ≡ [] → Quiet (emit e)
inspect (emitted e noTransfer) refl = refl , noTransfer

self-read : ∀ ctx → Quiet (readSelf ctx)
inspect (self-read ctx) refl = refl , refl

caller-read : ∀ ctx → Quiet (readCaller ctx)
inspect (caller-read ctx) refl = refl , refl

held-read : ∀ ctx color → Quiet (held ctx color)
inspect (held-read ctx color) refl = refl , refl

less-read : ∀ ctx deadline → Quiet (readTimeLess ctx deadline)
inspect (less-read ctx deadline) refl = refl , refl

greater-read : ∀ ctx deadline → Quiet (readTimeGreater ctx deadline)
inspect (greater-read ctx deadline) refl = refl , refl

inbox : ∀ entry → Quiet (inboxAppend entry)
inbox entry = bind (counted "inbox_count") λ count →
  bind (inserted "inbox" (nat count) entry refl) λ _ → bumped "inbox_count" 64 refl

entry-quiet : ∀ c ctx a epoch count → Quiet (entry c ctx a epoch count)
entry-quiet c ctx a epoch count = bind (self-read ctx) λ addr → pure (Device.entryAt-pure c addr a epoch count)

challenge-quiet : ∀ c grant operation ctx a args nonce → Quiet (challenge c grant operation ctx a args nonce)
challenge-quiet c grant operation ctx a args nonce = bind (self-read ctx) λ addr →
  pure (Binding.challengeAt-pure c grant operation addr a args nonce)

roll-quiet : ∀ c ctx a old → Quiet (roll c ctx a old)
roll-quiet c ctx a old = bind (excluded "devices" old refl) λ _ →
  bind (self-read ctx) λ addr →
  bind (counted "device_epoch") λ epoch →
  bind (bounded "use_counter" 64 (suc (counter a))) λ count →
  bind (pure (Device.entryAt-pure c addr a epoch count)) λ next →
  bind (included "devices" next refl) λ _ → ret next

ordered-program : Curve → Context → Auth → Value → Value → M Value
ordered-program p256 ctx a h old = verify p256 a h "invalid WebAuthn signature" >> roll p256 ctx a old
ordered-program c ctx a h old = roll c ctx a old >>= λ next → verify c a h "invalid signature" >> return next

ordered-quiet : ∀ c ctx a h old → Quiet (ordered-program c ctx a h old)
ordered-quiet p256 ctx a h old = bind (pure (Binding.verify-pure p256 a h "invalid WebAuthn signature")) λ _ →
  roll-quiet p256 ctx a old
ordered-quiet jubjub ctx a h old = bind (roll-quiet jubjub ctx a old) λ next →
  bind (pure (Binding.verify-pure jubjub a h "invalid signature")) λ _ → ret next
ordered-quiet k256 ctx a h old = bind (roll-quiet k256 ctx a old) λ next →
  bind (pure (Binding.verify-pure k256 a h "invalid signature")) λ _ → ret next

authorise-program : Curve → Context → Auth → Value → M Value
authorise-program c ctx a h = do
  keyGuard c (key a) "device key has small order"
  addr ← readSelf ctx
  epoch ← readCount "device_epoch"
  old ← entryAt c addr a epoch (counter a)
  known ← has "devices" old
  assert known "unknown device entry"
  next ← ordered-program c ctx a h old
  bump "auth_nonce" 64
  bump "round" 64
  return next

authorise-program-equal : ∀ c ctx a h → authorise-program c ctx a h ≡ authorise c ctx a h
authorise-program-equal jubjub ctx a h = refl
authorise-program-equal k256 ctx a h = refl
authorise-program-equal p256 ctx a h = refl

authorise-program-quiet : ∀ c ctx a h → Quiet (authorise-program c ctx a h)
authorise-program-quiet c ctx a h = bind (pure (Device.keyGuard-pure c (key a) "device key has small order")) λ _ →
  bind (self-read ctx) λ addr →
  bind (counted "device_epoch") λ epoch →
  bind (pure (Device.entryAt-pure c addr a epoch (counter a))) λ old →
  bind (setMembered "devices" old) λ known →
  bind (guard known "unknown device entry") λ _ →
  bind (ordered-quiet c ctx a h old) λ next →
  bind (bumped "auth_nonce" 64 refl) λ _ →
  bind (bumped "round" 64 refl) λ _ → ret next

authorise-quiet : ∀ c ctx a h → Quiet (authorise c ctx a h)
authorise-quiet c ctx a h = subst Quiet (authorise-program-equal c ctx a h) (authorise-program-quiet c ctx a h)

nonce-quiet : ∀ change nonce → Quiet (evolveNonce change nonce)
nonce-quiet change nonce = bind (lifted (degradeToTransient P nonce)) λ degraded →
  bind (lifted (transientHash P _)) λ evolved → lifted (upgradeFromTransient P evolved)

create-quiet : ∀ coin recipient → Quiet (createCoin coin recipient)
create-quiet coin recipient = bind (lifted (coinCommitment P coin recipient)) λ cm →
  emitted (createShielded coin recipient cm) refl

receive-quiet : ∀ ctx coin → Quiet (receiveCoin ctx coin)
receive-quiet ctx coin = bind (self-read ctx) λ addr →
  bind (create-quiet coin (tuple (bool false ∷ addr ∷ []))) λ _ → emitted (receiveShielded coin) refl

send-quiet : ∀ ctx isUser recipient amount coin → Quiet (sendCoin ctx isUser recipient amount coin)
send-quiet ctx isUser recipient amount coin = bind (self-read ctx) λ addr →
  bind (lifted (coinNullifier P (coinInfo coin) addr)) λ nf →
  bind (emitted (consumeShielded coin nf) refl) λ _ →
  bind (guard (amount ≤ᵇ number (at 2 coin)) "result of subtraction would be negative") λ _ →
  bind (nonce-quiet false (at 0 coin)) λ nonce →
  let sent = tuple (nonce ∷ at 1 coin ∷ nat amount ∷ []) in
  bind (create-quiet sent (tuple (bool isUser ∷ recipient ∷ []))) λ _ →
  bind (branch (not isUser ∧ equal recipient addr) (emitted (receiveShielded sent) refl) (ret tt)) λ _ →
  branch ((number (at 2 coin) ∸ amount) ≡ᵇ 0)
    (ret (sent , tuple (bool false ∷ tuple (zero32 ∷ zero32 ∷ nat 0 ∷ []) ∷ [])))
    (bind (nonce-quiet true (at 0 coin)) λ nonce′ →
      let changeCoin = tuple (nonce′ ∷ at 1 coin ∷ nat (number (at 2 coin) ∸ amount) ∷ []) in
      bind (create-quiet changeCoin (tuple (bool false ∷ addr ∷ []))) λ _ →
      bind (emitted (receiveShielded changeCoin) refl) λ _ → ret (sent , tuple (bool true ∷ changeCoin ∷ [])))

revoke-quiet : ∀ id → Quiet (revoke id)
revoke-quiet id = bind (membered "grants" id) λ present →
  bind (guard present "unknown grant") λ _ →
  bind (looked "grants" id) λ old →
  bind (guard (flag (grantActive old)) "grant not live") λ _ →
  inserted "grants" id (tuple (take 7 (fields old) ++ (bool false ∷ grantScope old ∷ []))) refl

cancel-quiet : Quiet cancel
cancel-quiet = bind (observed "pending_recovery") λ pending →
  bind (guard (flag pending) "no recovery pending") λ _ →
  bind (written "pending_recovery" (bool false) refl) λ _ →
  bind (written "pending_entry" zero32 refl) λ _ →
  bind (observed "pending_recovery_pk") λ pk →
  bind (lifted (ecMul P jubjub pk 0)) λ o →
  bind (written "pending_recovery_pk" o refl) λ _ → written "pending_not_before" (nat 0) refl

publish-quiet : ∀ xs → Quiet (publish xs)
publish-quiet xs = bind (observed "pending_recovery") λ pending →
  bind (guard (not (flag pending)) "recovery pending; cancel first") λ _ →
  bind (guard (1 ≤ᵇ number (x 6)) "phi must not be empty") λ _ →
  bind (guard (number (x 6) ≤ᵇ 4) "phi length out of range") λ _ →
  bind (branch (number (x 6) <ᵇ 2) (guard (number (x 3) ≡ᵇ 0) "unused phi slot 2 not zero") (ret tt)) λ _ →
  bind (branch (number (x 6) <ᵇ 3) (guard (number (x 4) ≡ᵇ 0) "unused phi slot 3 not zero") (ret tt)) λ _ →
  bind (branch (number (x 6) <ᵇ 4) (guard (number (x 5) ≡ᵇ 0) "unused phi slot 4 not zero") (ret tt)) λ _ →
  bind (guard (not (equal (x 1) zero32)) "session nonce is zero") λ _ →
  bind (observed "recovery_session") λ session →
  bind (guard (not (equal (x 1) session)) "session nonce reused") λ _ →
  bind (observed "recovery_pk") λ pk →
  bind (guard (not (equal (x 0) pk)) "recovery commitment reused") λ _ →
  bind (pure (Device.requireRecoveryKey-pure (x 0))) λ _ →
  bind (written "recovery_pk" (x 0) refl) λ _ →
  bind (written "recovery_session" (x 1) refl) λ _ →
  bind (inserted "recovery_phi" (nat 1) (x 2) refl) λ _ →
  bind (inserted "recovery_phi" (nat 2) (x 3) refl) λ _ →
  bind (inserted "recovery_phi" (nat 3) (x 4) refl) λ _ →
  bind (inserted "recovery_phi" (nat 4) (x 5) refl) λ _ →
  bind (written "recovery_phi_len" (x 6) refl) λ _ →
  bind (written "recovery_wrap" (x 7) refl) λ _ → written "recovery_version" (nat 1) refl
  where x = λ n → get n xs

issueWith-quiet : ∀ xs caller′ → Quiet (Device.issueWith xs caller′)
issueWith-quiet xs caller′ = bind (membered "grants" A.id) λ present →
  bind (branch present
    (bind (looked "grants" A.id) λ old →
      branch (flag (grantActive old))
        (bind (observed "device_epoch") λ epoch →
          branch (equal (grantEpoch old) epoch)
            (bind (observed "grant_generation") λ generation →
              guard (not (equal (grantGeneration old) generation)) "grant already active")
            (ret tt))
        (ret tt))
    (ret tt)) λ _ →
  bind (guard (spend ∨ readFlag) "empty scope") λ _ →
  bind (guard (spend ∨ not (Device.isSome′ caller′)) "read-only grant cannot restrict caller") λ _ →
  bind (guard (not (flag A.withdrawShielded ∨ flag A.withdrawToContract) ∨ readFlag) "shielded spend requires read") λ _ →
  bind (guard (number A.perCallCap ≤ᵇ number A.cap) "per-call cap above cap") λ _ →
  bind (guard (not spend ∨ (0 <ᵇ number A.cap)) "spend without cap") λ _ →
  bind (guard (not spend ∨ (number A.perCallCap ≤ᵇ number A.maxCoinValue)) "coin bound below per-call cap") λ _ →
  bind (guard (not readFlag ∨ not (equal A.readKeyHash zero32)) "read without delegate key") λ _ →
  bind (guard ((number A.windowLength ≡ᵇ 0) ∧ (number A.windowCap ≡ᵇ 0)) "window bounds reserved") λ _ →
  bind (guard (spend ∨ (equal A.color zero32 ∧ (number A.recipientKind ≡ᵇ 0) ∧ equal A.recipient zero32 ∧
    (number A.maxCoinValue ≡ᵇ 0) ∧ (number A.perCallCap ≡ᵇ 0) ∧ (number A.cap ≡ᵇ 0))) "read-only grant carries object fields") λ _ →
  bind (observed "device_epoch") λ epoch →
  bind (observed "grant_generation") λ generation →
  bind (observed "auth_nonce") λ issued →
  bind (pure (Device.spentCommit-pure A.salt 0)) λ spent →
  bind (pure (Device.objectCommit-pure A.salt A.color A.recipientKind A.recipient A.maxCoinValue)) λ object →
  bind (pure (Device.rpCommit-pure A.salt A.rpIdHash)) λ rp →
  bind (pure (Device.callerCommit-pure A.salt caller′)) λ caller →
  inserted "grants" A.id (tuple (epoch ∷ generation ∷ issued ∷ nat 0 ∷ spent ∷ nat 0 ∷ nat 0 ∷ bool true ∷
    tuple (A.withdrawUnshielded ∷ A.withdrawShielded ∷ A.withdrawToContract ∷ A.readFlag ∷ object ∷
      A.perCallCap ∷ A.cap ∷ A.expiresAt ∷ rp ∷ A.readKeyHash ∷ nat 0 ∷ nat 0 ∷ caller ∷ []) ∷ [])) refl
  where
  module A = IssueArguments xs
  spend = flag A.withdrawUnshielded ∨ flag A.withdrawShielded ∨ flag A.withdrawToContract
  readFlag = flag A.readFlag

issue-quiet : ∀ xs → Quiet (issue xs)
issue-quiet xs with get 16 xs
... | none = issueWith-quiet xs none
... | some v = issueWith-quiet xs (some v)
... | tuple (bool b ∷ v ∷ []) = issueWith-quiet xs (tuple (bool b ∷ v ∷ []))
... | nat n = issueWith-quiet xs (nat n)
... | bool b = issueWith-quiet xs (bool b)
... | bytes bs = issueWith-quiet xs (bytes bs)
... | tuple [] = issueWith-quiet xs (tuple [])
... | tuple (nat n ∷ vs) = issueWith-quiet xs (tuple (nat n ∷ vs))
... | tuple (bool b ∷ []) = issueWith-quiet xs (tuple (bool b ∷ []))
... | tuple (bool b ∷ v ∷ w ∷ vs) = issueWith-quiet xs (tuple (bool b ∷ v ∷ w ∷ vs))
... | tuple (bytes bs ∷ vs) = issueWith-quiet xs (tuple (bytes bs ∷ vs))
... | tuple (tuple ws ∷ vs) = issueWith-quiet xs (tuple (tuple ws ∷ vs))
... | tuple (none ∷ vs) = issueWith-quiet xs (tuple (none ∷ vs))
... | tuple (some w ∷ vs) = issueWith-quiet xs (tuple (some w ∷ vs))

activate-quiet : ∀ c ctx a salt → Quiet (activate c ctx a salt)
activate-quiet c ctx a salt = bind (observed "booted") λ booted →
  bind (guard (not (flag booted)) "already activated") λ _ →
  bind (pure (Device.keyGuard-pure c (key a) "device key has small order")) λ _ →
  bind (pure (Device.bootCommit-pure c a salt)) λ commitment →
  bind (observed "boot") λ boot →
  bind (guard (equal commitment boot) "boot commitment mismatch") λ _ →
  bind (self-read ctx) λ addr →
  bind (counted "device_epoch") λ epoch →
  bind (pure (Device.entryAt-pure c addr a epoch 0)) λ initial →
  bind (included "devices" initial refl) λ _ →
  bind (written "device_count" (nat 1) refl) λ _ →
  bind (written "booted" (bool true) refl) λ _ →
  bind (written "boot" zero32 refl) λ _ →
  bind (bumped "round" 64 refl) λ _ → ret unit

submit-quiet : ∀ ctx xs → Quiet (submit ctx xs)
submit-quiet ctx xs = bind (observed "pending_recovery") λ pending →
  bind (guard (not (flag pending)) "recovery already pending") λ _ →
  bind (counted "device_epoch") λ epoch →
  bind (guard (number A.epoch ≡ᵇ epoch) "stale epoch") λ _ →
  bind (counted "auth_nonce") λ nonce →
  bind (guard (number A.authNonce ≡ᵇ nonce) "stale authorisation nonce") λ _ →
  bind (observed "recovery_pk") λ pk →
  bind (pure (Device.requireRecoveryKey-pure pk)) λ _ →
  bind (pure (Device.requireRecoveryKey-pure A.successorKey)) λ _ →
  bind (pure (Device.requireRecoveryKey-pure A.nextRecoveryKey)) λ _ →
  bind (observed "recovery_pk") λ currentPk →
  bind (guard (not (equal A.nextRecoveryKey currentPk)) "recovery commitment reused") λ _ →
  bind (counted "device_epoch") λ currentEpoch →
  bind (bounded "device_epoch" 32 (suc currentEpoch)) λ postEpoch →
  bind (self-read ctx) λ addr →
  bind (observed "recovery_pk") λ signingPk →
  bind (counted "auth_nonce") λ signingNonce →
  bind (pure (Binding.hashTag-pure "midnight:account:recovery:submit:v1")) λ dst →
  bind (pure (Binding.hash-pure (b32 dst ∷ contract addr ∷ jub signingPk ∷ jub A.recoveryR ∷
    jub A.successorKey ∷ jub A.successorR ∷ jub A.nextRecoveryKey ∷ u32 (nat postEpoch) ∷
    u64 (nat signingNonce) ∷ u64 A.nowBound ∷ u64 A.grindNonce ∷ []))) λ h →
  bind (observed "recovery_pk") λ verifyingPk →
  bind (pure (Binding.SchnorrRun.state-free verifyingPk A.recoveryR A.recoveryS h "invalid recovery signature")) λ _ →
  bind (pure (Binding.SchnorrRun.state-free A.successorKey A.successorR A.successorS h "invalid successor co-signature")) λ _ →
  bind (greater-read ctx (number A.nowBound)) λ past →
  bind (guard (not past) "now bound is in the past") λ _ →
  bind (written "pending_recovery" (bool true) refl) λ _ →
  bind (entry-quiet jubjub ctx (auth A.successorKey 0 none none 0 0 none none none) postEpoch 0) λ successor →
  bind (written "pending_entry" successor refl) λ _ →
  bind (written "pending_recovery_pk" A.nextRecoveryKey refl) λ _ →
  bind (counted "veto_window") λ window →
  bind (write-count "pending_not_before" 64 (number A.nowBound + window) refl) λ _ →
  bind (bumped "round" 64 refl) λ _ → ret unit
  where module A = SubmitArguments xs

finalise-quiet : ∀ ctx → Quiet (finalise ctx)
finalise-quiet ctx = bind (observed "pending_recovery") λ pending →
  bind (guard (flag pending) "no recovery pending") λ _ →
  bind (counted "pending_not_before") λ deadline →
  bind (less-read ctx deadline) λ early →
  bind (guard (not early) "veto window still open") λ _ →
  bind (observed "pending_recovery_pk") λ pk →
  bind (pure (Device.requireRecoveryKey-pure pk)) λ _ →
  bind (bumped "device_epoch" 32 refl) λ _ →
  bind (cleared "devices" refl) λ _ →
  bind (observed "pending_entry") λ successor →
  bind (included "devices" successor refl) λ _ →
  bind (written "device_count" (nat 1) refl) λ _ →
  bind (observed "pending_recovery_pk") λ installingPk →
  bind (written "recovery_pk" installingPk refl) λ _ →
  bind (written "recovery_phi_len" (nat 0) refl) λ _ →
  bind (written "pending_recovery" (bool false) refl) λ _ →
  bind (written "pending_entry" zero32 refl) λ _ →
  bind (observed "pending_recovery_pk") λ clearingPk →
  bind (lifted (ecMul P jubjub clearingPk 0)) λ o →
  bind (written "pending_recovery_pk" o refl) λ _ →
  bind (written "pending_not_before" (nat 0) refl) λ _ →
  bind (bumped "auth_nonce" 64 refl) λ _ →
  bind (bumped "round" 64 refl) λ _ → ret unit

record-quiet : ∀ g → Quiet (validateGrantRecord g)
record-quiet g = bind (guard (flag (grantActive g)) "grant revoked") λ _ →
  bind (observed "device_epoch") λ epoch →
  bind (guard (equal (grantEpoch g) epoch) "grant epoch stale") λ _ →
  bind (observed "grant_generation") λ generation →
  guard (equal (grantGeneration g) generation) "grant generation stale"

id-quiet : ∀ c ctx ga → Quiet (grantId c ctx ga)
id-quiet jubjub ctx ga = bind (self-read ctx) λ addr →
  bind (pure (Binding.keyAtoms-pure jubjub (key (authorisation ga)))) λ ks →
  pure (Binding.hash-pure (b32 (pad 32 "midnight:account:grant:id:v1") ∷ contract addr ∷
    (ks ++ (b32 (origin ga) ∷ u8 (nat (slot ga)) ∷ []))))
id-quiet k256 ctx ga = bind (self-read ctx) λ addr →
  bind (pure (Binding.keyAtoms-pure k256 (key (authorisation ga)))) λ ks →
  pure (Binding.hash-pure (b32 (pad 32 "midnight:account:grant:id:k1:v1") ∷ contract addr ∷
    (ks ++ (u8 (nat (envelope (authorisation ga))) ∷ b32 (origin ga) ∷ u8 (nat (slot ga)) ∷ []))))
id-quiet p256 ctx ga = bind (self-read ctx) λ addr →
  bind (pure (Binding.keyAtoms-pure p256 (key (authorisation ga)))) λ ks →
  pure (Binding.hash-pure (b32 (pad 32 "midnight:account:grant:id:r1:v1") ∷ contract addr ∷
    (ks ++ (b32 (origin ga) ∷ u8 (nat (slot ga)) ∷ []))))

grant-guard : Curve → GrantAuth → M ⊤
grant-guard jubjub ga = requireSmallOrderFree (key (authorisation ga)) "grantee key has small order"
grant-guard k256 ga = assert (envelope (authorisation ga) ≡ᵇ 0) "envelope not admitted for a spend grant" >>
  requireK256Key (key (authorisation ga))
grant-guard p256 ga = hash (b32 (pad 32 "midnight:account:grant:origin:v1") ∷
  ("Bytes<21>" , at 1 (policy (authorisation ga))) ∷ []) >>= λ originHash →
  assert (equal originHash (origin ga)) "grant origin mismatch"

grant-guard-quiet : ∀ c ga → Quiet (grant-guard c ga)
grant-guard-quiet jubjub ga = pure (Device.keyGuard-pure jubjub (key (authorisation ga)) "grantee key has small order")
grant-guard-quiet k256 ga = bind (guard (envelope (authorisation ga) ≡ᵇ 0) "envelope not admitted for a spend grant") λ _ →
  pure (Device.keyGuard-pure k256 (key (authorisation ga)) "device key is the point at infinity")
grant-guard-quiet p256 ga = bind (pure (Binding.hash-pure _)) λ originHash →
  guard (equal originHash (origin ga)) "grant origin mismatch"

grant-rp : Curve → GrantAuth → Value → M ⊤
grant-rp p256 ga scope = rpCommit (salt ga) (at 0 (policy (authorisation ga))) >>= λ commitment →
  assert (equal commitment (scopeRPCommitment scope)) "grant RP mismatch"
grant-rp _ ga scope = return tt

grant-rp-quiet : ∀ c ga scope → Quiet (grant-rp c ga scope)
grant-rp-quiet jubjub ga scope = ret tt
grant-rp-quiet k256 ga scope = ret tt
grant-rp-quiet p256 ga scope = bind (pure (Device.rpCommit-pure (salt ga) (at 0 (policy (authorisation ga))))) λ commitment →
  guard (equal commitment (scopeRPCommitment scope)) "grant RP mismatch"

authenticate-program : Curve → Context → GrantAuth → M (Value × Value)
authenticate-program c ctx ga = do
  grant-guard c ga
  id ← grantId c ctx ga
  present ← memberMap "grants" id
  assert present "unknown grant"
  g ← lookup "grants" id
  validateGrantRecord g
  (if number (scopeExpiresAt (grantScope g)) ≡ᵇ 0 then return tt else
    (readTimeLess ctx (number (scopeExpiresAt (grantScope g))) >>= λ beforeExpiry → assert beforeExpiry "grant expired"))
  grant-rp c ga (grantScope g)
  return (id , g)

authenticate-program-equal : ∀ c ctx ga → authenticate-program c ctx ga ≡ authenticateGrant c ctx ga
authenticate-program-equal jubjub ctx ga = refl
authenticate-program-equal k256 ctx ga = refl
authenticate-program-equal p256 ctx ga = refl

authenticate-program-quiet : ∀ c ctx ga → Quiet (authenticate-program c ctx ga)
authenticate-program-quiet c ctx ga = bind (grant-guard-quiet c ga) λ _ →
  bind (id-quiet c ctx ga) λ id →
  bind (membered "grants" id) λ present →
  bind (guard present "unknown grant") λ _ →
  bind (looked "grants" id) λ g →
  bind (record-quiet g) λ _ →
  bind (branch (number (scopeExpiresAt (grantScope g)) ≡ᵇ 0) (ret tt)
    (bind (less-read ctx (number (scopeExpiresAt (grantScope g)))) λ beforeExpiry →
      guard beforeExpiry "grant expired")) λ _ →
  bind (grant-rp-quiet c ga (grantScope g)) λ _ → ret (id , g)

authenticate-quiet : ∀ c ctx ga → Quiet (authenticateGrant c ctx ga)
authenticate-quiet c ctx ga = subst Quiet (authenticate-program-equal c ctx ga) (authenticate-program-quiet c ctx ga)

caller-program : GrantAuth → Value → Value → M ⊤
caller-program ga scope none = assert false "grant requires a contract caller"
caller-program ga scope (some (tuple (bool isContract ∷ address ∷ []))) =
  assert isContract "grant requires a contract caller" >>
  (callerCommit (salt ga) (some address) >>= λ commitment →
    assert (equal commitment (scopeCallerCommitment scope)) "grant caller mismatch")
caller-program ga scope _ = abort (decoding "kernel.caller")

caller-program-quiet : ∀ ga scope caller → Quiet (caller-program ga scope caller)
caller-program-quiet ga scope none = guard false "grant requires a contract caller"
caller-program-quiet ga scope (some (tuple (bool isContract ∷ address ∷ []))) =
  bind (guard isContract "grant requires a contract caller") λ _ →
  bind (pure (Device.callerCommit-pure (salt ga) (some address))) λ commitment →
  guard (equal commitment (scopeCallerCommitment scope)) "grant caller mismatch"
inspect (caller-program-quiet ga scope (nat _)) ()
inspect (caller-program-quiet ga scope (bool _)) ()
inspect (caller-program-quiet ga scope (bytes _)) ()
inspect (caller-program-quiet ga scope (tuple _)) ()
inspect (caller-program-quiet ga scope (some (nat _))) ()
inspect (caller-program-quiet ga scope (some (bool _))) ()
inspect (caller-program-quiet ga scope (some (bytes _))) ()
inspect (caller-program-quiet ga scope (some none)) ()
inspect (caller-program-quiet ga scope (some (some _))) ()
inspect (caller-program-quiet ga scope (some (tuple []))) ()
inspect (caller-program-quiet ga scope (some (tuple (nat _ ∷ _)))) ()
inspect (caller-program-quiet ga scope (some (tuple (bytes _ ∷ _)))) ()
inspect (caller-program-quiet ga scope (some (tuple (tuple _ ∷ _)))) ()
inspect (caller-program-quiet ga scope (some (tuple (none ∷ _)))) ()
inspect (caller-program-quiet ga scope (some (tuple (some _ ∷ _)))) ()
inspect (caller-program-quiet ga scope (some (tuple (bool _ ∷ [])))) ()
inspect (caller-program-quiet ga scope (some (tuple (bool _ ∷ _ ∷ _ ∷ _)))) ()

caller-quiet : ∀ ctx ga scope → Quiet (checkCaller ctx ga scope)
inspect (caller-quiet ctx ga scope) execution with not (equal (scopeCallerCommitment scope) zero32)
inspect (caller-quiet ctx ga scope) execution | false = inspect (ret tt) execution
inspect (caller-quiet ctx ga scope) execution | true with caller ctx
... | some (tuple (bool isContract ∷ address ∷ [])) = inspect
  (bind (emitted (contextRead "caller" (some (tuple (bool isContract ∷ address ∷ [])))) refl) λ _ →
    caller-program-quiet ga scope (some (tuple (bool isContract ∷ address ∷ [])))) execution
... | none = ⊥-elim (rejected≢accepted execution)
... | nat _ = ⊥-elim (rejected≢accepted execution)
... | bool _ = ⊥-elim (rejected≢accepted execution)
... | bytes _ = ⊥-elim (rejected≢accepted execution)
... | tuple _ = ⊥-elim (rejected≢accepted execution)
... | some (nat _) = ⊥-elim (rejected≢accepted execution)
... | some (bool _) = ⊥-elim (rejected≢accepted execution)
... | some (bytes _) = ⊥-elim (rejected≢accepted execution)
... | some none = ⊥-elim (rejected≢accepted execution)
... | some (some _) = ⊥-elim (rejected≢accepted execution)
... | some (tuple []) = ⊥-elim (rejected≢accepted execution)
... | some (tuple (nat _ ∷ _)) = ⊥-elim (rejected≢accepted execution)
... | some (tuple (bytes _ ∷ _)) = ⊥-elim (rejected≢accepted execution)
... | some (tuple (tuple _ ∷ _)) = ⊥-elim (rejected≢accepted execution)
... | some (tuple (none ∷ _)) = ⊥-elim (rejected≢accepted execution)
... | some (tuple (some _ ∷ _)) = ⊥-elim (rejected≢accepted execution)
... | some (tuple (bool _ ∷ [])) = ⊥-elim (rejected≢accepted execution)
... | some (tuple (bool _ ∷ _ ∷ _ ∷ _)) = ⊥-elim (rejected≢accepted execution)

scope-quiet : ∀ op ctx ga xs coin g → Quiet (scopeCheck op ctx ga xs coin g)
scope-quiet op ctx ga xs coin g =
  bind (guard (flag (scopeAllows op scope)) "operation not in scope") λ _ →
  bind (caller-quiet ctx ga scope) λ _ →
  bind (pure (Device.objectCommit-pure (salt ga) (if shielded op then at 1 coin else get 0 xs)
    (recipientKind ga) (pinnedRecipient ga) (nat (maxCoinValue ga)))) λ object →
  bind (guard (equal object (scopeObjectCommitment scope)) "scope object mismatch") λ _ →
  bind (guard (amountOf op xs ≤ᵇ number (scopePerCallCap scope)) "amount above per-call cap") λ _ →
  bind (pure (Device.spentCommit-pure (salt ga) (spentPrev ga))) λ opening →
  bind (guard (equal opening (grantSpentCommitment g)) "spent opening mismatch") λ _ →
  bind (guard (spentPrev ga + amountOf op xs ≤ᵇ number (scopeCap scope)) "cumulative cap exceeded") λ _ →
  bind (bounded "new_spent" 128 (spentPrev ga + amountOf op xs)) λ spent →
  bind (guard ((number (recipientKind ga) ≡ᵇ 0) ∨
    ((number (recipientKind ga) ≡ᵇ thisKind op) ∧ equal (pinnedRecipient ga) (recipientOf op xs))) "recipient not admitted by pin") λ _ →
  ret spent
  where scope = grantScope g

settle-quiet : ∀ c ga id g h spent → Quiet (settle c ga id g h spent)
settle-quiet c ga id g h spent = bind (pure (Binding.verify-pure c (authorisation ga) h "invalid grant signature")) λ _ →
  bind (bounded "grant nonce" 64 (suc (number (grantNonce g)))) λ nonce →
  bind (pure (Device.spentCommit-pure (salt ga) spent)) λ commitment →
  bind (inserted "grants" id (tuple (take 3 (fields g) ++
    (nat nonce ∷ commitment ∷ drop 5 (fields g)))) refl) λ _ → bumped "round" 64 refl

nonPublic : Operation → Bool
nonPublic withdrawUnshielded = false
nonPublic _ = true

body-quiet : ∀ op ctx xs coin callerEntry → nonPublic op ≡ true → Quiet (body op ctx xs coin callerEntry)
body-quiet withdrawUnshielded ctx xs coin e ()
body-quiet withdrawShielded ctx xs coin e _ = bind (send-quiet ctx true (get 0 xs) (number (get 2 xs)) coin) λ where
  (sentCoin , change) → ret change
body-quiet withdrawToContract ctx xs coin e _ = bind (send-quiet ctx false (get 0 xs) (number (get 2 xs)) coin) λ where
  (sentCoin , change) → ret (tuple (sentCoin ∷ change ∷ []))
body-quiet appendInbox ctx xs coin e _ = bind (inbox (get 0 xs)) λ _ → ret unit
body-quiet rotateEncKey ctx xs coin e _ = bind (written "enc_key" (get 0 xs) refl) λ _ → ret unit
body-quiet addDevice ctx xs coin e _ = bind (setMembered "devices" (get 0 xs)) λ present →
  bind (guard (not present) "device entry already present") λ _ →
  bind (included "devices" (get 0 xs) refl) λ _ →
  bind (bumped "device_count" 8 refl) λ _ → ret unit
body-quiet removeDevice ctx xs coin e _ = bind (counted "device_count") λ count →
  bind (guard (1 <ᵇ count) "cannot remove last device") λ _ →
  bind (guard (not (equal (get 0 xs) e)) "cannot remove the authorising device") λ _ →
  bind (setMembered "devices" (get 0 xs)) λ present →
  bind (guard present "unknown device entry") λ _ →
  bind (excluded "devices" (get 0 xs) refl) λ _ →
  bind (counted "device_count") λ current →
  bind (write-count "device_count" 8 (current ∸ 1) refl) λ _ → ret unit
body-quiet issueGrant ctx xs coin e _ = bind (issue-quiet xs) λ _ → ret unit
body-quiet revokeGrant ctx xs coin e _ = bind (revoke-quiet (get 0 xs)) λ _ → ret unit
body-quiet revokeAllGrants ctx xs coin e _ = bind (bind (bumped "grant_generation" 32 refl) λ _ → cleared "grants" refl) λ _ → ret unit
body-quiet publishRecovery ctx xs coin e _ = bind (publish-quiet xs) λ _ → ret unit
body-quiet cancelRecovery ctx xs coin e _ = bind cancel-quiet λ _ → ret unit

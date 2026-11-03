{-# OPTIONS --safe --without-K #-}

-- Stateful bodies from Passport contracts/account.compact, including the
-- shared bodies of account-p256.compact's wrappers, pinned at fc19e471536f.
-- FullAccount dispatches them after ABI validation/authentication. Reads,
-- assertions, writes and native effects retain source evaluation order:
-- repeated reads are transcript observations, not redundant computations.
-- Raw layouts are documented locally: operation vectors beside operationAtoms,
-- coin fields beside coinInfo, and optional-change/result tuples beside sendCoin.

open import Conformance.FullAccountTypes

module Conformance.FullAccountBody (P : Primitives) where

open import Conformance.FullAccountCrypto P
open import Conformance.FullAccountLayouts
open import Data.Bool.Base
open import Data.List.Base using (List; []; _∷_; _++_; take; drop)
open import Data.Nat.Base hiding (equal)
open import Data.Product.Base
open import Data.String.Base using (String)
open import Data.Unit.Base

data Operation : Set where
  withdrawUnshielded withdrawShielded withdrawToContract appendInbox rotateEncKey
    addDevice removeDevice issueGrant revokeGrant revokeAllGrants publishRecovery cancelRecovery : Operation

operationName : Operation → String
operationName withdrawUnshielded = "withdraw_unshielded"
operationName withdrawShielded = "withdraw_shielded"
operationName withdrawToContract = "withdraw_shielded_to_contract"
operationName appendInbox = "append_inbox"
operationName rotateEncKey = "rotate_enc_key"
operationName addDevice = "add_device"
operationName removeDevice = "remove_device"
operationName issueGrant = "issue_grant"
operationName revokeGrant = "revoke_grant"
operationName revokeAllGrants = "revoke_all_grants"
operationName publishRecovery = "publish_recovery_session"
operationName cancelRecovery = "recover_cancel"

shielded : Operation → Bool
shielded withdrawShielded = true
shielded withdrawToContract = true
shielded _ = false

qualifiedAtom : Value → Atom
qualifiedAtom coin = "QualifiedShieldedCoinInfo" , coin

inboxAppend : Value → M ⊤
inboxAppend entry = do
  count ← readCount "inbox_count"
  insert "inbox" (nat count) entry
  bump "inbox_count" 64

credit : Value → ℕ → M ⊤
credit color amount = do
  present ← memberMap "unshielded_balances" color
  if present then (do
    old ← lookup "unshielded_balances" color
    n ← cast "unshielded_balances" 128 (number old + amount)
    insert "unshielded_balances" color (nat n))
    else insert "unshielded_balances" color (nat amount)

debit : Value → ℕ → M ⊤
debit color amount = do
  present ← memberMap "unshielded_balances" color
  assert present "no balance for color"
  old ← lookup "unshielded_balances" color
  assert (amount ≤ᵇ number old) "insufficient balance"
  n ← cast "unshielded_balances" 128 (number old ∸ amount)
  insert "unshielded_balances" color (nat n)

withdrawPublic : Value → ℕ → Value → M Value
withdrawPublic color amount recipient = do
  debit color amount
  emit (sendUnshielded color amount (tuple (bool false ∷ recipient ∷ [])))
  return unit

-- Coin tuple: [nonce, color, value]. A qualified input appends mt_index at 3;
-- commitment/nullifier preimages below deliberately use only the first three.
coinInfo : Value → Value
coinInfo coin = tuple (take 3 (fields coin))

evolveNonce : Bool → Value → M Value
evolveNonce change nonce = do
  degraded ← lift (degradeToTransient P nonce)
  evolved ← lift (transientHash P
    (le (ascii (if change then "midnight:kernel:nonce_evolve/2" else "midnight:kernel:nonce_evolve")) ∷ degraded ∷ []))
  lift (upgradeFromTransient P evolved)

createCoin : Value → Value → M ⊤
createCoin coin recipient = do
  cm ← lift (coinCommitment P coin recipient)
  emit (createShielded coin recipient cm)

receiveCoin : Context → Value → M ⊤
receiveCoin ctx coin = do
  addr ← readSelf ctx
  createCoin coin (tuple (bool false ∷ addr ∷ []))
  emit (receiveShielded coin)

-- The native send creates the input/nullifier before subtracting. Foreign
-- outputs remain explicit effects: the composed transaction must claim them.
-- Result is the pair (sent coin, change), where change is [present, coin].
-- The key-withdrawal body returns change alone; the contract-withdrawal body
-- returns [sent, change]. Grant.appendChange inspects these same layouts.
sendCoin : Context → Bool → Value → ℕ → Value → M (Value × Value)
sendCoin ctx isUser recipient amount coin = do
  addr ← readSelf ctx
  nf ← lift (coinNullifier P (coinInfo coin) addr)
  emit (consumeShielded coin nf)
  assert (amount ≤ᵇ number (at 2 coin)) "result of subtraction would be negative"
  let change = number (at 2 coin) ∸ amount
  nonce ← evolveNonce false (at 0 coin)
  let sent = tuple (nonce ∷ at 1 coin ∷ nat amount ∷ [])
  let destination = tuple (bool isUser ∷ recipient ∷ [])
  createCoin sent destination
  (if not isUser ∧ equal recipient addr then emit (receiveShielded sent) else return tt)
  if change ≡ᵇ 0 then
    return (sent , tuple (bool false ∷ tuple (zero32 ∷ zero32 ∷ nat 0 ∷ []) ∷ []))
    else (do
      nonce′ ← evolveNonce true (at 0 coin)
      let changeCoin = tuple (nonce′ ∷ at 1 coin ∷ nat change ∷ [])
      createCoin changeCoin (tuple (bool false ∷ addr ∷ []))
      emit (receiveShielded changeCoin)
      return (sent , tuple (bool true ∷ changeCoin ∷ [])))

callerCommit : Value → Value → M Value
callerCommit salt none = return zero32
callerCommit salt (some addr) = do
  c ← hash (b32 (pad 32 "midnight:account:grant:caller:v1") ∷ b32 salt ∷ contract addr ∷ [])
  assert (not (equal c zero32)) "reserved caller commitment"
  return c
callerCommit salt (tuple (bool present ∷ addr ∷ [])) = do
  assert (present ∨ equal addr zero32) "noncanonical absent caller"
  if present then callerCommit salt (some addr) else return zero32
callerCommit salt _ = abort (decoding "Maybe<ContractAddress>")

objectCommit : Value → Value → Value → Value → Value → M Value
objectCommit salt color kind recipient maxCoin = hash
  (b32 (pad 32 "midnight:account:grant:obj:v1") ∷ b32 salt ∷ b32 color ∷ u8 kind ∷ b32 recipient ∷ u128 maxCoin ∷ [])

spentCommit : Value → ℕ → M Value
spentCommit salt spent = hash
  (b32 (pad 32 "midnight:account:grant:spent:v1") ∷ b32 salt ∷ u128 (nat spent) ∷ [])

rpCommit : Value → Value → M Value
rpCommit salt rp = hash (b32 (pad 32 "midnight:account:grant:rp:v1") ∷ b32 salt ∷ b32 rp ∷ [])

scopeDigest : List Value → M Value
scopeDigest xs = do
  caller ← callerCommit A.salt A.caller
  hash (b32 (pad 32 "midnight:account:grant:scope:v2") ∷ b32 A.salt ∷
    ("Boolean" , A.withdrawUnshielded) ∷ ("Boolean" , A.withdrawShielded) ∷
    ("Boolean" , A.withdrawToContract) ∷ ("Boolean" , A.readFlag) ∷
    b32 A.color ∷ u8 A.recipientKind ∷ b32 A.recipient ∷ u128 A.maxCoinValue ∷
    u128 A.perCallCap ∷ u128 A.cap ∷ u64 A.expiresAt ∷ b32 A.rpIdHash ∷
    b32 A.readKeyHash ∷ u64 A.windowLength ∷ u128 A.windowCap ∷ b32 caller ∷ [])
  where module A = IssueArguments xs

-- Operation argument vectors (zero-based, authentication already split off):
-- withdrawUnshielded: [color, amount, recipient]
-- withdrawShielded/withdrawToContract: [recipient, color, amount]
-- appendInbox/rotateEncKey/addDevice/removeDevice/revokeGrant:
--   [entry]/[enc_key]/[entry]/[entry]/[grant_id], respectively.
-- issueGrant: IssueArguments in FullAccountLayouts.
-- publishRecovery: [recovery_pk, session_nonce, phi1, phi2, phi3, phi4, phi_len, wrap]
-- revokeAllGrants/cancelRecovery: [].
-- These layouts also govern publish/body and FullAccountGrant's spend helpers.
operationAtoms : Operation → List Value → Value → M (List Atom)
operationAtoms withdrawUnshielded xs coin = return
  (b32 (get 0 xs) ∷ u128 (get 1 xs) ∷ user (get 2 xs) ∷ [])
operationAtoms withdrawShielded xs coin = return
  (zswap (get 0 xs) ∷ b32 (get 1 xs) ∷ u128 (get 2 xs) ∷ qualifiedAtom coin ∷ [])
operationAtoms withdrawToContract xs coin = return
  (contract (get 0 xs) ∷ b32 (get 1 xs) ∷ u128 (get 2 xs) ∷ qualifiedAtom coin ∷ [])
operationAtoms appendInbox xs coin = return (("Bytes<192>" , get 0 xs) ∷ [])
operationAtoms rotateEncKey xs coin = return (b32 (get 0 xs) ∷ [])
operationAtoms addDevice xs coin = return (b32 (get 0 xs) ∷ [])
operationAtoms removeDevice xs coin = return (b32 (get 0 xs) ∷ [])
operationAtoms issueGrant xs coin = do
  digest ← scopeDigest xs
  return (b32 (get 0 xs) ∷ b32 digest ∷ [])
operationAtoms revokeGrant xs coin = return (b32 (get 0 xs) ∷ [])
operationAtoms revokeAllGrants xs coin = return []
operationAtoms publishRecovery xs coin = return
  (jub (get 0 xs) ∷ b32 (get 1 xs) ∷ fld (get 2 xs) ∷ fld (get 3 xs) ∷ fld (get 4 xs) ∷
    fld (get 5 xs) ∷ u8 (get 6 xs) ∷ ("Bytes<64>" , get 7 xs) ∷ [])
operationAtoms cancelRecovery xs coin = return []

issue : List Value → M ⊤
issue xs = do
  present ← memberMap "grants" A.id
  (if present then (do
    old ← lookup "grants" A.id
    if flag (grantActive old) then (do
      epoch ← read "device_epoch"
      if equal (grantEpoch old) epoch then (do
        generation ← read "grant_generation"
        assert (not (equal (grantGeneration old) generation)) "grant already active")
        else return tt)
      else return tt) else return tt)
  let spend = flag A.withdrawUnshielded ∨ flag A.withdrawShielded ∨ flag A.withdrawToContract
  let readFlag = flag A.readFlag
  assert (spend ∨ readFlag) "empty scope"
  assert (spend ∨ not (isSome A.caller)) "read-only grant cannot restrict caller"
  assert (not (flag A.withdrawShielded ∨ flag A.withdrawToContract) ∨ readFlag)
    "shielded spend requires read"
  assert (number A.perCallCap ≤ᵇ number A.cap) "per-call cap above cap"
  assert (not spend ∨ (0 <ᵇ number A.cap)) "spend without cap"
  assert (not spend ∨ (number A.perCallCap ≤ᵇ number A.maxCoinValue)) "coin bound below per-call cap"
  assert (not readFlag ∨ not (equal A.readKeyHash zero32)) "read without delegate key"
  assert ((number A.windowLength ≡ᵇ 0) ∧ (number A.windowCap ≡ᵇ 0)) "window bounds reserved"
  assert (spend ∨ (equal A.color zero32 ∧ (number A.recipientKind ≡ᵇ 0) ∧ equal A.recipient zero32 ∧
    (number A.maxCoinValue ≡ᵇ 0) ∧ (number A.perCallCap ≡ᵇ 0) ∧ (number A.cap ≡ᵇ 0)))
    "read-only grant carries object fields"
  epoch ← read "device_epoch"
  generation ← read "grant_generation"
  issued ← read "auth_nonce"
  spent ← spentCommit A.salt 0
  object ← objectCommit A.salt A.color A.recipientKind A.recipient A.maxCoinValue
  rp ← rpCommit A.salt A.rpIdHash
  caller ← callerCommit A.salt A.caller
  let scope = tuple (A.withdrawUnshielded ∷ A.withdrawShielded ∷ A.withdrawToContract ∷
        A.readFlag ∷ object ∷ A.perCallCap ∷ A.cap ∷ A.expiresAt ∷ rp ∷
        A.readKeyHash ∷ nat 0 ∷ nat 0 ∷ caller ∷ [])
  insert "grants" A.id (tuple (epoch ∷ generation ∷ issued ∷ nat 0 ∷ spent ∷
    nat 0 ∷ nat 0 ∷ bool true ∷ scope ∷ []))
  where
  module A = IssueArguments xs
  isSome : Value → Bool
  isSome (some _) = true
  isSome (tuple (bool b ∷ _ ∷ [])) = b
  isSome _ = false

revoke : Value → M ⊤
revoke id = do
  present ← memberMap "grants" id
  assert present "unknown grant"
  old ← lookup "grants" id
  assert (flag (grantActive old)) "grant not live"
  -- Preserve epoch through window_spent; replace only active, retaining scope.
  insert "grants" id (tuple (take 7 (fields old) ++ (bool false ∷ grantScope old ∷ [])))

cancel : M ⊤
cancel = do
  pending ← read "pending_recovery"
  assert (flag pending) "no recovery pending"
  write "pending_recovery" (bool false)
  write "pending_entry" zero32
  pk ← read "pending_recovery_pk"
  o ← lift (ecMul P jubjub pk 0)
  write "pending_recovery_pk" o
  write "pending_not_before" (nat 0)

publish : List Value → M ⊤
publish xs = do
  let x = λ n → get n xs
  pending ← read "pending_recovery"
  assert (not (flag pending)) "recovery pending; cancel first"
  assert (1 ≤ᵇ number (x 6)) "phi must not be empty"
  assert (number (x 6) ≤ᵇ 4) "phi length out of range"
  (if number (x 6) <ᵇ 2 then assert (number (x 3) ≡ᵇ 0) "unused phi slot 2 not zero" else return tt)
  (if number (x 6) <ᵇ 3 then assert (number (x 4) ≡ᵇ 0) "unused phi slot 3 not zero" else return tt)
  (if number (x 6) <ᵇ 4 then assert (number (x 5) ≡ᵇ 0) "unused phi slot 4 not zero" else return tt)
  assert (not (equal (x 1) zero32)) "session nonce is zero"
  session ← read "recovery_session"
  assert (not (equal (x 1) session)) "session nonce reused"
  pk ← read "recovery_pk"
  assert (not (equal (x 0) pk)) "recovery commitment reused"
  requireRecoveryKey (x 0)
  write "recovery_pk" (x 0)
  write "recovery_session" (x 1)
  insert "recovery_phi" (nat 1) (x 2)
  insert "recovery_phi" (nat 2) (x 3)
  insert "recovery_phi" (nat 3) (x 4)
  insert "recovery_phi" (nat 4) (x 5)
  write "recovery_phi_len" (x 6)
  write "recovery_wrap" (x 7)
  write "recovery_version" (nat 1)

body : Operation → Context → List Value → Value → Value → M Value
body withdrawUnshielded ctx xs coin callerEntry = withdrawPublic (get 0 xs) (number (get 1 xs)) (get 2 xs)
body withdrawShielded ctx xs coin callerEntry = do
  (sent , change) ← sendCoin ctx true (get 0 xs) (number (get 2 xs)) coin
  return change
body withdrawToContract ctx xs coin callerEntry = do
  (sent , change) ← sendCoin ctx false (get 0 xs) (number (get 2 xs)) coin
  return (tuple (sent ∷ change ∷ []))
body appendInbox ctx xs coin callerEntry = inboxAppend (get 0 xs) >> return unit
body rotateEncKey ctx xs coin callerEntry = write "enc_key" (get 0 xs) >> return unit
body addDevice ctx xs coin callerEntry = do
  present ← has "devices" (get 0 xs)
  assert (not present) "device entry already present"
  include "devices" (get 0 xs)
  bump "device_count" 8
  return unit
body removeDevice ctx xs coin callerEntry = do
  count ← readCount "device_count"
  assert (1 <ᵇ count) "cannot remove last device"
  assert (not (equal (get 0 xs) callerEntry)) "cannot remove the authorising device"
  present ← has "devices" (get 0 xs)
  assert present "unknown device entry"
  exclude "devices" (get 0 xs)
  currentCount ← readCount "device_count"
  writeCount "device_count" 8 (currentCount ∸ 1)
  return unit
body issueGrant ctx xs coin callerEntry = issue xs >> return unit
body revokeGrant ctx xs coin callerEntry = revoke (get 0 xs) >> return unit
body revokeAllGrants ctx xs coin callerEntry = bump "grant_generation" 32 >> clear "grants" >> return unit
body publishRecovery ctx xs coin callerEntry = publish xs >> return unit
body cancelRecovery ctx xs coin callerEntry = cancel >> return unit

activate : Curve → Context → Auth → Value → M Value
activate c ctx a salt = do
  booted ← read "booted"
  assert (not (flag booted)) "already activated"
  keyGuard c (key a) "device key has small order"
  commitment ← bootCommit c a salt
  boot ← read "boot"
  assert (equal commitment boot) "boot commitment mismatch"
  addr ← readSelf ctx
  epoch ← readCount "device_epoch"
  initial ← entryAt c addr a epoch 0
  include "devices" initial
  write "device_count" (nat 1)
  write "booted" (bool true)
  write "boot" zero32
  bump "round" 64
  return unit

submit : Context → List Value → M Value
submit ctx xs = do
  pending ← read "pending_recovery"
  assert (not (flag pending)) "recovery already pending"
  epoch ← readCount "device_epoch"
  assert (number A.epoch ≡ᵇ epoch) "stale epoch"
  nonce ← readCount "auth_nonce"
  assert (number A.authNonce ≡ᵇ nonce) "stale authorisation nonce"
  pk ← read "recovery_pk"
  requireRecoveryKey pk
  requireRecoveryKey A.successorKey
  requireRecoveryKey A.nextRecoveryKey
  -- These later recovery_pk/epoch/nonce reads are distinct source accesses;
  -- reusing earlier values would erase observations from the compared trace.
  currentPk ← read "recovery_pk"
  assert (not (equal A.nextRecoveryKey currentPk)) "recovery commitment reused"
  currentEpoch ← readCount "device_epoch"
  postEpoch ← cast "device_epoch" 32 (suc currentEpoch)
  addr ← readSelf ctx
  signingPk ← read "recovery_pk"
  signingNonce ← readCount "auth_nonce"
  dst ← hashTag "midnight:account:recovery:submit:v1"
  h ← hash (b32 dst ∷ contract addr ∷ jub signingPk ∷ jub A.recoveryR ∷
    jub A.successorKey ∷ jub A.successorR ∷ jub A.nextRecoveryKey ∷
    u32 (nat postEpoch) ∷ u64 (nat signingNonce) ∷ u64 A.nowBound ∷ u64 A.grindNonce ∷ [])
  verifyingPk ← read "recovery_pk"
  schnorr verifyingPk A.recoveryR A.recoveryS h "invalid recovery signature"
  schnorr A.successorKey A.successorR A.successorS h "invalid successor co-signature"
  past ← readTimeGreater ctx (number A.nowBound)
  assert (not past) "now bound is in the past"
  write "pending_recovery" (bool true)
  successor ← entry jubjub ctx (auth A.successorKey 0 none none 0 0 none none none) postEpoch 0
  write "pending_entry" successor
  write "pending_recovery_pk" A.nextRecoveryKey
  window ← readCount "veto_window"
  writeCount "pending_not_before" 64 (number A.nowBound + window)
  bump "round" 64
  return unit
  where module A = SubmitArguments xs

finalise : Context → M Value
finalise ctx = do
  pending ← read "pending_recovery"
  assert (flag pending) "no recovery pending"
  deadline ← readCount "pending_not_before"
  early ← readTimeLess ctx deadline
  assert (not early) "veto window still open"
  pk ← read "pending_recovery_pk"
  requireRecoveryKey pk
  bump "device_epoch" 32
  clear "devices"
  successor ← read "pending_entry"
  include "devices" successor
  write "device_count" (nat 1)
  installingPk ← read "pending_recovery_pk"
  write "recovery_pk" installingPk
  write "recovery_phi_len" (nat 0)
  write "pending_recovery" (bool false)
  write "pending_entry" zero32
  clearingPk ← read "pending_recovery_pk"
  o ← lift (ecMul P jubjub clearingPk 0)
  write "pending_recovery_pk" o
  write "pending_not_before" (nat 0)
  bump "auth_nonce" 64
  bump "round" 64
  return unit

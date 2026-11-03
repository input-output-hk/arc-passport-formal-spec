{-# OPTIONS --safe --without-K #-}

-- Grant-authenticated withdrawal twins from contracts/account.compact and
-- contracts/account-p256.compact at Passport fc19e471536f. The record/scope
-- layouts are named in FullAccountLayouts. Authentication, scope checks,
-- settlement and custody execute in source order; skipped branches produce
-- no ledger/context observations. Native effects describe local execution,
-- not authenticated transaction admission.
-- Raw spend-argument vectors are documented beside FullAccountBody.operationAtoms;
-- coin fields and change-result shapes beside FullAccountBody.coinInfo/sendCoin.
-- scopeCheck, grantChallengeArgs and appendChange use those same layouts.

open import Conformance.FullAccountTypes

module Conformance.FullAccountGrant (P : Primitives) where

open import Conformance.FullAccountBody P
open import Conformance.FullAccountCrypto P
open import Conformance.FullAccountLayouts
open import Data.Bool.Base
open import Data.List.Base using (List; []; _∷_; _++_; take; drop)
open import Data.Nat.Base hiding (equal)
open import Data.Product.Base
open import Data.String.Base using (String)
open import Data.Unit.Base

record GrantAuth : Set where
  constructor grantAuth
  field authorisation : Auth
        origin : Value
        slot : ℕ
        salt recipientKind pinnedRecipient : Value
        maxCoinValue spentPrev : ℕ
        changeEntry encryptionKey : Value
open GrantAuth public

grantId : Curve → Context → GrantAuth → M Value
grantId c ctx ga = do
  addr ← readSelf ctx
  ks ← keyAtoms c (key (authorisation ga))
  hash (b32 (tag c) ∷ contract addr ∷ (ks ++ envelopeAtom c ++
    (b32 (origin ga) ∷ u8 (nat (slot ga)) ∷ [])))
  where
  tag : Curve → Value
  tag jubjub = pad 32 "midnight:account:grant:id:v1"
  tag k256 = pad 32 "midnight:account:grant:id:k1:v1"
  tag p256 = pad 32 "midnight:account:grant:id:r1:v1"
  envelopeAtom : Curve → List Atom
  envelopeAtom k256 = u8 (nat (envelope (authorisation ga))) ∷ []
  envelopeAtom _ = []

-- The live-record guard used by authenticateGrant after the map lookup.
-- Keep the assertions and reads ordered: a revoked record does not read epoch,
-- and an old epoch does not read generation.
validateGrantRecord : Value → M ⊤
validateGrantRecord g = do
  assert (flag (grantActive g)) "grant revoked"
  epoch ← read "device_epoch"
  assert (equal (grantEpoch g) epoch) "grant epoch stale"
  generation ← read "grant_generation"
  assert (equal (grantGeneration g) generation) "grant generation stale"

authenticateGrant : Curve → Context → GrantAuth → M (Value × Value)
authenticateGrant c ctx ga = do
  guard c
  id ← grantId c ctx ga
  present ← memberMap "grants" id
  assert present "unknown grant"
  g ← lookup "grants" id
  validateGrantRecord g
  let scope = grantScope g
  (if number (scopeExpiresAt scope) ≡ᵇ 0 then return tt else (do
    beforeExpiry ← readTimeLess ctx (number (scopeExpiresAt scope))
    assert beforeExpiry "grant expired"))
  checkRP c scope
  return (id , g)
  where
  guard : Curve → M ⊤
  guard jubjub = requireSmallOrderFree (key (authorisation ga)) "grantee key has small order"
  guard k256 = do
    assert (envelope (authorisation ga) ≡ᵇ 0) "envelope not admitted for a spend grant"
    requireK256Key (key (authorisation ga))
  guard p256 = do
    originHash ← hash (b32 (pad 32 "midnight:account:grant:origin:v1") ∷
      ("Bytes<21>" , at 1 (policy (authorisation ga))) ∷ [])
    assert (equal originHash (origin ga)) "grant origin mismatch"
  checkRP : Curve → Value → M ⊤
  checkRP p256 scope = do
    commitment ← rpCommit (salt ga) (at 0 (policy (authorisation ga)))
    assert (equal commitment (scopeRPCommitment scope)) "grant RP mismatch"
  checkRP _ scope = return tt

checkCaller : Context → GrantAuth → Value → M ⊤
checkCaller ctx ga scope =
  if not (equal (scopeCallerCommitment scope) zero32) then (do
    caller ← readCaller ctx
    check caller) else return tt
  where
  check : Value → M ⊤
  check none = assert false "grant requires a contract caller"
  check (some (tuple (bool isContract ∷ address ∷ []))) = do
    assert isContract "grant requires a contract caller"
    commitment ← callerCommit (salt ga) (some address)
    assert (equal commitment (scopeCallerCommitment scope)) "grant caller mismatch"
  check _ = abort (decoding "kernel.caller")

scopeAllows : Operation → Value → Value
scopeAllows withdrawUnshielded = scopeWithdrawUnshielded
scopeAllows withdrawShielded = scopeWithdrawShielded
scopeAllows _ = scopeWithdrawShieldedToContract

thisKind : Operation → ℕ
thisKind withdrawUnshielded = 1
thisKind withdrawShielded = 2
thisKind _ = 3

amountOf : Operation → List Value → ℕ
amountOf withdrawUnshielded xs = number (get 1 xs)
amountOf _ xs = number (get 2 xs)

recipientOf : Operation → List Value → Value
recipientOf withdrawUnshielded xs = get 2 xs
recipientOf _ xs = get 0 xs

scopeCheck : Operation → Context → GrantAuth → List Value → Value → Value → M ℕ
scopeCheck op ctx ga xs coin g = do
  let scope = grantScope g
  assert (flag (scopeAllows op scope)) "operation not in scope"
  checkCaller ctx ga scope
  object ← objectCommit (salt ga) (if shielded op then at 1 coin else get 0 xs)
    (recipientKind ga) (pinnedRecipient ga) (nat (maxCoinValue ga))
  assert (equal object (scopeObjectCommitment scope)) "scope object mismatch"
  let amount = amountOf op xs
  assert (amount ≤ᵇ number (scopePerCallCap scope)) "amount above per-call cap"
  opening ← spentCommit (salt ga) (spentPrev ga)
  assert (equal opening (grantSpentCommitment g)) "spent opening mismatch"
  let wide = spentPrev ga + amount
  assert (wide ≤ᵇ number (scopeCap scope)) "cumulative cap exceeded"
  spent ← cast "new_spent" 128 wide
  assert ((number (recipientKind ga) ≡ᵇ 0) ∨
    ((number (recipientKind ga) ≡ᵇ thisKind op) ∧ equal (pinnedRecipient ga) (recipientOf op xs)))
    "recipient not admitted by pin"
  return spent

grantChallengeArgs : Operation → List Value → Value → GrantAuth → List Atom
grantChallengeArgs withdrawUnshielded xs coin ga =
  b32 (get 0 xs) ∷ u128 (get 1 xs) ∷ user (get 2 xs) ∷ []
grantChallengeArgs withdrawShielded xs coin ga =
  zswap (get 0 xs) ∷ b32 (get 1 xs) ∷ u128 (get 2 xs) ∷
  ("Bytes<192>" , changeEntry ga) ∷ b32 (encryptionKey ga) ∷ qualifiedAtom coin ∷ []
grantChallengeArgs _ xs coin ga =
  contract (get 0 xs) ∷ b32 (get 1 xs) ∷ u128 (get 2 xs) ∷
  ("Bytes<192>" , changeEntry ga) ∷ b32 (encryptionKey ga) ∷ qualifiedAtom coin ∷ []

settle : Curve → GrantAuth → Value → Value → Value → ℕ → M ⊤
settle c ga id g h spent = do
  verify c (authorisation ga) h "invalid grant signature"
  nonce ← cast "grant nonce" 64 (suc (number (grantNonce g)))
  commitment ← spentCommit (salt ga) spent
  -- Preserve epoch/gen/issued_at and the window/active/scope suffix; only
  -- nonce and spent_commit change in a successful grant settlement.
  insert "grants" id (tuple (take 3 (fields g) ++
    (nat nonce ∷ commitment ∷ drop 5 (fields g))))
  bump "round" 64

grantCall : Curve → Operation → Context → GrantAuth → List Value → M Value
grantCall c op ctx ga xs = do
  coin ← (if shielded op then held ctx (get 1 xs) else return none)
  (id , g) ← authenticateGrant c ctx ga
  spent ← scopeCheck op ctx ga xs coin g
  (if shielded op then (do
    assert (number (at 2 coin) ≤ᵇ maxCoinValue ga) "coin above max_coin_value"
    encryption ← read "enc_key"
    assert (equal (encryptionKey ga) encryption) "stale encryption key") else return tt)
  h ← challenge c true (operationName op) ctx (authorisation ga)
    (b32 id ∷ u64 (grantIssuedAt g) ∷ grantChallengeArgs op xs coin ga) (number (grantNonce g))
  settle c ga id g h spent
  result ← body op ctx xs coin none
  appendChange op result
  return result
  where
  hasChange : Value → Bool
  hasChange result = flag (at 0 result)
  appendChange : Operation → Value → M ⊤
  appendChange withdrawShielded result =
    if hasChange result then inboxAppend (changeEntry ga) else return tt
  appendChange withdrawToContract result =
    if hasChange (at 1 result) then inboxAppend (changeEntry ga) else return tt
  appendChange _ result = return tt

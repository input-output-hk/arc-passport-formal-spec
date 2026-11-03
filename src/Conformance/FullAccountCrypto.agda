{-# OPTIONS --safe --without-K #-}

-- Typed preimages and authentication for contracts/account.compact and
-- contracts/account-p256.compact at Passport fc19e471536f. The three curves
-- share the authorisation flow but retain their source-specific read/verify
-- order. Primitive cryptography is supplied by P, not proved in this module.

open import Conformance.FullAccountTypes

module Conformance.FullAccountCrypto (P : Primitives) where

open import Data.Bool.Base
open import Data.List.Base using (List; []; _∷_; _++_; map; take; drop)
open import Data.Nat.Base hiding (equal)
open import Data.Product.Base hiding (map)
open import Data.String.Base using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit.Base

b32 : Value → Atom
b32 v = "Bytes<32>" , v

u8 u32 u64 u128 fld jub : Value → Atom
u8 v = "Uint<8>" , v
u32 v = "Uint<32>" , v
u64 v = "Uint<64>" , v
u128 v = "Uint<128>" , v
fld v = "Field" , v
jub v = "JubjubPoint" , v

contract user zswap : Value → Atom
contract v = "ContractAddress" , v
user v = "UserAddress" , v
zswap v = "ZswapCoinPublicKey" , v

hash : List Atom → M Value
hash xs = lift (persistentHash P xs)

hashTag : String → M Value
hashTag tag = hash (("Bytes<64>" , pad 64 tag) ∷ [])

record Auth : Set where
  constructor auth
  field key : Value
        counter : ℕ
        sigR sigS : Value
        grind envelope : ℕ
        policy authenticator signature : Value
open Auth public

curveName : Curve → String
curveName jubjub = "jubjub"
curveName k256 = "k256"
curveName p256 = "p256"

armTag : Curve → String
armTag jubjub = "v1"
armTag k256 = "k1:v1"
armTag p256 = "r1:v1"

keyAtoms : Curve → Value → M (List Atom)
keyAtoms jubjub pk = return (jub pk ∷ [])
keyAtoms c pk = do
  (x , y) ← lift (pointCoordinates P c pk)
  return (b32 x ∷ b32 y ∷ [])

policyAtoms : Value → List Atom
policyAtoms policy = b32 (at 0 policy) ∷ ("Bytes<21>" , at 1 policy) ∷ []

identityOf : M Value
identityOf = lift (ecMulGenerator P jubjub 0)

requireSmallOrderFree : Value → String → M ⊤
requireSmallOrderFree pk message = do
  q ← lift (ecMul P jubjub pk 8)
  o ← identityOf
  assert (not (equal q o)) message

requireRecoveryKey : Value → M ⊤
requireRecoveryKey pk = do
  o ← identityOf
  assert (not (equal pk o)) "recovery key is the identity"
  requireSmallOrderFree pk "recovery key has small order"

requireK256Key : Value → M ⊤
requireK256Key pk = do
  (x , y) ← lift (pointCoordinates P k256 pk)
  assert (not (equal x zero32 ∧ equal y zero32)) "device key is the point at infinity"

entryAt : Curve → Value → Auth → ℕ → ℕ → M Value
entryAt jubjub addr a epoch count =
  hash (b32 (pad 32 "midnight:account:device:v1") ∷ contract addr ∷ jub (key a) ∷
    u32 (nat epoch) ∷ u64 (nat count) ∷ [])
entryAt k256 addr a epoch count = do
  ks ← keyAtoms k256 (key a)
  hash (b32 (pad 32 "midnight:account:device:k1:v2") ∷ contract addr ∷
    (ks ++ (u8 (nat (envelope a)) ∷ u32 (nat epoch) ∷ u64 (nat count) ∷ [])))
entryAt p256 addr a epoch count = do
  ks ← keyAtoms p256 (key a)
  hash (b32 (pad 32 "midnight:account:device:r1:v2") ∷ contract addr ∷
    (ks ++ policyAtoms (policy a) ++ (u32 (nat epoch) ∷ u64 (nat count) ∷ [])))

entry : Curve → Context → Auth → ℕ → ℕ → M Value
entry c ctx a epoch count = readSelf ctx >>= λ addr → entryAt c addr a epoch count

bootCommit : Curve → Auth → Value → M Value
bootCommit jubjub a salt = hash
  (b32 (pad 32 "midnight:account:boot:v1") ∷ b32 salt ∷ jub (key a) ∷ [])
bootCommit k256 a salt = do
  ks ← keyAtoms k256 (key a)
  hash (b32 (pad 32 "midnight:account:boot:k1:v2") ∷ b32 salt ∷
    (ks ++ (u8 (nat (envelope a)) ∷ [])))
bootCommit p256 a salt = do
  ks ← keyAtoms p256 (key a)
  hash (b32 (pad 32 "midnight:account:boot:r1:v2") ∷ b32 salt ∷
    (ks ++ policyAtoms (policy a)))

challengeAt : Curve → Bool → String → Value → Auth → List Atom → ℕ → M Value
challengeAt c grant operation addr a args nonce = do
  dst ← hashTag ("midnight:account:" ++ˢ (if grant then "grant:auth:" else "auth:")
    ++ˢ armTag c ++ˢ ":" ++ˢ operation)
  ks ← keyAtoms c (key a)
  hash (b32 dst ∷ contract addr ∷ (prefix c a ++ ks ++ args ++ suffix c a nonce))
  where
  prefix : Curve → Auth → List Atom
  prefix jubjub a = jub (sigR a) ∷ []
  prefix _ a = []
  suffix : Curve → Auth → ℕ → List Atom
  suffix jubjub a nonce = u64 (nat nonce) ∷ u64 (nat (grind a)) ∷ []
  suffix _ a nonce = u64 (nat nonce) ∷ []

challenge : Curve → Bool → String → Context → Auth → List Atom → ℕ → M Value
challenge c grant operation ctx a args nonce = do
  addr ← readSelf ctx
  challengeAt c grant operation addr a args nonce

schnorr : Value → Value → Value → Value → String → M ⊤
schnorr pk r s h message = do
  let c = le (rawBytes h)
  (if c <ᵇ fieldOrder then return tt else abort (bounds "Bytes<32> as Field" 255))
  lhs ← lift (ecMulGenerator P jubjub (number s % jubjubOrder))
  cp ← lift (ecMul P jubjub pk (c % jubjubOrder))
  rhs ← lift (ecAdd P jubjub r cp)
  assert (equal lhs rhs) message

envelopeDigest : ℕ → Value → M Value
envelopeDigest env h = do
  assert (env ≤ᵇ 1) "unknown envelope"
  plain ← hash (b32 h ∷ [])
  connector ← hash (("Bytes<27>" , pad 27 "midnight_signed_message:32:") ∷ b32 h ∷ [])
  return (if env ≡ᵇ 1 then connector else plain)

-- WebAuthn byte encoding and verification (account-p256.compact).
-- The arithmetic helpers are total on naturals: division by zero yields zero
-- and remainder by zero returns the dividend. Base64url only calls them with
-- positive constants 4, 16 and 64; these zero cases do not model Compact casts.
quotient remainder : ℕ → ℕ → ℕ
quotient n zero = 0
quotient n (suc d) = n / suc d
remainder n zero = n
remainder n (suc d) = n % suc d

b64char : ℕ → ℕ
b64char n = if n <ᵇ 26 then n + 65 else
  if n <ᵇ 52 then n + 71 else
  if n <ᵇ 62 then n ∸ 4 else
  if n ≡ᵇ 62 then 45 else 95

base64url : Bytes → Bytes
base64url (a ∷ b ∷ c ∷ rest) =
  b64char (quotient a 4) ∷
  b64char (remainder a 4 * 16 + quotient b 16) ∷
  b64char (remainder b 16 * 4 + quotient c 64) ∷
  b64char (remainder c 64) ∷ base64url rest
base64url (a ∷ b ∷ []) =
  b64char (quotient a 4) ∷ b64char (remainder a 4 * 16 + quotient b 16) ∷
  b64char (remainder b 16 * 4) ∷ []
base64url (a ∷ []) = b64char (quotient a 4) ∷ b64char (remainder a 4 * 16) ∷ []
base64url [] = []

checkOrigin : Bytes → M ⊤
checkOrigin [] = return tt
checkOrigin (b ∷ bs) = do
  assert ((33 ≤ᵇ b) ∧ (b ≤ᵇ 126) ∧ not (b ≡ᵇ 34) ∧ not (b ≡ᵇ 92)) "invalid origin bytes"
  checkOrigin bs

webAuthn : Auth → Value → String → M ⊤
webAuthn a h message = do
  let ad = rawBytes (authenticator a)
  assert (equal (bytes (take 32 ad)) (at 0 (policy a))) "WebAuthn RP mismatch"
  let flags = numberAt32 ad
  assert ((flags ≡ᵇ 5) ∨ (flags ≡ᵇ 13) ∨ (flags ≡ᵇ 29)) "WebAuthn flags require UP and UV"
  let origin = at 1 (policy a)
  checkOrigin (rawBytes origin)
  clientHash ← hash
    (("Bytes<36>" , pad 36 "{\"type\":\"webauthn.get\",\"challenge\":\"") ∷
     ("Bytes<43>" , bytes (base64url (rawBytes h))) ∷
     ("Bytes<12>" , pad 12 "\",\"origin\":\"") ∷ ("Bytes<21>" , origin) ∷
     ("Bytes<22>" , pad 22 "\",\"crossOrigin\":false}") ∷ [])
  digest ← hash (("Bytes<37>" , authenticator a) ∷ b32 clientHash ∷ [])
  assert (not (number (at 0 (signature a)) ≡ᵇ 0)) "zero ECDSA r"
  assert (not (number (at 1 (signature a)) ≡ᵇ 0)) "zero ECDSA s"
  valid ← lift (ecdsaVerify P p256 digest (signature a) (key a))
  assert valid message
  where
  numberAt32 : Bytes → ℕ
  numberAt32 bs with drop 32 bs
  ... | [] = 0
  ... | b ∷ _ = b

-- Return to the shared authentication flow: curve-specific verification,
-- followed by device rolling in the source-specified order below.
verify : Curve → Auth → Value → String → M ⊤
verify jubjub a h message = schnorr (key a) (sigR a) (sigS a) h message
verify k256 a h message = do
  digest ← envelopeDigest (envelope a) h
  valid ← lift (ecdsaVerify P k256 digest (signature a) (key a))
  assert valid message
verify p256 a h message = webAuthn a h message

keyGuard : Curve → Value → String → M ⊤
keyGuard jubjub pk message = requireSmallOrderFree pk message
keyGuard k256 pk message = requireK256Key pk
keyGuard p256 pk message = return tt

roll : Curve → Context → Auth → Value → M Value
roll c ctx a old = do
  exclude "devices" old
  addr ← readSelf ctx
  epoch ← readCount "device_epoch"
  nextCounter ← cast "use_counter" 64 (suc (counter a))
  next ← entryAt c addr a epoch nextCounter
  include "devices" next
  return next

authorise : Curve → Context → Auth → Value → M Value
authorise c ctx a h = do
  keyGuard c (key a) "device key has small order"
  addr ← readSelf ctx
  epoch ← readCount "device_epoch"
  old ← entryAt c addr a epoch (counter a)
  known ← has "devices" old
  assert known "unknown device entry"
  next ← ordered c old
  bump "auth_nonce" 64
  bump "round" 64
  return next
  where
  ordered : Curve → Value → M Value
  ordered p256 old = do
    verify p256 a h "invalid WebAuthn signature"
    roll p256 ctx a old
  ordered c old = do
    next ← roll c ctx a old
    verify c a h "invalid signature"
    return next

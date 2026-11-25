{-# OPTIONS --safe --without-K #-}

-- Atom order is the source preimage order, not a type-tagged wire format.
-- Source map and domain literals: docs/commitment-binding-audit.md.
module Conformance.CommitmentLayouts where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_)
open import Data.String.Base using (String)

open import Conformance.CommitmentEncoding
open import Conformance.FullAccountTypes using (Curve; jubjub; k256; p256; Primitives)
import Conformance.FullAccountBody

b32 b21 b64 b192 u8 u32 u64 u128 booleanAtom fieldAtom contract user zswap jub coin qualifiedCoin : String × Shape
b32 = "Bytes<32>" , octets 32
b21 = "Bytes<21>" , octets 21
b64 = "Bytes<64>" , octets 64
b192 = "Bytes<192>" , octets 192
u8 = "Uint<8>" , uint 1
u32 = "Uint<32>" , uint 4
u64 = "Uint<64>" , uint 8
u128 = "Uint<128>" , uint 16
booleanAtom = "Boolean" , boolean
fieldAtom = "Field" , fieldElement
contract = "ContractAddress" , octets 32
user = "UserAddress" , octets 32
zswap = "ZswapCoinPublicKey" , octets 32
jub = "JubjubPoint" , structure (fieldElement ∷ fieldElement ∷ [])
coin = "ShieldedCoinInfo" , structure (octets 32 ∷ octets 32 ∷ uint 16 ∷ [])
qualifiedCoin = "QualifiedShieldedCoinInfo" , structure (octets 32 ∷ octets 32 ∷ uint 16 ∷ uint 8 ∷ [])

keyLayout : Curve → Layout
keyLayout jubjub = jub ∷ []
keyLayout k256 = b32 ∷ b32 ∷ []
keyLayout p256 = b32 ∷ b32 ∷ []

policyLayout : Curve → Layout
policyLayout jubjub = []
policyLayout k256 = u8 ∷ []
policyLayout p256 = b32 ∷ b21 ∷ []

data Commitment : Set where
  device bootstrap grantIdentifier : Curve → Commitment
  object spent presentCaller relyingParty origin scope recoverySubmit : Commitment

commitmentLayout : Commitment → Layout
commitmentLayout (device c) = b32 ∷ contract ∷ (keyLayout c ++ policyLayout c ++ (u32 ∷ u64 ∷ []))
commitmentLayout (bootstrap c) = b32 ∷ b32 ∷ (keyLayout c ++ policyLayout c)
commitmentLayout (grantIdentifier jubjub) = b32 ∷ contract ∷ jub ∷ b32 ∷ u8 ∷ []
commitmentLayout (grantIdentifier k256) = b32 ∷ contract ∷ b32 ∷ b32 ∷ u8 ∷ b32 ∷ u8 ∷ []
commitmentLayout (grantIdentifier p256) = b32 ∷ contract ∷ b32 ∷ b32 ∷ b32 ∷ u8 ∷ []
commitmentLayout object = b32 ∷ b32 ∷ b32 ∷ u8 ∷ b32 ∷ u128 ∷ []
commitmentLayout spent = b32 ∷ b32 ∷ u128 ∷ []
commitmentLayout presentCaller = b32 ∷ b32 ∷ contract ∷ []
commitmentLayout relyingParty = b32 ∷ b32 ∷ b32 ∷ []
commitmentLayout origin = b32 ∷ b21 ∷ []
commitmentLayout scope = b32 ∷ b32 ∷ booleanAtom ∷ booleanAtom ∷ booleanAtom ∷ booleanAtom ∷
  b32 ∷ u8 ∷ b32 ∷ u128 ∷ u128 ∷ u128 ∷ u64 ∷ b32 ∷ b32 ∷ u64 ∷ u128 ∷ b32 ∷ []
commitmentLayout recoverySubmit = b32 ∷ contract ∷ jub ∷ jub ∷ jub ∷ jub ∷ jub ∷ u32 ∷ u64 ∷ u64 ∷ u64 ∷ []

-- Operation is the existing source enumeration; no second operation convention.
module Challenges (P : Primitives) where
  open Conformance.FullAccountBody P using (Operation; withdrawUnshielded; withdrawShielded; withdrawToContract;
    appendInbox; rotateEncKey; addDevice; removeDevice; issueGrant; revokeGrant; revokeAllGrants; publishRecovery; cancelRecovery)

  operationLayout : Operation → Layout
  operationLayout withdrawUnshielded = b32 ∷ u128 ∷ user ∷ []
  operationLayout withdrawShielded = zswap ∷ b32 ∷ u128 ∷ qualifiedCoin ∷ []
  operationLayout withdrawToContract = contract ∷ b32 ∷ u128 ∷ qualifiedCoin ∷ []
  operationLayout appendInbox = b192 ∷ []
  operationLayout rotateEncKey = b32 ∷ []
  operationLayout addDevice = b32 ∷ []
  operationLayout removeDevice = b32 ∷ []
  operationLayout issueGrant = b32 ∷ b32 ∷ []
  operationLayout revokeGrant = b32 ∷ []
  operationLayout revokeAllGrants = []
  operationLayout publishRecovery = jub ∷ b32 ∷ fieldAtom ∷ fieldAtom ∷ fieldAtom ∷ fieldAtom ∷ u8 ∷ b64 ∷ []
  operationLayout cancelRecovery = []

  challengeLayout : Curve → Layout → Layout
  challengeLayout jubjub args = b32 ∷ contract ∷ jub ∷ (keyLayout jubjub ++ args ++ (u64 ∷ u64 ∷ []))
  challengeLayout k256 args = b32 ∷ contract ∷ (keyLayout k256 ++ args ++ (u64 ∷ []))
  challengeLayout p256 args = b32 ∷ contract ∷ (keyLayout p256 ++ args ++ (u64 ∷ []))

  deviceChallengeLayout : Curve → Operation → Layout
  deviceChallengeLayout c op = challengeLayout c (operationLayout op)

  -- Only these three operations have grant-authorized source calls.
  data GrantOperation : Set where
    unshielded shielded toContract : GrantOperation

  grantOperationLayout : GrantOperation → Layout
  grantOperationLayout unshielded = b32 ∷ u64 ∷ b32 ∷ u128 ∷ user ∷ []
  grantOperationLayout shielded = b32 ∷ u64 ∷ zswap ∷ b32 ∷ u128 ∷ b192 ∷ b32 ∷ qualifiedCoin ∷ []
  grantOperationLayout toContract = b32 ∷ u64 ∷ contract ∷ b32 ∷ u128 ∷ b192 ∷ b32 ∷ qualifiedCoin ∷ []

  grantChallengeLayout : Curve → GrantOperation → Layout
  grantChallengeLayout c op = challengeLayout c (grantOperationLayout op)

{-# OPTIONS --safe --without-K #-}

-- The cryptographic surface the account model consumes, abstract here and bound to the
-- implementation's compiled pure circuits / compact-runtime in Conformance.Main.
-- Argument orders follow `contract/contracts/account.compact` at Passport `5d12798`;
-- every challenge takes `(self, sig_r, pk, …, nonce, grind)` except `challengeSubmit`.
module Conformance.Primitives where

open import Data.Nat.Base
open import Relation.Binary.Definitions using (DecidableEquality)

-- JubJub prime-order subgroup order r_J (MIP-0013 §2).
jubjubOrder : ℕ
jubjubOrder = 0x0e7db4ea6533afa906673b0101343b00a6682093ccc81082d0970e5ed6f72cb7

-- BLS12-381 scalar field modulus: `Bytes<32> as Field` aborts on a little-endian value ≥ q.
fieldOrder : ℕ
fieldOrder = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

record Primitives : Set₁ where
  field Bytes32 Bytes64 Point : Set
        _≟ᴮ_ : DecidableEquality Bytes32
        _≟ᵂ_ : DecidableEquality Bytes64
        _≟ᴾ_ : DecidableEquality Point
        -- pad(32, "")
        zero32 : Bytes32
        -- derive_device_entry_with_jubjub(self, pk, epoch, counter)
        deviceEntry : Bytes32 → Point → ℕ → ℕ → Bytes32
        -- challenge_withdraw_unshielded_with_jubjub(…, color, amount, recipient, …)
        challengeWithdraw : Bytes32 → Point → Point → Bytes32 → ℕ → Bytes32 → ℕ → ℕ → Bytes32
        -- challenge_{add,remove}_device_with_jubjub(…, entry, …), challenge_rotate_enc_key_with_jubjub(…, new_key, …)
        challengeAddDevice challengeRemoveDevice challengeRotateEncKey : Bytes32 → Point → Point → Bytes32 → ℕ → ℕ → Bytes32
        -- challenge_publish_recovery_session_with_jubjub(…, new_recovery_pk, session_nonce, phi_1..4, phi_len, wrap, …)
        challengePublish : Bytes32 → Point → Point → Point → Bytes32 → ℕ → ℕ → ℕ → ℕ → ℕ → Bytes64 → ℕ → ℕ → Bytes32
        -- challenge_recover_cancel_with_jubjub(…)
        challengeCancel : Bytes32 → Point → Point → ℕ → ℕ → Bytes32
        -- challenge_recover_submit(self, recovery_key, sig_r_recovery, successor_pk, sig_r_successor,
        --   successor_recovery_pk, post_epoch, nonce, now_upper, grind)
        challengeSubmit : Bytes32 → Point → Point → Point → Point → Point → ℕ → ℕ → ℕ → ℕ → Bytes32
        ecMulG : ℕ → Point
        ecMul : Point → ℕ → Point
        ecAdd : Point → Point → Point
        -- Little-endian reading of a 32-byte hash (the `Bytes<32> as Field` cast below r_J).
        le : Bytes32 → ℕ

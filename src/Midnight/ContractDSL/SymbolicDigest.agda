{-# OPTIONS --safe --without-K #-}

module Midnight.ContractDSL.SymbolicDigest where

open import Data.Nat.Base
open import Data.Nat.Properties using (_≟_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- Domain-separated mathematical symbols, not persistentHash byte encodings
-- or a cryptographic preimage-security assumption.
data Digest : Set where
  lockKey : ℕ → ℕ → Digest
  merkleLeaf : ℕ → Digest
  merkleBranch : Digest → Digest → Digest

publicKey : ℕ → ℕ → Digest
publicKey = lockKey

digestEq : (x y : Digest) → Dec (x ≡ y)
digestEq (lockKey r k) (lockKey r′ k′) with r ≟ r′ | k ≟ k′
... | yes refl | yes refl = yes refl
... | no neq | _ = no (λ { refl → neq refl })
... | _ | no neq = no (λ { refl → neq refl })
digestEq (lockKey _ _) (merkleLeaf _) = no (λ ())
digestEq (lockKey _ _) (merkleBranch _ _) = no (λ ())
digestEq (merkleLeaf _) (lockKey _ _) = no (λ ())
digestEq (merkleBranch _ _) (lockKey _ _) = no (λ ())
digestEq (merkleLeaf x) (merkleLeaf y) with x ≟ y
... | yes refl = yes refl
... | no neq = no (λ { refl → neq refl })
digestEq (merkleLeaf _) (merkleBranch _ _) = no (λ ())
digestEq (merkleBranch _ _) (merkleLeaf _) = no (λ ())
digestEq (merkleBranch l r) (merkleBranch l′ r′) with digestEq l l′ | digestEq r r′
... | yes refl | yes refl = yes refl
... | no neq | _ = no (λ { refl → neq refl })
... | _ | no neq = no (λ { refl → neq refl })

emptyRoot : ℕ → Digest
emptyRoot zero = merkleLeaf 0
emptyRoot (suc n) = merkleBranch (emptyRoot n) (emptyRoot n)

padRoot : ℕ → ℕ → Digest → Digest
padRoot zero h r = r
padRoot (suc n) h r = padRoot n (suc h) (merkleBranch r (emptyRoot h))

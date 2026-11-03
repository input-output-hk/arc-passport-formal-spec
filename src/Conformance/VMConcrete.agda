{-# OPTIONS --safe --without-K #-}

-- Canonical little-endian atoms are represented by their natural number and
-- atom alignment (0 = field, 1 = compress, n + 2 = Bytes[n]). The account uses
-- atom alignments, not alignment-option branches. The transport rejects those.
-- Serialization sizes follow midnight-ledger base-crypto/src/fab/serialize.rs;
-- identifying that source interpretation with installed WASM remains trusted.
module Conformance.VMConcrete where

open import Data.Bool.Base
open import Data.List.Base using (List; []; _∷_; _++_; length; foldr)
import Data.List.Properties as List
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base
open import Data.Nat.DivMod using (_/_)
open import Data.Nat.Properties using (_≟_)
open import Data.Product.Base
import Data.Product.Properties as Product
open import Relation.Binary.PropositionalEquality

open import Conformance.VM

Aligned : Set
Aligned = List ℕ × List ℕ

natural : Aligned → Maybe ℕ
natural (n ∷ [] , _) = just n
natural _ = nothing

boolean : Aligned → Maybe Bool
boolean (0 ∷ [] , _) = just false
boolean (1 ∷ [] , _) = just true
boolean _ = nothing

truth : Aligned → Bool
truth (0 ∷ [] , _) = false
truth _ = true

fromNat : ℕ → Aligned
fromNat n = n ∷ [] , 10 ∷ []

fromByte : ℕ → Aligned
fromByte n = n ∷ [] , 3 ∷ []

fromBool : Bool → Aligned
fromBool false = fromByte 0
fromBool true = fromByte 1

flaggedSize : ℕ → ℕ
flaggedSize n = if n <ᵇ 32 then 1 else if n <ᵇ 4096 then 2 else if n <ᵇ 524288 then 3 else 1000

-- Repeated byte division takes at most n steps. Numeric fuel avoids building
-- the standard logarithm's unary accessibility witness for a 256-bit integer.
byteLength : ℕ → ℕ
byteLength n = go n n
  where
  go : ℕ → ℕ → ℕ
  go zero _ = 0
  go (suc fuel) zero = 0
  go (suc fuel) (suc n) = suc (go fuel (suc n / 256))

wordSize : ℕ → ℕ
wordSize n = if (0 <ᵇ n) ∧ (n <ᵇ 32) then 1 else flaggedSize (byteLength n) + byteLength n

alignmentSize : ℕ → ℕ
alignmentSize zero = 1
alignmentSize (suc zero) = 1
alignmentSize (suc (suc n)) = flaggedSize n

sequenceSize : (ℕ → ℕ) → List ℕ → ℕ
sequenceSize f (n ∷ []) = f n
sequenceSize f ns = flaggedSize (length ns) + foldr (λ n sum → f n + sum) 0 ns

byteSize : Aligned → ℕ
byteSize (words , alignments) = sequenceSize wordSize words + sequenceSize alignmentSize alignments

concatenate : Aligned → Aligned → Maybe Aligned
concatenate (a , aa) (b , ba) = just (a ++ b , aa ++ ba)

atoms : Atoms
atoms = record
  { Aligned = Aligned
  ; _≟ᴬ_ = Product.≡-dec (List.≡-dec _≟_) (List.≡-dec _≟_)
  ; natural = natural ; boolean = boolean ; truth = truth
  ; fromNat = fromNat ; fromByte = fromByte ; fromBool = fromBool
  ; empty = [] , [] ; byteSize = byteSize ; cellBound = 32768
  ; concatenate = concatenate ; natural-roundtrip = λ n → refl
  ; boolean-roundtrip = λ { false → refl ; true → refl } }

module VM = Machine atoms

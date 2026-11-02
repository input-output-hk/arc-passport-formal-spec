{-# OPTIONS --safe --without-K #-}

-- Trusted pure primitive boundary. External adapters must validate every reply:
-- digest replies are lowercase hex32; point replies are exactly two naturals.
open import Data.String.Base using (String)

module Conformance.Oracle (backend : String → String) where

open import Data.Bool.Base using (if_then_else_)
import Data.Char.Base as Char
open import Data.List.Base using (List; []; _∷_) renaming (_++_ to _++ˡ_)
open import Data.Maybe.Base using (fromMaybe)
open import Data.Nat.Base
open import Data.Nat.Properties using (_≟_)
open import Data.Nat.Show using (show; readMaybe)
open import Data.Product.Base
import Data.Product.Properties as ΣP
open import Data.String.Base using (words; unwords; toList)
import Data.String.Properties as String
open import Function.Base using (_∘_)

open import Conformance.Primitives

nat : String → ℕ
nat = fromMaybe 0 ∘ readMaybe 10

decodePoint : String → ℕ × ℕ
decodePoint s with words s
... | x ∷ y ∷ _ = nat x , nat y
... | _ = 0 , 0

ask : List String → String
ask = backend ∘ unwords

hexDigit : Char.Char → ℕ
hexDigit c = let n = Char.toℕ c in if n <ᵇ 58 then n ∸ 48 else n ∸ 87

leBytes : List Char.Char → ℕ
leBytes (h ∷ l ∷ rest) = 16 * hexDigit h + hexDigit l + 256 * leBytes rest
leBytes _ = 0

pt : ℕ × ℕ → List String
pt (x , y) = show x ∷ show y ∷ []

-- Byte strings travel as lowercase hex, points as decimal affine coordinates.
primitives : Primitives
primitives = record
  { Bytes32 = String ; Bytes64 = String ; Point = ℕ × ℕ
  ; _≟ᴮ_ = String._≟_ ; _≟ᵂ_ = String._≟_ ; _≟ᴾ_ = ΣP.≡-dec _≟_ _≟_
  ; zero32 = "0000000000000000000000000000000000000000000000000000000000000000"
  ; deviceEntry = λ self pk e c → ask ("entry" ∷ self ∷ pt pk ++ˡ show e ∷ show c ∷ [])
  ; challengeWithdraw = λ self R pk color a rcpt n g →
      ask ("chal-w" ∷ self ∷ pt R ++ˡ pt pk ++ˡ color ∷ show a ∷ rcpt ∷ show n ∷ show g ∷ [])
  ; challengeAddDevice = gated "chal-add"
  ; challengeRemoveDevice = gated "chal-rm"
  ; challengeRotateEncKey = gated "chal-rot"
  ; challengePublish = λ self R pk q sess φ₁ φ₂ φ₃ φ₄ len w n g →
      ask ("chal-pub" ∷ self ∷ pt R ++ˡ pt pk ++ˡ pt q ++ˡ sess ∷ show φ₁ ∷ show φ₂ ∷ show φ₃ ∷ show φ₄ ∷ show len ∷ w ∷ show n ∷ show g ∷ [])
  ; challengeCancel = λ self R pk n g → ask ("chal-cancel" ∷ self ∷ pt R ++ˡ pt pk ++ˡ show n ∷ show g ∷ [])
  ; challengeSubmit = λ self rpk Rᵣ q Rₛ q′ e n u g →
      ask ("chal-submit" ∷ self ∷ pt rpk ++ˡ pt Rᵣ ++ˡ pt q ++ˡ pt Rₛ ++ˡ pt q′ ++ˡ show e ∷ show n ∷ show u ∷ show g ∷ [])
  ; ecMulG = λ k → decodePoint (ask ("mulg" ∷ show k ∷ []))
  ; ecMul = λ p k → decodePoint (ask ("mul" ∷ pt p ++ˡ show k ∷ []))
  ; ecAdd = λ p q → decodePoint (ask ("add" ∷ pt p ++ˡ pt q))
  ; le = leBytes ∘ toList }
  where
  gated : String → String → ℕ × ℕ → ℕ × ℕ → String → ℕ → ℕ → String
  gated op self R pk x n g = ask (op ∷ self ∷ pt R ++ˡ pt pk ++ˡ x ∷ show n ∷ show g ∷ [])


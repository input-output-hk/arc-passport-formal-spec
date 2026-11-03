{-# OPTIONS --safe --without-K #-}

-- Typed ABI/collection representation relations used by VMProperties.
-- Keys have one declared ABI type: Uint8 and Boolean may share concrete bytes,
-- so cross-type injectivity would be a false encoding assumption.
module Conformance.VMAccount where

open import Data.Bool.Base
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; suc; _+_)
open import Data.Product.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (does)

import Conformance.FullAccountTypes as Account
open import Conformance.VM

module Representation (A : Atoms) where
  open Atoms A hiding (empty)
  module M = Machine A

  record AtomEncoding : Set₁ where
    field Key : Set
          keyValue : Key → Account.Value
          encodeKey : Key → Aligned
          encodeValue : Account.Value → Aligned
          equality : ∀ x y → does (encodeKey x ≟ᴬ encodeKey y) ≡ Account.equal (keyValue x) (keyValue y)

  module Encoded (E : AtomEncoding) where
    open AtomEncoding E

    data MapEntries : List Account.Value → List (Aligned × M.Value) → Set where
      empty : MapEntries [] []
      entry : ∀ {k v xs ys} → MapEntries xs ys →
        MapEntries (Account.tuple (keyValue k ∷ v ∷ []) ∷ xs) ((encodeKey k , M.cell (encodeValue v)) ∷ ys)

    data SetEntries : List Account.Value → List (Aligned × M.Value) → Set where
      empty : SetEntries [] []
      entry : ∀ {k xs ys} → SetEntries xs ys → SetEntries (keyValue k ∷ xs) ((encodeKey k , M.null) ∷ ys)

    -- VM.prepare advances by suc (pc + skip); a non-branching opcode has skip=0.
    -- Retaining this form keeps the local opcode statements definitionally aligned.
    nextPC : ℕ → ℕ
    nextPC pc = suc (pc + 0)

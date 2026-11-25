{-# OPTIONS --safe --without-K #-}

-- Fixed-width recipes of independent-hash.ts, over the existing source Values.
-- Canonical is an input condition, not a claim that arbitrary primitive calls
-- or native point representations satisfy it. See docs/commitment-binding-audit.md.
module Conformance.CommitmentEncoding where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_; length; take; drop; map)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat.Base
open import Data.Product.Base using (_×_; _,_)
open import Data.String.Base using (String)
open import Relation.Binary.PropositionalEquality

open import Conformance.FullAccountTypes using (Value; nat; bool; bytes; tuple; Bytes; Atom; fieldOrder; le; rawBytes; number; flag; fields)

data Shape : Set where
  octets uint : ℕ → Shape
  boolean fieldElement : Shape
  structure : List Shape → Shape

mutual
  width : Shape → ℕ
  width (octets n) = n
  width (uint n) = n
  width boolean = 1
  width fieldElement = 32
  width (structure ss) = widths ss

  widths : List Shape → ℕ
  widths [] = 0
  widths (s ∷ ss) = width s + widths ss

mutual
  data Canonical : Shape → Value → Set where
    octetValue : ∀ {n bs} → length bs ≡ n → All (_< 256) bs → Canonical (octets n) (bytes bs)
    uintValue : ∀ {n x} → x < 256 ^ n → Canonical (uint n) (nat x)
    booleanValue : ∀ b → Canonical boolean (bool b)
    fieldValue : ∀ {x} → x < fieldOrder → Canonical fieldElement (nat x)
    structureValue : ∀ {ss vs} → CanonicalValues ss vs → Canonical (structure ss) (tuple vs)

  data CanonicalValues : List Shape → List Value → Set where
    [] : CanonicalValues [] []
    _∷_ : ∀ {s ss v vs} → Canonical s v → CanonicalValues ss vs → CanonicalValues (s ∷ ss) (v ∷ vs)

littleEndian : ℕ → ℕ → Bytes
littleEndian zero x = []
littleEndian (suc n) x = x % 256 ∷ littleEndian n (x / 256)

mutual
  encodeValue : Shape → Value → Bytes
  encodeValue (octets n) v = rawBytes v
  encodeValue (uint n) v = littleEndian n (number v)
  encodeValue boolean v = (if flag v then 1 else 0) ∷ []
  encodeValue fieldElement v = littleEndian 32 (number v)
  encodeValue (structure ss) v = encodeValues ss (fields v)

  encodeValues : List Shape → List Value → Bytes
  encodeValues [] vs = []
  encodeValues (s ∷ ss) [] = []
  encodeValues (s ∷ ss) (v ∷ vs) = encodeValue s v ++ encodeValues ss vs

mutual
  decodeValue : Shape → Bytes → Value
  decodeValue (octets n) bs = bytes bs
  decodeValue (uint n) bs = nat (le bs)
  decodeValue boolean bs = bool (le bs ≡ᵇ 1)
  decodeValue fieldElement bs = nat (le bs)
  decodeValue (structure ss) bs = tuple (decodeValues ss bs)

  decodeValues : List Shape → Bytes → List Value
  decodeValues [] bs = []
  decodeValues (s ∷ ss) bs = decodeValue s (take (width s) bs) ∷ decodeValues ss (drop (width s) bs)

Layout : Set
Layout = List (String × Shape)

data CanonicalAtoms : Layout → List Atom → Set where
  [] : CanonicalAtoms [] []
  _∷_ : ∀ {name s ss v vs} → Canonical s v → CanonicalAtoms ss vs →
    CanonicalAtoms ((name , s) ∷ ss) ((name , v) ∷ vs)

encodeAtoms : Layout → List Atom → Bytes
encodeAtoms [] vs = []
encodeAtoms (s ∷ ss) [] = []
encodeAtoms ((name , s) ∷ ss) ((label , v) ∷ vs) = encodeValue s v ++ encodeAtoms ss vs

decodeAtoms : Layout → Bytes → List Atom
decodeAtoms [] bs = []
decodeAtoms ((name , s) ∷ ss) bs = (name , decodeValue s (take (width s) bs)) ∷ decodeAtoms ss (drop (width s) bs)

{-# OPTIONS --safe --without-K #-}

module Conformance.CommitmentEncodingProof where

open import Data.Bool.Base using (false; true)
open import Data.List.Base using (List; []; _∷_; _++_; length; take; drop)
open import Data.List.Properties using (length-++; ++-identityʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.Nat.Base
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality

open import Conformance.FullAccountTypes using (Value; nat; bool; bytes; tuple; Bytes; Atom; fieldOrder; le)
open import Conformance.CommitmentEncoding

private variable
  n x : ℕ
  s : Shape
  ss : List Shape
  v : Value
  vs : List Value
  layout : Layout
  atoms other : List Atom

field-fits : fieldOrder ≤ 256 ^ 32
field-fits = ≤ᵇ⇒≤ fieldOrder (256 ^ 32) tt

littleEndian-length : ∀ n x → length (littleEndian n x) ≡ n
littleEndian-length zero x = refl
littleEndian-length (suc n) x = cong suc (littleEndian-length n (x / 256))

littleEndian-octets : ∀ n x → All (_< 256) (littleEndian n x)
littleEndian-octets zero x = []
littleEndian-octets (suc n) x = m%n<n x 256 ∷ littleEndian-octets n (x / 256)

littleEndian-roundtrip : x < 256 ^ n → le (littleEndian n x) ≡ x
littleEndian-roundtrip {x = zero} {n = zero} bound = refl
littleEndian-roundtrip {x = suc x} {n = zero} (s≤s ())
littleEndian-roundtrip {x = x} {n = suc n} bound = trans
  (cong (λ q → x % 256 + 256 * q)
    (littleEndian-roundtrip {n = n} (m<n*o⇒m/o<n (subst (x <_) (*-comm 256 (256 ^ n)) bound))))
  (trans (cong (x % 256 +_) (*-comm 256 (x / 256))) (sym (m≡m%n+[m/n]*n x 256)))

cut-prefix : ∀ (xs ys : Bytes) → take (length xs) (xs ++ ys) ≡ xs
cut-prefix [] ys = refl
cut-prefix (x ∷ xs) ys = cong (x ∷_) (cut-prefix xs ys)

cut-suffix : ∀ (xs ys : Bytes) → drop (length xs) (xs ++ ys) ≡ ys
cut-suffix [] ys = refl
cut-suffix (x ∷ xs) ys = cut-suffix xs ys

mutual
  encoded-length : Canonical s v → length (encodeValue s v) ≡ width s
  encoded-length (octetValue len valid) = len
  encoded-length (uintValue {n} {x} bound) = littleEndian-length n x
  encoded-length (booleanValue false) = refl
  encoded-length (booleanValue true) = refl
  encoded-length (fieldValue {x} bound) = littleEndian-length 32 x
  encoded-length (structureValue valid) = encoded-values-length valid

  encoded-values-length : CanonicalValues ss vs → length (encodeValues ss vs) ≡ widths ss
  encoded-values-length [] = refl
  encoded-values-length (_∷_ {s} {ss} {v} {vs} valid rest) = trans
    (length-++ (encodeValue s v))
    (cong₂ _+_ (encoded-length valid) (encoded-values-length rest))

mutual
  value-roundtrip : Canonical s v → decodeValue s (encodeValue s v) ≡ v
  value-roundtrip (octetValue len valid) = refl
  value-roundtrip (uintValue {n} bound) = cong nat (littleEndian-roundtrip {n = n} bound)
  value-roundtrip (booleanValue false) = refl
  value-roundtrip (booleanValue true) = refl
  value-roundtrip (fieldValue bound) = cong nat (littleEndian-roundtrip {n = 32} (<-≤-trans bound field-fits))
  value-roundtrip (structureValue valid) = cong tuple (values-roundtrip valid)

  values-roundtrip : CanonicalValues ss vs → decodeValues ss (encodeValues ss vs) ≡ vs
  values-roundtrip [] = refl
  values-roundtrip (_∷_ {s} {ss} {v} {vs} valid rest)
    rewrite sym (encoded-length valid)
      | cut-prefix (encodeValue s v) (encodeValues ss vs)
      | cut-suffix (encodeValue s v) (encodeValues ss vs)
      | value-roundtrip valid | values-roundtrip rest = refl

atoms-roundtrip : CanonicalAtoms layout atoms → decodeAtoms layout (encodeAtoms layout atoms) ≡ atoms
atoms-roundtrip [] = refl
atoms-roundtrip (_∷_ {name} {s} {ss} {v} {vs} valid rest)
  rewrite sym (encoded-length valid)
    | cut-prefix (encodeValue s v) (encodeAtoms ss vs)
    | cut-suffix (encodeValue s v) (encodeAtoms ss vs)
    | value-roundtrip valid | atoms-roundtrip rest = refl

atoms-injective : CanonicalAtoms layout atoms → CanonicalAtoms layout other →
  encodeAtoms layout atoms ≡ encodeAtoms layout other → atoms ≡ other
atoms-injective {layout = layout} left right same = trans (sym (atoms-roundtrip left))
  (trans (cong (decodeAtoms layout) same) (atoms-roundtrip right))

atoms-distinct : CanonicalAtoms layout atoms → CanonicalAtoms layout other →
  atoms ≢ other → encodeAtoms layout atoms ≢ encodeAtoms layout other
atoms-distinct left right different same = different (atoms-injective left right same)

value-injective : ∀ {a b} → Canonical s a → Canonical s b →
  encodeValue s a ≡ encodeValue s b → a ≡ b
value-injective {s = s} left right same = trans (sym (value-roundtrip left))
  (trans (cong (decodeValue s) same) (value-roundtrip right))

mutual
  encoded-octets : Canonical s v → All (_< 256) (encodeValue s v)
  encoded-octets (octetValue len valid) = valid
  encoded-octets (uintValue {n} {x} bound) = littleEndian-octets n x
  encoded-octets (booleanValue false) = s≤s z≤n ∷ []
  encoded-octets (booleanValue true) = s≤s (s≤s z≤n) ∷ []
  encoded-octets (fieldValue {x} bound) = littleEndian-octets 32 x
  encoded-octets (structureValue valid) = encoded-values-octets valid

  encoded-values-octets : CanonicalValues ss vs → All (_< 256) (encodeValues ss vs)
  encoded-values-octets [] = []
  encoded-values-octets (valid ∷ rest) = All.++⁺ (encoded-octets valid) (encoded-values-octets rest)

atoms-octets : CanonicalAtoms layout atoms → All (_< 256) (encodeAtoms layout atoms)
atoms-octets [] = []
atoms-octets (valid ∷ rest) = All.++⁺ (encoded-octets valid) (atoms-octets rest)

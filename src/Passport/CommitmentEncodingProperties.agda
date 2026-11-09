{-# OPTIONS --safe --without-K #-}

-- Canonical typed preimages, not hash outputs, are distinguished here.
-- Read CommitmentEncoding.Canonical for exact widths/bounds and
-- CommitmentLayouts for the audited source field order. Native codec
-- correspondence and source admission of these conditions remain obligations.
-- No recovery of omitted fields, absent-caller salt, or semantic curve points.
module Passport.CommitmentEncodingProperties where

open import Data.List.Base using (List)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat.Base
open import Relation.Binary.PropositionalEquality

open import Conformance.CommitmentEncoding
open import Conformance.CommitmentLayouts
open import Conformance.FullAccountTypes using (Value; Atom; le; Primitives; Curve)
import Conformance.CommitmentEncodingProof as Proof
import Conformance.FullAccountBody

private variable
  shape : Shape
  value : Value
  layout : Layout
  left right : List Atom

bounded-little-endian-roundtrip : ∀ {width value} → value < 256 ^ width →
  le (littleEndian width value) ≡ value
bounded-little-endian-roundtrip {width} = Proof.littleEndian-roundtrip {n = width}

canonical-value-roundtrip : Canonical shape value → decodeValue shape (encodeValue shape value) ≡ value
canonical-value-roundtrip = Proof.value-roundtrip

canonical-value-injective : ∀ {left right} → Canonical shape left → Canonical shape right →
  encodeValue shape left ≡ encodeValue shape right → left ≡ right
canonical-value-injective = Proof.value-injective

serialized-octets : CanonicalAtoms layout left → All (_< 256) (encodeAtoms layout left)
serialized-octets = Proof.atoms-octets

fixed-layout-roundtrip : CanonicalAtoms layout left → decodeAtoms layout (encodeAtoms layout left) ≡ left
fixed-layout-roundtrip = Proof.atoms-roundtrip

fixed-layout-injective : CanonicalAtoms layout left → CanonicalAtoms layout right →
  encodeAtoms layout left ≡ encodeAtoms layout right → left ≡ right
fixed-layout-injective = Proof.atoms-injective

included-fields-distinct : (kind : Commitment) →
  CanonicalAtoms (commitmentLayout kind) left → CanonicalAtoms (commitmentLayout kind) right →
  left ≢ right → encodeAtoms (commitmentLayout kind) left ≢ encodeAtoms (commitmentLayout kind) right
included-fields-distinct kind = Proof.atoms-distinct

module SourceChallenges (P : Primitives) where
  open Challenges P
  open Conformance.FullAccountBody P using (Operation)

  device-challenge-distinct : (curve : Curve) (op : Operation) →
    CanonicalAtoms (deviceChallengeLayout curve op) left → CanonicalAtoms (deviceChallengeLayout curve op) right →
    left ≢ right → encodeAtoms (deviceChallengeLayout curve op) left ≢ encodeAtoms (deviceChallengeLayout curve op) right
  device-challenge-distinct curve op = Proof.atoms-distinct

  grant-challenge-distinct : (curve : Curve) (op : GrantOperation) →
    CanonicalAtoms (grantChallengeLayout curve op) left → CanonicalAtoms (grantChallengeLayout curve op) right →
    left ≢ right → encodeAtoms (grantChallengeLayout curve op) left ≢ encodeAtoms (grantChallengeLayout curve op) right
  grant-challenge-distinct curve op = Proof.atoms-distinct

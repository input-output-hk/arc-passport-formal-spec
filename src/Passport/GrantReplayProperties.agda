{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

-- Historical grant replay exclusion, including accepted zero-value withdrawals.
-- Read GrantReplay.Spend / SameIssuance first: the first and hypothetical later
-- spend are committed runtime occurrences with an arbitrary intervening trace;
-- no accepted reissue for their shared identifier may occur in that trace.
-- Nonce growth and retained issuance identity are source conclusions, not
-- assumptions. Amount positivity and spent-opening binding are unnecessary.
--
-- The byte-signature exclusion additionally needs RelevantRequestBinding and
-- SignatureTokenInterpretation (GrantReplay). Both are relevant-pair crypto
-- premises, not claims proved by the symbolic model. Token exclusion needs only
-- the former. Existing provenance machinery explains later available tokens;
-- it never consumes the old token or forbids fresh authorized signatures.
-- Scope: local source/runtime execution, not ledger adoption or unforgeability.
-- Proofs: GrantReplayProof. The source encoding is FullAccountSignatureBinding.
module Passport.GrantReplayProperties (P : Primitives) (address : Value) where

open import Conformance.FullAccountSignatureBinding P
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (_<_)
open import Data.Product.Base using (Σ; _×_)
open import Data.Sum.Base using (_⊎_)
import Midnight.ContractDSL.SymbolicSigning as Signing
open import Passport.GrantReplay P address
import Passport.GrantReplayProof P address as Proof
open import Passport.RevocationExclusion P address
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

certify-spend : ∀ {c op s t} (event : CommittedOccurrence s t) →
  Resolved event (Runtime.grant c op) → Spend s t
certify-spend = Proof.certify-spend

-- A successful call's request has a successful source encoding; the symbolic
-- provenance theorem's digest premise can be discharged with this witness.
spend-message : ∀ {s t} (spend : Spend s t) →
  Σ Value λ d → encode (Spend.signingKey spend) (Spend.request spend) ≡ just d
spend-message = Proof.spend-message

same-issuance-nonce : ∀ {s first later final} (old : Spend s first) (trace : Runs.Trace first later)
  (next : Spend later final) → SameIssuance old trace next →
  Spend.issuance next ≡ Spend.issuance old × Spend.nonce old < Spend.nonce next
same-issuance-nonce = Proof.same-issuance-nonce

historical-request-separated : ∀ {s first later final} (old : Spend s first) (trace : Runs.Trace first later)
  (next : Spend later final) → SameIssuance old trace next →
  nonceView (Spend.request old) ≢ nonceView (Spend.request next)
historical-request-separated = Proof.historical-request-separated

-- No later committed spend can reuse this signature under the two stated laws.
-- The hypothetical later spend can use different arguments: identical-call replay
-- is included, but neither a new signature nor a reissued grant is excluded.
historical-signature-replay-excluded : ∀ {s first later final} (old : Spend s first)
  (trace : Runs.Trace first later) (next : Spend later final) → SameIssuance old trace next →
  RelevantRequestBinding (Spend.signingKey old) (Spend.request old) (Spend.signingKey next) (Spend.request next) →
  SignatureTokenInterpretation old next → SameSignature old next → ⊥
historical-signature-replay-excluded = Proof.historical-signature-replay-excluded

module SymbolicReplay (ownership : Key → Signing.Ownership) where
  open Symbolic ownership
  private module Q = Proof.SymbolicReplay ownership

  historical-token-replay-excluded : ∀ {s first later final} (old : Spend s first)
    (trace : Runs.Trace first later) (next : Spend later final) → SameIssuance old trace next →
    RelevantRequestBinding (Spend.signingKey old) (Spend.request old) (Spend.signingKey next) (Spend.request next) →
    token (Spend.signingKey old) (Spend.request old) ≢ token (Spend.signingKey next) (Spend.request next)
  historical-token-replay-excluded = Q.historical-token-replay-excluded

  -- IssuedAgreement is trace-scoped nonce-view agreement for actual honest
  -- signing occurrences with this digest, not global encoding injectivity.
  later-token-provenance : ∀ {s t knowledge} (next : Spend s t) →
    (trace : Signatures.Trace Signatures.initial knowledge) →
    (d : Value) → encode (Spend.signingKey next) (Spend.request next) ≡ just d →
    IssuedAgreement nonceView trace (Spend.signingKey next) d (Spend.request next) →
    Signatures.Available knowledge (token (Spend.signingKey next) (Spend.request next)) →
    Signatures.Controlled knowledge (Spend.signingKey next) ⊎
    Σ (Signatures.HonestlyIssued trace (token (Spend.signingKey next) (Spend.request next))) λ issued →
      nonceView (Signatures.HonestlyIssued.request issued) ≡ just (Spend.nonce next)
  later-token-provenance = Q.later-token-provenance

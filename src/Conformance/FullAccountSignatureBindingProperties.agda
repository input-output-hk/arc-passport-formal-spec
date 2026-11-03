{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

-- Signature binding for the full account (Conformance.FullAccountSignatureBinding).
-- From actual successful verification: primitive observations, state-free
-- acceptance, and the source-computed request whose encoding is the accepted
-- digest. Then symbolic provenance of that request's token. Nothing here
-- proves unforgeability, hash injectivity or human consent; request-level
-- conclusions take the explicit trace-scoped IssuedAgreement premise.
-- Proofs: Conformance.FullAccountSignatureBindingProof.
module Conformance.FullAccountSignatureBindingProperties (P : Primitives) where

open import Conformance.FullAccountBody P using (operationName)
open import Conformance.FullAccountCrypto P
open import Conformance.FullAccountExecution using (Succeeded)
open import Conformance.FullAccountSignatureBinding P
import Conformance.FullAccountSignatureBindingProof P as Proof
open import Data.Bool.Base using (true)
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (Σ; _×_)
open import Data.Sum.Base using (_⊎_)
import Midnight.ContractDSL.SymbolicSigning as Signing
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Actual verification

-- verify accepted: Schnorr arithmetic on h, or ECDSA on the k256 envelope or
-- WebAuthn assertion digest of h, with the signature bytes of Auth a.
verification-evidence : ∀ c a h message {s} → Succeeded (verify c a h message) s → Verified c a h
verification-evidence = Proof.verification-evidence

-- schnorr accepted (recovery-key and successor co-signatures of recover_submit).
schnorr-evidence : ∀ pk R S h message {s} → Succeeded (schnorr pk R S h message) s →
  SchnorrAccepts pk R S h
schnorr-evidence = Proof.schnorr-evidence

-- Verification neither reads nor changes the ledger, so the device path's
-- check after rolling and the gates below agree with any starting state.
challengeAt-preserves : ∀ c grant operation addr a args nonce {s h t es} →
  challengeAt c grant operation addr a args nonce s ≡ accepted h t es → t ≡ s
challengeAt-preserves = Proof.challengeAt-preserves

verify-preserves : ∀ c a h message {s v t es} → verify c a h message s ≡ accepted v t es → t ≡ s
verify-preserves = Proof.verify-preserves

schnorr-preserves : ∀ pk R S h message {s v t es} → schnorr pk R S h message s ≡ accepted v t es → t ≡ s
schnorr-preserves = Proof.schnorr-preserves

verified-digest : ∀ c a h message {s} → Succeeded (verify c a h message) s → (verified : Verified c a h) →
  verifiedDigest c a h message ≡ just (signedDigest verified)
verified-digest = Proof.verified-digest

schnorr-accepted : ∀ pk R S h message {s} → Succeeded (schnorr pk R S h message) s →
  schnorrAccepted pk R S h message ≡ true
schnorr-accepted = Proof.schnorr-accepted

------------------------------------------------------------------------
-- Exact message binding

-- The request of an actual challengeAt call encodes to the digest its
-- verification accepted; no collision or injectivity assumption is used.
authorisation-message : ∀ c grant op addr a args nonce {s h t es} →
  challengeAt c grant (operationName op) addr a args nonce s ≡ accepted h t es →
  (verified : Verified c a h) →
  encode (authorisingKey c a) (authorisedRequest c grant op addr a args nonce) ≡ just (signedDigest verified)
authorisation-message = Proof.authorisation-message

-- recover_submit's digest is the encoding of its request for any Schnorr key,
-- so the recovery key and the successor sign the same message.
recovery-message : ∀ r pk {s dst t es u h v fs} →
  hashTag recoverySubmitTag s ≡ accepted dst t es → hash (submitPreimage dst r) u ≡ accepted h v fs →
  encode (signingKey jubjub pk) (recoveryRequest r) ≡ just h
recovery-message = Proof.recovery-message

------------------------------------------------------------------------
-- Symbolic provenance of request tokens

module _ (ownership : Key → Signing.Ownership) where
  open Symbolic ownership
  open Signing.Model interface
    using (Trace; Available; Controlled; HonestlyIssued; module HonestlyIssued; initial)
  private module Q = Proof.Provenance ownership

  -- In an initial-rooted signing trace, an available request token is under
  -- attacker control or was honestly issued for a request with the same
  -- message, possibly a different request.
  message-provenance : ∀ {k r d t} → encode k r ≡ just d → (trace : Trace initial t) →
    Available t (token k r) →
    Controlled t k ⊎ Σ (HonestlyIssued trace (token k r)) λ issued →
      encode k (HonestlyIssued.request issued) ≡ just d
  message-provenance = Q.message-provenance

  -- With trace-scoped agreement, the honestly issued request has r's view.
  request-provenance : ∀ {X : Set} (view : Request → X) {k r d t} → encode k r ≡ just d →
    (trace : Trace initial t) → IssuedAgreement view trace k d r → Available t (token k r) →
    Controlled t k ⊎ Σ (HonestlyIssued trace (token k r)) λ issued →
      view (HonestlyIssued.request issued) ≡ view r
  request-provenance = Q.request-provenance

  -- Device and grant calls: actual challenge and verification to provenance.
  authorisation-provenance : ∀ c grant op addr a args nonce message {s h t es u final} →
    challengeAt c grant (operationName op) addr a args nonce s ≡ accepted h t es →
    Succeeded (verify c a h message) u →
    (trace : Trace initial final) →
    Available final (token (authorisingKey c a) (authorisedRequest c grant op addr a args nonce)) →
    Σ (Verified c a h) λ verified →
      Controlled final (authorisingKey c a) ⊎
      Σ (HonestlyIssued trace (token (authorisingKey c a) (authorisedRequest c grant op addr a args nonce)))
        λ issued → encode (authorisingKey c a) (HonestlyIssued.request issued) ≡ just (signedDigest verified)
  authorisation-provenance = Q.authorisation-provenance

  -- recover_submit: either signer, recovery key or successor (possession proof).
  recovery-provenance : ∀ r pk R S message {s dst t es u h v fs w final} →
    hashTag recoverySubmitTag s ≡ accepted dst t es →
    hash (submitPreimage dst r) u ≡ accepted h v fs →
    Succeeded (schnorr pk R S h message) w →
    (trace : Trace initial final) →
    Available final (token (signingKey jubjub pk) (recoveryRequest r)) →
    SchnorrAccepts pk R S h ×
      (Controlled final (signingKey jubjub pk) ⊎
       Σ (HonestlyIssued trace (token (signingKey jubjub pk) (recoveryRequest r))) λ issued →
         encode (signingKey jubjub pk) (HonestlyIssued.request issued) ≡ just h)
  recovery-provenance = Q.recovery-provenance

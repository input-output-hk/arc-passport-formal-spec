{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

-- Symbolic signing vocabulary for the full account at Passport fc19e471536f.
-- A Request is what a key holder is asked to sign: an operation challenge
-- (FullAccountCrypto.challengeAt's inputs) with its scheme input, or the
-- recover_submit fields co-signed by the recovery and successor keys. encode
-- runs the source hash-and-sign encoding: the Schnorr challenge digest, the
-- k256 envelopeDigest of it, or the p256 WebAuthn assertion digest of it. A
-- Message is that final digest, or nothing when a primitive fails.
--
-- encode is not assumed injective. Verified and SchnorrAccepts record what the
-- actual verifier observed of its primitives; they are not an unforgeability
-- claim. ECDSA and the Schnorr equation are satisfiable for adversarially
-- chosen digests, so a symbolic signature token is meaningful only as the
-- encoding of a source-computed Request (Symbolic.token), never for a bare
-- digest. Statements: Conformance.FullAccountSignatureBindingProperties.
module Conformance.FullAccountSignatureBinding (P : Primitives) where

open import Conformance.FullAccountBody P
open import Conformance.FullAccountCrypto P
open import Conformance.FullAccountLayouts
open import Data.Bool.Base using (Bool; true; _∨_; if_then_else_)
open import Data.List.Base using (List; []; _∷_; drop; take)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Data.Nat.Base using (ℕ; _≡ᵇ_; _≤ᵇ_; _<ᵇ_; _%_)
open import Data.Product.Base using (_,_)
open import Data.String.Base using (String)
open import Level using (0ℓ)
import Midnight.ContractDSL.SymbolicSigning as Signing
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Keys, requests and messages

record Key : Set where
  constructor signingKey
  field curve : Curve
        point : Value

-- Scheme-specific signed inputs: the Schnorr commitment R and grind nonce
-- enter the challenge preimage; the k256 envelope kind and the WebAuthn
-- authenticator data and origin wrap the challenge digest.
data SchemeInput : Set where
  jubjubSchnorr : (commitment : Value) (grindNonce : ℕ) → SchemeInput
  k256Ecdsa : (envelopeKind : ℕ) → SchemeInput
  p256WebAuthn : (authenticatorData origin : Value) → SchemeInput

-- challengeAt's inputs other than the key and scheme input: device
-- (forGrant false) or grant domain, operation, account address, operation
-- atoms, and the authorisation or grant nonce.
record Challenge : Set where
  constructor operationChallenge
  field forGrant : Bool
        operation : Operation
        account : Value
        atoms : List Atom
        nonce : ℕ

-- recover_submit's hashed fields, in preimage order.
record RecoveryChallenge : Set where
  constructor recoveryChallenge
  field account recoveryKey recoveryCommitment successorKey successorCommitment
          nextRecoveryKey : Value
        epoch nonce : ℕ
        nowBound grindNonce : Value

data Request : Set where
  operationRequest : Challenge → SchemeInput → Request
  recoveryRequest : RecoveryChallenge → Request

Message : Set
Message = Maybe Value

------------------------------------------------------------------------
-- Source encodings

outcome : ∀ {A : Set} → Execution A → Maybe A
outcome (rejected _) = nothing
outcome (accepted v _ _) = just v

-- The computations evaluated here read and write no ledger cell
-- (FullAccountSignatureBindingProof shows each is state-independent), so
-- the empty starting ledger is immaterial.
evaluate : ∀ {A : Set} → M A → Maybe A
evaluate m = outcome (m (state []))

-- envelopeDigest's two hashed preimages (FullAccountCrypto).
plainEnvelope connectedEnvelope : Value → List Atom
plainEnvelope h = b32 h ∷ []
connectedEnvelope h = ("Bytes<27>" , pad 27 "midnight_signed_message:32:") ∷ b32 h ∷ []

-- The clientDataJSON and assertion preimages that FullAccountCrypto.webAuthn
-- hashes inline; the Proof module derives them from its actual evaluation.
clientDataPreimage : Value → Value → List Atom
clientDataPreimage origin h =
  ("Bytes<36>" , pad 36 "{\"type\":\"webauthn.get\",\"challenge\":\"") ∷
  ("Bytes<43>" , bytes (base64url (rawBytes h))) ∷
  ("Bytes<12>" , pad 12 "\",\"origin\":\"") ∷ ("Bytes<21>" , origin) ∷
  ("Bytes<22>" , pad 22 "\",\"crossOrigin\":false}") ∷ []

assertionPreimage : Value → Value → List Atom
assertionPreimage authenticatorData clientHash = ("Bytes<37>" , authenticatorData) ∷ b32 clientHash ∷ []

webAuthnDigest : Value → Value → Value → M Value
webAuthnDigest authenticatorData origin h =
  hash (clientDataPreimage origin h) >>= λ clientHash → hash (assertionPreimage authenticatorData clientHash)

-- recover_submit's inline domain tag and challenge preimage (FullAccountBody.submit).
recoverySubmitTag : String
recoverySubmitTag = "midnight:account:recovery:submit:v1"

submitPreimage : Value → RecoveryChallenge → List Atom
submitPreimage dst r =
  b32 dst ∷ contract account ∷ jub recoveryKey ∷ jub recoveryCommitment ∷ jub successorKey ∷
  jub successorCommitment ∷ jub nextRecoveryKey ∷ u32 (nat epoch) ∷ u64 (nat nonce) ∷
  u64 nowBound ∷ u64 grindNonce ∷ []
  where open RecoveryChallenge r

recoveryDigest : RecoveryChallenge → M Value
recoveryDigest r = hashTag recoverySubmitTag >>= λ dst → hash (submitPreimage dst r)

-- challengeAt reads only the key, Schnorr commitment and grind nonce of Auth.
requestAuth : Value → SchemeInput → Auth
requestAuth pk (jubjubSchnorr commitment grindNonce) = auth pk 0 commitment none grindNonce 0 none none none
requestAuth pk _ = auth pk 0 none none 0 0 none none none

challengeDigest : Curve → Value → Challenge → SchemeInput → M Value
challengeDigest c pk ch scheme =
  challengeAt c forGrant (operationName operation) account (requestAuth pk scheme) atoms nonce
  where open Challenge ch

-- A key encodes only requests of its own scheme; recovery uses Schnorr.
encode : Key → Request → Message
encode (signingKey jubjub pk) (operationRequest ch (jubjubSchnorr commitment grindNonce)) =
  evaluate (challengeDigest jubjub pk ch (jubjubSchnorr commitment grindNonce))
encode (signingKey k256 pk) (operationRequest ch (k256Ecdsa kind)) =
  evaluate (challengeDigest k256 pk ch (k256Ecdsa kind) >>= envelopeDigest kind)
encode (signingKey p256 pk) (operationRequest ch (p256WebAuthn ad origin)) =
  evaluate (challengeDigest p256 pk ch (p256WebAuthn ad origin) >>= webAuthnDigest ad origin)
encode (signingKey jubjub _) (recoveryRequest r) = evaluate (recoveryDigest r)
encode _ _ = nothing

------------------------------------------------------------------------
-- Requests of actual calls

authorisingKey : Curve → Auth → Key
authorisingKey c a = signingKey c (key a)

schemeInput : Curve → Auth → SchemeInput
schemeInput jubjub a = jubjubSchnorr (sigR a) (grind a)
schemeInput k256 a = k256Ecdsa (envelope a)
schemeInput p256 a = p256WebAuthn (authenticator a) (at 1 (policy a))

-- The request of a challengeAt call made with Auth a: device calls use
-- grant false, grant calls true and the grant record's nonce.
authorisedRequest : Curve → Bool → Operation → Value → Auth → List Atom → ℕ → Request
authorisedRequest c grant op addr a args nonce =
  operationRequest (operationChallenge grant op addr args nonce) (schemeInput c a)

-- submit's request from its address, recovery key read, argument vector,
-- post-recovery epoch and authorisation nonce.
submitChallenge : Value → Value → List Value → ℕ → ℕ → RecoveryChallenge
submitChallenge addr signingPk xs postEpoch signingNonce =
  recoveryChallenge addr signingPk A.recoveryR A.successorKey A.successorR A.nextRecoveryKey
    postEpoch signingNonce A.nowBound A.grindNonce
  where module A = SubmitArguments xs

-- Initial ownership and requiring token k r for a verified source request are
-- ideal-signing interpretation choices, not consequences of raw arithmetic.
-- A concrete realization must account for one signature verifying distinct
-- digests through Schnorr's le(h) mod jubjubOrder or ECDSA's digest reduction.
-- Obtained tokens remain replayable; no signature-consumption rule is added.
module Symbolic (ownership : Key → Signing.Ownership) where
  interface : Signing.Interface 0ℓ
  interface = record
    { Key = Key ; Request = Request ; Message = Message ; ownership = ownership ; encode = encode }

  module Signatures = Signing.Model interface

  token : Key → Request → Signatures.Token
  token k r = Signatures.signature k (encode k r)

  -- Trace-scoped agreement, a premise that is not proved: every request
  -- honestly signed with k in trace that encodes to the accepted digest d
  -- has the same view as r. It concerns only requests actually issued in
  -- that trace, not every request that might collide at d. view selects the
  -- security-relevant part of a request, or is the identity.
  IssuedAgreement : ∀ {X : Set} → (Request → X) → ∀ {s t} → Signatures.Trace s t →
    Key → Value → Request → Set
  IssuedAgreement view trace k d r = ∀ r′ before →
    Signatures.Occurs (Signatures.honestSign k r′) before trace → encode k r′ ≡ just d →
    view r′ ≡ view r

------------------------------------------------------------------------
-- Verification evidence observed from FullAccountCrypto.verify and schnorr

record SchnorrAccepts (pk R S h : Value) : Set where
  constructor schnorrAccepts
  field inField : (le (rawBytes h) <ᵇ fieldOrder) ≡ true
        lhs scaled rhs : Value
        generatorMultiple : ecMulGenerator P jubjub (number S % jubjubOrder) ≡ success lhs
        challengeMultiple : ecMul P jubjub pk (le (rawBytes h) % jubjubOrder) ≡ success scaled
        commitmentSum : ecAdd P jubjub R scaled ≡ success rhs
        balanced : equal lhs rhs ≡ true

record EnvelopeDigest (kind : ℕ) (h d : Value) : Set where
  constructor enveloped
  field admitted : (kind ≤ᵇ 1) ≡ true
        plain connector : Value
        plainHash : persistentHash P (plainEnvelope h) ≡ success plain
        connectorHash : persistentHash P (connectedEnvelope h) ≡ success connector
        selected : d ≡ (if kind ≡ᵇ 1 then connector else plain)

-- The flags byte at offset 32 has user presence and user verification set.
-- This is the authenticator's claim, not evidence of human consent.
record AuthenticatorFlags (authenticatorData : Value) : Set where
  constructor flagged
  field flags : ℕ
        remaining : Bytes
        flagsByte : drop 32 (rawBytes authenticatorData) ≡ flags ∷ remaining
        presentAndVerified : ((flags ≡ᵇ 5) ∨ (flags ≡ᵇ 13) ∨ (flags ≡ᵇ 29)) ≡ true

record WebAuthnDigest (authenticatorData origin h d : Value) : Set where
  constructor webAuthnHashed
  field clientHash : Value
        clientDataHash : persistentHash P (clientDataPreimage origin h) ≡ success clientHash
        assertionHash : persistentHash P (assertionPreimage authenticatorData clientHash) ≡ success d

-- verify c a h accepted: Schnorr on h itself, or ECDSA on a final digest d
-- distinct from the operation challenge h.
data Verified : Curve → Auth → Value → Set where
  jubjubVerified : ∀ {a h} → SchnorrAccepts (key a) (sigR a) (sigS a) h → Verified jubjub a h
  k256Verified : ∀ {a h} d → EnvelopeDigest (envelope a) h d →
    ecdsaVerify P k256 d (signature a) (key a) ≡ success true → Verified k256 a h
  p256Verified : ∀ {a h} d →
    equal (bytes (take 32 (rawBytes (authenticator a)))) (at 0 (policy a)) ≡ true →
    AuthenticatorFlags (authenticator a) →
    WebAuthnDigest (authenticator a) (at 1 (policy a)) h d →
    ecdsaVerify P p256 d (signature a) (key a) ≡ success true → Verified p256 a h

signedDigest : ∀ {c a h} → Verified c a h → Value
signedDigest {h = h} (jubjubVerified _) = h
signedDigest (k256Verified d _ _) = d
signedDigest (p256Verified d _ _ _ _) = d

------------------------------------------------------------------------
-- State-free verification gates, evaluated with the actual verifier

finalDigest : Curve → Auth → Value → M Value
finalDigest jubjub a h = return h
finalDigest k256 a h = envelopeDigest (envelope a) h
finalDigest p256 a h = webAuthnDigest (authenticator a) (at 1 (policy a)) h

verifiedDigest : Curve → Auth → Value → String → Maybe Value
verifiedDigest c a h message = evaluate (verify c a h message >> finalDigest c a h)

schnorrAccepted : Value → Value → Value → Value → String → Bool
schnorrAccepted pk R S h message = is-just (evaluate (schnorr pk R S h message))

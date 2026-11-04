{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes hiding (context)

-- Historical replay vocabulary. GrantReplayProperties is the reader entry;
-- GrantReplayProof.certify-spend extracts Spend from a committed runtime call.
module Passport.GrantReplay (P : Primitives) (address : Value) where

open import Conformance.FullAccountBody P
open import Conformance.FullAccountCrypto P hiding (auth)
open import Conformance.FullAccountGrant P
open import Conformance.FullAccountGrantSecurity P hiding (identifier)
open import Conformance.FullAccountLayouts
open import Conformance.FullAccountSignatureBinding P hiding (signingKey)
open import Data.Bool.Base using (true)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; take)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_)
open import Passport.GrantEffects P using (Issuance; issuanceOf)
open import Passport.GrantSpending P using (parseGrantAuth)
open import Passport.RevocationExclusion P address
open import Relation.Binary.PropositionalEquality using (_≡_)

record Spend (before after : State) : Set where
  field curve : Curve
        operation : Operation
        event : CommittedOccurrence before after
        resolved : Resolved event (Runtime.grant curve operation)
        finalState : GrantFinalState curve operation (occurrenceContext event)
          (parseGrantAuth curve operation (occurrenceArguments event))
          (take 3 (occurrenceArguments event)) before after

  evidence = GrantFinalState.callEvidence finalState
  context = occurrenceContext event
  auth = authorisation (parseGrantAuth curve operation (occurrenceArguments event))
  identifier = GrantCallEvidence.identifier evidence
  recordValue = GrantCallEvidence.grantRecord evidence
  issuance = issuanceOf identifier recordValue
  nonce = number (grantNonce recordValue)
  signingKey = authorisingKey curve auth
  request = authorisedRequest curve true operation (self context) auth
    (grantChallengeAtoms operation (take 3 (occurrenceArguments event))
      (grantCoin operation context) (parseGrantAuth curve operation (occurrenceArguments event))
      identifier recordValue) nonce

-- ReissuedIn records actual accepted issue occurrences, not equality of endpoint
-- records. Its absence fixes the retained issuance, even if a map id is reused
-- elsewhere. Revocation/recovery and refused calls remain in the intervening trace.
SameIssuance : ∀ {s first later final} → Spend s first → Runs.Trace first later → Spend later final → Set
SameIssuance old trace next =
  (ReissuedIn (Spend.identifier old) trace → ⊥) ×
  (Spend.identifier next ≡ Spend.identifier old)

nonceView : Request → Maybe ℕ
nonceView (operationRequest ch _) = just (Challenge.nonce ch)
nonceView (recoveryRequest _) = nothing

-- Only these two source requests must agree on nonce when their final encoded
-- messages agree. No global hash injectivity is assumed, and this is not proved
-- by nonce growth. It covers the complete source hash/envelope/WebAuthn encoding.
RelevantRequestBinding : Key → Request → Key → Request → Set
RelevantRequestBinding k r k′ r′ =
  k ≡ k′ → encode k r ≡ encode k′ r′ → nonceView r ≡ nonceView r′

signatureMaterial : Curve → Auth → List Value
signatureMaterial jubjub a = sigR a ∷ sigS a ∷ []
signatureMaterial k256 a = signature a ∷ []
signatureMaterial p256 a = signature a ∷ []

SameSignature : ∀ {s t u v} → Spend s t → Spend u v → Set
SameSignature old next = Spend.signingKey old ≡ Spend.signingKey next ×
  signatureMaterial (Spend.curve old) (Spend.auth old) ≡
  signatureMaterial (Spend.curve next) (Spend.auth next)

-- External realization law for this relevant pair of successful source calls:
-- reusing the same signature material realizes the same exact-message token.
-- SymbolicSigning does NOT prove this law about bytes. Schnorr scalar reduction,
-- ECDSA digest reduction/multiple verifying messages, and wrapper equivalences
-- must be covered by a concrete realization, not inferred from changed nonces.
SignatureTokenInterpretation : ∀ {s t u v} → Spend s t → Spend u v → Set
SignatureTokenInterpretation old next = SameSignature old next →
  encode (Spend.signingKey old) (Spend.request old) ≡
  encode (Spend.signingKey next) (Spend.request next)

{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes using (Primitives; Value)
open import Midnight.ContractDSL.SymbolicSigning using (Ownership)
import Conformance.FullAccountSignatureBinding as SignatureBinding

-- Each request computation below uses just one entrypoint's guard evidence.
-- Obtain that evidence from FullAccountDeviceSecurityProperties.device-call-evidence,
-- FullAccountGrantSecurityProperties.grant-call-evidence, or
-- FullAccountRecoverySecurityProperties.submit-evidence respectively.
-- AccountRequestDispatchProperties connects these source builders to the actual
-- dispatcher's signedRequests and requiredTokens. Its dispatched-available feeds
-- request-views at AccountSecurity.Histories.signingHistory h, using the joint
-- invocation's token premise. Agreement is trace-scoped, not digest injectivity;
-- approval is a trusted input, not human consent. Full concrete certifications
-- remain in AccountSecurityProof.accepted-call[-provenance/-requests].
module Passport.AccountSecurityProperties (P : Primitives) (address : Value)
  (ownership : SignatureBinding.Key P → Ownership) where

open import Data.List.Base using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (Σ; uncurry′)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Passport.AccountSecurity P address ownership
open Symbolic using (module Signatures)
import Passport.AccountSecurityProof P address ownership as Proof

-- These equalities identify the exact source-computed requests; they neither
-- assume authorization from acceptance nor combine unrelated entrypoint guards.
device-request-computation : ∀ c op ctx xs {s v t} (evidence : Device.DeviceCall c op ctx xs s v t) →
  deviceRequests c op ctx xs s ≡ calledRequest evidence ∷ []
device-request-computation = Proof.device-request-computation

grant-request-computation : ∀ c op ctx ga ys {s} (evidence : Grant.GrantCallEvidence c op ctx ga ys s) →
  grantRequests c op ctx ga ys s ≡ grantedRequest evidence ∷ []
grant-request-computation = Proof.grant-request-computation

submission-request-computation : ∀ ctx xs {s t} (evidence : Recovery.Submission.Evidence ctx xs s t) →
  recoveryRequests ctx xs s ≡ submittedRequests evidence
submission-request-computation = Proof.submission-request-computation

-- Available tokens for encoded requests yield attacker control or honest
-- issuance of the same view. Apply separately to the path selected by dispatch;
-- no Device, Grant or Recovery guard record appears in this provenance claim.
request-views : ∀ {X : Set} (view : Binding.Request → X) {knowledge}
  (trace : Signatures.Trace Signatures.initial knowledge) {requests} →
  All (λ request → Σ Value (Encodes request)) requests →
  All (TraceAgreement view trace) requests →
  All (λ request → Signatures.Available knowledge (uncurry′ Symbolic.token request)) requests →
  All (TraceRequestProvenance view trace) requests
request-views = Proof.request-views

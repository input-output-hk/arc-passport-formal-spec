{-# OPTIONS --safe --without-K #-}

-- Projection and signing-provenance properties of joint signing/contract
-- histories (Midnight.ContractDSL.AdversarialLifecycle). Provenance is
-- message-level (see SymbolicSigning) and concerns tokens available when a call
-- is constructed. It does not say that an accepted call was authorized, that a
-- token matches the request the call intends, or that `required` describes any
-- concrete signature check: that remains the instance's interpretation.
-- Approval remains a trusted abstract input, not authenticated consent. Scope:
-- docs/conformance-testing-plan.md#symbolic-signing-and-adversarial-histories.
module Midnight.ContractDSL.AdversarialLifecycleProperties where

open import Data.List.Base using (List)
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (_,_; proj₂)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (_◅◅_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Midnight.ContractDSL.AdversarialLifecycle
open import Midnight.ContractDSL.Lifecycle
import Midnight.ContractDSL.AdversarialLifecycleProof as Proof
import Midnight.ContractDSL.SymbolicSigning as Signing

module Properties {ℓ} (L : Lifecycle ℓ) (identity : Lifecycle.Identity L)
  (S : Signing.Interface ℓ)
  (required : Lifecycle.State L → Lifecycle.Environment L → Lifecycle.Call L →
    List (Signing.Model.Token S)) where
  open Joint L identity S required
  open Signatures using (Token; module Token; Available; Controlled; HonestlyIssued)
  module P = Proof.Proofs L identity S required

  -- Projecting an extended joint history extends the projected account history
  -- and initial signing trace by the projections of the new steps.
  contract-history-extend : ∀ {s t} (h : History s) (trace : Trace s t) →
    contractHistory (extend h trace) ≡ Contract.extend (contractHistory h) (contractTrace trace)
  contract-history-extend = P.contract-history-extend

  signing-history-extend : ∀ {s t} (h : History s) (trace : Trace s t) →
    signingHistory (extend h trace) ≡ signingHistory h ◅◅ signingTrace trace
  signing-history-extend = P.signing-history-extend

  -- Every token known at a reachable joint state has a currently attacker-
  -- controlled key, or an approved honestSign in the projected signing trace.
  signature-provenance : ∀ {final} (h : History final) {τ : Token} →
    Available (proj₂ final) τ →
    Controlled (proj₂ final) (Token.key τ) ⊎ HonestlyIssued (signingHistory h) τ
  signature-provenance = P.signature-provenance

  -- In particular this holds for every token an invocation from contract state
  -- `contract` requires, since Step.invocation demands this availability premise.
  required-provenance : ∀ {contract knowledge environment call}
    (h : History (contract , knowledge)) →
    All (Available knowledge) (required contract environment call) →
    All (λ τ → Controlled knowledge (Token.key τ) ⊎ HonestlyIssued (signingHistory h) τ)
      (required contract environment call)
  required-provenance = P.required-provenance

{-# OPTIONS --safe --without-K #-}

module Midnight.ContractDSL.AdversarialLifecycleProof where

open import Data.List.Base using (List)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Product using (_,_; proj₂)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Midnight.ContractDSL.AdversarialLifecycle
open import Midnight.ContractDSL.Lifecycle
import Midnight.ContractDSL.SymbolicSigning as Signing
import Midnight.ContractDSL.SymbolicSigningProof as SigningProof

module Proofs {ℓ} (L : Lifecycle ℓ) (identity : Lifecycle.Identity L)
  (S : Signing.Interface ℓ)
  (required : Lifecycle.State L → Lifecycle.Environment L → Lifecycle.Call L →
    List (Signing.Model.Token S)) where
  open Joint L identity S required
  open Signatures using (Token; module Token; Available; Controlled; HonestlyIssued)
  module Core = SigningProof.Proofs S

  contract-trace-◅◅ : ∀ {s t u} (xs : Trace s t) (ys : Trace t u) →
    contractTrace (xs ◅◅ ys) ≡ contractTrace xs ◅◅ contractTrace ys
  contract-trace-◅◅ ε ys = refl
  contract-trace-◅◅ (signing _ ◅ xs) ys = contract-trace-◅◅ xs ys
  contract-trace-◅◅ (invocation environment call outcome _ executed ◅ xs) ys =
    cong (Contract.event environment call outcome executed ◅_) (contract-trace-◅◅ xs ys)

  signing-trace-◅◅ : ∀ {s t u} (xs : Trace s t) (ys : Trace t u) →
    signingTrace (xs ◅◅ ys) ≡ signingTrace xs ◅◅ signingTrace ys
  signing-trace-◅◅ ε ys = refl
  signing-trace-◅◅ (signing x ◅ xs) ys =
    cong (x ◅_) (signing-trace-◅◅ xs ys)
  signing-trace-◅◅ (invocation _ _ _ _ _ ◅ xs) ys = signing-trace-◅◅ xs ys

  contract-history-extend : ∀ {s t} (h : History s) (trace : Trace s t) →
    contractHistory (extend h trace) ≡ Contract.extend (contractHistory h) (contractTrace trace)
  contract-history-extend h trace = let open History h in
    cong (Contract.rooted deploymentEnvironment deployment deploymentOutcome initial initialized)
      (contract-trace-◅◅ execution trace)

  signing-history-extend : ∀ {s t} (h : History s) (trace : Trace s t) →
    signingHistory (extend h trace) ≡ signingHistory h ◅◅ signingTrace trace
  signing-history-extend h trace = signing-trace-◅◅ (History.execution h) trace

  signature-provenance : ∀ {final} (h : History final) {τ : Token} →
    Available (proj₂ final) τ →
    Controlled (proj₂ final) (Token.key τ) ⊎ HonestlyIssued (signingHistory h) τ
  signature-provenance h = Core.signature-provenance (signingHistory h)

  required-provenance : ∀ {contract knowledge environment call}
    (h : History (contract , knowledge)) →
    All (Available knowledge) (required contract environment call) →
    All (λ τ → Controlled knowledge (Token.key τ) ⊎ HonestlyIssued (signingHistory h) τ)
      (required contract environment call)
  required-provenance h = All.map (signature-provenance h)

{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes using (Primitives; Value)
open import Midnight.ContractDSL.SymbolicSigning using (Ownership)
import Conformance.FullAccountSignatureBinding as SignatureBinding

-- Dispatcher and request computation only: no entrypoint's guard certificate.
-- AccountSecurityProperties treats device, grant and submission evidence one
-- path at a time. These bridges connect those focused computations to the
-- concrete signedRequests/requiredTokens used by AccountSecurity.Histories.
-- In a rooted joint history h, an invocation supplies dispatched-available's
-- premise; apply AccountSecurityProperties.request-views to the resulting path
-- requests and Histories.signingHistory h. Full accepted-call certificates and
-- their concrete provenance proofs remain in AccountSecurityProof.
module Passport.AccountRequestDispatchProperties (P : Primitives) (address : Value)
  (ownership : SignatureBinding.Key P → Ownership) where

open import Data.List.Base using (map)
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (Σ; uncurry′)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Conformance.FullAccountTypes using (arguments)
import Passport.Account as Account
open import Passport.AccountLifecycle P using (RuntimeCall; executionContext)
open import Passport.AccountSecurity P address ownership
import Passport.AccountSecurityProof P address ownership as Proof
open Semantics using (Entrypoint)
open Symbolic using (module Signatures)

dispatches : ∀ env (call : RuntimeCall) {before answer effects after} →
  Account.Transition P (executionContext address env) (RuntimeCall.request call) before
    (Account.committed answer effects) after →
  Σ Entrypoint λ e → Dispatched e env call before answer after effects
dispatches = Proof.dispatches

dispatched-requests : ∀ e env call {before answer effects after} →
  Dispatched e env call before answer after effects →
  signedRequests before env call ≡
    entrypointRequests e (executionContext address env) (arguments (RuntimeCall.request call)) before
dispatched-requests = Proof.dispatched-requests

dispatched-tokens : ∀ e env call {before answer effects after} →
  Dispatched e env call before answer after effects →
  requiredTokens before env call ≡ map (uncurry′ Symbolic.token)
    (entrypointRequests e (executionContext address env) (arguments (RuntimeCall.request call)) before)
dispatched-tokens = Proof.dispatched-tokens

dispatched-available : ∀ e env call {before answer effects after knowledge} →
  Dispatched e env call before answer after effects →
  All (Signatures.Available knowledge) (requiredTokens before env call) →
  All (λ request → Signatures.Available knowledge (uncurry′ Symbolic.token request))
    (entrypointRequests e (executionContext address env) (arguments (RuntimeCall.request call)) before)
dispatched-available = Proof.dispatched-available

{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes using (Primitives; Value)
open import Midnight.ContractDSL.SymbolicSigning using (Ownership)
import Conformance.FullAccountSignatureBinding as SignatureBinding

-- Local contract security of accepted full-account runtime calls
-- (Passport.AccountSecurity). Guard facts are derived from the actual
-- dispatcher and entrypoint evaluators for any primitive backend P; nothing
-- assumes an accepted call was authorized. Cryptographic content enters only
-- through the joint histories' invocation premise: requiredTokens, the tokens
-- of source-computed requests whose signatures verify, must be available
-- (an ideal symbolic boundary; its scope is in AccountSecurity's header).
-- Provenance is message-level unless the trace-scoped agreement premise is
-- supplied; approval is a trusted abstract input, not human consent. These
-- are local source-execution results, not ledger admission or adoption.
-- Proofs: Passport.AccountSecurityProof.
module Passport.AccountSecurityProperties (P : Primitives) (address : Value)
  (ownership : SignatureBinding.Key P → Ownership) where

open import Data.Bool.Base using (true)
open import Data.List.Base using (List)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe.Base using (just)
open import Data.Product using (Σ; _×_; _,_; uncurry′)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Conformance.FullAccountTypes using (flag)
import Passport.Account as Account
open import Passport.AccountLifecycle P using (RuntimeCall; executionContext)
open import Passport.AccountSecurity P address ownership
import Passport.AccountSecurityProof as AccountSecurityProof
open Semantics using (finaliseRecovery)
open Symbolic using (module Signatures)

module Proof = AccountSecurityProof P address ownership

-- Every accepted runtime call resolves, by the dispatcher's own lookup, to a
-- runtime entrypoint (never the constructor). AcceptedCall then records that
-- entrypoint's evaluator evidence and the requests whose signatures it
-- verified, and these are exactly the signed requests computed from the
-- before state. Grant calls resolve only for withdrawals, and their evidence
-- includes the grant record stored in the final state (advanced nonce, new
-- spent commitment). Activation, deposits and finalisation verify no signature.
accepted-call : ∀ env (call : RuntimeCall) {before answer effects after} →
  Account.Transition P (executionContext address env) (RuntimeCall.request call) before
    (Account.committed answer effects) after →
  Σ (List SignedRequest) λ requests → AcceptedCall env call before answer after effects requests ×
    signedRequests before env call ≡ requests
accepted-call = Proof.accepted-call

-- An accepted invocation from a rooted joint history: the token of each
-- verified request is attacker-controlled at that joint state or honestly
-- issued in the history's signing trace.
accepted-call-provenance : ∀ {before knowledge after env call answer effects}
  (h : Histories.History (before , knowledge)) →
  All (Signatures.Available knowledge) (requiredTokens before env call) →
  Account.Transition P (executionContext address env) (RuntimeCall.request call) before
    (Account.committed answer effects) after →
  Σ (List SignedRequest) λ requests → AcceptedCall env call before answer after effects requests ×
    All (λ request → Provenance h (uncurry′ Symbolic.token request)) requests
accepted-call-provenance = Proof.accepted-call-provenance

-- Under SignatureBinding's trace-scoped agreement premise for each signed
-- request the call carries (any honestly signed request with the same key and
-- digest in the history's signing trace has the same view), each verified
-- request's key is attacker-controlled, or a request with that view was
-- approved and honestly signed. No global digest uniqueness is assumed.
accepted-call-requests : ∀ {X : Set} (view : Binding.Request → X)
  {before knowledge after env call answer effects}
  (h : Histories.History (before , knowledge)) →
  All (Signatures.Available knowledge) (requiredTokens before env call) →
  All (AgreesIn view h) (signedRequests before env call) →
  Account.Transition P (executionContext address env) (RuntimeCall.request call) before
    (Account.committed answer effects) after →
  Σ (List SignedRequest) λ requests → AcceptedCall env call before answer after effects requests ×
    All (RequestProvenance view h) requests
accepted-call-requests = Proof.accepted-call-requests

-- In a deployment-rooted account history, a flagged pending recovery record
-- comes from an actual accepted recover_submit step of that history, after
-- which every step is a refusal or an accepted ordinary call keeping the
-- pending cells: no later submission, cancellation or finalisation.
pending-origin : ∀ {s p} (h : Runs.History s) → Recovery.Stores s "pending_recovery" p →
  flag p ≡ true → SubmittedIn (Runs.History.execution h)
pending-origin = Proof.pending-origin

-- The same for joint histories, in their projected account trace.
joint-pending-origin : ∀ {s knowledge p} (h : Histories.History (s , knowledge)) →
  Recovery.Stores s "pending_recovery" p → flag p ≡ true →
  SubmittedIn (Histories.contractTrace (Histories.History.execution h))
joint-pending-origin = Proof.joint-pending-origin

-- An accepted finalisation at the end of a history enacts the successor entry,
-- recovery key and deadline installed by that history's submission
-- occurrence. This is local contract safety: no guardian consent, fairness or
-- ledger adoption is claimed.
finalisation-enacts-occurrence : ∀ env (call : RuntimeCall) {before answer effects after} →
  (h : Runs.History before) → resolve (RuntimeCall.request call) ≡ just finaliseRecovery →
  Account.Transition P (executionContext address env) (RuntimeCall.request call) before
    (Account.committed answer effects) after →
  EnactsOccurrence (executionContext address env) (Runs.History.execution h) after
finalisation-enacts-occurrence = Proof.finalisation-enacts-occurrence

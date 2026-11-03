{-# OPTIONS --safe --without-K #-}

-- Checked properties of the symbolic signing model in SymbolicSigning.
-- Provenance is message-level (encode may collide); it does not identify the
-- request a later call intends, and it says nothing about contract acceptance.
-- Approval is a trusted abstract input, not authenticated consent. Scope:
-- docs/conformance-testing-plan.md#symbolic-signing-and-adversarial-histories.
module Midnight.ContractDSL.SymbolicSigningProperties where

open import Data.List.Membership.Propositional using (_∈_)
open import Data.Sum.Base using (_⊎_)
open import Midnight.ContractDSL.SymbolicSigning
import Midnight.ContractDSL.SymbolicSigningProof as Proof
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

module Properties {ℓ} (S : Interface ℓ) where
  open Interface S
  open Model S
  module P = Proof.Proofs S

  -- Attacker control (attacker ownership or compromise) is never lost.
  step-controlled : ∀ {s t k} → Transition s t → Controlled s k → Controlled t k
  step-controlled = P.step-controlled

  trace-controlled : ∀ {s t k} → Trace s t → Controlled s k → Controlled t k
  trace-controlled = P.trace-controlled

  -- Issued signature tokens are never consumed, so they remain replayable.
  step-available : ∀ {s t τ} → Transition s t → Available s τ → Available t τ
  step-available = P.step-available

  trace-available : ∀ {s t τ} → Trace s t → Available s τ → Available t τ
  trace-available = P.trace-available

  -- Approvals persist and may back any number of later honest signatures.
  step-approved : ∀ {s t k r} → Transition s t → Approved s k r → Approved t k r
  step-approved = P.step-approved

  trace-approved : ∀ {s t k r} → Trace s t → Approved s k r → Approved t k r
  trace-approved = P.trace-approved

  -- From the empty initial state, a token is available only if its key is now
  -- attacker-controlled or the trace contains an approved honest signing of a
  -- request that encodes to its message.
  signature-provenance : ∀ {t τ} (trace : Trace initial t) → Available t τ →
    Controlled t (Token.key τ) ⊎ HonestlyIssued trace τ
  signature-provenance = P.signature-provenance

  -- For an honest key still uncompromised at the end, only honest issuance remains.
  honest-signature-provenance : ∀ {t τ} (trace : Trace initial t) → Available t τ →
    ownership (Token.key τ) ≡ honest → ¬ (Token.key τ ∈ State.compromised t) →
    HonestlyIssued trace τ
  honest-signature-provenance = P.honest-signature-provenance

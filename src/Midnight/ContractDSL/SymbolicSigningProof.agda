{-# OPTIONS --safe --without-K #-}

module Midnight.ContractDSL.SymbolicSigningProof where

open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; map₂)
open import Midnight.ContractDSL.SymbolicSigning
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module Proofs {ℓ} (S : Interface ℓ) where
  open Interface S
  open Model S

  apply-controlled : ∀ {s k} e → Controlled s k → Controlled (apply e s) k
  apply-controlled (approve _ _) c = c
  apply-controlled (honestSign _ _) c = c
  apply-controlled (attackerSign _ _) c = c
  apply-controlled (compromise _) c = map₂ there c

  apply-available : ∀ {s τ} e → Available s τ → Available (apply e s) τ
  apply-available (approve _ _) a = a
  apply-available (honestSign _ _) a = there a
  apply-available (attackerSign _ _) a = there a
  apply-available (compromise _) a = a

  apply-approved : ∀ {s k r} e → Approved s k r → Approved (apply e s) k r
  apply-approved (approve _ _) a = there a
  apply-approved (honestSign _ _) a = a
  apply-approved (attackerSign _ _) a = a
  apply-approved (compromise _) a = a

  step-controlled : ∀ {s t k} → Transition s t → Controlled s k → Controlled t k
  step-controlled (transition e _ refl) c = apply-controlled e c

  trace-controlled : ∀ {s t k} → Trace s t → Controlled s k → Controlled t k
  trace-controlled ε c = c
  trace-controlled (x ◅ rest) c = trace-controlled rest (step-controlled x c)

  step-available : ∀ {s t τ} → Transition s t → Available s τ → Available t τ
  step-available (transition e _ refl) a = apply-available e a

  trace-available : ∀ {s t τ} → Trace s t → Available s τ → Available t τ
  trace-available ε a = a
  trace-available (x ◅ rest) a = trace-available rest (step-available x a)

  step-approved : ∀ {s t k r} → Transition s t → Approved s k r → Approved t k r
  step-approved (transition e _ refl) a = apply-approved e a

  trace-approved : ∀ {s t k r} → Trace s t → Approved s k r → Approved t k r
  trace-approved ε a = a
  trace-approved (x ◅ rest) a = trace-approved rest (step-approved x a)

  ------------------------------------------------------------------------
  -- Provenance

  later-issued : ∀ {s m t τ} (x : Transition s m) {rest : Trace m t} →
    HonestlyIssued rest τ → HonestlyIssued (x ◅ rest) τ
  later-issued x (issued r b h a e o) = issued r b h a e (later x o)

  -- The token added by the first, permitted event of a trace.
  fresh : ∀ {s t τ e} (p : Permitted s e) (rest : Trace (apply e s) t) →
    Available (apply e s) τ →
    Available s τ ⊎ Controlled t (Token.key τ) ⊎ HonestlyIssued (transition e p refl ◅ rest) τ
  fresh (honestApproval _) _ a = inj₁ a
  fresh {s = s} p@(approvedSigning {r = r} h approval) rest (here refl) =
    inj₂ (inj₂ (issued r s h approval refl (now p refl rest)))
  fresh (approvedSigning _ _) _ (there a) = inj₁ a
  fresh (controlledSigning {k} c) rest (here refl) =
    inj₂ (inj₁ (trace-controlled {k = k} rest c))
  fresh (controlledSigning _) _ (there a) = inj₁ a
  fresh anyCompromise _ a = inj₁ a

  -- Every token available at the end was available at the start, has a key
  -- controlled at the end, or was honestly issued within the trace.
  origin : ∀ {s t τ} (trace : Trace s t) → Available t τ →
    Available s τ ⊎ Controlled t (Token.key τ) ⊎ HonestlyIssued trace τ
  origin ε a = inj₁ a
  origin (transition e p refl ◅ rest) a with origin rest a
  ... | inj₁ a′ = fresh p rest a′
  ... | inj₂ (inj₁ c) = inj₂ (inj₁ c)
  ... | inj₂ (inj₂ i) = inj₂ (inj₂ (later-issued (transition e p refl) i))

  signature-provenance : ∀ {t τ} (trace : Trace initial t) → Available t τ →
    Controlled t (Token.key τ) ⊎ HonestlyIssued trace τ
  signature-provenance trace a with origin trace a
  ... | inj₁ ()
  ... | inj₂ provenance = provenance

  honest≢attacker : honest ≢ attacker
  honest≢attacker ()

  honest-signature-provenance : ∀ {t τ} (trace : Trace initial t) → Available t τ →
    ownership (Token.key τ) ≡ honest → ¬ (Token.key τ ∈ State.compromised t) →
    HonestlyIssued trace τ
  honest-signature-provenance trace a h uncompromised with signature-provenance trace a
  ... | inj₁ (inj₁ owned) = ⊥-elim (honest≢attacker (trans (sym h) owned))
  ... | inj₁ (inj₂ c) = ⊥-elim (uncompromised c)
  ... | inj₂ issuance = issuance

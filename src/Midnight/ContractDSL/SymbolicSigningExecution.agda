{-# OPTIONS --safe --without-K #-}

-- Optional executable support for SymbolicSigning's declarative policy.
-- Decidable equality is needed here, not by the model or its security properties.
-- certify turns a successful step into a permitted model Transition; the
-- properties' lookup closure does not depend on these decision procedures.
module Midnight.ContractDSL.SymbolicSigningExecution where

import Data.List.Membership.DecPropositional as DecMembership
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base using (_,_)
open import Data.Product.Properties using (≡-dec)
open import Midnight.ContractDSL.SymbolicSigning
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (map′; _×-dec_; _⊎-dec_)

module Executable {ℓ} (S : Interface ℓ)
  (keyEq : DecidableEquality (Interface.Key S))
  (requestEq : DecidableEquality (Interface.Request S))
  (messageEq : DecidableEquality (Interface.Message S)) where
  open Interface S
  open Model S
  open State

  module KeyMembership = DecMembership keyEq
  module ApprovalMembership = DecMembership (≡-dec keyEq requestEq)

  tokenEq : DecidableEquality Token
  tokenEq (signature k m) (signature k′ m′) =
    map′ (λ { (refl , refl) → refl }) (λ { refl → refl , refl }) (keyEq k k′ ×-dec messageEq m m′)

  module TokenMembership = DecMembership tokenEq

  honest? : (o : Ownership) → Dec (o ≡ honest)
  honest? honest = yes refl
  honest? attacker = no λ ()

  attacker? : (o : Ownership) → Dec (o ≡ attacker)
  attacker? honest = no λ ()
  attacker? attacker = yes refl

  controlled? : (s : State) (k : Key) → Dec (Controlled s k)
  controlled? s k = attacker? (ownership k) ⊎-dec KeyMembership._∈?_ k (compromised s)

  approved? : (s : State) (k : Key) (r : Request) → Dec (Approved s k r)
  approved? s k r = ApprovalMembership._∈?_ (k , r) (approvals s)

  available? : (s : State) (τ : Token) → Dec (Available s τ)
  available? s τ = TokenMembership._∈?_ τ (signatures s)

  permitted? : (s : State) (e : Event) → Dec (Permitted s e)
  permitted? s (approve k r) =
    map′ honestApproval (λ { (honestApproval h) → h }) (honest? (ownership k))
  permitted? s (honestSign k r) =
    map′ (λ (h , a) → approvedSigning h a) (λ { (approvedSigning h a) → h , a })
      (honest? (ownership k) ×-dec approved? s k r)
  permitted? s (attackerSign k m) =
    map′ controlledSigning (λ { (controlledSigning c) → c }) (controlled? s k)
  permitted? s (compromise k) = yes anyCompromise

  step : Event → State → Maybe State
  step e s with permitted? s e
  ... | yes _ = just (apply e s)
  ... | no _ = nothing

  certify : ∀ {e s t} → step e s ≡ just t → Transition s t
  certify {e} {s} executed with permitted? s e
  certify {e} refl | yes p = transition e p refl
  certify () | no _

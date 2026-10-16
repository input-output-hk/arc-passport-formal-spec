{-# OPTIONS --safe --without-K #-}

open import Midnight.ContractDSL.Ledger

module Midnight.ContractDSL.ReplayProof (L : Semantics) (Assertion : Set) where

open import Class.DecEq
open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Midnight.ContractDSL.Program L Assertion

open Semantics L
open Execution L

private
  variable A : Set
           k : Kind
           s t : State
           r : Res k

  validate-self : (o : Op k) (t : State) → validate o r (inj₂ (r , t)) ≡ just t
  validate-self {r = r} o t with r ≟ r
  ... | yes _ = refl
  ... | no neq = ⊥-elim (neq refl)

  same-view : (o : Op k) → prepare o s ≡ inj₂ (r , t) → apply o r s ≡ just t
  same-view o eq = trans (cong (validate o _) eq) (validate-self o _)

  validate-rebase : (o : Op k) (x : Res k) (r : Failure k ⊎ (Res k × State)) →
    validate o x r ≡ just t → r ≡ inj₂ (x , t)
  validate-rebase o x (inj₂ (y , s)) eq with x ≟ y | eq
  ... | yes refl | refl = refl

  rebase : (o : Op k) → apply o r s ≡ just t → prepare o s ≡ inj₂ (r , t)
  rebase o = validate-rebase o _ (prepare o _)

  prefix-success : (e : Event) (r : Outcome A) {a : A} {j : Journal} →
    prefix e r ≡ inj₂ (finished a t j) → ∃[ es ] j ≡ e ∷ es × r ≡ inj₂ (finished a t es)
  prefix-success e (inj₂ (finished a t j)) refl = j , refl , refl

  replay-operation : (now : ℕ) (o : Op k) (x : Res k) (j : Journal) →
    replay now (operated o x ∷ j) s ≡ just t →
    ∃[ u ] apply o x s ≡ just u × replay now j u ≡ just t
  replay-operation {s = s} now o x j eq with apply o x s
  ... | just u = u , refl , eq

  replay-required : (now : ℕ) (c : Condition) (j : Journal) →
    replay now (required c ∷ j) s ≡ just t → replay now j s ≡ just t
  replay-required now c j eq with holds c now
  ... | true = eq

replay-refinement : (p : Program A) (now : ℕ) {s₀ s t₀ t : State} {a : A} {j : Journal} →
  eval p s₀ ≡ inj₂ (finished a t₀ j) → replay now j s ≡ just t →
  eval p s ≡ inj₂ (finished a t j)
replay-refinement (pure a) now refl refl = refl
replay-refinement (step (ledger o) k) now {s₀} {s} ev rp with prepare o s₀
... | inj₂ (x , u₀) with prefix-success (operated o x) (eval (k x) u₀) ev
... | es , refl , tail with replay-operation now o x es rp
... | u , app , rest rewrite rebase o app =
  cong (prefix (operated o x)) (replay-refinement (k x) now tail rest)
replay-refinement (step (require true err) k) now ev rp = replay-refinement (k tt) now ev rp
replay-refinement (step (publish v) k) now {s₀} ev rp
  with prefix-success (published v) (eval (k tt) s₀) ev
... | es , refl , tail = cong (prefix (published v)) (replay-refinement (k tt) now tail rp)
replay-refinement (step (atChain c) k) now {s₀} {s} ev rp
  with prefix-success (required c) (eval (k tt) s₀) ev
... | es , refl , tail = cong (prefix (required c))
  (replay-refinement (k tt) now tail (replay-required now c es rp))

same-view-replay : (p : Program A) (now : ℕ) {s t : State} {a : A} {j : Journal} →
  eval p s ≡ inj₂ (finished a t j) → Eligible now j → replay now j s ≡ just t
same-view-replay (pure a) now refl eligible = refl
same-view-replay (step (ledger o) k) now {s} ev eligible with prepare o s in prepared
... | inj₂ (x , u) with prefix-success (operated o x) (eval (k x) u) ev
... | es , refl , tail rewrite same-view o prepared = same-view-replay (k x) now tail eligible
same-view-replay (step (require true err) k) now ev eligible = same-view-replay (k tt) now ev eligible
same-view-replay (step (publish v) k) now {s} ev eligible
  with prefix-success (published v) (eval (k tt) s) ev
... | es , refl , tail = same-view-replay (k tt) now tail eligible
same-view-replay (step (atChain c) k) now {s} ev eligible
  with prefix-success (required c) (eval (k tt) s) ev
... | es , refl , tail rewrite proj₁ eligible = same-view-replay (k tt) now tail (proj₂ eligible)

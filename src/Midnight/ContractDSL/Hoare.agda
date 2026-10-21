{-# OPTIONS --safe --without-K #-}

open import Midnight.ContractDSL.Ledger

module Midnight.ContractDSL.Hoare (L : Semantics) (Assertion : Set) where

open import Data.Bool
open import Data.List
open import Data.Maybe hiding (_>>=_)
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Function

open Semantics L
open import Midnight.ContractDSL.Program L Assertion
import Midnight.ContractDSL.Properties L Assertion as Replay

private variable A B : Set

onSuccess : (Finished A → Set) → Outcome A → Set
onSuccess Q (inj₁ _) = ⊤
onSuccess Q (inj₂ r) = Q r

Hoare : (State → Set) → Program A → (Outcome A → Set) → Set
Hoare P p Q = ∀ s → P s → Q (eval p s)

lift-Hoare : {P : State → Set} {Q : Outcome A → Set}
  (p : Program A) (now : ℕ) → Hoare P p Q →
  ∀ {s₀ s a t₀ t j} → P s → eval p s₀ ≡ inj₂ (finished a t₀ j) →
  replay now j s ≡ just t → Q (inj₂ (finished a t j))
lift-Hoare {Q = Q} p now h {s = s} pre ev rp =
  subst Q (Replay.replay-refinement p now ev rp) (h s pre)

hoare-pure : {P : State → Set} {Q : Outcome A → Set} (a : A) →
  (∀ s → P s → Q (inj₂ (finished a s []))) → Hoare P (pure a) Q
hoare-pure a h = h

hoare-assert : {P : State → Set} {Q : Outcome ⊤ → Set}
  (b : Bool) (err : Assertion) →
  (∀ s → P s → b ≡ false → Q (inj₁ (assertionError err))) →
  (∀ s → P s → b ≡ true  → Q (inj₂ (finished tt s []))) →
  Hoare P (assert b err) Q
hoare-assert false err failed passed s pre = failed s pre refl
hoare-assert true err failed passed s pre = passed s pre refl

hoare-ledger : {k : Kind} {P : State → Set} {Q : Outcome (Res k) → Set}
  (o : Op k) →
  (∀ s err → P s → prepare o s ≡ inj₁ err → Q (inj₁ (operationError err))) →
  (∀ s x t → P s → prepare o s ≡ inj₂ (x , t) →
    Q (inj₂ (finished x t (operated o x ∷ [])))) →
  Hoare P (perform (ledger o)) Q
hoare-ledger o failed passed s pre with prepare o s in prepared
... | inj₁ err = failed s err pre prepared
... | inj₂ (x , t) = passed s x t pre prepared

hoare-bind : {P : State → Set} {R : Outcome A → Set}
  {Q : Outcome B → Set} (p : Program A) (f : A → Program B) →
  Hoare P p R →
  (∀ err → R (inj₁ err) → Q (inj₁ err)) →
  (∀ a js → Hoare (λ u → R (inj₂ (finished a u js))) (f a)
    (λ outcome → Q (prefixJournal js outcome))) →
  Hoare P (p >>= f) Q
hoare-bind p f first failed rest s pre rewrite eval-bind p f s
  with eval p s | first s pre
... | inj₁ err | held = failed err held
... | inj₂ (finished a u js) | held = rest a js u held

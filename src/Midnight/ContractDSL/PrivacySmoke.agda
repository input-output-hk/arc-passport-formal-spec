{-# OPTIONS --safe --without-K --guardedness #-}

-- Exhaustive joint-tree normalization: warm check ~25 s with -M16G -H1G.
-- The canonical 3 GiB heap exhausts on the unified interpreter's private drafts.

module Midnight.ContractDSL.PrivacySmoke where

open import Data.Bool.Base hiding (_≤_; _<_)
open import Data.Empty
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base hiding (_≤_; _<_)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; ½; _≤_; _<_)
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)

import Data.Rational.Properties as ℚP
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Advantage
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.Uniform
open import CategoricalCrypto.Iface
open import ProbabilisticLogic.Dp.Advantage
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Agree
open import CategoricalCrypto.Protocol.Observe
open import Midnight.ContractDSL.MidnightLedger
open import Midnight.ContractDSL.Merkle
open import Midnight.ContractDSL.MerkleFixture hiding (a; b; c; d)
open import Midnight.ContractDSL.Privacy
open import Midnight.ContractDSL.Program midnight Assertion hiding (step)

open I using (accepted; rejected)
open Prepared
open I.Statement
open View

singleTag : Bool → Dist⊥ Bool
singleTag cl = uniform-Bool >>=ᴹ λ m → return⊥ (cl xor m)

single-tag-uniform : (cl tag : Bool) → Prᵇ⊥ tag (singleTag cl) ≡ ½
single-tag-uniform false false = refl
single-tag-uniform false true = refl
single-tag-uniform true false = refl
single-tag-uniform true true = refl

tag : Journal → Maybe Bool
tag [] = nothing
tag (operated (flagMember b) _ ∷ xs) = just b
tag (_ ∷ xs) = tag xs

attack : View → Bool
attack v with tag (effects (publicClaim (firstDraft v))) |
  tag (effects (publicClaim (secondDraft v)))
... | just x | just y = x xor y
... | _ | _ = false

successfulView : View → Bool
successfulView (view p accepted x q accepted y) = true
successfulView _ = false

system : Variant → Bool → Protocol unitᴵ SessionIf
system v w = assembled idealResources (history v w)

-- This reader retains the full joint view, not only the XOR verdict. It drives
-- five distinct activations of the very same composed upstream protocol.
jointTree : (P : Protocol unitᴵ SessionIf) → Calls unitᴵ (Maybe View)
jointTree P = step P (init P) beginSession >>=ᶜ λ
  { (s , ready) → step P s prepareFirst >>=ᶜ λ
      { (s , draft p) → step P s submitFirst >>=ᶜ λ
          { (s , outcome v x) → step P s prepareSecond >>=ᶜ λ
              { (s , draft q) → step P s submitSecond >>=ᶜ λ
                  { (s , outcome w y) → ret (just (view p v x q w y))
                  ; _ → ret nothing }
              ; _ → ret nothing }
          ; _ → ret nothing }
      ; _ → ret nothing }
  ; _ → ret nothing }

jointObservable : Variant → Bool → Dist⊥ (Maybe View)
jointObservable v w = evalC (jointTree (system v w))

secure-joint-observable-equality : jointObservable secure false ≈Mℚ jointObservable secure true
secure-joint-observable-equality F = refl

successfulProbability : Variant → Bool → ℚ
successfulProbability v w = Pr (system v w) (observer successfulView)

secure-same-success : successfulProbability secure false ≡ 1ℚ
secure-same-success = refl
secure-different-success : successfulProbability secure true ≡ 1ℚ
secure-different-success = refl
insecure-same-success : successfulProbability insecure false ≡ 1ℚ
insecure-same-success = refl
insecure-different-success : successfulProbability insecure true ≡ 1ℚ
insecure-different-success = refl

attackProbability : Variant → Bool → ℚ
attackProbability v w = Pr (system v w) (observer attack)

secure-observer-same : attackProbability secure false ≡ attackProbability secure true
secure-observer-same = refl
insecure-observer-zero : attackProbability insecure false ≡ 0ℚ
insecure-observer-zero = refl
insecure-observer-one : attackProbability insecure true ≡ 1ℚ
insecure-observer-one = refl

insecure-gap-one : advᵇ⊥ true (runObs (system insecure false) (observer attack))
  (runObs (system insecure true) (observer attack)) ≡ 1ℚ
insecure-gap-one = refl

-- Keep the finite settling budget abstract: unfolding its machine derivation
-- while checking a contradiction needlessly expands the entire execution.
opaque
  attack-one-settles : Σ ℕ (λ n → (m : ℕ) →
    Pr≤[ true ] (n + m) (runᴹ (morphism (system insecure true)) (observer attack)) ≡ 1ℚ)
  attack-one-settles = history-observation-settles idealResources (history insecure true)
    true (observer attack) 1ℚ insecure-observer-one

  attack-zero-upper : Upper (runᴹ (morphism (system insecure false)) (observer attack)) 0ℚ
  attack-zero-upper = history-observation-upper idealResources (history insecure false)
    (observer attack) 0ℚ (ℚP.≤-reflexive insecure-observer-zero)

-- The negation is of HistoryPrivacy, exactly the property proved secure.
insecure-not-private : ¬ HistoryPrivacy idealResources (history insecure false) (history insecure true)
insecure-not-private h = impossible (ℚP.≤-trans (ℚP.≤-reflexive (sym (hp 0)))
  (ℚP.≤-trans bd (ℚP.+-monoˡ-≤ ½ (attack-zero-upper m))))
  where
  positive : 0ℚ < ½
  positive = toWitness {a? = 0ℚ ℚP.<? ½} tt
  impossible : ¬ (1ℚ ≤ ½)
  impossible = toWitnessFalse {a? = 1ℚ ℚP.≤? ½} tt
  n-and-hp = attack-one-settles
  n = proj₁ n-and-hp
  hp = proj₂ n-and-hp
  m-and-bd = proj₂ (h (observer attack) ½ positive) true (n + 0)
  m = proj₁ m-and-bd
  bd = proj₂ m-and-bd

freshPair : Bool → Dist-ℚ (Bool × Bool)
freshPair world = uniform-Bool >>=ᴹ λ x → uniform-Bool >>=ᴹ λ y →
  return-ℚ (x , (world xor y))

pairIndicator : Bool → Bool → Bool × Bool → ℚ
pairIndicator false false (false , false) = 1ℚ
pairIndicator false true (false , true) = 1ℚ
pairIndicator true false (true , false) = 1ℚ
pairIndicator true true (true , true) = 1ℚ
pairIndicator _ _ _ = 0ℚ

fresh-pair-quarter : (w x y : Bool) → E (freshPair w) (pairIndicator x y) ≡ (½ ℚ.* ½)
fresh-pair-quarter false false false = refl
fresh-pair-quarter false false true = refl
fresh-pair-quarter false true false = refl
fresh-pair-quarter false true true = refl
fresh-pair-quarter true false false = refl
fresh-pair-quarter true false true = refl
fresh-pair-quarter true true false = refl
fresh-pair-quarter true true true = refl

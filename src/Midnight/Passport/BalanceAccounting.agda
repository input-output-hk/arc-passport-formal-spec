{-# OPTIONS --safe #-}

-- Accounting for one selected balance query. A keyed interface selects a
-- different port and transaction valuation for each account–asset pair.
module Midnight.Passport.BalanceAccounting where

open import Data.Integer using (ℤ; 0ℤ; +_; _+_; _≤_)
open import Data.Nat using (ℕ)
open import Data.Product
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Machine.Core
import CategoricalCrypto.Machine.Relay as Relay
open import CategoricalCrypto.Machine.Relay using (Port)
open import CategoricalCrypto.Machine.Valuation

module BalanceAccounting {A B : Channel} (M : Machine A B)
  (port : Port M ⊤ ℕ)
  (txValue : Val (Machine.machine-channel M))
  (s₀ : Machine.State M) (b₀ : ℕ) where

  open Machine M renaming (State to S)

  Answers : S → ℕ → Set
  Answers s = Relay.Answers port s tt

  netFlow : ∀ {s₁ s₂} → Trace M s₁ s₂ → ℤ
  netFlow = flow txValue

  realBalance : ∀ {s} → Trace M s₀ s → ℤ
  realBalance t = + b₀ + netFlow t

  Sound : Set
  Sound = ∀ {s a} (t : Trace M s₀ s) → Answers s a → + a ≤ realBalance t

  EventuallyAccurate : Set
  EventuallyAccurate = ∀ {s} (t : Trace M s₀ s) →
    ∃[ s' ] Σ[ u ∈ Trace M s s' ]
      (netFlow u ≡ 0ℤ × ∃[ a ] (+ a ≡ realBalance t × Answers s' a))

  PromptlyAccurate : Set
  PromptlyAccurate = ∀ {s} (t : Trace M s₀ s) →
    ∃[ a ] (+ a ≡ realBalance t × Answers s a)

  Statement : Set
  Statement = Sound × EventuallyAccurate

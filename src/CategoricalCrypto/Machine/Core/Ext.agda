{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- CategoricalCrypto.Machine.Core.Ext
--
-- Vocabulary `CategoricalCrypto.Machine.Core` leaves out: the messages a
-- machine's own channel carries, and concatenation of its traces.
------------------------------------------------------------------------

module CategoricalCrypto.Machine.Core.Ext where

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Machine.Core

private variable A B : Channel

Msg : Machine A B → Mode → Set
Msg M m = modeType m (Machine.machine-channel M)

module _ {M : Machine A B} where
  infixl 5 _++ᵗ_
  _++ᵗ_ : ∀ {s₁ s₂ s₃} → Trace M s₁ s₂ → Trace M s₂ s₃ → Trace M s₁ s₃
  t ++ᵗ []                   = t
  t ++ᵗ (u ∷ʳ⟨ i , o , st ⟩) = (t ++ᵗ u) ∷ʳ⟨ i , o , st ⟩

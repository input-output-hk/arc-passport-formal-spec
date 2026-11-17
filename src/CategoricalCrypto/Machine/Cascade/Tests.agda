{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

module CategoricalCrypto.Machine.Cascade.Tests where

open import categorical-crypto.Prelude hiding (id; _∘_)
open import Data.Integer using (0ℤ)

open import Tactic.Defaults
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Cascade
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Simulation
open import CategoricalCrypto.Machine.Valuation
open import CategoricalCrypto.Machine.Wiring

open Machine
private variable A B C D : Channel

--------------------------------------------------------------------------------
-- Tensor round-trip: constructing a tagged component step then inverting it
-- selects the matching handler. Stated on genuine `CompRel` values, so no
-- opaque reshuffle is in play.

comp-elimL-law : ∀ {M₁ : Machine A B} {M₂ : Machine C D} {sₐ mᵢ mₒ sₐ' s₂}
                 (st : stepRel M₁ sₐ mᵢ mₒ sₐ')
               → comp-elim {M₁ = M₁} {M₂ = M₂} {P = ℕ} (compL {s₂ = s₂} st) (λ _ → 0) (λ _ → 1) ≡ 0
comp-elimL-law st = refl

comp-elimR-law : ∀ {M₁ : Machine A B} {M₂ : Machine C D} {sᵦ mᵢ mₒ sᵦ' s₁}
                 (st : stepRel M₂ sᵦ mᵢ mₒ sᵦ')
               → comp-elim {M₁ = M₁} {M₂ = M₂} {P = ℕ} (compR {s₁ = s₁} st) (λ _ → 0) (λ _ → 1) ≡ 1
comp-elimR-law st = refl

comp-invL-law : ∀ {M₁ : Machine A B} {M₂ : Machine C D} {sₐ mᵢ mₒ sₐ' s₂}
                (st : stepRel M₁ sₐ mᵢ mₒ sₐ')
              → comp-inv {M₁ = M₁} {M₂ = M₂} {P = ℕ} (compL {s₂ = s₂} st)
                  (λ _ _ _ _ → 0) (λ _ _ _ _ → 1) ≡ 0
comp-invL-law st = refl

-- Lane-determined inversion at the lane the step was tagged on hands the step
-- back unchanged: the tag injectivity it coerces through must be unfolded for
-- the coercion to compute away.

opaque
  unfolding tagˡ-inj tagʳ-inj

  comp-atˡ-just-law : ∀ {M₁ : Machine A B} {M₂ : Machine C D} {sₐ mᵢ mₒ sₐ' s₂}
                      (st : stepRel M₁ sₐ mᵢ (just mₒ) sₐ')
                    → comp-atˡ-just {M₁ = M₁} {M₂ = M₂} (compL {s₂ = s₂} st)
                        (λ st' _ → st') ≡ st
  comp-atˡ-just-law st = refl

  comp-atʳ-just-law : ∀ {M₁ : Machine A B} {M₂ : Machine C D} {sᵦ mᵢ mₒ sᵦ' s₁}
                      (st : stepRel M₂ sᵦ mᵢ (just mₒ) sᵦ')
                    → comp-atʳ-just {M₁ = M₁} {M₂ = M₂} (compR {s₁ = s₁} st)
                        (λ st' _ → st') ≡ st
  comp-atʳ-just-law st = refl

--------------------------------------------------------------------------------
-- Trace base computation law (any traced machine).

trace-base-law : ∀ {N : Machine (A ⊗₀ C) (B ⊗₀ C)} {s i o s'} (st : stepRel N s i o s')
               → trace-ind {M = N} (λ _ → ℕ) (λ _ → 1) (λ _ n → suc n) (λ _ n → suc n) Trace[ st ] ≡ 1
trace-base-law st = refl

--------------------------------------------------------------------------------
-- Composition layer against the real `_∘_` solver terms: `trace-ind` traverses
-- the cascade of a genuine `M ∘ M` step, counting its nodes. Exercises that a
-- composite step IS a `TraceRel` cascade whose whole traced machine is inferred
-- through `tr`'s two `modifyStepRel` layers and the inner `⊗₁` — the inversion
-- entry point, validated on concrete hand-rolled machines.

Uᶜ : Channel
Uᶜ = ⊤ ⇿ ⊤

M : Machine Uᶜ Uᶜ
M = StatelessMachine λ _ _ → ⊤

∘-nodes : ∀ {s i o s'} → stepRel (M ∘ M) s i o s' → ℕ
∘-nodes = trace-ind (λ _ → ℕ) (λ _ → 1) (λ _ n → suc n) (λ _ n → suc n)

--------------------------------------------------------------------------------
-- ⊗₁ reshuffle against the real baked `_⊗₁_` solver: build a composite step from
-- a left component step (`⊗₁-mkˡ`), invert it back to a `CompRel` at the named
-- message (`⊗₁-compˡ`), and confirm `comp-elim` routes to the left handler.
-- Needs the Channel.Core unfolding to reduce the baked solver in `comp-elim`.
-- The step carries a *value-bearing* output on the codomain wire (`inj₂`), the
-- shape an answer takes, which the old `nothing`-only inversion could not reach.

opaque
  unfolding _⊗₀_ destruct-⊗ ⊗-right-intro ⊗-sym ⊗-combine ⊗-fusion ⊗-right-neutral
            ⊗₁-mkˡ ⊗₁-compˡ ⊗₁-inˡ

  ⊗₁-reshuffle-roundtrip
    : ∀ {s₂ : ⊤} (st : stepRel M tt (ϵ ⊗R ↑ᵢ tt) (just (L⊗ (ϵ ᵗ¹) ↑ᵢ tt)) tt)
    → comp-elim {M₁ = M} {M₂ = M} {P = ℕ}
        (⊗₁-compˡ {M₁ = M} {M₂ = M} {i = ϵ ⊗R ↑ᵢ tt} {o = just (L⊗ (ϵ ᵗ¹) ↑ᵢ tt)}
          (⊗₁-mkˡ (compL {s₂ = s₂} st)))
        (λ _ → 0) (λ _ → 1) ≡ 0
  ⊗₁-reshuffle-roundtrip st = refl

--------------------------------------------------------------------------------
-- Weight bookkeeping across the real baked reshuffle: a `⊗₁` link of a
-- flow-preserving simulation, at weights that mark the left factor's domain
-- wire (the shape the architecture's CHAIN-wire valuations have) and vanish on
-- the right factor, which is then `Neutral` for free. The same link then
-- transports to a weight written out message by message, which is what makes
-- the structured form no restriction.

Vᶜ : Channel
Vᶜ = ℤ ⇿ ℤ

Mⱽ : Machine Vᶜ Vᶜ
Mⱽ = StatelessMachine λ _ _ → ⊤

-- a wire whose messages are worth what they carry
wireᵥ : MVal Vᶜ
wireᵥ In  x = x
wireᵥ Out x = x

⊗₁-link : Preserves (⊗₁-simˡ {M₁ = Mⱽ} {M₂ = Mⱽ})
                    (netVal (bdryᵥ (wireᵥ ⊗ᵥ 0ᵥ) (0ᵥ {Vᶜ} ⊗ᵥ 0ᵥ)))
                    (netVal (bdryᵥ wireᵥ 0ᵥ))
⊗₁-link = ⊗₁ᵥ-preservesˡ {μ = wireᵥ} {0ᵥ} {0ᵥ} {0ᵥ} (zeroᵥ-neutral 0ᵥ-zero 0ᵥ-zero)

opaque
  unfolding _⊗₀_ destruct-⊗ ⊗-right-intro ⊗-sym ⊗-combine ⊗-fusion ⊗-right-neutral

  μ⊗ : MVal ((Vᶜ ⊗₀ Vᶜ) ⊗ᵀ (Vᶜ ⊗₀ Vᶜ))
  μ⊗ In  (inj₁ (inj₁ x)) = x
  μ⊗ In  (inj₁ (inj₂ _)) = 0ℤ
  μ⊗ In  (inj₂ _)        = 0ℤ
  μ⊗ Out (inj₁ (inj₁ x)) = x
  μ⊗ Out (inj₁ (inj₂ _)) = 0ℤ
  μ⊗ Out (inj₂ _)        = 0ℤ

  structuredᵥ : bdryᵥ (wireᵥ ⊗ᵥ 0ᵥ) (0ᵥ {Vᶜ} ⊗ᵥ 0ᵥ) ≗ᵥ μ⊗
  structuredᵥ In  (inj₁ (inj₁ _)) = refl
  structuredᵥ In  (inj₁ (inj₂ _)) = refl
  structuredᵥ In  (inj₂ (inj₁ _)) = refl
  structuredᵥ In  (inj₂ (inj₂ _)) = refl
  structuredᵥ Out (inj₁ (inj₁ _)) = refl
  structuredᵥ Out (inj₁ (inj₂ _)) = refl
  structuredᵥ Out (inj₂ (inj₁ _)) = refl
  structuredᵥ Out (inj₂ (inj₂ _)) = refl

⊗₁-link-exotic : Preserves (⊗₁-simˡ {M₁ = Mⱽ} {M₂ = Mⱽ})
                           (netVal μ⊗) (netVal (bdryᵥ wireᵥ 0ᵥ))
⊗₁-link-exotic = preserves-cong (netVal-cong structuredᵥ) (λ _ _ → refl) ⊗₁-link

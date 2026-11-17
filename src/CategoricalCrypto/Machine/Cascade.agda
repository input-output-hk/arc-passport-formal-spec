{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

module CategoricalCrypto.Machine.Cascade where

open import categorical-crypto.Prelude hiding (id; _∘_)
open import Data.Maybe.Base using () renaming (map to mapₘ)
open import Data.Maybe.Properties using (just-injective)

open import Tactic.Defaults
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core

private variable A B C D : Channel

--------------------------------------------------------------------------------
-- modifyStepRel is definitional: a step of the wrapped machine reduces to a
-- step of the core at translated messages.

module _ {p : ∀ {m} → C ⊗₀ D ᵀ [ m ]⇒[ m ] A ⊗₀ B ᵀ} {M : Machine A B} where
  open Machine

  unmodify : ∀ {s i o s'} → stepRel (modifyStepRel p M) s i o s'
           → stepRel M s (app {mᵢ = In} p i) (mapₘ (app {mₒ = Out} p) o) s'
  unmodify st = st

  remodify : ∀ {s i o s'} → stepRel M s (app {mᵢ = In} p i) (mapₘ (app {mₒ = Out} p) o) s'
           → stepRel (modifyStepRel p M) s i o s'
  remodify st = st

--------------------------------------------------------------------------------
-- Tensor messages: the two ways a component's message sits in a tensor — tagged
-- as `Tensor.CompRel` sees it, and embedded at the `_⊗₁_` boundary. These depend
-- on the channels alone (a machine is not recoverable from such a type), so they
-- live here and are used at whatever machines.

module _ {A B C D : Channel} where
  tagˡ : ∀ {m} → modeType m (A ⊗ᵀ B) → modeType m ((A ⊗ᵀ B) ⊗₀ (C ⊗ᵀ D))
  tagˡ {m} = app {mᵢ = m} {mₒ = m} ((ϵ ⊗R) ↑)

  tagʳ : ∀ {m} → modeType m (C ⊗ᵀ D) → modeType m ((A ⊗ᵀ B) ⊗₀ (C ⊗ᵀ D))
  tagʳ {m} = app {mᵢ = m} {mₒ = m} (L⊗ ϵ ↑)

  opaque
    unfolding _⊗₀_ destruct-⊗ ⊗-right-intro ⊗-sym ⊗-combine ⊗-fusion ⊗-right-neutral

    -- a component's message at the `M₁ ⊗₁ M₂` boundary
    ⊗₁-inˡ : ∀ {m} → modeType m (A ⊗ᵀ B) → modeType m ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ D))
    ⊗₁-inˡ {In}  (inj₁ x) = inj₁ (inj₁ x)
    ⊗₁-inˡ {In}  (inj₂ x) = inj₂ (inj₁ x)
    ⊗₁-inˡ {Out} (inj₁ x) = inj₁ (inj₁ x)
    ⊗₁-inˡ {Out} (inj₂ x) = inj₂ (inj₁ x)

    ⊗₁-inʳ : ∀ {m} → modeType m (C ⊗ᵀ D) → modeType m ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ D))
    ⊗₁-inʳ {In}  (inj₁ x) = inj₁ (inj₂ x)
    ⊗₁-inʳ {In}  (inj₂ x) = inj₂ (inj₂ x)
    ⊗₁-inʳ {Out} (inj₁ x) = inj₁ (inj₂ x)
    ⊗₁-inʳ {Out} (inj₂ x) = inj₂ (inj₂ x)

    tagˡ-inj : ∀ {m} {x y : modeType m (A ⊗ᵀ B)} → tagˡ x ≡ tagˡ y → x ≡ y
    tagˡ-inj {In}  refl = refl
    tagˡ-inj {Out} refl = refl

    tagʳ-inj : ∀ {m} {x y : modeType m (C ⊗ᵀ D)} → tagʳ x ≡ tagʳ y → x ≡ y
    tagʳ-inj {In}  refl = refl
    tagʳ-inj {Out} refl = refl

    tagˡ≢tagʳ : ∀ {m} {x : modeType m (A ⊗ᵀ B)} {y : modeType m (C ⊗ᵀ D)}
              → tagˡ x ≡ tagʳ y → ⊥
    tagˡ≢tagʳ {In}  ()
    tagˡ≢tagʳ {Out} ()

--------------------------------------------------------------------------------
-- The message translations baked into the library's combinators.
--
-- `_⊗₁_`, `tr` and `_∘_` wrap their cores (`Tensor.CompRel`, `TraceRel`) in
-- `modifyStepRel ⇒-solver` layers, so a step of the wrapper *is* a step of the
-- core at translated messages. Each translation must be elaborated at the same
-- fully generic shape the library solves it at: running the solver on an
-- already instantiated shape yields a different (if equivalent) term.

private
  module S⊗ {X Y Z W : Channel} where
    sol : ∀ {m} → (X ⊗₀ Z) ⊗₀ (Y ⊗₀ W) ᵀ [ m ]⇒[ m ] (X ⊗₀ Y ᵀ) ⊗₀ ((Z ⊗₀ W ᵀ) ᵀ) ᵀ
    sol = ⇒-solver

  module S∣ {X Y Z : Channel} where
    -- `_∣ˡ` and `_∣^ˡ`, the two restrictions `tr` is assembled from
    dom : ∀ {m} → X ⊗₀ Z ᵀ [ m ]⇒[ m ] (X ⊗₀ Y) ⊗₀ Z ᵀ
    dom = ⇒-solver

    cod : ∀ {m} → X ⊗₀ Y ᵀ [ m ]⇒[ m ] X ⊗₀ (Y ⊗₀ Z) ᵀ
    cod = ⇒-solver

module _ {A B C D : Channel} where
  ⊗₁-msg : ∀ {m} → (A ⊗₀ C) ⊗₀ (B ⊗₀ D) ᵀ [ m ]⇒[ m ] (A ⊗₀ B ᵀ) ⊗₀ ((C ⊗₀ D ᵀ) ᵀ) ᵀ
  ⊗₁-msg = S⊗.sol {A} {B} {C} {D}

module _ {A B C : Channel} where
  -- `tr`'s two layers, outer first, as a `tr`-step's messages cross them
  tr-cod : ∀ {m} → A ⊗₀ B ᵀ [ m ]⇒[ m ] A ⊗₀ (B ⊗₀ C) ᵀ
  tr-cod = S∣.cod {A} {B} {C}

  tr-dom : ∀ {m} → A ⊗₀ (B ⊗₀ C) ᵀ [ m ]⇒[ m ] (A ⊗₀ C) ⊗₀ (B ⊗₀ C) ᵀ
  tr-dom = S∣.dom {A} {C} {B ⊗₀ C}

  tr-msg : ∀ {m} → A ⊗₀ B ᵀ [ m ]⇒[ m ] (A ⊗₀ C) ⊗₀ (B ⊗₀ C) ᵀ
  tr-msg = tr-cod ⇒ₜ tr-dom

  -- the reshuffle `_∘_` applies to the tensor it traces over …
  ∘-reshuffle : ∀ {m} → (A ⊗₀ B) ⊗₀ (C ⊗₀ B) ᵀ [ m ]⇒[ m ] (A ⊗₀ B) ⊗₀ (B ⊗₀ C) ᵀ
  ∘-reshuffle = ⇒-solver

  -- … and on into the tensor core's own channel
  ∘-msg : ∀ {m} → (A ⊗₀ B) ⊗₀ (C ⊗₀ B) ᵀ [ m ]⇒[ m ] (A ⊗₀ B ᵀ) ⊗₀ ((B ⊗₀ C ᵀ) ᵀ) ᵀ
  ∘-msg = ∘-reshuffle ⇒ₜ ⊗₁-msg {A} {B} {B} {C}

--------------------------------------------------------------------------------
-- Tensor steps: labelled inversion and construction.
--
-- A step of M₁ ⊗₁ M₂ is definitionally a `Tensor.CompRel` step — a single
-- labelled component step tagged left/right, its message embedded into the
-- combined channel `AllCs`. `comp-elim` hands the caller that component step
-- WITH its messages; `comp-inv` also keeps the messages linked to the
-- composite's. Both fire on a genuine `CompRel` value; reach one from a
-- ⊗₁-step with `⊗₁-compˡ/ʳ`.

module _ {M₁ : Machine A B} {M₂ : Machine C D} where
  open Tensor M₁ M₂ using (AllCs; CompRel; Step₁; Step₂)
  open Machine

  comp-elim : ∀ {ℓ} {s i o s'} {P : Set ℓ}
            → CompRel s i o s'
            → (∀ {sₐ mᵢ mₒ sₐ'} → stepRel M₁ sₐ mᵢ mₒ sₐ' → P)
            → (∀ {sᵦ mᵢ mₒ sᵦ'} → stepRel M₂ sᵦ mᵢ mₒ sᵦ' → P)
            → P
  comp-elim (Step₁ st) l _ = l st
  comp-elim (Step₂ st) _ r = r st

  -- Inversion that keeps the link between the composite's messages and the
  -- component's: the link comes back as propositional *equations*, because the
  -- unifier cannot recover it on its own (the output index is `map f ?mₒ`, and
  -- `map` does not decompose). With `i`/`o` universally quantified the
  -- constructor patterns discharge the equations by `refl`, and a caller holding
  -- concrete messages recovers the component's by injectivity of the tags.
  comp-inv : ∀ {ℓ} {s i o s'} {P : Set ℓ}
           → CompRel s i o s'
           → (∀ {mᵢ mₒ} → i ≡ tagˡ {m = In} mᵢ → o ≡ mapₘ (tagˡ {m = Out}) mₒ
              → stepRel M₁ (proj₁ s) mᵢ mₒ (proj₁ s') → proj₂ s ≡ proj₂ s' → P)
           → (∀ {mᵢ mₒ} → i ≡ tagʳ {m = In} mᵢ → o ≡ mapₘ (tagʳ {m = Out}) mₒ
              → stepRel M₂ (proj₂ s) mᵢ mₒ (proj₂ s') → proj₁ s ≡ proj₁ s' → P)
           → P
  comp-inv (Step₁ st) l _ = l refl refl st refl
  comp-inv (Step₂ st) _ r = r refl refl st refl

  -- Lane-determined inversion: where the input sits already says which factor
  -- stepped, so only one continuation is left and it keeps the caller's own name
  -- for that input. The output is still an equation (`comp-inv`, above).
  comp-atˡ : ∀ {ℓ} {s mᵢ o s'} {P : Set ℓ}
           → CompRel s (tagˡ {m = In} mᵢ) o s'
           → (∀ {mₒ} → o ≡ mapₘ (tagˡ {m = Out}) mₒ
              → stepRel M₁ (proj₁ s) mᵢ mₒ (proj₁ s') → proj₂ s ≡ proj₂ s' → P)
           → P
  comp-atˡ {s = s} {s' = s'} st k =
    comp-inv st (λ e₁ e₂ st' eq → k e₂ (subst (λ z → stepRel M₁ (proj₁ s) z _ (proj₁ s'))
                                              (sym (tagˡ-inj e₁)) st') eq)
                (λ e₁ _ _ _ → ⊥-elim (tagˡ≢tagʳ e₁))

  comp-atʳ : ∀ {ℓ} {s mᵢ o s'} {P : Set ℓ}
           → CompRel s (tagʳ {m = In} mᵢ) o s'
           → (∀ {mₒ} → o ≡ mapₘ (tagʳ {m = Out}) mₒ
              → stepRel M₂ (proj₂ s) mᵢ mₒ (proj₂ s') → proj₁ s ≡ proj₁ s' → P)
           → P
  comp-atʳ {s = s} {s' = s'} st k =
    comp-inv st (λ e₁ _ _ _ → ⊥-elim (tagˡ≢tagʳ (sym e₁)))
                (λ e₁ e₂ st' eq → k e₂ (subst (λ z → stepRel M₂ (proj₂ s) z _ (proj₂ s'))
                                              (sym (tagʳ-inj e₁)) st') eq)

  -- Both messages on one lane: the factor's step, at the caller's messages.
  comp-atˡ-just : ∀ {ℓ} {s mᵢ mₒ s'} {P : Set ℓ}
                → CompRel s (tagˡ {m = In} mᵢ) (just (tagˡ {m = Out} mₒ)) s'
                → (stepRel M₁ (proj₁ s) mᵢ (just mₒ) (proj₁ s') → proj₂ s ≡ proj₂ s' → P)
                → P
  comp-atˡ-just {s = s} {mᵢ} {mₒ} {s'} {P} st k = comp-atˡ st go
    where
      go : ∀ {mₒ'} → just (tagˡ {m = Out} mₒ) ≡ mapₘ (tagˡ {m = Out}) mₒ'
         → stepRel M₁ (proj₁ s) mᵢ mₒ' (proj₁ s') → proj₂ s ≡ proj₂ s' → P
      go {nothing} ()
      go {just _}  e st' = k (subst (λ z → stepRel M₁ (proj₁ s) mᵢ (just z) (proj₁ s'))
                                   (sym (tagˡ-inj (just-injective e))) st')

  comp-atʳ-just : ∀ {ℓ} {s mᵢ mₒ s'} {P : Set ℓ}
                → CompRel s (tagʳ {m = In} mᵢ) (just (tagʳ {m = Out} mₒ)) s'
                → (stepRel M₂ (proj₂ s) mᵢ (just mₒ) (proj₂ s') → proj₁ s ≡ proj₁ s' → P)
                → P
  comp-atʳ-just {s = s} {mᵢ} {mₒ} {s'} {P} st k = comp-atʳ st go
    where
      go : ∀ {mₒ'} → just (tagʳ {m = Out} mₒ) ≡ mapₘ (tagʳ {m = Out}) mₒ'
         → stepRel M₂ (proj₂ s) mᵢ mₒ' (proj₂ s') → proj₁ s ≡ proj₁ s' → P
      go {nothing} ()
      go {just _}  e st' = k (subst (λ z → stepRel M₂ (proj₂ s) mᵢ (just z) (proj₂ s'))
                                   (sym (tagʳ-inj (just-injective e))) st')

  -- No step crosses lanes: the factor the input picks is the one that emits.
  comp-atˡ-cross : ∀ {s mᵢ mₒ s'}
                 → CompRel s (tagˡ {m = In} mᵢ) (just (tagʳ {m = Out} mₒ)) s' → ⊥
  comp-atˡ-cross {s = s} {mᵢ} {mₒ} {s'} st = comp-atˡ st go
    where
      go : ∀ {mₒ'} → just (tagʳ {m = Out} mₒ) ≡ mapₘ (tagˡ {m = Out}) mₒ'
         → stepRel M₁ (proj₁ s) mᵢ mₒ' (proj₁ s') → proj₂ s ≡ proj₂ s' → ⊥
      go {nothing} ()
      go {just _}  e _ _ = tagˡ≢tagʳ (sym (just-injective e))

  comp-atʳ-cross : ∀ {s mᵢ mₒ s'}
                 → CompRel s (tagʳ {m = In} mᵢ) (just (tagˡ {m = Out} mₒ)) s' → ⊥
  comp-atʳ-cross {s = s} {mᵢ} {mₒ} {s'} st = comp-atʳ st go
    where
      go : ∀ {mₒ'} → just (tagˡ {m = Out} mₒ) ≡ mapₘ (tagʳ {m = Out}) mₒ'
         → stepRel M₂ (proj₂ s) mᵢ mₒ' (proj₂ s') → proj₁ s ≡ proj₁ s' → ⊥
      go {nothing} ()
      go {just _}  e _ _ = tagˡ≢tagʳ (just-injective e)

  -- Construction at the combined channel: a left/right component step becomes a
  -- CompRel step with the handoff message tagged (`Step₁`/`Step₂` directly).
  compL : ∀ {sₐ mᵢ mₒ sₐ' s₂} → stepRel M₁ sₐ mᵢ mₒ sₐ'
        → CompRel (sₐ , s₂) (tagˡ {m = In} mᵢ) (mapₘ (tagˡ {m = Out}) mₒ) (sₐ' , s₂)
  compL = Step₁

  compR : ∀ {sᵦ mᵢ mₒ sᵦ' s₁} → stepRel M₂ sᵦ mᵢ mₒ sᵦ'
        → CompRel (s₁ , sᵦ) (tagʳ {m = In} mᵢ) (mapₘ (tagʳ {m = Out}) mₒ) (s₁ , sᵦ')
  compR = Step₂

  ------------------------------------------------------------------------------
  -- ⊗₁ reshuffle: crossing the `modifyStepRel ⇒-solver` layer between a
  -- `CompRel` step and a genuine `M₁ ⊗₁ M₂` step. The solver baked into `_⊗₁_`
  -- is built from Channel.Core's `opaque` tensor combinators, so
  -- `app ⟨baked solver⟩` is stuck until they are unfolded; under
  -- `opaque unfolding` it reduces, and `⊗₁-inˡ/ʳ` name the boundary message a
  -- tagged one comes from. The solver is pinned by inference (the expected
  -- `M₁ ⊗₁ M₂` step type) — never re-elaborated in a signature. Both
  -- directions are value-bearing: the composite's output is stated as a
  -- per-message embedding, so no `map f ?o` ever has to be inverted.

  opaque
    unfolding ⊗₁-inˡ ⊗₁-inʳ

    -- The two step forms reduce to the same `CompRel` as soon as the message is
    -- constructor-headed: `app ⟨baked solver⟩ (inj-nest x)` computes, whereas at
    -- an abstract message the baked solver and any re-elaborated one are merely
    -- equivalent (shape-sensitivity), so the coercions go by message position.
    ⊗₁-compˡ : ∀ {s s' i o}
             → stepRel (M₁ ⊗₁ M₂) s (⊗₁-inˡ {m = In} i) (mapₘ (⊗₁-inˡ {m = Out}) o) s'
             → CompRel s (tagˡ {m = In} i) (mapₘ (tagˡ {m = Out}) o) s'
    ⊗₁-compˡ {i = inj₁ _} {o = nothing}       st = st
    ⊗₁-compˡ {i = inj₁ _} {o = just (inj₁ _)} st = st
    ⊗₁-compˡ {i = inj₁ _} {o = just (inj₂ _)} st = st
    ⊗₁-compˡ {i = inj₂ _} {o = nothing}       st = st
    ⊗₁-compˡ {i = inj₂ _} {o = just (inj₁ _)} st = st
    ⊗₁-compˡ {i = inj₂ _} {o = just (inj₂ _)} st = st

    ⊗₁-compʳ : ∀ {s s' i o}
             → stepRel (M₁ ⊗₁ M₂) s (⊗₁-inʳ {m = In} i) (mapₘ (⊗₁-inʳ {m = Out}) o) s'
             → CompRel s (tagʳ {m = In} i) (mapₘ (tagʳ {m = Out}) o) s'
    ⊗₁-compʳ {i = inj₁ _} {o = nothing}       st = st
    ⊗₁-compʳ {i = inj₁ _} {o = just (inj₁ _)} st = st
    ⊗₁-compʳ {i = inj₁ _} {o = just (inj₂ _)} st = st
    ⊗₁-compʳ {i = inj₂ _} {o = nothing}       st = st
    ⊗₁-compʳ {i = inj₂ _} {o = just (inj₁ _)} st = st
    ⊗₁-compʳ {i = inj₂ _} {o = just (inj₂ _)} st = st

    -- … and with the output at the *other* factor, which `comp-atˡ/ʳ-cross`
    -- then rules out
    ⊗₁-compˡʳ : ∀ {s s' i o}
              → stepRel (M₁ ⊗₁ M₂) s (⊗₁-inˡ {m = In} i) (mapₘ (⊗₁-inʳ {m = Out}) o) s'
              → CompRel s (tagˡ {m = In} i) (mapₘ (tagʳ {m = Out}) o) s'
    ⊗₁-compˡʳ {i = inj₁ _} {o = nothing}       st = st
    ⊗₁-compˡʳ {i = inj₁ _} {o = just (inj₁ _)} st = st
    ⊗₁-compˡʳ {i = inj₁ _} {o = just (inj₂ _)} st = st
    ⊗₁-compˡʳ {i = inj₂ _} {o = nothing}       st = st
    ⊗₁-compˡʳ {i = inj₂ _} {o = just (inj₁ _)} st = st
    ⊗₁-compˡʳ {i = inj₂ _} {o = just (inj₂ _)} st = st

    ⊗₁-compʳˡ : ∀ {s s' i o}
              → stepRel (M₁ ⊗₁ M₂) s (⊗₁-inʳ {m = In} i) (mapₘ (⊗₁-inˡ {m = Out}) o) s'
              → CompRel s (tagʳ {m = In} i) (mapₘ (tagˡ {m = Out}) o) s'
    ⊗₁-compʳˡ {i = inj₁ _} {o = nothing}       st = st
    ⊗₁-compʳˡ {i = inj₁ _} {o = just (inj₁ _)} st = st
    ⊗₁-compʳˡ {i = inj₁ _} {o = just (inj₂ _)} st = st
    ⊗₁-compʳˡ {i = inj₂ _} {o = nothing}       st = st
    ⊗₁-compʳˡ {i = inj₂ _} {o = just (inj₁ _)} st = st
    ⊗₁-compʳˡ {i = inj₂ _} {o = just (inj₂ _)} st = st

    ⊗₁-mkˡ : ∀ {s s' i o}
           → CompRel s (tagˡ {m = In} i) (mapₘ (tagˡ {m = Out}) o) s'
           → stepRel (M₁ ⊗₁ M₂) s (⊗₁-inˡ {m = In} i) (mapₘ (⊗₁-inˡ {m = Out}) o) s'
    ⊗₁-mkˡ {i = inj₁ _} {o = nothing}       st = st
    ⊗₁-mkˡ {i = inj₁ _} {o = just (inj₁ _)} st = st
    ⊗₁-mkˡ {i = inj₁ _} {o = just (inj₂ _)} st = st
    ⊗₁-mkˡ {i = inj₂ _} {o = nothing}       st = st
    ⊗₁-mkˡ {i = inj₂ _} {o = just (inj₁ _)} st = st
    ⊗₁-mkˡ {i = inj₂ _} {o = just (inj₂ _)} st = st

    ⊗₁-mkʳ : ∀ {s s' i o}
           → CompRel s (tagʳ {m = In} i) (mapₘ (tagʳ {m = Out}) o) s'
           → stepRel (M₁ ⊗₁ M₂) s (⊗₁-inʳ {m = In} i) (mapₘ (⊗₁-inʳ {m = Out}) o) s'
    ⊗₁-mkʳ {i = inj₁ _} {o = nothing}       st = st
    ⊗₁-mkʳ {i = inj₁ _} {o = just (inj₁ _)} st = st
    ⊗₁-mkʳ {i = inj₁ _} {o = just (inj₂ _)} st = st
    ⊗₁-mkʳ {i = inj₂ _} {o = nothing}       st = st
    ⊗₁-mkʳ {i = inj₂ _} {o = just (inj₁ _)} st = st
    ⊗₁-mkʳ {i = inj₂ _} {o = just (inj₂ _)} st = st

    -- Every boundary message is one factor's. Stated at the machines like the
    -- coercions: the channels are not recoverable from a message type, so a
    -- caller pins them by pinning `M₁`/`M₂`.
    ⊗₁-in-split : ∀ {m} (x : modeType m ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ D)))
                → (∃[ y ] x ≡ ⊗₁-inˡ y) ⊎ (∃[ y ] x ≡ ⊗₁-inʳ y)
    ⊗₁-in-split {In}  (inj₁ (inj₁ y)) = inj₁ (inj₁ y , refl)
    ⊗₁-in-split {In}  (inj₁ (inj₂ y)) = inj₂ (inj₁ y , refl)
    ⊗₁-in-split {In}  (inj₂ (inj₁ y)) = inj₁ (inj₂ y , refl)
    ⊗₁-in-split {In}  (inj₂ (inj₂ y)) = inj₂ (inj₂ y , refl)
    ⊗₁-in-split {Out} (inj₁ (inj₁ y)) = inj₁ (inj₁ y , refl)
    ⊗₁-in-split {Out} (inj₁ (inj₂ y)) = inj₂ (inj₁ y , refl)
    ⊗₁-in-split {Out} (inj₂ (inj₁ y)) = inj₁ (inj₂ y , refl)
    ⊗₁-in-split {Out} (inj₂ (inj₂ y)) = inj₂ (inj₂ y , refl)

--------------------------------------------------------------------------------
-- Trace: the labelled cascade. `TraceRel M` is the labelled trace with
-- distinguished boundary — `inM`/`outM` are the net external in/out messages,
-- the hidden-channel handoffs sit at the constructor joints. `trace-ind` is its
-- induction principle, handing each node its underlying step WITH messages.
--
-- Kept implicit in the traced machine so a `tr`/`_∘_` step feeds in directly:
-- its type reduces to `TraceRel _` and the machine is inferred.

module _ {M : Machine (A ⊗₀ C) (B ⊗₀ C)} where
  open Machine M

  trace-ind : ∀ {ℓ} (P : ∀ {s i o s'} → TraceRel M s i o s' → Set ℓ)
    → (∀ {s i o s'} (st : stepRel s i o s') → P (Trace[ st ]))
    → (∀ {s s' s'' inM outC outM}
         (st : stepRel s inM (just ((L⊗ ϵ) ⊗R ↑ₒ outC)) s')
         {rest : TraceRel M s' (L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹ ↑ᵢ outC) outM s''}
       → P rest → P (st Trace∷ₒ rest))
    → (∀ {s s' s'' inM inC outM}
         (st : stepRel s inM (just (L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹ ↑ₒ inC)) s')
         {rest : TraceRel M s' ((L⊗ ϵ) ⊗R ↑ᵢ inC) outM s''}
       → P rest → P (st Trace∷ᵢ rest))
    → ∀ {s i o s'} (t : TraceRel M s i o s') → P t
  trace-ind P f[] fₒ fᵢ Trace[ st ]       = f[] st
  trace-ind P f[] fₒ fᵢ (st Trace∷ₒ rest) = fₒ st (trace-ind P f[] fₒ fᵢ rest)
  trace-ind P f[] fₒ fᵢ (st Trace∷ᵢ rest) = fᵢ st (trace-ind P f[] fₒ fᵢ rest)

  -- Case analysis with the boundary messages in view: either the cascade is one
  -- node, or its head hands a message to the hidden wire and the rest continues
  -- from there. No equations needed — the indices are variables in every
  -- constructor, so a caller holding concrete ones may split directly.
  trace-inv : ∀ {ℓ} {s i o s'} {P : Set ℓ} → TraceRel M s i o s'
    → (stepRel s i o s' → P)
    → (∀ {s₁ outW} → stepRel s i (just ((L⊗ ϵ) ⊗R ↑ₒ outW)) s₁
       → TraceRel M s₁ (L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹ ↑ᵢ outW) o s' → P)
    → (∀ {s₁ inW} → stepRel s i (just (L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹ ↑ₒ inW)) s₁
       → TraceRel M s₁ ((L⊗ ϵ) ⊗R ↑ᵢ inW) o s' → P)
    → P
  trace-inv Trace[ st ]       f _ _ = f st
  trace-inv (st Trace∷ₒ rest) _ g _ = g st rest
  trace-inv (st Trace∷ᵢ rest) _ _ h = h st rest

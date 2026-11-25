{-# OPTIONS --safe --without-K #-}

module Conformance.VMProof where

open import Data.Bool.Base
open import Data.List.Base using (length)
open import Data.Maybe.Base using (nothing; just)
open import Data.Nat.Base
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality
open import Midnight.ContractDSL.Ledger
open import Conformance.VM

module Proofs (A : Atoms) where
  open Machine A

  step-prepare : ∀ {op s t} → Step op s t → prepare op s ≡ inj₂ (tt , t)
  step-prepare {s = machine pc xs} (step p) rewrite p = refl

  step-apply : ∀ {op s t} → Step op s t → Execution.apply semantics {k = tt} op tt s ≡ just t
  step-apply p rewrite step-prepare p = refl

  apply-step : ∀ {op s t} → Execution.apply semantics {k = tt} op tt s ≡ just t → Step op s t
  apply-step {op} {machine pc xs} accepted with execute op xs in computed | accepted
  ... | inj₁ e | ()
  ... | inj₂ (skip , ys) | refl = step computed

  journal-admission : ∀ {s ops t} → Journal s ops t → replay ops s ≡ just t
  journal-admission done = refl
  journal-admission (next p ps) rewrite step-apply p = journal-admission ps

  program-admission : ∀ {program fuel s t} → ProgramRun program fuel s t → run fuel program s ≡ just t
  program-admission (halt p) rewrite p = refl
  program-admission (advance notDone fetched stepped rest)
    rewrite notDone | fetched | step-apply stepped = program-admission rest

  run-sound : ∀ {fuel program s t} → run fuel program s ≡ just t → ProgramRun program fuel s t
  run-sound {zero} {program} {s} accepted with pc s ≡ᵇ length program in finished
  ... | true with accepted
  ...   | refl = halt finished
  run-sound {zero} {program} {s} accepted | false with accepted
  ...   | ()
  run-sound {suc fuel} {program} {s} accepted with pc s ≡ᵇ length program in finished
  ... | true with accepted
  ...   | refl = halt finished
  run-sound {suc fuel} {program} {s} accepted | false with at (pc s) program in fetched
  ...   | inj₁ e with accepted
  ...     | ()
  run-sound {suc fuel} {program} {s} accepted | false | inj₂ op
    with Execution.apply semantics {k = tt} op tt s in applied
  ...     | nothing with accepted
  ...       | ()
  run-sound {suc fuel} {program} {s} accepted | false | inj₂ op | just u =
    advance finished fetched (apply-step applied) (run-sound {fuel} {program} {u} accepted)

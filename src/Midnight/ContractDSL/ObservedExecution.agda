{-# OPTIONS --safe --without-K #-}

open import Midnight.ContractDSL.Ledger

module Midnight.ContractDSL.ObservedExecution (L : Semantics) (Assertion : Set) where

open import Data.Bool
open import Data.List
open import Data.Nat using (ℕ)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open Semantics L
open import Midnight.ContractDSL.Program L Assertion

-- Unlike the certified journal, trace entries include attempts preceding an abort.
data TraceEntry : Set where
  queried : ∀ {k} → Op k → Failure k ⊎ Res k → TraceEntry
  publication : ℕ → TraceEntry
  chainCondition : Condition → TraceEntry

Trace = List TraceEntry

record ExecutionReport (A : Set) : Set where
  constructor report
  field trace : Trace
        evaluation : Outcome A
open ExecutionReport public

recordEvent : ∀ {A} → TraceEntry → Event → ExecutionReport A → ExecutionReport A
recordEvent observed event run =
  report (observed ∷ trace run) (prefix event (evaluation run))

execute : ∀ {A} → Program A → State → ExecutionReport A
execute (pure a) s = report [] (inj₂ (finished a s []))
execute (step (ledger o) k) s with prepare o s
... | inj₁ err = report (queried o (inj₁ err) ∷ []) (inj₁ (operationError err))
... | inj₂ (x , t) = recordEvent (queried o (inj₂ x)) (operated o x) (execute (k x) t)
execute (step (require false err) k) s = report [] (inj₁ (assertionError err))
execute (step (require true err) k) s = execute (k tt) s
execute (step (publish n) k) s = recordEvent (publication n) (published n) (execute (k tt) s)
execute (step (atChain c) k) s = recordEvent (chainCondition c) (required c) (execute (k tt) s)

execute-correct : ∀ {A} (p : Program A) (s : State) → eval p s ≡ evaluation (execute p s)
execute-correct (pure a) s = refl
execute-correct (step (ledger o) k) s with prepare o s
... | inj₁ err = refl
... | inj₂ (x , t) = cong (prefix (operated o x)) (execute-correct (k x) t)
execute-correct (step (require false err) k) s = refl
execute-correct (step (require true err) k) s = execute-correct (k tt) s
execute-correct (step (publish n) k) s = cong (prefix (published n)) (execute-correct (k tt) s)
execute-correct (step (atChain c) k) s = cong (prefix (required c)) (execute-correct (k tt) s)

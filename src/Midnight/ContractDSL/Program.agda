{-# OPTIONS --safe --without-K #-}

open import Midnight.ContractDSL.Ledger

-- eval returns an error or a finished result, working state and ordered journal.
-- replay checks that journal against the current state and time now.
-- Correctness statements: Properties.agda; executable example: Example.agda.
module Midnight.ContractDSL.Program (L : Semantics) (Assertion : Set) where

open import Data.Bool
open import Data.List
open import Data.Maybe hiding (_>>=_)
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open Semantics L
open Execution L

private variable A B : Set
                 k : Kind

data Error : Set where
  operationError : Failure k → Error
  assertionError : Assertion → Error

data Condition : Set where
  timeAtLeast timeAtMost : ℕ → Condition

holds : Condition → ℕ → Bool
holds (timeAtLeast t) now = t ≤ᵇ now
holds (timeAtMost t)  now = now ≤ᵇ t

data ResultCode : Set where
  ledgerResult : Kind → ResultCode
  unitResult   : ResultCode

private variable c : ResultCode

ResultValue : ResultCode → Set
ResultValue (ledgerResult k) = Res k
ResultValue unitResult       = ⊤

data Effect : ResultCode → Set where
  ledger  : Op k → Effect (ledgerResult k)
  require : Bool → Assertion → Effect unitResult
  publish : ℕ → Effect unitResult
  atChain : Condition → Effect unitResult

data Program (A : Set) : Set where
  pure : A → Program A
  step : Effect c → (ResultValue c → Program A) → Program A

infixl 1 _>>=_ _>>_
_>>=_ : Program A → (A → Program B) → Program B
pure a >>= f = f a
step e k >>= f = step e (λ x → k x >>= f)

_>>_ : Program A → Program B → Program B
p >> q = p >>= λ _ → q

perform : Effect c → Program (ResultValue c)
perform e = step e pure

assert : Bool → Assertion → Program ⊤
assert b err = perform (require b err)

--------------------------------------------------------------------------------
-- Evaluating programs

data Event : Set where
  operated  : Op k → Res k → Event
  published : ℕ → Event
  required  : Condition → Event

Journal = List Event

record Finished (A : Set) : Set where
  constructor finished
  field result  : A
        working : State
        journal : Journal
open Finished public

Outcome : Set → Set
Outcome A = Error ⊎ Finished A

prefix : Event → Outcome A → Outcome A
prefix e (inj₁ err) = inj₁ err
prefix e (inj₂ (finished a s j)) = inj₂ (finished a s (e ∷ j))

eval : Program A → State → Outcome A
eval (pure a) s = inj₂ (finished a s [])
eval (step (ledger o) k) s with prepare o s
... | inj₁ err = inj₁ (operationError err)
... | inj₂ (x , t) = prefix (operated o x) (eval (k x) t)
eval (step (require false err) k) s = inj₁ (assertionError err)
eval (step (require true err) k) s = eval (k tt) s
eval (step (publish v) k) s = prefix (published v) (eval (k tt) s)
eval (step (atChain c) k) s = prefix (required c) (eval (k tt) s)

--------------------------------------------------------------------------------
-- Journals

replay : ℕ → Journal → State → Maybe State
replay slot [] s = just s
replay slot (operated o x ∷ j) s with apply o x s
... | nothing = nothing
... | just t  = replay slot j t
replay slot (published v ∷ j) s = replay slot j s
replay slot (required  c ∷ j) s with holds c slot
... | false = nothing
... | true  = replay slot j s

Eligible : ℕ → Journal → Set
Eligible now [] = ⊤
Eligible now (operated o x ∷ j) = Eligible now j
Eligible now (published  v ∷ j) = Eligible now j
Eligible now (required   c ∷ j) = holds c now ≡ true × Eligible now j

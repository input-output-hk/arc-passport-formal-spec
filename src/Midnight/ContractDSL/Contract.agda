{-# OPTIONS --safe --without-K #-}

open import Midnight.ContractDSL.Ledger

module Midnight.ContractDSL.Contract (L : Semantics) (Assertion : Set) where

open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Function

open Semantics L
open import Midnight.ContractDSL.Program L Assertion

record Contract : Set₁ where
  field self : ℕ
        EntryPoint : Set
        Input Result : EntryPoint → Set
        body : (self : ℕ) (n : EntryPoint) → Input n → Program (Result n)

  record Transaction : Set where
    field target : ℕ
          entry : EntryPoint
          input : Input entry
          view : State
          execution : Finished (Result entry)
          certified : eval (body target entry input) view ≡ inj₂ execution
  open Transaction

  build : (n : EntryPoint) → Input n → State → Error ⊎ Transaction
  build n a s with eval (body self n a) s in evaluated
  ... | inj₁ err = inj₁ err
  ... | inj₂ run = inj₂ record
    { target = self ; entry = n ; input = a ; view = s ; execution = run ; certified = evaluated }

  data Verdict : Set where
    accepted rejected : Verdict

  admit : (now : ℕ) → State → Transaction → State × Verdict
  admit now s tx = case target tx ≟ self of λ where
    (no _)  → s , rejected
    (yes _) → case replay now (journal (execution tx)) s of λ where
      nothing  → s , rejected
      (just t) → t , accepted

  -- Attempts at one contract instance; slots, build views and order are
  -- unrestricted. Monotone time and scheduling policies are not assumed.
  data Admissions : State → State → Set where
    done : ∀ {s} → Admissions s s
    next : ∀ {s u t} (now : ℕ) (tx : Transaction) (v : Verdict) →
      admit now s tx ≡ (u , v) → Admissions u t → Admissions s t

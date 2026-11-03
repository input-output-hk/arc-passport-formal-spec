{-# OPTIONS --safe --without-K #-}

-- Complete account transition specification. AccountRecovery remains the
-- deliberately smaller recovery abstraction; its theorem statements are not
-- assertions about the additional bootstrap, grant, inbox, or native effects.
-- Conformance.FullAccount supplies dispatch; its Body, Grant and Crypto modules
-- define the circuit semantics (see the definition route in Passport.agda).
module Passport.Account where

open import Conformance.FullAccount using (dispatch)
open import Conformance.FullAccountTypes
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base hiding (equal)
open import Data.Product.Base
open import Relation.Binary.PropositionalEquality

record Deployment : Set where
  constructor deployment
  field initialDeviceBoot encryptionKey initialRecoveryKey initialRecoveryWrap : Value
        vetoWindowSeconds : ℕ
open Deployment public

deploy : Primitives → Context → Deployment → Execution Value
deploy P ctx d = dispatch P ctx
  (rawCall "constructor" (initialDeviceBoot d ∷ encryptionKey d ∷ initialRecoveryKey d ∷
    initialRecoveryWrap d ∷ nat (vetoWindowSeconds d) ∷ [])) (state [])

data Observation : Set where
  committed : Value → List Effect → Observation
  reverted : Error → Observation

-- Rejection exposes neither a tentative ledger nor tentative native effects.
-- Admission of a committed native-effect list is a transaction/VM obligation,
-- distinct from execution of the Compact author program represented here.
transaction : State → Execution Value → Observation × State
transaction old (rejected e) = reverted e , old
transaction old (accepted answer next effects) = committed answer effects , next

step : Primitives → Context → RawCall → State → Observation × State
step P ctx call s = transaction s (dispatch P ctx call s)

-- A graph of step, not an independently defined admission relation. Its
-- determinism follows from this equation, not from a circuit-specific proof.
record Transition (P : Primitives) (ctx : Context) (call : RawCall) (before : State)
    (observation : Observation) (after : State) : Set where
  constructor transition
  field execution : step P ctx call before ≡ (observation , after)
open Transition public


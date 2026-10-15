{-# OPTIONS --safe --without-K #-}

open import Conformance.Primitives

module Conformance.RecoveryAuthorityDefinitions (P : Primitives)
  (self : Primitives.Bytes32 P) (Compromised : Primitives.Point P → Set) where

open import Data.Bool.Base
open import Data.List.Relation.Unary.All hiding (self)
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Conformance.AccountLedger P
open import Conformance.Custody P self
open import Conformance.Recovery P self
import Passport.AccountRecovery P self as Account
open Account using (module Chain)
open Chain using (Admissions; done; next)

open Primitives P

-- A collision boundary, not a property of the abstract primitive interface.
KeySeparation : Set
KeySeparation = ∀ pk q e f c d →
  deviceEntry self pk e c ≡ deviceEntry self q f d → pk ≡ q

EntrySafe : Bytes32 → Set
EntrySafe entry = ∀ pk epoch counter → Compromised pk →
  entry ≢ deviceEntry self pk epoch counter

record Safe (s : State) : Set where
  constructor safe
  field devicesSafe : All EntrySafe (devices s)
        pendingSafe : pending s ≡ true → EntrySafe (pendingEntry s)
open Safe public

-- Authority-theorem hypothesis, not enforced by the contract: enrolment entries
-- exclude every epoch/counter encoding of a compromised key (including future
-- encodings), and recovery submissions select uncompromised successor devices.
InputPolicy : (n : Account.Name) → Account.Input n → Set
InputPolicy (Account.jubjub Account.addDevice) (entry , _) = EntrySafe entry
InputPolicy Account.recoverSubmit a = ¬ Compromised (SubmitArgs.successorPk a)
InputPolicy _ _ = ⊤

-- All certificate openings related to the claim satisfy the input hypothesis.
TransactionPolicy : Chain.Tx → Set
TransactionPolicy tx = ∀ e → Chain.Rel (Chain.Tx.claim tx) e →
  InputPolicy (Chain.Statement.name (Chain.Tx.claim tx)) (Chain.Evidence.inputs e)

-- The hypothesis covers every transaction of the unrestricted execution,
-- including rejected steps; it is not a condition for contract admission.
data TracePolicy : ∀ {s t} → Admissions s t → Set where
  policy-done : ∀ {s} → TracePolicy (done {s})
  policy-next : ∀ {s u t ctx tx v admitted} {rest : Admissions u t} →
    TransactionPolicy tx → TracePolicy rest →
    TracePolicy (next {s} ctx tx v admitted rest)

-- The endpoint and every intermediate ledger, not only a one-step invariant.
data SafeAdmissions : ∀ {s t} → Admissions s t → Set where
  all-done : ∀ {s} → Safe s → SafeAdmissions (done {s})
  all-next : ∀ {s u t ctx tx v admitted} {rest : Admissions u t} →
    Safe s → SafeAdmissions rest →
    SafeAdmissions (next {s} ctx tx v admitted rest)

DeviceAuthority : State → Point → ℕ → Set
DeviceAuthority s pk counter =
  deviceEntry self pk (deviceEpoch s) counter ∈ᵇ devices s ≡ true

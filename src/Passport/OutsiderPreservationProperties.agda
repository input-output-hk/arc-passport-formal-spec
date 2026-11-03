{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes using (Primitives; Value)

-- Permissionless deposits and refused attempts preserve structural authority
-- and selected stored recovery resources along actual deployment-rooted local
-- histories. This does not promise availability: deposits spend the finite round
-- budget and shielded deposits spend inbox capacity; refusal rollback does not
-- refund real transaction costs. Environment time can expire grants, proving
-- access may be missing, and native assets may fail admission. Successful
-- activation and recovery finalisation are legitimate authority changes, not
-- attacks covered by this class. No cryptographic laws or caller-honesty premise.
module Passport.OutsiderPreservationProperties (P : Primitives) (address : Value) where

open import Conformance.FullAccountTypes
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (_+_; _<ᵇ_; _^_)
open import Data.Bool.Base using (true)
open import Data.Product.Base using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Passport.Account as Account
open import Passport.OutsiderPreservation P address
import Passport.OutsiderPreservationProof as Proof

rooted-outsider-preservation : ∀ {s t} → Runs.History s → (trace : OutsiderTrace s t) →
  Runs.History t × Frame s t × ResourcesPreserved s t ×
  (∀ entry → Enrolled entry s → Enrolled entry t)
rooted-outsider-preservation = Proof.history-preserved P address

exact-round-cost : ∀ {s t} (trace : OutsiderTrace s t) → RoundCost trace
exact-round-cost = Proof.round-cost P address

finite-round-budget : ∀ {s t} (trace : OutsiderTrace s t) → RoundFits s →
  ((successfulDeposits trace + roundValue s) <ᵇ 2 ^ 64) ≡ true
finite-round-budget = Proof.round-budget P address

successful-bootstrap-excluded : ∀ call c {v es} →
  resolve call ≡ just (Semantics.activation c) →
  OutsiderAction call (Account.committed v es) → ⊥
successful-bootstrap-excluded = Proof.activation-excluded P address

successful-finalisation-excluded : ∀ call {v es} →
  resolve call ≡ just Semantics.finaliseRecovery →
  OutsiderAction call (Account.committed v es) → ⊥
successful-finalisation-excluded = Proof.finalisation-excluded P address

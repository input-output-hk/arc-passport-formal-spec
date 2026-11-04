{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes using (Primitives; Value)

-- Ordinary removal consumes a literal entry, not every opening of a key.
-- Statements: DeviceRemovalProperties; source extraction: DeviceRemovalProof.
module Passport.DeviceRemoval (P : Primitives) (address : Value) where

open import Conformance.FullAccountTypes
open import Conformance.FullAccountBody P using (removeDevice)
open import Conformance.FullAccountDeviceSecurity P
open import Data.Bool.Base using (true; false)
open import Data.Nat.Base using (_<ᵇ_; _∸_)
open import Passport.RevocationExclusion P address
open import Relation.Binary.PropositionalEquality using (_≡_)

removedEntry : ∀ {s t} → CommittedOccurrence s t → Value
removedEntry event = callIdentifier removeDevice (CommittedOccurrence.call event)

-- The body sees the state AFTER authorisation has rolled the caller. Its
-- counter is a stored count, not a theorem equating count with set cardinality.
record RemovalEffect (target caller : Value) (before after : State) : Set where
  field targetLive : member target (fields (cell "devices" before)) ≡ true
        callerDistinct : equal target caller ≡ false
        moreThanOne : (1 <ᵇ counterValue "device_count" before) ≡ true
        devicesRemoved : cell "devices" after ≡
          tuple (removeSet target (fields (cell "devices" before)))
        countWritten : cell "device_count" after ≡
          nat (counterValue "device_count" before ∸ 1)

record Removal (c : Curve) {s t : State} (event : CommittedOccurrence s t) : Set where
  field call : DeviceCall c removeDevice (occurrenceContext event) (occurrenceArguments event)
          s (CommittedOccurrence.answer event) t
        callerIsRolled : DeviceCall.callerEntry call ≡ DeviceCall.rolledEntry call
        effect : RemovalEffect (removedEntry event) (DeviceCall.rolledEntry call)
          (DeviceCall.authorisedState call) t
        targetOriginallyLive : member (removedEntry event) (fields (cell "devices" s)) ≡ true
        originalCountGuard : (1 <ᵇ counterValue "device_count" s) ≡ true
        countDecremented : cell "device_count" t ≡ nat (counterValue "device_count" s ∸ 1)
        countStrictlyDecreased :
          (counterValue "device_count" t <ᵇ counterValue "device_count" s) ≡ true

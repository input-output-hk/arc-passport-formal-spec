{-# OPTIONS --safe --without-K #-}

open import Conformance.Primitives
import Conformance.RecoveryAuthorityDefinitions

-- Reading route: Passport.AccountRecovery.contract, then unrestricted
-- Chain.Admissions from the generic Interpreter. RecoveryAuthorityDefinitions exposes
-- the compromise set, collision boundary, and separate TracePolicy hypothesis.
-- Proofs: RecoveryAuthorityProof; this file presents their explicit types.
-- Model prerequisites: the account dispatch, Recovery circuits, Custody seam and
-- AccountLedger.State/prepare. Program.eval builds a working state and journal;
-- Protocol.Interpreter.admission verifies the certificate and atomically
-- replays its journal against the current ledger, enforcing chain conditions.
-- Eval-only reset claims are distinct from the accepted-finalisation claims.
-- This covers corrected replacement, not sourceShaped or grant authority.
-- Compromised is fixed throughout the trace: subsequent compromise of a successor
-- is outside this claim. Signature unforgeability is NOT proved or needed to
-- reject an absent compromised key; treating an accepted honest-key call as an
-- honest party's intent additionally needs authentication/unforgeability.
-- Atomic ordered replay and chain-time enforcement are those of ContractDSL's
-- Interpreter, not a theorem about a deployed chain. The stamped concrete map's
-- current-epoch projection is a correspondence obligation, not a checked refinement.
module Conformance.RecoveryAuthority (P : Primitives)
  (self : Primitives.Bytes32 P) (Compromised : Primitives.Point P → Set)
  (separation : Conformance.RecoveryAuthorityDefinitions.KeySeparation P self Compromised) where

open import Data.Empty
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Conformance.AccountLedger P
open import Conformance.Custody P self
open import Conformance.Recovery P self
open import Conformance.RecoveryAuthorityDefinitions P self Compromised
import Passport.AccountRecovery P self as Account
open Account using (module Chain)
open Chain using (Admissions)
import Conformance.RecoveryAuthorityProof P self Compromised separation as Proof
open import Midnight.ContractDSL.Program accountLedger Assertion

open Primitives P

trace-safety : ∀ {s t} (trace : Admissions s t) → TracePolicy trace → Safe s → SafeAdmissions trace
trace-safety = Proof.trace-safe

trace-authority-exclusion : ∀ {s t} (trace : Admissions s t) → TracePolicy trace → Safe s →
  ∀ pk counter → Compromised pk → ¬ DeviceAuthority t pk counter
trace-authority-exclusion = Proof.trace-authority-excluded

compromised-key-excluded : ∀ {s} pk counter → Safe s → Compromised pk →
  ¬ DeviceAuthority s pk counter
compromised-key-excluded = Proof.authority-excluded

-- Recovery can establish the invariant even when the old device set is unsafe;
-- the successor entry must be unrelated to every compromised key encoding.
recovery-resets-authority : ∀ {s result t journal} → EntrySafe (pendingEntry s) →
  eval (finaliseRecovery corrected) s ≡ inj₂ (finished result t journal) → Safe t
recovery-resets-authority = Proof.finalise-reset

circuit-safety : ∀ n input → InputPolicy n input →
  ∀ {s result t journal} → Safe s →
  eval (Account.circuit corrected n input) s ≡ inj₂ (finished result t journal) → Safe t
circuit-safety = Proof.circuit-safe

trace-compromised-call-impossible : ∀ {s t} (trace : Admissions s t) → TracePolicy trace → Safe s →
  ∀ g p a → Compromised (pk a) → ∀ {result u journal} →
  eval (Account.gated g p a) t ≡ inj₂ (finished result u journal) → ⊥
trace-compromised-call-impossible = Proof.trace-compromised-call-impossible

recovery-trace-exclusion : ∀ {s recovered t result journal} → EntrySafe (pendingEntry s) →
  eval (finaliseRecovery corrected) s ≡ inj₂ (finished result recovered journal) →
  (trace : Admissions recovered t) → TracePolicy trace →
  ∀ pk counter → Compromised pk → ¬ DeviceAuthority t pk counter
recovery-trace-exclusion = Proof.recovery-trace-exclusion

accepted-finalisation-resets-authority : ∀ ctx tx {s recovered} →
  Chain.Statement.name (Chain.Tx.claim tx) ≡ Account.recoverFinalise →
  EntrySafe (pendingEntry s) →
  Chain.admission ctx s tx ≡ (recovered , Chain.accepted) → Safe recovered
accepted-finalisation-resets-authority = Proof.accepted-finalisation-reset

accepted-recovery-trace-exclusion : ∀ ctx tx {s recovered t} →
  Chain.Statement.name (Chain.Tx.claim tx) ≡ Account.recoverFinalise →
  EntrySafe (pendingEntry s) →
  Chain.admission ctx s tx ≡ (recovered , Chain.accepted) →
  (trace : Admissions recovered t) → TracePolicy trace →
  ∀ pk counter → Compromised pk → ¬ DeviceAuthority t pk counter
accepted-recovery-trace-exclusion = Proof.accepted-recovery-trace-exclusion

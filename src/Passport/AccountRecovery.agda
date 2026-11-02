{-# OPTIONS --safe --without-K #-}

open import Conformance.Primitives

-- Recovery-relevant shared account slice, with a caller-supplied post-bootstrap
-- State. Read contract, Chain.Admissions, then RecoveryExecution/RecoveryAuthority.
-- Circuit bodies: Conformance.Recovery; authorisation: Conformance.Custody.
-- TracePolicy is a separate theorem hypothesis, not an admission restriction.
-- Assumptions and limits: docs/conformance-recovery.md#checked-formal-scope.
module Passport.AccountRecovery (P : Primitives)
  (self : Primitives.Bytes32 P) where

open import Data.Nat.Base
open import Data.Product.Base
open import Data.Unit.Base

import Conformance.AccountLedger
module Ledger = Conformance.AccountLedger P
open Ledger
open import Conformance.Custody P self
open import Conformance.Recovery P self
open import Midnight.ContractDSL.Program accountLedger Assertion
open import Midnight.ContractDSL.Contract accountLedger Assertion

open Primitives P

------------------------------------------------------------------------
-- Entrypoints and authorisation
------------------------------------------------------------------------

data Gated : Set where
  withdrawUnshielded addDevice removeDevice rotateEncKey publishRecoverySession recoverCancel : Gated

Payload : Gated → Set
Payload withdrawUnshielded = Bytes32 × ℕ × Bytes32
Payload addDevice = Bytes32
Payload removeDevice = Bytes32
Payload rotateEncKey = Bytes32
Payload publishRecoverySession = PublishArgs
Payload recoverCancel = ⊤

challengeOf : (g : Gated) → Payload g → Challenge
challengeOf withdrawUnshielded (c , a , r) R pk = challengeWithdraw self R pk c a r
challengeOf addDevice e R pk = challengeAddDevice self R pk e
challengeOf removeDevice e R pk = challengeRemoveDevice self R pk e
challengeOf rotateEncKey k R pk = challengeRotateEncKey self R pk k
challengeOf publishRecoverySession (publishArgs pk′ n (φ₁ , φ₂ , φ₃ , φ₄) len w) R pk =
  challengePublish self R pk pk′ n φ₁ φ₂ φ₃ φ₄ len w
challengeOf recoverCancel _ R pk = challengeCancel self R pk

gated : (g : Gated) → Payload g → Authorisation → Program ⊤
gated g p a = do
  authorise a (challengeOf g p)
  chip g p
  where
  chip : (g : Gated) → Payload g → Program ⊤
  chip withdrawUnshielded (c , x , _) = doWithdraw c x
  chip addDevice e = doAddDevice e
  chip removeDevice e = doRemoveDevice e (pk a) (useCounter a)
  chip rotateEncKey k = doRotateEncKey k
  chip publishRecoverySession args = doPublish args
  chip recoverCancel _ = doCancel

data Name : Set where
  depositUnshielded recoverSubmit recoverFinalise : Name
  jubjub : Gated → Name

Input : Name → Set
Input depositUnshielded = Bytes32 × ℕ
Input recoverSubmit = SubmitArgs
Input recoverFinalise = ⊤
Input (jubjub g) = Payload g × Authorisation

------------------------------------------------------------------------
-- Contract assembly
------------------------------------------------------------------------

-- The variant argument is only for historical source-shaped conformance.
-- All advertised properties and unrestricted executions use contract below.
circuit : Finalisation → (n : Name) → Input n → Program ⊤
circuit variant depositUnshielded (c , a) = deposit c a
circuit variant recoverSubmit = submitRecovery
circuit variant recoverFinalise _ = finaliseRecovery variant
circuit variant (jubjub g) (p , a) = gated g p a

assemble : Finalisation → Contract
assemble variant = record
  { self = 0 ; EntryPoint = Name ; Input = Input ; Result = λ _ → ⊤
  ; body = λ _ n a → circuit variant n a }

-- Intended proof subject: finalisation replaces the old device set with the
-- recorded successor. assemble sourceShaped is a historical comparator only.
contract : Contract
contract = assemble corrected

-- Logical account identity Contract.self = 0; the Bytes32 parameter self is the
-- challenge domain. See Conformance.Monitor for the transport identity boundary.
module Chain = Contract contract

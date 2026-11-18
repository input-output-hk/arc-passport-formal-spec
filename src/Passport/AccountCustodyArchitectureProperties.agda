{-# OPTIONS --safe #-}

open import Relation.Binary.Definitions using (DecidableEquality)

-- Whole-architecture preservation, for each account–asset key in one ledger.
-- Only the passport-key relay laws are assumptions: concrete custody supplies
-- soundness, prompt accuracy, AnswersOnly, and CanAnswer. See the model in
-- AccountCustodyArchitecture and the implementation in its Proof module.
-- This is abstract finalized-event accounting, not native Midnight refinement,
-- asynchronous synchronization, or snapshot-progress (P12).
module Passport.AccountCustodyArchitectureProperties
  (Account Asset TxId : Set)
  (_≟Account_ : DecidableEquality Account)
  (_≟Asset_ : DecidableEquality Asset)
  (_≟Id_ : DecidableEquality TxId) where

open import Data.Product using (_×_)
open import Relation.Nullary.Decidable using (Dec)

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Relay
open import CategoricalCrypto.Machine.Simulation
open import Midnight.Passport.BalanceAccounting
open import Midnight.Passport.Flow using (simAC)
open import Midnight.Passport.Semantics using (MachineModel)
import Passport.AccountCustodyArchitecture
import Passport.AccountCustodyArchitectureProof

module A = Passport.AccountCustodyArchitecture
  Account Asset TxId _≟Account_ _≟Asset_ _≟Id_
module Proof = Passport.AccountCustodyArchitectureProof
  Account Asset TxId _≟Account_ _≟Asset_ _≟Id_
open A.C.Ledger using (State; Transaction; Key)

module Execution
  (Authorized : State → Transaction → Set)
  (authorized? : ∀ s t → Dec (Authorized s t)) where

  module Deployment
    (TBDᶜ SYNCᶜ : Channel)
    (SignRequest Signature ShareRequest ShareResponse : Set)
    (WitnessRequest WitnessResponse LedgerWrite WalletState : Set)
    (UserRequest ChainResult : Set) where

    module D = A.Execution.Deployment Authorized authorized? TBDᶜ SYNCᶜ
      SignRequest Signature ShareRequest ShareResponse
      WitnessRequest WitnessResponse LedgerWrite WalletState UserRequest ChainResult
    module P = Proof.Execution.Deployment Authorized authorized? TBDᶜ SYNCᶜ
      SignRequest Signature ShareRequest ShareResponse
      WitnessRequest WitnessResponse LedgerWrite WalletState UserRequest ChainResult
    open D using (Components; machineModel)

    module Theorem (components : Components)
      (s₀ : Machine.State (MachineModel.⟦architecture⟧ (machineModel components)))
      (key : Key) where

      module O = D.Observation components s₀ key
      open O.Theorem using (pkRelay)

      -- The initial balance is read from the custody component of the initial
      -- whole-system state; callers cannot choose an unrelated scalar balance.
      module G = BalanceAccounting
        (MachineModel.⟦architecture⟧ (machineModel components))
        (O.Ports.userPort (MachineModel.⟦architecture⟧ (machineModel components)))
        O.Theorem.txValue s₀
        (A.C.report (Sim.π (simAC (machineModel components)) s₀) key)

      -- Every reported balance is bounded by genesis plus signed adopted flow;
      -- an exact answer is available after a transaction-free continuation.
      preservation-of-value
        : ForwardsQuery pkRelay → ForwardsAnswer pkRelay
        → NoInvention pkRelay → Responsive pkRelay
        → G.Sound × G.EventuallyAccurate
      preservation-of-value = P.Theorem.preservation-of-value components s₀ key

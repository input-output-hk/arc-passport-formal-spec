{-# OPTIONS --safe #-}

open import Relation.Binary.Definitions using (DecidableEquality)

-- The complete Passport diagram with a concrete finalized-ledger custody box.
-- The other eight boxes are implementations supplied by the deployment.
module Passport.AccountCustodyArchitecture
  (Account Asset TxId : Set)
  (_≟Account_ : DecidableEquality Account)
  (_≟Asset_ : DecidableEquality Asset)
  (_≟Id_ : DecidableEquality TxId) where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Relation.Nullary.Decidable using (Dec)

open import CategoricalCrypto.Channel.Core as Ch hiding (_⊗₀_)
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Simulation
import Midnight.Passport.ArchitectureAccounting as Accounting
open import Midnight.Passport.Flow using (simAC)
open import Midnight.Passport.Semantics
  hiding (didContract; nameService; peerDevices; recoveryHelpers; indexer;
          localWallet; proofServer; passportKey)
import Passport.AccountCustody

module C = Passport.AccountCustody Account Asset TxId _≟Account_ _≟Asset_ _≟Id_
open C.Ledger using (State; Transaction; Key)

module Execution
  (Authorized : State → Transaction → Set)
  (authorized? : ∀ s t → Dec (Authorized s t)) where

  module Deployment
    (TBDᶜ SYNCᶜ : Channel)
    (SignRequest Signature ShareRequest ShareResponse : Set)
    (WitnessRequest WitnessResponse LedgerWrite WalletState : Set)
    (UserRequest ChainResult : Set) where

    module Custody = C.Execution.MachineInterface Authorized authorized?
      TBDᶜ SignRequest Signature LedgerWrite

    data UserT : Mode → Set where
      result : ChainResult → UserT In
      balanceIs : Key → ℕ → UserT In
      request : UserRequest → UserT Out
      getBalance : Key → UserT Out

    userChannel : Channel
    userChannel = simpleChannel UserT

    channelModel : ChannelModel
    channelModel = record
      { ⟦TBD⟧ = TBDᶜ
      ; ⟦TBD-SYNC⟧ = SYNCᶜ
      ; ⟦RECOVERY-P5⟧ = ShareResponse ⇿ ShareRequest
      ; ⟦READ-STATE⟧ = C.ChainEvent ⇿ ⊥
      ; ⟦JUBJUB-SCHNORR⟧ = Custody.accountChannel
      ; ⟦STATE⟧ = WalletState ⇿ ⊥
      ; ⟦WITNESS-IPC⟧ = WitnessResponse ⇿ WitnessRequest
      ; ⟦CHAIN⟧ = Custody.chainChannel
      ; ⟦User⟧ = userChannel
      }

    open ChannelModel channelModel using (⟦_⟧₀)

    record Components : Set₁ where
      field
        didContract : Machine ⟦ unit ⟧₀ ⟦ Var TBD ⟧₀
        nameService : Machine ⟦ unit ⟧₀ ⟦ Var TBD ⟧₀
        peerDevices : Machine ⟦ unit ⟧₀ ⟦ Var TBD-SYNC ⟧₀
        recoveryHelpers : Machine ⟦ unit ⟧₀ ⟦ Var RECOVERY-P5 ⟧₀
        indexer : Machine ⟦ unit ⟧₀ ⟦ Var READ-STATE ⟧₀
        localWallet : Machine ⟦ Var TBD-SYNC ⟧₀ ⟦ Var STATE ⟧₀
        proofServer : Machine ⟦ unit ⟧₀ ⟦ Var WITNESS-IPC ⟧₀
        passportKey : Machine
          ⟦ Var RECOVERY-P5 ⊗₀ Var READ-STATE ⊗₀ Var JUBJUB-SCHNORR
            ⊗₀ Var STATE ⊗₀ Var WITNESS-IPC ⟧₀ ⟦ Var User ⟧₀

    machineModel : Components → MachineModel channelModel
    machineModel components = record
      { ⟦didContract⟧ = Components.didContract components
      ; ⟦nameService⟧ = Components.nameService components
      ; ⟦peerDevices⟧ = Components.peerDevices components
      ; ⟦recoveryHelpers⟧ = Components.recoveryHelpers components
      ; ⟦indexer⟧ = Components.indexer components
      ; ⟦accountCustody⟧ = Custody.accountCustody
      ; ⟦localWallet⟧ = Components.localWallet components
      ; ⟦proofServer⟧ = Components.proofServer components
      ; ⟦passportKey⟧ = Components.passportKey components
      }

    module Observation (components : Components)
      (s₀ : Machine.State (MachineModel.⟦architecture⟧ (machineModel components)))
      (key : Key) where

      genesis : State
      genesis = Sim.π (simAC (machineModel components)) s₀

      genesisBalance : ℕ
      genesisBalance = C.report genesis key

      module Ports = Accounting channelModel
        (Custody.getBalance key) (Custody.balanceIs key)
        (getBalance key) (balanceIs key)
      module Theorem = Ports.Theorem (machineModel components)
        (C.effect key) s₀ genesisBalance

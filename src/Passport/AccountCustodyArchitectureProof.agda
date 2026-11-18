{-# OPTIONS --safe #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Passport.AccountCustodyArchitectureProof
  (Account Asset TxId : Set)
  (_≟Account_ : DecidableEquality Account)
  (_≟Asset_ : DecidableEquality Asset)
  (_≟Id_ : DecidableEquality TxId) where

open import Data.Product using (_×_)
open import Relation.Nullary.Decidable using (Dec)

open import CategoricalCrypto.Channel.Core as Ch
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Relay
open import Midnight.Passport.Semantics using (MachineModel)
import Midnight.Passport.Properties as Generic
import Passport.AccountCustodyArchitecture
import Passport.AccountCustodyProperties

module A = Passport.AccountCustodyArchitecture
  Account Asset TxId _≟Account_ _≟Asset_ _≟Id_
module Local = Passport.AccountCustodyProperties
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
    module L = Local.Execution.MachineInterface Authorized authorized?
      TBDᶜ SignRequest Signature LedgerWrite
    open D using (Components; machineModel; channelModel; module Custody)

    module Theorem (components : Components)
      (s₀ : Machine.State (MachineModel.⟦architecture⟧ (machineModel components)))
      (key : Key) where

      module O = D.Observation components s₀ key
      open O using (genesis; genesisBalance)
      open O.Theorem using (module G; pkRelay)
      module P = Generic channelModel
        (Custody.getBalance key) (Custody.balanceIs key)
        (D.getBalance key) (D.balanceIs key)

      preservation-of-value
        : ForwardsQuery pkRelay → ForwardsAnswer pkRelay
        → NoInvention pkRelay → Responsive pkRelay
        → G.Sound × G.EventuallyAccurate
      preservation-of-value fq fa ni rsp =
        P.Theorem.preservation-of-value (machineModel components)
          (A.C.effect key) s₀ genesisBalance
          (L.sound key genesis) (L.promptlyAccurate key genesis)
          fq fa ni rsp (L.answersOnly key) (L.canAnswer key)

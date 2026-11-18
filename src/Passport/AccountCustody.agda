{-# OPTIONS --safe #-}

open import Relation.Binary.Definitions using (DecidableEquality)

-- A finalized-event reporting machine, not a native Midnight execution model.
-- Both account and asset qualify every query; authorization is ledger-wide.
module Passport.AccountCustody
  (Account Asset TxId : Set)
  (_≟Account_ : DecidableEquality Account)
  (_≟Asset_ : DecidableEquality Asset)
  (_≟Id_ : DecidableEquality TxId) where

open import Data.Integer.Base using (ℤ; 0ℤ; _⊖_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary.Decidable using (Dec; yes; no)

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Relay using (Port; wirePort; codᵍ)
open import CategoricalCrypto.Machine.Valuation
import Passport.FinalizedLedger

module Ledger = Passport.FinalizedLedger Account Asset TxId _≟Account_ _≟Asset_ _≟Id_
open Ledger public using (State; Transaction; Key; balance; credit; debit; apply)

report : State → Key → ℕ
report s (a , x) = balance s a x

data ChainEvent : Set where
  adopted rejected : Transaction → ChainEvent

effect : Key → ChainEvent → ℤ
effect (a , x) (adopted t) = credit t a x ⊖ debit t a x
effect k (rejected t) = 0ℤ

module Channels (SignRequest Signature : Set) where
  data JubjubSchnorrT : Mode → Set where
    sign : SignRequest → JubjubSchnorrT In
    balanceIs : Key → ℕ → JubjubSchnorrT In
    signed : Signature → JubjubSchnorrT Out
    getBalance : Key → JubjubSchnorrT Out

  accountChannel : Channel
  accountChannel = simpleChannel JubjubSchnorrT

module Execution
  (Authorized : State → Transaction → Set)
  (authorized? : ∀ s t → Dec (Authorized s t)) where

  module Finalize = Ledger.Execution Authorized authorized?
  open Finalize using (finalize; decideValid)

  -- A mismatched claimed outcome is not a rejected ledger attempt: it is
  -- refused at the event boundary, and cannot become a machine trace step.
  receive : State → ChainEvent → Maybe State
  receive s (adopted t) with decideValid s t
  ... | yes _ = just (apply s t)
  ... | no _ = nothing
  receive s (rejected t) with decideValid s t
  ... | yes _ = nothing
  ... | no _ = just s

  module MachineInterface (TBD : Channel) (SignRequest Signature LedgerWrite : Set) where
    open Channels SignRequest Signature public

    chainChannel : Channel
    chainChannel = ChainEvent ⇿ LedgerWrite

    domain codomain : Channel
    domain = TBD ⊗₀ (TBD ⊗₀ (chainChannel ⊗₀ I))
    codomain = accountChannel ⊗₀ I

    chainInput : ChainEvent → Channel.inType (domain ⊗ᵀ codomain)
    chainInput e = (L⊗ (L⊗ (ϵ ⊗R))) ⊗R ↑ᵢ e

    queryInput : Key → Channel.inType (domain ⊗ᵀ codomain)
    queryInput k = codᵍ ↑ₒ getBalance k

    answerOutput : Key → ℕ → Channel.outType (domain ⊗ᵀ codomain)
    answerOutput k n = codᵍ ↑ᵢ balanceIs k n

    data Step : MachineType domain codomain State where
      adopt : ∀ {s t} → finalize s t ≡ Ledger.accepted (apply s t) →
        Step s (chainInput (adopted t)) nothing (apply s t)
      reject : ∀ {s t} → finalize s t ≡ Ledger.rejected s →
        Step s (chainInput (rejected t)) nothing s
      query : ∀ {s k} → Step s (queryInput k) (just (answerOutput k (report s k))) s

    accountCustody : Machine domain codomain
    accountCustody = MkMachine Step

    acPort : Key → Port accountCustody ⊤ ℕ
    acPort k = wirePort accountChannel accountCustody
      (λ _ → getBalance k) (λ _ → balanceIs k)

    chainᵥ : Key → MVal chainChannel
    chainᵥ k In e = effect k e
    chainᵥ k Out _ = 0ℤ

    txValue : Key → Val (Machine.machine-channel accountCustody)
    txValue k i _ = bdryᵥ
      (0ᵥ ⊗ᵥ (0ᵥ ⊗ᵥ (chainᵥ k ⊗ᵥ 0ᵥ))) (0ᵥ ⊗ᵥ 0ᵥ) In i

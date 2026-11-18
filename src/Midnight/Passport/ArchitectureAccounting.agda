{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ)
open import CategoricalCrypto.Channel.Core as Ch hiding (_⊗₀_)
open import Midnight.Passport.Semantics

-- Each invocation selects one query from the channel model; other queries and
-- all architecture boxes remain part of the same machine.
module Midnight.Passport.ArchitectureAccounting
  (cm : ChannelModel) (let open ChannelModel cm)
  (getBalance : Channel.outType ⟦JUBJUB-SCHNORR⟧)
  (balanceIs : ℕ → Channel.inType ⟦JUBJUB-SCHNORR⟧)
  (getBalanceᵁ : Channel.outType ⟦User⟧)
  (balanceIsᵁ : ℕ → Channel.inType ⟦User⟧)
  where

open import Data.Integer using (ℤ)
open import Data.Unit using (⊤)

open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Relay using (Port; Relay; wirePort)
open import CategoricalCrypto.Machine.Simulation
open import CategoricalCrypto.Machine.Valuation
open import Midnight.Passport.BalanceAccounting
open import Midnight.Passport.Flow
import Midnight.Passport.QueryRouting as QR

userPort : (M : Machine ⟦ Var CHAIN ⟧₀ ⟦ Var User ⟧₀) → Port M ⊤ ℕ
userPort M = wirePort ⟦User⟧ M (λ _ → getBalanceᵁ) (λ _ → balanceIsᵁ)

acPort : (AC : Machine ⟦ Var TBD ⊗₀ Var TBD ⊗₀ Var CHAIN ⟧₀
                      ⟦ Var JUBJUB-SCHNORR ⟧₀) → Port AC ⊤ ℕ
acPort AC = wirePort ⟦JUBJUB-SCHNORR⟧ AC (λ _ → getBalance) (λ _ → balanceIs)

module Theorem
  (mm : MachineModel cm)
  (let open MachineModel mm using (⟦architecture⟧; ⟦accountCustody⟧; ⟦passportKey⟧))
  (txval : Channel.inType ⟦CHAIN⟧ → ℤ)
  (s₀ : Machine.State ⟦architecture⟧) (b₀ : ℕ) where

  txValue : Val (Machine.machine-channel ⟦architecture⟧)
  txValue i _ = μ⊤ mm txval In i

  txValueᴬ : Val (Machine.machine-channel ⟦accountCustody⟧)
  txValueᴬ i _ = μᴬ mm txval In i

  module G = BalanceAccounting ⟦architecture⟧ (userPort ⟦architecture⟧) txValue s₀ b₀
  module L = BalanceAccounting ⟦accountCustody⟧ (acPort ⟦accountCustody⟧)
    txValueᴬ (Sim.π (simAC mm) s₀) b₀

  pkRelay : Relay ⟦passportKey⟧ ⊤ ℕ
  pkRelay = QR.pkRelay mm getBalance balanceIs getBalanceᵁ balanceIsᵁ

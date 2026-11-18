{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ)
open import CategoricalCrypto.Channel.Core as Ch hiding (_⊗₀_)
open import Midnight.Passport.Semantics

module Midnight.Passport.PropertiesProof
  (cm : ChannelModel) (let open ChannelModel cm)
  (getBalance : Channel.outType ⟦JUBJUB-SCHNORR⟧)
  (balanceIs : ℕ → Channel.inType ⟦JUBJUB-SCHNORR⟧)
  (getBalanceᵁ : Channel.outType ⟦User⟧)
  (balanceIsᵁ : ℕ → Channel.inType ⟦User⟧)
  where

open import Data.Integer using (ℤ; +_; _+_; _≤_)
open import Data.List using ([])
open import Data.Product
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Relay hiding (sound; complete)
open import CategoricalCrypto.Machine.Simulation
open import CategoricalCrypto.Machine.Valuation
import Midnight.Passport.ArchitectureAccounting as Accounting
open import Midnight.Passport.BalanceAccounting
open import Midnight.Passport.Flow
import Midnight.Passport.QueryRouting as QR

module A = Accounting cm getBalance balanceIs getBalanceᵁ balanceIsᵁ

-- Keep trace reasoning abstract in the machines: expanding the full wiring
-- while elaborating these proofs forces unnecessary architecture conversion.
module GlobalFromLocal {X Y Xᴬ Yᴬ : Channel}
  (M : Machine X Y) (AC : Machine Xᴬ Yᴬ)
  (port : Port M ⊤ ℕ) (portᴬ : Port AC ⊤ ℕ)
  (txValue : Val (Machine.machine-channel M))
  (txValueᴬ : Val (Machine.machine-channel AC))
  (s₀ : Machine.State M) (b₀ : ℕ) (sim : Sim M AC)
  (fp : Preserves sim txValue txValueᴬ)
  (routed : Routing sim port portᴬ) where

  open Sim sim
  module G = BalanceAccounting M port txValue s₀ b₀
  module L = BalanceAccounting AC portᴬ txValueᴬ (π s₀) b₀

  sound : L.Sound → G.Sound
  sound ls {a = a} t gans =
    subst (λ z → + a ≤ + b₀ + z) (flow-onTrace fp t)
      (ls (onTrace t) (Routing.sound routed gans))

  eventuallyAccurate : L.PromptlyAccurate → G.EventuallyAccurate
  eventuallyAccurate lp t with lp (onTrace t)
  ... | a , eq , lans =
      _ , [] , refl , a
    , trans eq (cong (λ z → + b₀ + z) (flow-onTrace fp t))
    , Routing.complete routed lans

  statement : L.Sound → L.PromptlyAccurate → G.Sound × G.EventuallyAccurate
  statement ls lp = sound ls , eventuallyAccurate lp

module Theorem
  (mm : MachineModel cm)
  (let open MachineModel mm using (⟦architecture⟧; ⟦accountCustody⟧))
  (txval : Channel.inType ⟦CHAIN⟧ → ℤ)
  (s₀ : Machine.State ⟦architecture⟧) (b₀ : ℕ) where

  open A.Theorem mm txval s₀ b₀

  top-val : ∀ i o → netVal (μ⊤ mm txval) i o ≡ txValue i o
  top-val = netVal-in {μ = μ⊤ mm txval} (μ⊤-out mm txval)

  ac-val : ∀ i o → netVal (μᴬ mm txval) i o ≡ txValueᴬ i o
  ac-val = netVal-in {μ = μᴬ mm txval} (μᴬ-out mm txval)

  flowPreserving : Preserves (simAC mm) txValue txValueᴬ
  flowPreserving = preserves-cong top-val ac-val (flowAC mm txval)

  queryRouted : ForwardsQuery pkRelay → ForwardsAnswer pkRelay
    → NoInvention pkRelay → Responsive pkRelay
    → AnswersOnly (A.acPort ⟦accountCustody⟧)
    → CanAnswer (A.acPort ⟦accountCustody⟧)
    → Routing (simAC mm) (A.userPort ⟦architecture⟧) (A.acPort ⟦accountCustody⟧)
  queryRouted = QR.balance-routes mm getBalance balanceIs getBalanceᵁ balanceIsᵁ

  private
    module GFL = GlobalFromLocal ⟦architecture⟧ ⟦accountCustody⟧
      (A.userPort ⟦architecture⟧) (A.acPort ⟦accountCustody⟧)
      txValue txValueᴬ s₀ b₀ (simAC mm) flowPreserving

  preservation-of-value
    : L.Sound → L.PromptlyAccurate
    → ForwardsQuery pkRelay → ForwardsAnswer pkRelay
    → NoInvention pkRelay → Responsive pkRelay
    → AnswersOnly (A.acPort ⟦accountCustody⟧)
    → CanAnswer (A.acPort ⟦accountCustody⟧)
    → G.Sound × G.EventuallyAccurate
  preservation-of-value ls lp fq fa ni rsp ao ca =
    GFL.statement (queryRouted fq fa ni rsp ao ca) ls lp

{-# OPTIONS --safe --without-K #-}

open import Conformance.Primitives
import Conformance.AccountLedger as AccountLedger

-- Wallet/signing protocols for Passport.AccountRecovery. These clients are not
-- premises of contract traces; raw transition checking lives in Monitor.
module Conformance.Account (P : Primitives) (self : Primitives.Bytes32 P)
  (variant : AccountLedger.Finalisation P) where

open import Data.Bool.Base
open import Data.List.Base using (List; []; _∷_; foldl)
open import Data.Maybe.Base using (Maybe; nothing; just)
import Data.Maybe.Base as Maybe
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Data.Vec.Base using (Vec; toList)
open import Function.Base using (case_of_; _∘_)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import Conformance.AccountLedger P
open import Conformance.Coins
open import Conformance.Custody P self
open import Conformance.Recovery P self
open import Passport.AccountRecovery P self hiding (module Chain)

open Primitives P

open import Midnight.ContractDSL.Program accountLedger Assertion
import Midnight.ContractDSL.Contract accountLedger Assertion as DSL

-- Wallet instance: selected finalisation variant, logical account identity 0.
module Chain = DSL.Contract (assemble variant)

------------------------------------------------------------------------
-- Clients: signers and wallet

-- The (R, s) pairs in argument order and the shared grind nonce.
record Signature : Set where
  constructor signature
  field nonces : List (Point × ℕ)
        grind : ℕ

-- Loop bounds standing in for the signers' unbounded `for (;;)`; each iteration
-- succeeds with probability ≈ r_J / 2²⁵⁶ ≈ 0.057, so exhaustion has mass < 10⁻¹².
drawBound grindBound : ℕ
drawBound = 512
grindBound = 512

fromBitsBE : {n : ℕ} → Vec Bool n → ℕ
fromBitsBE = foldl (λ acc b → 2 * acc + (if b then 1 else 0)) 0 ∘ toList

-- `randomJubjubScalar`: big-endian 256-bit draws, rejected outside [1, r_J).
sampleNonce : {A : Iface} {X : Set} → ℕ → (ℕ → Calls A X) → Calls A X
sampleNonce zero k = dead
sampleNonce (suc fuel) k = uniformVec 256 λ v → let r = fromBitsBE v in
  if (0 <ᵇ r) ∧ (r <ᵇ jubjubOrder) then k r else sampleNonce fuel k

grindChallenge : ℕ → ℕ → (ℕ → Bytes32) → Maybe (ℕ × ℕ)
grindChallenge zero g h = nothing
grindChallenge (suc fuel) g h = let c = le (h g) in
  if c <ᵇ jubjubOrder then just (g , c) else grindChallenge fuel (suc g) h

respond : ℕ → ℕ → ℕ → ℕ
respond r c sk = (r + c % jubjubOrder * (sk % jubjubOrder) % jubjubOrder) % jubjubOrder

sign : {A : Iface} {X : Set} → ℕ → (Point → ℕ → Bytes32) → (Point → ℕ → ℕ → Calls A X) → Calls A X
sign sk challenge k = sampleNonce drawBound λ r → let R = ecMulG r in
  case grindChallenge grindBound 0 (challenge R) of λ
    { nothing → dead
    ; (just (g , c)) → k R (respond r c sk) g }

-- Both nonces are drawn first (recovery, then successor); one grind serves both.
signPair : {A : Iface} {X : Set} → ℕ → ℕ → (Point → Point → ℕ → Bytes32) →
  (Point → ℕ → Point → ℕ → ℕ → Calls A X) → Calls A X
signPair sk₁ sk₂ challenge k = sampleNonce drawBound λ r₁ → sampleNonce drawBound λ r₂ →
  let R₁ = ecMulG r₁ in let R₂ = ecMulG r₂ in
  case grindChallenge grindBound 0 (challenge R₁ R₂) of λ
    { nothing → dead
    ; (just (g , c)) → k R₁ (respond r₁ c sk₁) R₂ (respond r₂ c sk₂) g }

data Request : Set where
  -- `pk` is presented and `sk` signs, so wrong-key calls are expressible; `nonce` is the
  -- auth_nonce the client observed.
  signed : (g : Gated) → Payload g → (pk : Point) (useCounter sk nonce : ℕ) → Request
  -- `recoveryPk`, `epoch` and `nonce` are the ledger values the client observed.
  recover : (recoverySk successorSk : ℕ) (successorRecoveryPk recoveryPk : Point) (epoch nonce nowUpper : ℕ) → Request
  -- A call built outside the wallet: permissionless circuits, replays, tampered arguments.
  raw : (n : Name) → Input n → Request

data Settlement : Set where
  committed refused : Settlement
  aborted : Error → Settlement

record StepReport : Set where
  constructor stepReport
  field signatures : Maybe Signature
        settlement : Settlement

-- The wallet boundary builds against the supplied view, then submits only the
-- certified transaction to the contract. Invalid candidate journals are Monitor's
-- responsibility, not part of this client interface.
InvocationIf : Iface
InvocationIf = (Error ⊎ Chain.Verdict) ⇿ (Σ Name Input)

execute : ℕ → State → Protocol unitᴵ InvocationIf
execute now initial = record { St = State ; init = initial ; step = invoke }
  where
  invoke : State → Σ Name Input → Calls unitᴵ (State × (Error ⊎ Chain.Verdict))
  invoke s (n , a) with Chain.build n a s
  ... | inj₁ err = ret (s , inj₁ err)
  ... | inj₂ tx = let t , v = Chain.admit s (Chain.submit now tx) in ret (t , inj₂ v)

transact : Maybe Signature → (n : Name) → Input n → Calls InvocationIf StepReport
transact σ n a = call (n , a) λ
  { (inj₁ e) → ret (stepReport σ (aborted e))
  ; (inj₂ Chain.accepted) → ret (stepReport σ committed)
  ; (inj₂ Chain.rejected) → ret (stepReport σ refused) }

walletStep : Request → Calls InvocationIf StepReport
walletStep (signed g p pk uc sk nonce) = sign sk (λ R → challengeOf g p R pk nonce) λ R s gr →
  transact (just (signature ((R , s) ∷ []) gr)) (jubjub g) (p , authorisation pk uc R s gr)
walletStep (recover skᵣ skₛ q′ rpk e n u) =
  signPair skᵣ skₛ (λ Rᵣ Rₛ → challengeSubmit self rpk Rᵣ q Rₛ q′ (suc e) n u) λ Rᵣ sᵣ Rₛ sₛ gr →
    transact (just (signature ((Rᵣ , sᵣ) ∷ (Rₛ , sₛ) ∷ []) gr)) recoverSubmit (submitArgs q q′ e n u Rᵣ sᵣ Rₛ sₛ gr)
  where q = ecMulG skₛ
walletStep (raw n a) = transact nothing n a

wallet : Protocol InvocationIf (StepReport ⇿ Request)
wallet = record { St = ⊤ ; init = tt ; step = λ _ q → walletStep q >>=ᶜ λ r → ret (tt , r) }

assembled : ℕ → State → Protocol unitᴵ (StepReport ⇿ Request)
assembled t s = wallet ∘ᵖ execute t s

-- Oracle 1: one wallet activation at block time `t` against the system holding `s`.
stepModel : ℕ → State → Request → List Bool → Maybe ((State × StepReport) × List Bool)
stepModel t s q bs = Maybe.map (λ (((_ , u) , r) , rest) → (u , r) , rest)
  (stepCoins (assembled t s) (init (assembled t s)) bs q)


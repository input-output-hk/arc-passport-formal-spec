{-# OPTIONS --safe --without-K #-}

open import Conformance.Primitives
import Conformance.AccountLedger as AccountLedger

-- Wallet/signing protocols and executable conformance oracles for the account
-- recovery specification in Passport.AccountRecovery. The variant selects the
-- intended contract or its historical source-shaped comparator; neither wallet
-- construction nor these decision procedures is a premise of contract traces.
-- See docs/conformance-spike.md and docs/conformance-recovery.md.
module Conformance.Account (P : Primitives) (self : Primitives.Bytes32 P)
  (variant : AccountLedger.Finalisation P) where

open import Data.Bool.Base
open import Data.List.Base using (List; []; _∷_; foldl)
import Data.List.Properties as List
open import Data.Maybe.Base using (Maybe; nothing; just)
import Data.Maybe.Base as Maybe
open import Data.Nat.Base
open import Data.Nat.Properties using (_≟_)
open import Data.Product.Base
import Data.Product.Properties as ΣP
open import Data.String.Base using (String)
open import Data.String.Properties using (_==_)
open import Data.Sum.Base
import Data.Sum.Properties as ⊎P
open import Data.Unit.Base
open import Data.Vec.Base using (Vec; toList)
open import Function.Base using (case_of_; _∘_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import Conformance.AccountLedger P
open import Conformance.Coins
open import Conformance.Custody P self
open import Conformance.Decidable
open import Conformance.Recovery P self
open import Passport.AccountRecovery P self

open Primitives P

open import Midnight.ContractDSL.Program accountLedger Assertion
open import Midnight.ContractDSL.Protocol accountLedger Assertion

open ExactCommunication (assemble variant)
open Interpreter (assemble variant) scheme 0

-- The chain view of one activation: the Interpreter's account and the block time.
at : ℕ → Context
at = context 0

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

transact : Maybe Signature → (n : Name) → Input n → Calls ClientIf StepReport
transact σ n a = call (build n a tt 0) λ
  { (built _ _ _ _) → call submit λ
      { (submitted accepted) → ret (stepReport σ committed)
      ; _ → ret (stepReport σ refused) }
  ; (buildFailed e _) → ret (stepReport σ (aborted e))
  ; _ → ret (stepReport σ refused) }

walletStep : Request → Calls ClientIf StepReport
walletStep (signed g p pk uc sk nonce) = sign sk (λ R → challengeOf g p R pk nonce) λ R s gr →
  transact (just (signature ((R , s) ∷ []) gr)) (jubjub g) (p , authorisation pk uc R s gr)
walletStep (recover skᵣ skₛ q′ rpk e n u) =
  signPair skᵣ skₛ (λ Rᵣ Rₛ → challengeSubmit self rpk Rᵣ q Rₛ q′ (suc e) n u) λ Rᵣ sᵣ Rₛ sₛ gr →
    transact (just (signature ((Rᵣ , sᵣ) ∷ (Rₛ , sₛ) ∷ []) gr)) recoverSubmit (submitArgs q q′ e n u Rᵣ sᵣ Rₛ sₛ gr)
  where q = ecMulG skₛ
walletStep (raw n a) = transact nothing n a

wallet : Protocol ClientIf (StepReport ⇿ Request)
wallet = record { St = ⊤ ; init = tt ; step = λ _ q → walletStep q >>=ᶜ λ r → ret (tt , r) }

assembled : ℕ → State → Protocol unitᴵ (StepReport ⇿ Request)
assembled t s = wallet ∘ᵖ system (at t) s

-- Oracle 1: one wallet activation at block time `t` against the system holding `s`.
stepModel : ℕ → State → Request → List Bool → Maybe ((State × StepReport) × List Bool)
stepModel t s q bs = Maybe.map (λ (((_ , _ , u , _) , r) , rest) → (u , r) , rest)
  (stepCoins (assembled t s) (init (assembled t s)) bs q)

------------------------------------------------------------------------
-- Certificate decision (ExactCommunication relation)

private
  infixr 4 _⊗_
  _⊗_ : {A B : Set} → DecidableEquality A → DecidableEquality B → DecidableEquality (A × B)
  d₁ ⊗ d₂ = ΣP.≡-dec d₁ d₂

_≟ᴳ_ : DecidableEquality Gated
_≟ᴳ_ = via tag untag (λ
  { withdrawUnshielded → refl ; addDevice → refl ; removeDevice → refl ; rotateEncKey → refl
  ; publishRecoverySession → refl ; recoverCancel → refl }) _≟_
  where
  tag : Gated → ℕ
  tag withdrawUnshielded = 0
  tag addDevice = 1
  tag removeDevice = 2
  tag rotateEncKey = 3
  tag publishRecoverySession = 4
  tag recoverCancel = 5
  untag : ℕ → Maybe Gated
  untag 0 = just withdrawUnshielded
  untag 1 = just addDevice
  untag 2 = just removeDevice
  untag 3 = just rotateEncKey
  untag 4 = just publishRecoverySession
  untag 5 = just recoverCancel
  untag _ = nothing

_≟ᴺ_ : DecidableEquality Name
_≟ᴺ_ = via encode decode (λ
  { depositUnshielded → refl ; recoverSubmit → refl ; recoverFinalise → refl
  ; (jubjub _) → refl }) (⊎P.≡-dec _≟_ _≟ᴳ_)
  where
  encode : Name → ℕ ⊎ Gated
  encode depositUnshielded = inj₁ 0
  encode recoverSubmit = inj₁ 1
  encode recoverFinalise = inj₁ 2
  encode (jubjub g) = inj₂ g
  decode : ℕ ⊎ Gated → Maybe Name
  decode (inj₁ 0) = just depositUnshielded
  decode (inj₁ 1) = just recoverSubmit
  decode (inj₁ 2) = just recoverFinalise
  decode (inj₁ _) = nothing
  decode (inj₂ g) = just (jubjub g)

decAuthorisation : DecidableEquality Authorisation
decAuthorisation = via (λ (authorisation pk u R s g) → pk , u , R , s , g)
  (λ (pk , u , R , s , g) → just (authorisation pk u R s g)) (λ _ → refl)
  (_≟ᴾ_ ⊗ _≟_ ⊗ _≟ᴾ_ ⊗ _≟_ ⊗ _≟_)

decPayload : (g : Gated) → DecidableEquality (Payload g)
decPayload withdrawUnshielded = _≟ᴮ_ ⊗ _≟_ ⊗ _≟ᴮ_
decPayload addDevice = _≟ᴮ_
decPayload removeDevice = _≟ᴮ_
decPayload rotateEncKey = _≟ᴮ_
decPayload publishRecoverySession = via (λ (publishArgs pk n φ len w) → pk , n , φ , len , w)
  (λ (pk , n , φ , len , w) → just (publishArgs pk n φ len w)) (λ _ → refl)
  (_≟ᴾ_ ⊗ _≟ᴮ_ ⊗ (_≟_ ⊗ _≟_ ⊗ _≟_ ⊗ _≟_) ⊗ _≟_ ⊗ _≟ᵂ_)
decPayload recoverCancel tt tt = yes refl

decInput : (n : Name) → DecidableEquality (Input n)
decInput depositUnshielded = _≟ᴮ_ ⊗ _≟_
decInput recoverSubmit = via
  (λ (submitArgs q q′ e n u Rᵣ sᵣ Rₛ sₛ g) → q , q′ , e , n , u , Rᵣ , sᵣ , Rₛ , sₛ , g)
  (λ (q , q′ , e , n , u , Rᵣ , sᵣ , Rₛ , sₛ , g) → just (submitArgs q q′ e n u Rᵣ sᵣ Rₛ sₛ g)) (λ _ → refl)
  (_≟ᴾ_ ⊗ _≟ᴾ_ ⊗ _≟_ ⊗ _≟_ ⊗ _≟_ ⊗ _≟ᴾ_ ⊗ _≟_ ⊗ _≟ᴾ_ ⊗ _≟_ ⊗ _≟_)
decInput recoverFinalise tt tt = yes refl
decInput (jubjub g) = decPayload g ⊗ decAuthorisation

decTuple : DecidableEquality Tuple
decTuple = via (λ (tuple acc n a r o) → acc , (n , a) , o) (λ (acc , (n , a) , o) → just (tuple acc n a tt o)) (λ _ → refl)
  (_≟_ ⊗ ΣP.≡-dec _≟ᴺ_ (λ {n} → decInput n) ⊗ _≟_)

decCondition : DecidableEquality Condition
decCondition = via
  (λ { (timeAtLeast t) → inj₁ t ; (timeAtMost t) → inj₂ t })
  (λ { (inj₁ t) → just (timeAtLeast t) ; (inj₂ t) → just (timeAtMost t) })
  (λ { (timeAtLeast _) → refl ; (timeAtMost _) → refl })
  (⊎P.≡-dec _≟_ _≟_)

decEvent : DecidableEquality Event
decEvent = via
  (λ { (operated o x) → inj₁ (_ , o , x) ; (published v) → inj₂ (inj₁ v) ; (required c) → inj₂ (inj₂ c) })
  (λ { (inj₁ (_ , o , x)) → just (operated o x) ; (inj₂ (inj₁ v)) → just (published v) ; (inj₂ (inj₂ c)) → just (required c) })
  (λ { (operated _ _) → refl ; (published _) → refl ; (required _) → refl })
  (⊎P.≡-dec decOperated (⊎P.≡-dec _≟_ decCondition))

_≟ᴶ_ : DecidableEquality Journal
_≟ᴶ_ = List.≡-dec decEvent

decRun : (p : Program ⊤) (s : State) (j : Journal) → Dec (Σ State λ t → eval p s ≡ inj₂ (finished tt t j))
decRun p s j with eval p s
... | inj₁ _ = no λ { (_ , ()) }
... | inj₂ (finished _ t j′) = map′ (λ { refl → t , refl }) (λ { (_ , refl) → refl }) (j′ ≟ᴶ j)

decRel : (x : Statement) (e : Evidence x) → Dec (Rel x e)
decRel (statement acc n pa bind j) (evidence s a w r o) =
  decInput n a pa ×-dec decTuple (tuple acc n a r o) bind ×-dec decRun (circuit variant n a) s j

certified : Tx → Bool
certified (transaction x invalid) = false
certified (transaction x (certificate e _)) = does (decRel x e)

------------------------------------------------------------------------
-- Oracle 2: judge an observed transition

data Observed : Set where
  succeeded : Observed
  failed : String → Observed

-- An abort must leave the state untouched and carry the expected code; an admission
-- refusal (a chain-time requirement) is observed as the code "refused".
failedAs : String → State → State → Observed → Bool
failedAs _ s s′ succeeded = false
failedAs code s s′ (failed c) = (c == code) ∧ (s′ ≈ᵇ s)

succeededAs : State → State → Observed → Bool
succeededAs t s′ succeeded = s′ ≈ᵇ t
succeededAs t s′ (failed _) = false

-- `observed` is the implementation's verdict with its abort message mapped to `errorCode`.
decide : ℕ → State → (n : Name) → Input n → State → Observed → Bool
decide t s n a s′ observed = judge (eval (circuit variant n a) s) refl
  where
  settled : State × Verdict → Bool
  settled (u , accepted) = succeededAs u s′ observed
  settled (_ , rejected) = failedAs "refused" s s′ observed

  judge : (o : Outcome ⊤) → eval (circuit variant n a) s ≡ o → Bool
  judge (inj₁ e) _ = failedAs (errorCode e) s s′ observed
  judge (inj₂ (finished r u j)) eq = let tx = makeTx n a tt 0 s r u j eq in certified tx ∧ settled (admission (at t) s tx)

{-# OPTIONS --safe --without-K #-}

-- Pure token codec and command entry: respond takes the trusted primitive backend
-- and a request line. Backend fixes that backend; Line then fixes the Bytes32
-- challenge domain self and finalisation variant (not the logical account identity).
-- check/normalize consume monitor-v1 observations; prepare builds a candidate.
-- The separate step oracle drives wallet/signing clients with supplied coin bits.
-- Grammar and backend contract:
-- docs/conformance-recovery.md#serialization-and-executable-adapter

module Conformance.Wire where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_; _∨_)
import Data.Char.Base as Char
open import Data.List.Base using (List; []; _∷_; length; concatMap) renaming (_++_ to _++ˡ_)
open import Data.Maybe.Base using (Maybe; nothing; just; _>>=_)
import Data.Maybe.Base as Maybe
open import Data.Nat.Base
open import Data.Nat.Show using (show; readMaybe)
open import Data.Product.Base
open import Data.String.Base using (String; _++_; words; unwords; toList)
import Data.String.Properties as String
open import Data.Unit.Base
open import Function.Base using (_∘_)

open import Data.Bool.ListAction using (all; any)
open import Data.Sum.Base

open import Relation.Nullary using (does)
import Conformance.Account
import Conformance.Monitor

module Backend (backend : String → String) where
  open import Conformance.Oracle backend
  open import Conformance.AccountLedger primitives

  Tokens = List String
  Parse : Set → Set
  Parse A = Tokens → Maybe (A × Tokens)

  tok : Parse String
  tok [] = nothing
  tok (t ∷ ts) = just (t , ts)

  decimal : String → Bool
  decimal t with toList t
  ... | [] = false
  ... | cs = all (λ c → (48 ≤ᵇ Char.toℕ c) ∧ (Char.toℕ c ≤ᵇ 57)) cs

  hex : ℕ → String → Bool
  hex n t = (length (toList t) ≡ᵇ n) ∧ all digit (toList t)
    where
    digit : Char.Char → Bool
    digit c = let k = Char.toℕ c in
      ((48 ≤ᵇ k) ∧ (k ≤ᵇ 57)) ∨ ((97 ≤ᵇ k) ∧ (k ≤ᵇ 102))

  bytesP : ℕ → Parse String
  bytesP n ts = do
    (t , ts) ← tok ts
    if hex n t then just (t , ts) else nothing

  bytes32P bytes64P : Parse String
  bytes32P = bytesP 64
  bytes64P = bytesP 128

  flagP : Parse Bool
  flagP ("0" ∷ ts) = just (false , ts)
  flagP ("1" ∷ ts) = just (true , ts)
  flagP _ = nothing

  unique : List String → Bool
  unique [] = true
  unique (x ∷ xs) = (if any (λ y → does (String._≟_ x y)) xs then false else true) ∧ unique xs

  num : Parse ℕ
  num ts = do
    (t , ts) ← tok ts
    if decimal t then Maybe.map (_, ts) (readMaybe 10 t) else nothing

  pointP : Parse (ℕ × ℕ)
  pointP ts = do
    (x , ts) ← num ts
    (y , ts) ← num ts
    just ((x , y) , ts)

  many : {A : Set} → ℕ → Parse A → Parse (List A)
  many zero p ts = just ([] , ts)
  many (suc n) p ts = do
    (x , ts) ← p ts
    (xs , ts) ← many n p ts
    just (x ∷ xs , ts)

  phiP : Parse Phi
  phiP ts = do
    (a , ts) ← num ts
    (b , ts) ← num ts
    (c , ts) ← num ts
    (d , ts) ← num ts
    just ((a , b , c , d) , ts)

  stateP : Parse State
  stateP ts = do
    (r , ts) ← num ts
    (n , ts) ← num ts
    (e , ts) ← num ts
    (c , ts) ← num ts
    (nd , ts) ← num ts
    (ds , ts) ← many nd bytes32P ts
    (nb , ts) ← num ts
    (bs , ts) ← many nb entryP ts
    (k , ts) ← bytes32P ts
    (rpk , ts) ← pointP ts
    (φ , ts) ← optional ts
    (len , ts) ← num ts
    (sess , ts) ← bytes32P ts
    (w , ts) ← bytes64P ts
    (pend , ts) ← flagP ts
    (pe , ts) ← bytes32P ts
    (ppk , ts) ← pointP ts
    (t , ts) ← num ts
    (v , ts) ← num ts
    if unique ds ∧ unique (Data.List.Base.map proj₁ bs)
      then just (state r n e c ds bs k rpk φ len sess w pend pe ppk t v , ts) else nothing
    where
    entryP : Parse (String × ℕ)
    entryP ts = do
      (k , ts) ← bytes32P ts
      (v , ts) ← num ts
      just ((k , v) , ts)
    optional : Parse (Maybe Phi)
    optional ("0" ∷ ts) = just (nothing , ts)
    optional ("4" ∷ ts) = Maybe.map (λ (φ , ts) → just φ , ts) (phiP ts)
    optional _ = nothing

  showPoint : ℕ × ℕ → String
  showPoint = unwords ∘ pt

  showState : State → String
  showState (state r n e c ds bs k rpk φ len sess w pend pe ppk t v) = unwords
    ((show r ∷ show n ∷ show e ∷ show c ∷ show (length ds) ∷ []) ++ˡ ds
    ++ˡ (show (length bs) ∷ []) ++ˡ concatMap (λ (k , v) → k ∷ show v ∷ []) bs
    ++ˡ (k ∷ showPoint rpk ∷ showPhi φ ∷ show len ∷ sess ∷ w
      ∷ (if pend then "1" else "0") ∷ pe ∷ showPoint ppk ∷ show t ∷ show v ∷ []))
    where
    showPhi : Maybe Phi → String
    showPhi nothing = "0"
    showPhi (just (a , b , c , d)) = unwords ("4" ∷ show a ∷ show b ∷ show c ∷ show d ∷ [])

  module Line (self : String) (variant : Finalisation) where
    module Wallet = Conformance.Account primitives self variant
    open Wallet
    module M = Conformance.Monitor primitives self variant
    open M
    open import Conformance.Custody primitives self
    open import Conformance.Recovery primitives self
    open import Passport.AccountRecovery primitives self
    open import Midnight.ContractDSL.Program accountLedger Assertion hiding (_>>=_; _>>_)

    gatedP : Parse (Σ Gated Payload)
    gatedP ("W" ∷ ts) = do
      (c , ts) ← bytes32P ts
      (a , ts) ← num ts
      (r , ts) ← bytes32P ts
      just ((withdrawUnshielded , c , a , r) , ts)
    gatedP ("A" ∷ ts) = Maybe.map (λ (e , ts) → (addDevice , e) , ts) (bytes32P ts)
    gatedP ("R" ∷ ts) = Maybe.map (λ (e , ts) → (removeDevice , e) , ts) (bytes32P ts)
    gatedP ("K" ∷ ts) = Maybe.map (λ (k , ts) → (rotateEncKey , k) , ts) (bytes32P ts)
    gatedP ("P" ∷ ts) = do
      (q , ts) ← pointP ts
      (sess , ts) ← bytes32P ts
      (φ , ts) ← phiP ts
      (len , ts) ← num ts
      (w , ts) ← bytes64P ts
      just ((publishRecoverySession , publishArgs q sess φ len w) , ts)
    gatedP ("C" ∷ ts) = just ((recoverCancel , tt) , ts)
    gatedP _ = nothing

    callP : Parse (Σ Name Input)
    callP ("D" ∷ ts) = do
      (c , ts) ← bytes32P ts
      (a , ts) ← num ts
      just ((depositUnshielded , c , a) , ts)
    callP ("F" ∷ ts) = just ((recoverFinalise , tt) , ts)
    callP ("U" ∷ ts) = do
      (q , ts) ← pointP ts
      (q′ , ts) ← pointP ts
      (e , ts) ← num ts
      (n , ts) ← num ts
      (u , ts) ← num ts
      (Rᵣ , ts) ← pointP ts
      (sᵣ , ts) ← num ts
      (Rₛ , ts) ← pointP ts
      (sₛ , ts) ← num ts
      (g , ts) ← num ts
      just ((recoverSubmit , submitArgs q q′ e n u Rᵣ sᵣ Rₛ sₛ g) , ts)
    callP ("J" ∷ ts) = do
      ((g , p) , ts) ← gatedP ts
      (pk , ts) ← pointP ts
      (uc , ts) ← num ts
      (R , ts) ← pointP ts
      (s , ts) ← num ts
      (gr , ts) ← num ts
      just ((jubjub g , p , authorisation pk uc R s gr) , ts)
    callP _ = nothing

    showFlag : Bool → String
    showFlag b = if b then "1" else "0"

    showGated : (g : Gated) → Payload g → String
    showGated withdrawUnshielded (c , a , r) = unwords ("W" ∷ c ∷ show a ∷ r ∷ [])
    showGated addDevice e = "A " ++ e
    showGated removeDevice e = "R " ++ e
    showGated rotateEncKey k = "K " ++ k
    showGated publishRecoverySession (publishArgs q sess (a , b , c , d) len w) =
      unwords ("P" ∷ showPoint q ∷ sess ∷ show a ∷ show b ∷ show c ∷ show d ∷ show len ∷ w ∷ [])
    showGated recoverCancel tt = "C"

    showCall : RawCall → String
    showCall (depositUnshielded , c , a) = unwords ("D" ∷ c ∷ show a ∷ [])
    showCall (recoverFinalise , tt) = "F"
    showCall (recoverSubmit , submitArgs q q′ e n u Rᵣ sᵣ Rₛ sₛ g) =
      unwords ("U" ∷ showPoint q ∷ showPoint q′ ∷ show e ∷ show n ∷ show u
        ∷ showPoint Rᵣ ∷ show sᵣ ∷ showPoint Rₛ ∷ show sₛ ∷ show g ∷ [])
    showCall (jubjub g , p , authorisation pk uc R s gr) =
      unwords ("J" ∷ showGated g p ∷ showPoint pk ∷ show uc ∷ showPoint R ∷ show s ∷ show gr ∷ [])

    opP : Parse (Σ Kind Op)
    opP ("readNonce" ∷ ts) = just ((count , readNonce) , ts)
    opP ("readRound" ∷ ts) = just ((count , readRound) , ts)
    opP ("readEpoch" ∷ ts) = just ((count , readEpoch) , ts)
    opP ("readDeviceCount" ∷ ts) = just ((count , readDeviceCount) , ts)
    opP ("readVetoWindow" ∷ ts) = just ((count , readVetoWindow) , ts)
    opP ("readNotBefore" ∷ ts) = just ((count , readNotBefore) , ts)
    opP ("readBalance" ∷ ts) = Maybe.map (λ (c , ts) → (count , readBalance c) , ts) (bytes32P ts)
    opP ("readPending" ∷ ts) = just ((flag , readPending) , ts)
    opP ("deviceMember" ∷ ts) = Maybe.map (λ (e , ts) → (flag , deviceMember e) , ts) (bytes32P ts)
    opP ("balanceMember" ∷ ts) = Maybe.map (λ (c , ts) → (flag , balanceMember c) , ts) (bytes32P ts)
    opP ("readRecoveryPk" ∷ ts) = just ((point , readRecoveryPk) , ts)
    opP ("readPendingRecoveryPk" ∷ ts) = just ((point , readPendingRecoveryPk) , ts)
    opP ("readSession" ∷ ts) = just ((bytes , readSession) , ts)
    opP ("readPendingEntry" ∷ ts) = just ((bytes , readPendingEntry) , ts)
    opP ("writeBalance" ∷ ts) = do
      (c , ts) ← bytes32P ts
      (n , ts) ← num ts
      just ((unit , writeBalance c n) , ts)
    opP ("insertDevice" ∷ ts) = Maybe.map (λ (e , ts) → (unit , insertDevice e) , ts) (bytes32P ts)
    opP ("removeDevice" ∷ ts) = Maybe.map (λ (e , ts) → (unit , removeDevice e) , ts) (bytes32P ts)
    opP ("resetDevices" ∷ ts) = just ((unit , resetDevices) , ts)
    opP ("setEncKey" ∷ ts) = Maybe.map (λ (e , ts) → (unit , setEncKey e) , ts) (bytes32P ts)
    opP ("writeNonce" ∷ ts) = Maybe.map (λ (n , ts) → (unit , writeNonce n) , ts) (num ts)
    opP ("writeRound" ∷ ts) = Maybe.map (λ (n , ts) → (unit , writeRound n) , ts) (num ts)
    opP ("writeEpoch" ∷ ts) = Maybe.map (λ (n , ts) → (unit , writeEpoch n) , ts) (num ts)
    opP ("writeDeviceCount" ∷ ts) = Maybe.map (λ (n , ts) → (unit , writeDeviceCount n) , ts) (num ts)
    opP ("writeNotBefore" ∷ ts) = Maybe.map (λ (n , ts) → (unit , writeNotBefore n) , ts) (num ts)
    opP ("writePhiLen" ∷ ts) = Maybe.map (λ (n , ts) → (unit , writePhiLen n) , ts) (num ts)
    opP ("writeRecoveryPk" ∷ ts) = Maybe.map (λ (p , ts) → (unit , writeRecoveryPk p) , ts) (pointP ts)
    opP ("writePendingRecoveryPk" ∷ ts) = Maybe.map (λ (p , ts) → (unit , writePendingRecoveryPk p) , ts) (pointP ts)
    opP ("writeSession" ∷ ts) = Maybe.map (λ (b , ts) → (unit , writeSession b) , ts) (bytes32P ts)
    opP ("writePendingEntry" ∷ ts) = Maybe.map (λ (b , ts) → (unit , writePendingEntry b) , ts) (bytes32P ts)
    opP ("writePending" ∷ ts) = Maybe.map (λ (b , ts) → (unit , writePending b) , ts) (flagP ts)
    opP ("insertPhi1" ∷ ts) = Maybe.map (λ (n , ts) → (unit , insertPhi1 n) , ts) (num ts)
    opP ("insertPhi2" ∷ ts) = Maybe.map (λ (n , ts) → (unit , insertPhi2 n) , ts) (num ts)
    opP ("insertPhi3" ∷ ts) = Maybe.map (λ (n , ts) → (unit , insertPhi3 n) , ts) (num ts)
    opP ("insertPhi4" ∷ ts) = Maybe.map (λ (n , ts) → (unit , insertPhi4 n) , ts) (num ts)
    opP ("writeWrap" ∷ ts) = Maybe.map (λ (w , ts) → (unit , writeWrap w) , ts) (bytes64P ts)
    opP _ = nothing

    resultP : (k : Kind) → Parse (Res k)
    resultP count ("count" ∷ ts) = num ts
    resultP flag ("flag" ∷ ts) = flagP ts
    resultP unit ("unit" ∷ "-" ∷ ts) = just (tt , ts)
    resultP point ("point" ∷ ts) = pointP ts
    resultP bytes ("bytes" ∷ ts) = bytes32P ts
    resultP _ _ = nothing

    eventP : Parse Event
    eventP ("op" ∷ ts) = do
      ((k , op) , ts) ← opP ts
      (x , ts) ← resultP k ts
      just (operated op x , ts)
    eventP ("publish" ∷ ts) = Maybe.map (λ (n , ts) → published n , ts) (num ts)
    eventP ("require" ∷ "min" ∷ ts) = Maybe.map (λ (n , ts) → required (timeAtLeast n) , ts) (num ts)
    eventP ("require" ∷ "max" ∷ ts) = Maybe.map (λ (n , ts) → required (timeAtMost n) , ts) (num ts)
    eventP _ = nothing

    showOp : {k : Kind} → Op k → String
    showOp readNonce = "readNonce"
    showOp readRound = "readRound"
    showOp readEpoch = "readEpoch"
    showOp readDeviceCount = "readDeviceCount"
    showOp readVetoWindow = "readVetoWindow"
    showOp readNotBefore = "readNotBefore"
    showOp (readBalance c) = "readBalance " ++ c
    showOp readPending = "readPending"
    showOp (deviceMember e) = "deviceMember " ++ e
    showOp (balanceMember c) = "balanceMember " ++ c
    showOp readRecoveryPk = "readRecoveryPk"
    showOp readPendingRecoveryPk = "readPendingRecoveryPk"
    showOp readSession = "readSession"
    showOp readPendingEntry = "readPendingEntry"
    showOp (writeBalance c n) = unwords ("writeBalance" ∷ c ∷ show n ∷ [])
    showOp (insertDevice e) = "insertDevice " ++ e
    showOp (removeDevice e) = "removeDevice " ++ e
    showOp resetDevices = "resetDevices"
    showOp (setEncKey e) = "setEncKey " ++ e
    showOp (writeNonce n) = "writeNonce " ++ show n
    showOp (writeRound n) = "writeRound " ++ show n
    showOp (writeEpoch n) = "writeEpoch " ++ show n
    showOp (writeDeviceCount n) = "writeDeviceCount " ++ show n
    showOp (writeNotBefore n) = "writeNotBefore " ++ show n
    showOp (writePhiLen n) = "writePhiLen " ++ show n
    showOp (writeRecoveryPk p) = "writeRecoveryPk " ++ showPoint p
    showOp (writePendingRecoveryPk p) = "writePendingRecoveryPk " ++ showPoint p
    showOp (writeSession b) = "writeSession " ++ b
    showOp (writePendingEntry b) = "writePendingEntry " ++ b
    showOp (writePending b) = "writePending " ++ showFlag b
    showOp (insertPhi1 n) = "insertPhi1 " ++ show n
    showOp (insertPhi2 n) = "insertPhi2 " ++ show n
    showOp (insertPhi3 n) = "insertPhi3 " ++ show n
    showOp (insertPhi4 n) = "insertPhi4 " ++ show n
    showOp (writeWrap w) = "writeWrap " ++ w

    showResult : (k : Kind) → Res k → String
    showResult count n = "count " ++ show n
    showResult flag b = "flag " ++ showFlag b
    showResult unit tt = "unit -"
    showResult point p = "point " ++ showPoint p
    showResult bytes b = "bytes " ++ b

    showEvent : Event → String
    showEvent (operated {k} op x) = unwords ("op" ∷ showOp op ∷ showResult k x ∷ [])
    showEvent (published n) = "publish " ++ show n
    showEvent (required (timeAtLeast n)) = "require min " ++ show n
    showEvent (required (timeAtMost n)) = "require max " ++ show n

    journalP : Parse Journal
    journalP ("J" ∷ ts) = do
      (n , ts) ← num ts
      many n eventP ts
    journalP _ = nothing

    candidateP : Parse Candidate
    candidateP ts = do
      (acc , ts) ← num ts
      (s , ts) ← stateP ts
      (call , ts) ← callP ts
      (j , ts) ← journalP ts
      just (candidate acc s call j , ts)

    showCandidate : Candidate → String
    showCandidate (candidate acc s call j) =
      unwords (show acc ∷ showState s ∷ showCall call ∷ "J" ∷ show (length j)
        ∷ Data.List.Base.map showEvent j)

    -- Agda Observed is the host APIs' Outcome, not the DSL evaluation Outcome;
    -- see Conformance.Monitor.Observed for the constructor/token mapping.
    observedP : Parse M.Observed
    observedP ("ok" ∷ ts) = just (M.accepted , ts)
    observedP ("refused" ∷ ts) = just (M.rejected , ts)
    observedP ("fail" ∷ code ∷ ts) = just (M.aborted code , ts)
    observedP _ = nothing

    showObserved : M.Observed → String
    showObserved M.accepted = "ok"
    showObserved M.rejected = "refused"
    showObserved (M.aborted code) = "fail " ++ code

    transitionP : Parse Transition
    transitionP ("call" ∷ ts) = do
      (acc , ts) ← num ts
      (time , ts) ← num ts
      (call , ts) ← callP ts
      (observed , ts) ← observedP ts
      just (invocation (context acc time) call observed , ts)
    transitionP ("admit" ∷ ts) = do
      (acc , ts) ← num ts
      (time , ts) ← num ts
      (c , ts) ← candidateP ts
      (observed , ts) ← observedP ts
      just (M.admission (context acc time) c observed , ts)
    transitionP _ = nothing

    showTransition : Transition → String
    showTransition (invocation (context acc time) call observed) =
      unwords ("call" ∷ show acc ∷ show time ∷ showCall call ∷ showObserved observed ∷ [])
    showTransition (M.admission (context acc time) c observed) =
      unwords ("admit" ∷ show acc ∷ show time ∷ showCandidate c ∷ showObserved observed ∷ [])

    observationP : Parse Observation
    observationP ts = do
      (s , ts) ← stateP ts
      (tr , ts) ← transitionP ts
      (t , ts) ← stateP ts
      just (observation s tr t , ts)

    showObservation : Observation → String
    showObservation (observation s tr t) =
      unwords (showState s ∷ showTransition tr ∷ showState t ∷ [])

    preparationP : Parse (ℕ × State × RawCall)
    preparationP ts = do
      (acc , ts) ← num ts
      (s , ts) ← stateP ts
      (call , ts) ← callP ts
      just ((acc , s , call) , ts)

    prepareLine : Tokens → String
    prepareLine ts with preparationP ts
    ... | just ((acc , s , call) , []) with prepareCandidate acc s call
    ...   | inj₁ err = "= fail " ++ errorCode err
    ...   | inj₂ c = "= candidate " ++ showCandidate c
    prepareLine _ | _ = "= error malformed prepare"

    ------------------------------------------------------------------------
    -- Separate wallet step oracle (not a monitor-v1 observation)
    ------------------------------------------------------------------------

    bitsP : Parse (List Bool)
    bitsP ("B" ∷ "-" ∷ ts) = just ([] , ts)
    bitsP ("B" ∷ b ∷ ts) = if all binary (toList b)
      then just (Data.List.Base.map (λ c → Char.toℕ c ≡ᵇ 49) (toList b) , ts) else nothing
      where
      binary : Char.Char → Bool
      binary c = (Char.toℕ c ≡ᵇ 48) ∨ (Char.toℕ c ≡ᵇ 49)
    bitsP _ = nothing

    requestP : Parse Request
    requestP ("S" ∷ ts) = do
      ((g , p) , ts) ← gatedP ts
      (pk , ts) ← pointP ts
      (uc , ts) ← num ts
      (sk , ts) ← num ts
      (n , ts) ← num ts
      just (signed g p pk uc sk n , ts)
    requestP ("U" ∷ ts) = do
      (skᵣ , ts) ← num ts
      (skₛ , ts) ← num ts
      (q′ , ts) ← pointP ts
      (rpk , ts) ← pointP ts
      (e , ts) ← num ts
      (n , ts) ← num ts
      (u , ts) ← num ts
      just (recover skᵣ skₛ q′ rpk e n u , ts)
    requestP ("X" ∷ ts) = Maybe.map (λ ((n , a) , ts) → raw n a , ts) (callP ts)
    requestP _ = nothing


    showSettlement : Settlement → String
    showSettlement committed = "ok"
    showSettlement refused = "refused"
    showSettlement (Wallet.aborted e) = "fail " ++ errorCode e

    showSigned : Maybe Signature → String
    showSigned nothing = "-"
    showSigned (just (signature rs g)) =
      unwords (concatMap (λ (R , s) → pt R ++ˡ show s ∷ []) rs) ++ " " ++ show g

    stepP : Parse (ℕ × State × Request × List Bool)
    stepP ts = do
      (t , ts) ← num ts
      (s , ts) ← stateP ts
      (q , ts) ← requestP ts
      (bs , ts) ← bitsP ts
      just ((t , s , q , bs) , ts)

    stepLine : Tokens → String
    stepLine ts with stepP ts
    ... | just ((t , s , q , bs) , []) with stepModel t s q bs
    ...   | nothing = "= stuck"
    ...   | just ((u , stepReport σ out) , rest) =
      "= " ++ showSettlement out ++ " sig " ++ showSigned σ ++ " state " ++ showState u ++ " rest " ++ show (length rest)
    stepLine _ | _ = "= error malformed step"

  variantP : String → Maybe Finalisation
  variantP "source" = just sourceShaped
  variantP "corrected" = just corrected
  variantP _ = nothing

  showVariant : Finalisation → String
  showVariant sourceShaped = "source"
  showVariant corrected = "corrected"

  record Envelope : Set where
    constructor envelope
    field variant : Finalisation
          self : String
          observed : Conformance.Monitor.Observation primitives self variant

  complete : {A : Set} → Parse A → Tokens → Maybe A
  complete parser ts with parser ts
  ... | just (x , []) = just x
  ... | _ = nothing

  decode : String → Maybe Envelope
  decode input with words input
  ... | "monitor-v1" ∷ v ∷ self ∷ ts = do
    variant ← variantP v
    if hex 64 self
      then Maybe.map (envelope variant self) (complete (Line.observationP self variant) ts)
      else nothing
  ... | _ = nothing

  encode : Envelope → String
  encode (envelope variant self observed) =
    unwords ("monitor-v1" ∷ showVariant variant ∷ self ∷ Line.showObservation self variant observed ∷ [])

  check : Envelope → Bool
  check (envelope variant self observed) = Conformance.Monitor.check primitives self variant observed

  respond : String → String
  respond line with words line
  ... | "check" ∷ ts with decode (unwords ts)
  ...   | nothing = "= error malformed observation"
  ...   | just obs = if check obs then "= true" else "= false"
  respond _ | "normalize" ∷ ts with decode (unwords ts)
  ...   | nothing = "= error malformed observation"
  ...   | just obs = "= " ++ encode obs
  respond _ | "prepare" ∷ v ∷ self ∷ ts with variantP v
  ...   | nothing = "= error unknown variant"
  ...   | just variant = if hex 64 self then Line.prepareLine self variant ts else "= error malformed self"
  respond _ | "step" ∷ v ∷ self ∷ ts with variantP v
  ...   | nothing = "= error unknown variant"
  ...   | just variant = if hex 64 self then Line.stepLine self variant ts else "= error malformed self"
  respond _ | _ = "= error unknown request"

respond : (String → String) → String → String
respond = Backend.respond

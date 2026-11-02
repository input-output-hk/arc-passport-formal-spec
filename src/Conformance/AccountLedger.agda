{-# OPTIONS --safe --without-K #-}

open import Conformance.Primitives

-- Account cells, Set/Map queries and mutations of the pinned Compact account.
-- Each Op is one ledger access; circuit combinations live in Custody/Recovery.
-- Phi projects the four published slots, not arbitrary Compact maps: insertion
-- into an empty projection fills unrepresented slots with zero until the other
-- inserts execute. No circuit reads those intermediate slots; aborts roll back.
-- The constant recovery_version is projected away.
module Conformance.AccountLedger (P : Primitives) where

open import Class.DecEq using (DecEq)
open import Data.Bool.Base
open import Data.Bool.ListAction using (all; any)
open import Data.Bool.Properties using () renaming (_≟_ to _≟ᵇ_)
open import Data.List.Base using (List; []; _∷_; filter)
import Data.List.Properties as List
open import Data.Maybe.Base using (Maybe; nothing; just; maybe′)
import Data.Maybe.Properties as Maybe
open import Data.Nat.Base
open import Data.Nat.Properties using (_≟_)
open import Data.Product.Base
import Data.Product.Properties as ΣP
open import Data.Sum.Base
import Data.Sum.Properties as ⊎P
open import Data.Unit.Base
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Conformance.Decidable
open import Midnight.ContractDSL.Ledger

open Primitives P

Phi : Set
Phi = ℕ × ℕ × ℕ × ℕ

_≟φ_ : DecidableEquality (Maybe Phi)
_≟φ_ = Maybe.≡-dec (ΣP.≡-dec _≟_ (ΣP.≡-dec _≟_ (ΣP.≡-dec _≟_ _≟_)))

record State : Set where
  constructor state
  field round authNonce deviceEpoch deviceCount : ℕ
        devices : List Bytes32
        balances : List (Bytes32 × ℕ)
        encKey : Bytes32
        recoveryPk : Point
        phi : Maybe Phi
        phiLen : ℕ
        session : Bytes32
        wrap : Bytes64
        pending : Bool
        pendingEntry : Bytes32
        pendingRecoveryPk : Point
        pendingNotBefore vetoWindow : ℕ
open State public

-- Uint<n> ledger cells: a cast past the bound aborts the call.
uint8 uint32 uint64 uint128 : ℕ
uint8 = 2 ^ 8
uint32 = 2 ^ 32
uint64 = 2 ^ 64
uint128 = 2 ^ 128

_∈ᵇ_ : Bytes32 → List Bytes32 → Bool
x ∈ᵇ xs = any (λ y → does (x ≟ᴮ y)) xs

insertSet : Bytes32 → List Bytes32 → List Bytes32
insertSet x xs = if x ∈ᵇ xs then xs else x ∷ xs

removeSet : Bytes32 → List Bytes32 → List Bytes32
removeSet x = filter (λ y → ¬? (x ≟ᴮ y))

lookup : Bytes32 → List (Bytes32 × ℕ) → Maybe ℕ
lookup c [] = nothing
lookup c ((d , a) ∷ m) = if does (c ≟ᴮ d) then just a else lookup c m

insertMap : Bytes32 → ℕ → List (Bytes32 × ℕ) → List (Bytes32 × ℕ)
insertMap c a [] = (c , a) ∷ []
insertMap c a ((d , b) ∷ m) = if does (c ≟ᴮ d) then (c , a) ∷ m else (d , b) ∷ insertMap c a m

_≈ᵇ_ : State → State → Bool
s ≈ᵇ t = (round s ≡ᵇ round t) ∧ (authNonce s ≡ᵇ authNonce t) ∧ (deviceEpoch s ≡ᵇ deviceEpoch t)
  ∧ (deviceCount s ≡ᵇ deviceCount t)
  ∧ all (_∈ᵇ devices t) (devices s) ∧ all (_∈ᵇ devices s) (devices t)
  ∧ all (λ (c , a) → within (balances t) c a) (balances s) ∧ all (λ (c , a) → within (balances s) c a) (balances t)
  ∧ does (encKey s ≟ᴮ encKey t) ∧ does (recoveryPk s ≟ᴾ recoveryPk t) ∧ does (phi s ≟φ phi t)
  ∧ (phiLen s ≡ᵇ phiLen t) ∧ does (session s ≟ᴮ session t) ∧ does (wrap s ≟ᵂ wrap t)
  ∧ does (pending s ≟ᵇ pending t) ∧ does (pendingEntry s ≟ᴮ pendingEntry t)
  ∧ does (pendingRecoveryPk s ≟ᴾ pendingRecoveryPk t) ∧ (pendingNotBefore s ≡ᵇ pendingNotBefore t)
  ∧ (vetoWindow s ≡ᵇ vetoWindow t)
  where within : List (Bytes32 × ℕ) → Bytes32 → ℕ → Bool
        within m c a = maybe′ (_≡ᵇ a) false (lookup c m)

------------------------------------------------------------------------
-- Operations

data Kind : Set where
  count flag unit point bytes : Kind

Res : Kind → Set
Res count = ℕ
Res flag = Bool
Res unit = ⊤
Res point = Point
Res bytes = Bytes32

data Op : Kind → Set where
  readNonce readRound readEpoch readDeviceCount readVetoWindow readNotBefore : Op count
  readBalance : Bytes32 → Op count
  readPending : Op flag
  deviceMember balanceMember : Bytes32 → Op flag
  readRecoveryPk readPendingRecoveryPk : Op point
  readSession readPendingEntry : Op bytes
  writeBalance : Bytes32 → ℕ → Op unit
  insertDevice removeDevice setEncKey : Bytes32 → Op unit
  resetDevices : Op unit
  writeNonce writeRound writeEpoch writeDeviceCount writeNotBefore writePhiLen : ℕ → Op unit
  writeRecoveryPk writePendingRecoveryPk : Point → Op unit
  writeSession writePendingEntry : Bytes32 → Op unit
  writePending : Bool → Op unit
  insertPhi1 insertPhi2 insertPhi3 insertPhi4 : ℕ → Op unit
  writeWrap : Bytes64 → Op unit

data Failure (k : Kind) : Set where
  overflow absent : Failure k

bounded : ℕ → ℕ → (ℕ → State) → Failure unit ⊎ (⊤ × State)
bounded bound n next = if n <ᵇ bound then inj₂ (tt , next n) else inj₁ overflow

read : {k : Kind} {A : Set} → A → State → Failure k ⊎ (A × State)
read x s = inj₂ (x , s)

write : State → Failure unit ⊎ (⊤ × State)
write s = inj₂ (tt , s)

prepare : {k : Kind} → Op k → State → Failure k ⊎ (Res k × State)
prepare readNonce s = read (authNonce s) s
prepare readRound s = read (round s) s
prepare readEpoch s = read (deviceEpoch s) s
prepare readDeviceCount s = read (deviceCount s) s
prepare readVetoWindow s = read (vetoWindow s) s
prepare readNotBefore s = read (pendingNotBefore s) s
prepare readPending s = read (pending s) s
prepare (deviceMember e) s = read (e ∈ᵇ devices s) s
prepare (balanceMember c) s = read (maybe′ (λ _ → true) false (lookup c (balances s))) s
prepare (readBalance c) s with lookup c (balances s)
... | nothing = inj₁ absent
... | just n = read n s
prepare readRecoveryPk s = read (recoveryPk s) s
prepare readPendingRecoveryPk s = read (pendingRecoveryPk s) s
prepare readSession s = read (session s) s
prepare readPendingEntry s = read (pendingEntry s) s
prepare (writeBalance c n) s = bounded uint128 n λ n → record s { balances = insertMap c n (balances s) }
prepare (insertDevice e) s = write (record s { devices = insertSet e (devices s) })
prepare (removeDevice e) s = write (record s { devices = removeSet e (devices s) })
prepare resetDevices s = write (record s { devices = [] })
prepare (setEncKey k) s = write (record s { encKey = k })
prepare (writeNonce n) s = bounded uint64 n λ n → record s { authNonce = n }
prepare (writeRound n) s = bounded uint64 n λ n → record s { round = n }
prepare (writeEpoch n) s = bounded uint32 n λ n → record s { deviceEpoch = n }
prepare (writeDeviceCount n) s = bounded uint8 n λ n → record s { deviceCount = n }
prepare (writeNotBefore n) s = bounded uint64 n λ n → record s { pendingNotBefore = n }
prepare (writePhiLen n) s = bounded uint8 n λ n → record s { phiLen = n }
prepare (writeRecoveryPk pk) s = write (record s { recoveryPk = pk })
prepare (writePendingRecoveryPk pk) s = write (record s { pendingRecoveryPk = pk })
prepare (writeSession n) s = write (record s { session = n })
prepare (writePendingEntry e) s = write (record s { pendingEntry = e })
prepare (writePending b) s = write (record s { pending = b })
prepare (insertPhi1 n) s =
  let (_ , b , c , d) = maybe′ (λ x → x) (0 , 0 , 0 , 0) (phi s)
  in write (record s { phi = just (n , b , c , d) })
prepare (insertPhi2 n) s =
  let (a , _ , c , d) = maybe′ (λ x → x) (0 , 0 , 0 , 0) (phi s)
  in write (record s { phi = just (a , n , c , d) })
prepare (insertPhi3 n) s =
  let (a , b , _ , d) = maybe′ (λ x → x) (0 , 0 , 0 , 0) (phi s)
  in write (record s { phi = just (a , b , n , d) })
prepare (insertPhi4 n) s =
  let (a , b , c , _) = maybe′ (λ x → x) (0 , 0 , 0 , 0) (phi s)
  in write (record s { phi = just (a , b , c , n) })
prepare (writeWrap w) s = write (record s { wrap = w })

-- The source inserts one entry; Recovery.install gives corrected set replacement.
data Finalisation : Set where
  sourceShaped corrected : Finalisation

decRes : (k : Kind) → DecidableEquality (Res k)
decRes count = _≟_
decRes flag = _≟ᵇ_
decRes unit tt tt = yes refl
decRes point = _≟ᴾ_
decRes bytes = _≟ᴮ_

resultEquality : (k : Kind) → DecEq (Res k)
resultEquality k = record { _≟_ = decRes k }

accountLedger : Semantics
accountLedger = record
  { State = State ; Kind = Kind ; Res = Res ; Op = Op ; Failure = Failure
  ; prepare = prepare ; DecEq-Res = λ {k} → resultEquality k }

------------------------------------------------------------------------
-- Decidable equality of operations (journal comparison)

_≟ᴷ_ : DecidableEquality Kind
_≟ᴷ_ = via tag untag (λ { count → refl ; flag → refl ; unit → refl ; point → refl ; bytes → refl }) _≟_
  where
  tag : Kind → ℕ
  tag count = 0
  tag flag = 1
  tag unit = 2
  tag point = 3
  tag bytes = 4
  untag : ℕ → Maybe Kind
  untag 0 = just count
  untag 1 = just flag
  untag 2 = just unit
  untag 3 = just point
  untag 4 = just bytes
  untag _ = nothing

-- Each operation is encoded as a tag, unique within its kind, and its arguments.
private
  Atom : Set
  Atom = ℕ ⊎ Bytes32 ⊎ Point ⊎ Bytes64

  pattern n# x = inj₁ x
  pattern b# x = inj₂ (inj₁ x)
  pattern p# x = inj₂ (inj₂ (inj₁ x))
  pattern w# x = inj₂ (inj₂ (inj₂ x))

  Code : Set
  Code = ℕ × List Atom

  encode : {k : Kind} → Op k → Code
  encode readNonce = 0 , []
  encode readEpoch = 1 , []
  encode readDeviceCount = 2 , []
  encode readVetoWindow = 3 , []
  encode readNotBefore = 4 , []
  encode readRound = 5 , []
  encode (readBalance c) = 6 , b# c ∷ []
  encode readPending = 0 , []
  encode (deviceMember e) = 1 , b# e ∷ []
  encode (balanceMember c) = 2 , b# c ∷ []
  encode readRecoveryPk = 0 , []
  encode readPendingRecoveryPk = 1 , []
  encode readSession = 0 , []
  encode readPendingEntry = 1 , []
  encode (writeBalance c n) = 0 , b# c ∷ n# n ∷ []
  encode (insertDevice e) = 1 , b# e ∷ []
  encode (removeDevice e) = 2 , b# e ∷ []
  encode resetDevices = 3 , []
  encode (setEncKey e) = 4 , b# e ∷ []
  encode (writeNonce n) = 5 , n# n ∷ []
  encode (writeRound n) = 6 , n# n ∷ []
  encode (writeEpoch n) = 7 , n# n ∷ []
  encode (writeDeviceCount n) = 8 , n# n ∷ []
  encode (writeNotBefore n) = 9 , n# n ∷ []
  encode (writePhiLen n) = 10 , n# n ∷ []
  encode (writeRecoveryPk pk) = 11 , p# pk ∷ []
  encode (writePendingRecoveryPk pk) = 12 , p# pk ∷ []
  encode (writeSession n) = 13 , b# n ∷ []
  encode (writePendingEntry e) = 14 , b# e ∷ []
  encode (writePending false) = 15 , []
  encode (writePending true) = 16 , []
  encode (insertPhi1 n) = 17 , n# n ∷ []
  encode (insertPhi2 n) = 18 , n# n ∷ []
  encode (insertPhi3 n) = 19 , n# n ∷ []
  encode (insertPhi4 n) = 20 , n# n ∷ []
  encode (writeWrap w) = 21 , w# w ∷ []

  decode : (k : Kind) → Code → Maybe (Op k)
  decode count (0 , []) = just readNonce
  decode count (1 , []) = just readEpoch
  decode count (2 , []) = just readDeviceCount
  decode count (3 , []) = just readVetoWindow
  decode count (4 , []) = just readNotBefore
  decode count (5 , []) = just readRound
  decode count (6 , b# c ∷ []) = just (readBalance c)
  decode flag (0 , []) = just readPending
  decode flag (1 , b# e ∷ []) = just (deviceMember e)
  decode flag (2 , b# c ∷ []) = just (balanceMember c)
  decode point (0 , []) = just readRecoveryPk
  decode point (1 , []) = just readPendingRecoveryPk
  decode bytes (0 , []) = just readSession
  decode bytes (1 , []) = just readPendingEntry
  decode unit (0 , b# c ∷ n# n ∷ []) = just (writeBalance c n)
  decode unit (1 , b# e ∷ []) = just (insertDevice e)
  decode unit (2 , b# e ∷ []) = just (removeDevice e)
  decode unit (3 , []) = just resetDevices
  decode unit (4 , b# e ∷ []) = just (setEncKey e)
  decode unit (5 , n# n ∷ []) = just (writeNonce n)
  decode unit (6 , n# n ∷ []) = just (writeRound n)
  decode unit (7 , n# n ∷ []) = just (writeEpoch n)
  decode unit (8 , n# n ∷ []) = just (writeDeviceCount n)
  decode unit (9 , n# n ∷ []) = just (writeNotBefore n)
  decode unit (10 , n# n ∷ []) = just (writePhiLen n)
  decode unit (11 , p# pk ∷ []) = just (writeRecoveryPk pk)
  decode unit (12 , p# pk ∷ []) = just (writePendingRecoveryPk pk)
  decode unit (13 , b# n ∷ []) = just (writeSession n)
  decode unit (14 , b# e ∷ []) = just (writePendingEntry e)
  decode unit (15 , []) = just (writePending false)
  decode unit (16 , []) = just (writePending true)
  decode unit (17 , n# n ∷ []) = just (insertPhi1 n)
  decode unit (18 , n# n ∷ []) = just (insertPhi2 n)
  decode unit (19 , n# n ∷ []) = just (insertPhi3 n)
  decode unit (20 , n# n ∷ []) = just (insertPhi4 n)
  -- Agda rejects numeric literal patterns above 20; suc 20 is tag 21.
  decode unit (suc 20 , w# w ∷ []) = just (writeWrap w)
  decode _ _ = nothing

  decode-encode : {k : Kind} (o : Op k) → decode k (encode o) ≡ just o
  decode-encode readNonce = refl
  decode-encode readEpoch = refl
  decode-encode readDeviceCount = refl
  decode-encode readVetoWindow = refl
  decode-encode readNotBefore = refl
  decode-encode readRound = refl
  decode-encode (readBalance _) = refl
  decode-encode readPending = refl
  decode-encode (deviceMember _) = refl
  decode-encode (balanceMember _) = refl
  decode-encode readRecoveryPk = refl
  decode-encode readPendingRecoveryPk = refl
  decode-encode readSession = refl
  decode-encode readPendingEntry = refl
  decode-encode (writeBalance _ _) = refl
  decode-encode (insertDevice _) = refl
  decode-encode (removeDevice _) = refl
  decode-encode resetDevices = refl
  decode-encode (setEncKey _) = refl
  decode-encode (writeNonce _) = refl
  decode-encode (writeRound _) = refl
  decode-encode (writeEpoch _) = refl
  decode-encode (writeDeviceCount _) = refl
  decode-encode (writeNotBefore _) = refl
  decode-encode (writePhiLen _) = refl
  decode-encode (writeRecoveryPk _) = refl
  decode-encode (writePendingRecoveryPk _) = refl
  decode-encode (writeSession _) = refl
  decode-encode (writePendingEntry _) = refl
  decode-encode (writePending false) = refl
  decode-encode (writePending true) = refl
  decode-encode (insertPhi1 _) = refl
  decode-encode (insertPhi2 _) = refl
  decode-encode (insertPhi3 _) = refl
  decode-encode (insertPhi4 _) = refl
  decode-encode (writeWrap _) = refl

decOp : {k : Kind} → DecidableEquality (Op k)
decOp {k} = via encode (decode k) decode-encode
  (ΣP.≡-dec _≟_ (List.≡-dec (⊎P.≡-dec _≟_ (⊎P.≡-dec _≟ᴮ_ (⊎P.≡-dec _≟ᴾ_ _≟ᵂ_)))))

-- An operation together with its result, the payload of a journal `operated` event.
decOperated : DecidableEquality (Σ Kind λ k → Op k × Res k)
decOperated = ΣP.≡-dec _≟ᴷ_ λ {k} → ΣP.≡-dec decOp (decRes k)

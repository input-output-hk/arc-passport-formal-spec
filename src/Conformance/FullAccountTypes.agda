{-# OPTIONS --safe --without-K #-}

-- Native curve arithmetic, SHA-256/Compact atom encoding, and transaction coin
-- commitments are interpretation parameters. Circuit control flow, assertions,
-- bounded casts, ledger mutations, and effect ordering are executable below.
module Conformance.FullAccountTypes where

open import Data.Bool.Base
open import Data.Char.Base using (toℕ)
open import Data.List.Base using (List; []; _∷_; _++_; map; filterᵇ; length; take; drop; replicate)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base hiding (equal)
open import Data.Nat.Properties using (_≟_)
open import Data.Product.Base hiding (map)
open import Data.String.Base using (String; toList) renaming (_++_ to _++ˢ_)
open import Data.String.Properties using () renaming (_≟_ to _≟ˢ_)
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (does)

Bytes : Set
Bytes = List ℕ

data Value : Set where
  nat : ℕ → Value
  bool : Bool → Value
  bytes : Bytes → Value
  tuple : List Value → Value
  none : Value
  some : Value → Value

mutual
  equal : Value → Value → Bool
  equal (nat x) (nat y) = x ≡ᵇ y
  equal (bool false) (bool false) = true
  equal (bool true) (bool true) = true
  equal (bytes x) (bytes y) = equalNats x y
  equal (tuple x) (tuple y) = equalValues x y
  equal none none = true
  equal (some x) (some y) = equal x y
  equal _ _ = false

  equalValues : List Value → List Value → Bool
  equalValues [] [] = true
  equalValues (x ∷ xs) (y ∷ ys) = equal x y ∧ equalValues xs ys
  equalValues _ _ = false

  equalNats : Bytes → Bytes → Bool
  equalNats [] [] = true
  equalNats (x ∷ xs) (y ∷ ys) = (x ≡ᵇ y) ∧ equalNats xs ys
  equalNats _ _ = false

stringEqual : String → String → Bool
stringEqual x y = does (x ≟ˢ y)

ascii : String → Bytes
ascii s = map toℕ (toList s)

pad : ℕ → String → Value
pad n s = bytes (take n (ascii s ++ replicate n 0))

zero32 : Value
zero32 = pad 32 ""

zero64 : Value
zero64 = pad 64 ""

identity : Value
identity = tuple (nat 0 ∷ nat 1 ∷ [])

unit : Value
unit = tuple []

fieldOrder jubjubOrder : ℕ
fieldOrder = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
jubjubOrder = 0x0e7db4ea6533afa906673b0101343b00a6682093ccc81082d0970e5ed6f72cb7

get : ℕ → List Value → Value
get zero (x ∷ xs) = x
get (suc n) (x ∷ xs) = get n xs
get _ [] = none

fields : Value → List Value
fields (tuple xs) = xs
fields _ = []

at : ℕ → Value → Value
at n x = get n (fields x)

number : Value → ℕ
number (nat n) = n
number _ = 0

flag : Value → Bool
flag (bool b) = b
flag _ = false

rawBytes : Value → Bytes
rawBytes (bytes bs) = bs
rawBytes _ = []

le : Bytes → ℕ
le [] = 0
le (x ∷ xs) = x + 256 * le xs

member : Value → List Value → Bool
member x [] = false
member x (y ∷ ys) = equal x y ∨ member x ys

insertSet : Value → List Value → List Value
insertSet x xs = if member x xs then xs else xs ++ (x ∷ [])

removeSet : Value → List Value → List Value
removeSet x = filterᵇ (λ y → not (equal x y))

lookupMap : Value → List Value → Maybe Value
lookupMap k [] = nothing
lookupMap k (tuple (x ∷ v ∷ []) ∷ xs) = if equal k x then just v else lookupMap k xs
lookupMap k (_ ∷ xs) = lookupMap k xs

insertMap : Value → Value → List Value → List Value
insertMap k v [] = tuple (k ∷ v ∷ []) ∷ []
insertMap k v (tuple (x ∷ y ∷ []) ∷ xs) =
  if equal k x then tuple (k ∷ v ∷ []) ∷ xs else tuple (x ∷ y ∷ []) ∷ insertMap k v xs
insertMap k v (x ∷ xs) = x ∷ insertMap k v xs

record State : Set where
  constructor state
  field ledger : List (String × Value)
open State public

lookupCell : String → List (String × Value) → Maybe Value
lookupCell k [] = nothing
lookupCell k ((x , v) ∷ xs) = if stringEqual k x then just v else lookupCell k xs

insertCell : String → Value → List (String × Value) → List (String × Value)
insertCell k v [] = (k , v) ∷ []
insertCell k v ((x , w) ∷ xs) = if stringEqual k x then (k , v) ∷ xs else (x , w) ∷ insertCell k v xs

cell : String → State → Value
cell k s with lookupCell k (ledger s)
... | nothing = none
... | just v = v

StateRelation : State → State → Set
StateRelation s t = ∀ k → cell k s ≡ cell k t

record Context : Set where
  constructor context
  field self : Value
        blockTime : ℕ
        -- none, some [true, ContractAddress], or some [false, UserAddress].
        caller : Value
        heldCoin : Value
open Context public

record RawCall : Set where
  constructor rawCall
  field name : String
        arguments : List Value
open RawCall public

data Error : Set where
  assertion : String → Error
  bounds : String → ℕ → Error
  decoding : String → Error
  primitiveFailure : String → Error

data Result (A : Set) : Set where
  failure : Error → Result A
  success : A → Result A

data Curve : Set where
  jubjub k256 p256 : Curve

-- Atom names are Compact ABI types, preserving widths and point/address layout.
Atom : Set
Atom = String × Value

record Primitives : Set where
  field persistentHash : List Atom → Result Value
        transientHash : List ℕ → Result ℕ
        degradeToTransient : Value → Result ℕ
        upgradeFromTransient : ℕ → Result Value
        pointCoordinates : Curve → Value → Result (Value × Value)
        ecMulGenerator : Curve → ℕ → Result Value
        ecMul : Curve → Value → ℕ → Result Value
        ecAdd : Curve → Value → Value → Result Value
        ecdsaVerify : Curve → Value → Value → Value → Result Bool
        -- The native coin commitment/nullifier functions, not sendShielded.
        coinCommitment : Value → Value → Result Value
        coinNullifier : Value → Value → Result Value
open Primitives public

data Effect : Set where
  readCell : String → Value → Effect
  writeCell : String → Value → Effect
  mapMember : String → Value → Bool → Effect
  mapLookup : String → Value → Value → Effect
  mapInsert : String → Value → Value → Effect
  setMember : String → Value → Bool → Effect
  setInsert setRemove : String → Value → Effect
  reset : String → Effect
  contextRead : String → Value → Effect
  witness : String → Value → Value → Effect
  receiveUnshielded : Value → ℕ → Effect
  sendUnshielded : Value → ℕ → Value → Effect
  receiveShielded : Value → Effect
  consumeShielded : Value → Value → Effect
  createShielded : Value → Value → Value → Effect

data Execution (A : Set) : Set where
  rejected : Error → Execution A
  accepted : A → State → List Effect → Execution A

M : Set → Set
M A = State → Execution A

private variable A B : Set

return : A → M A
return x s = accepted x s []

infixl 1 _>>=_ _>>_
_>>=_ : M A → (A → M B) → M B
(m >>= f) s with m s
... | rejected e = rejected e
... | accepted x t es with f x t
...   | rejected e = rejected e
...   | accepted y u fs = accepted y u (es ++ fs)

_>>_ : M A → M B → M B
m >> n = m >>= λ _ → n

abort : Error → M A
abort e s = rejected e

lift : Result A → M A
lift (failure e) = abort e
lift (success x) = return x

assert : Bool → String → M ⊤
assert b message = if b then return tt else abort (assertion message)

emit : Effect → M ⊤
emit e s = accepted tt s (e ∷ [])

read : String → M Value
read k s with lookupCell k (ledger s)
... | nothing = rejected (decoding ("missing ledger field: " ++ˢ k))
... | just v = accepted v s (readCell k v ∷ [])

write : String → Value → M ⊤
write k v s = accepted tt (state (insertCell k v (ledger s))) (writeCell k v ∷ [])

cast : String → ℕ → ℕ → M ℕ
cast label bits n = if n <ᵇ (2 ^ bits) then return n else abort (bounds label bits)

writeCount : String → ℕ → ℕ → M ⊤
writeCount label bits n = cast label bits n >>= λ v → write label (nat v)

readCount : String → M ℕ
readCount label = read label >>= λ v → return (number v)

bump : String → ℕ → M ⊤
bump label bits = readCount label >>= λ n → writeCount label bits (suc n)

memberMap : String → Value → M Bool
memberMap label k s =
  let b = present (lookupMap k (fields (cell label s)))
  in accepted b s (mapMember label k b ∷ [])
  where
  present : Maybe Value → Bool
  present nothing = false
  present (just _) = true

lookup : String → Value → M Value
lookup label k s with lookupMap k (fields (cell label s))
... | nothing = rejected (decoding ("absent map key: " ++ˢ label))
... | just v = accepted v s (mapLookup label k v ∷ [])

insert : String → Value → Value → M ⊤
insert label k v s = accepted tt
  (state (insertCell label (tuple (insertMap k v (fields (cell label s)))) (ledger s)))
  (mapInsert label k v ∷ [])

has : String → Value → M Bool
has label k s =
  let b = member k (fields (cell label s))
  in accepted b s (setMember label k b ∷ [])

include exclude : String → Value → M ⊤
include label k s = accepted tt
  (state (insertCell label (tuple (insertSet k (fields (cell label s)))) (ledger s))) (setInsert label k ∷ [])
exclude label k s = accepted tt
  (state (insertCell label (tuple (removeSet k (fields (cell label s)))) (ledger s))) (setRemove label k ∷ [])

clear : String → M ⊤
clear label s = accepted tt (state (insertCell label (tuple []) (ledger s))) (reset label ∷ [])

-- Context comparisons are immediate source-execution observations. The effect
-- records the comparison's bound, while its result uses this Context's time;
-- these are not deferred conditions in the recovery DSL admission relation.
readTimeLess : Context → ℕ → M Bool
readTimeLess ctx n = emit (contextRead "blockTimeLessThan" (nat n)) >> return (blockTime ctx <ᵇ n)

readTimeGreater : Context → ℕ → M Bool
readTimeGreater ctx n = emit (contextRead "blockTimeGreaterThan" (nat n)) >> return (n <ᵇ blockTime ctx)

readSelf : Context → M Value
readSelf ctx = emit (contextRead "self" (self ctx)) >> return (self ctx)

readCaller : Context → M Value
readCaller ctx = emit (contextRead "caller" (caller ctx)) >> return (caller ctx)

held : Context → Value → M Value
held ctx color = emit (witness "held_coin" color (heldCoin ctx)) >> return (heldCoin ctx)

-- Constructor parameters are boot commitment, encryption key, recovery key,
-- recovery wrap and veto-window seconds, in the Compact constructor's order.
-- Stale recovery slots remain represented after their live length is cleared.
initialState : Value → Value → Value → Value → ℕ → State
initialState boot encryption recovery wrap window = state
  (("round" , nat 0) ∷ ("enc_key" , encryption) ∷ ("inbox" , tuple []) ∷
   ("inbox_count" , nat 0) ∷ ("unshielded_balances" , tuple []) ∷
   ("spec_version" , nat 3) ∷ ("devices" , tuple []) ∷
   ("device_epoch" , nat 0) ∷ ("device_count" , nat 0) ∷ ("auth_nonce" , nat 0) ∷
   ("boot" , boot) ∷ ("booted" , bool false) ∷ ("grants" , tuple []) ∷
   ("grant_generation" , nat 0) ∷ ("recovery_pk" , recovery) ∷
   ("recovery_phi" , tuple []) ∷ ("recovery_phi_len" , nat 0) ∷
   ("recovery_session" , zero32) ∷ ("recovery_wrap" , wrap) ∷
   ("recovery_version" , nat 1) ∷ ("pending_recovery" , bool false) ∷
   ("pending_entry" , zero32) ∷ ("pending_recovery_pk" , identity) ∷
   ("pending_not_before" , nat 0) ∷ ("veto_window" , nat window) ∷ [])

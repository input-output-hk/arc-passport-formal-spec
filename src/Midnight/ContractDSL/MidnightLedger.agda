{-# OPTIONS --safe --without-K #-}

module Midnight.ContractDSL.MidnightLedger where

open import Data.Bool.Base hiding (_≤_; _<_)
open import Data.Bool.Properties using () renaming (_≟_ to boolEq)
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Nat.Properties using (_≟_; _≤?_)
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Midnight.ContractDSL.Ledger
open import Midnight.ContractDSL.SymbolicDigest

data Kind : Set where
  boolean natural digest trivial : Kind

El : Kind → Set
El boolean = Bool
El natural = ℕ
El digest = Digest
El trivial = ⊤

data Assertion : Set where
  uninitialised unauthorised assertionFailed : Assertion

data Failure : Set where
  counterFailure : Failure

data FieldRef : Kind → Set where
  lockState : FieldRef boolean
  lockAuthority : FieldRef digest
  lockValue : FieldRef natural

record State : Set where
  constructor state
  field locked : Bool
        authority : Digest
        value round : ℕ
        root : Digest
        falseFlag trueFlag : Bool
open State public

getField : {k : Kind} → FieldRef k → State → El k
getField lockState = locked
getField lockAuthority = authority
getField lockValue = value

putField : {k : Kind} → FieldRef k → El k → State → State
putField lockState b s = record s { locked = b }
putField lockAuthority a s = record s { authority = a }
putField lockValue v s = record s { value = v }

fieldEq : {k : Kind} → (f : FieldRef k) → (x y : El k) → Dec (x ≡ y)
fieldEq lockState = boolEq
fieldEq lockAuthority = digestEq
fieldEq lockValue = _≟_

maxCounter : ℕ
maxCounter = 18446744073709551615

-- The source counter has Uint64 storage and Uint16 delta arguments.
addCounter : ℕ → ℕ → Maybe ℕ
addCounter n d with d ≤? 65535 | (n + d) ≤? maxCounter
... | yes _ | yes _ = just (n + d)
... | no _ | _ = nothing
... | _ | no _ = nothing

addCounter-spec : (n d : ℕ) {v : ℕ} → addCounter n d ≡ just v →
  v ≡ n + d × d ≤ 65535 × v ≤ maxCounter
addCounter-spec n d eq with d ≤? 65535 | (n + d) ≤? maxCounter
... | yes delta | yes bound with eq
...   | refl = refl , delta , bound
addCounter-spec n d eq | no _ | _ with eq
...   | ()
addCounter-spec n d eq | yes _ | no _ with eq
...   | ()

data CounterId : Set where
  lockRound : CounterId

data Op : Kind → Set where
  readField : {k : Kind} → FieldRef k → Op k
  writeField : {k : Kind} → FieldRef k → El k → Op trivial
  readRound : CounterId → Op natural
  incrementCounter : CounterId → ℕ → Op trivial
  counterLessThan : CounterId → ℕ → Op boolean
  checkRoot : Digest → Op boolean
  updateRoot : Digest → Op trivial
  flagMember : Bool → Op boolean
  updateFlags : Bool → Bool → Op trivial

resultEq : {k : Kind} → Op k → (x y : El k) → Dec (x ≡ y)
resultEq (readField f) = fieldEq f
resultEq (writeField f v) tt tt = yes refl
resultEq (readRound c) = _≟_
resultEq (incrementCounter c d) tt tt = yes refl
resultEq (counterLessThan c b) = boolEq
resultEq (checkRoot _) = boolEq
resultEq (updateRoot _) tt tt = yes refl
resultEq (flagMember _) = boolEq
resultEq (updateFlags _ _) tt tt = yes refl

prepare : {k : Kind} → Op k → State → Failure ⊎ (El k × State)
prepare (readField f) s = inj₂ (getField f s , s)
prepare (writeField f v) s = inj₂ (tt , putField f v s)
prepare (readRound lockRound) s = inj₂ (round s , s)
prepare (incrementCounter lockRound d) s with addCounter (round s) d
... | nothing = inj₁ counterFailure
... | just n = inj₂ (tt , record s { round = n })
prepare (counterLessThan lockRound b) s = inj₂ ((round s <ᵇ b) , s)
prepare (checkRoot r) s = inj₂ (⌊ digestEq r (root s) ⌋ , s)
prepare (updateRoot r) s = inj₂ (tt , record s { root = r })
prepare (flagMember false) s = inj₂ (falseFlag s , s)
prepare (flagMember true) s = inj₂ (trueFlag s , s)
prepare (updateFlags f t) s = inj₂ (tt , record s { falseFlag = f ; trueFlag = t })

midnight : Semantics
midnight = record
  { State = State ; Kind = Kind ; El = El ; Op = Op ; Failure = Failure
  ; prepare = prepare ; resultEq = resultEq }

put-get : {k : Kind} (f : FieldRef k) (x : El k) (s : State) →
  getField f (putField f x s) ≡ x
put-get lockState x s = refl
put-get lockAuthority x s = refl
put-get lockValue x s = refl

clear-frame : (s : State) (n : ℕ) →
  authority (record (putField lockState false s) { round = n }) ≡ authority s ×
  value (record (putField lockState false s) { round = n }) ≡ value s
clear-frame s n = refl , refl

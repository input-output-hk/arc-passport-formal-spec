{-# OPTIONS --safe --without-K #-}

module Midnight.ContractDSL.MerkleState where

open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base
open import Data.Maybe.Base hiding (_>>=_)
open import Data.Nat.Base
open import Data.Nat.Properties using (_≟_)
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import CategoricalCrypto.Iface
import CategoricalCrypto.Protocol as Upstream
open import CategoricalCrypto.Strategy using (Strat; ask; out)
open import Midnight.ContractDSL.FixtureLedger
open import Midnight.ContractDSL.MidnightLedger
open import Midnight.ContractDSL.Merkle
open import Midnight.ContractDSL.MerkleFixture as Fixture hiding (initial)
open import Midnight.ContractDSL.Program midnight Assertion
open import Midnight.ContractDSL.Protocol midnight Assertion
open import Midnight.ContractDSL.SymbolicDigest

-- Any matching mutable root suffices; this is not restricted to the fixture.
matching-success : (item : FieldValue) (p : Path) (s : State) →
  leaf p ≡ item → pathRoot p ≡ root s →
  eval (checkSecure item p) s ≡ inj₂ (finished tt s (operated (checkRoot (pathRoot p)) true ∷ []))
matching-success item p s leaf-ok root-ok with leaf p ≟ item
... | no neq = ⊥-elim (neq leaf-ok)
... | yes _ with digestEq (pathRoot p) (root s)
...   | no neq = ⊥-elim (neq root-ok)
...   | yes _ = refl

data Entry : Set where
  membership replaceRoot replaceFlags : Entry

Input : Entry → Set
Input membership = FieldValue
Input replaceRoot = Digest
Input replaceFlags = Bool × Bool

Witness : (n : Entry) → Input n → Set
Witness membership _ = Path
Witness replaceRoot _ = ⊤
Witness replaceFlags _ = ⊤

-- Root/flag maintenance is deliberately unrestricted in this regression
-- contract; it makes no source-level access-control correspondence claim.
merkleContract : Contract
merkleContract = record
  { Name = Entry ; Input = Input ; PublicArgs = Input ; Result = λ _ → ⊤
  ; Witness = Witness ; publicArgs = λ _ x → x
  ; body = λ _ → λ
      { membership item p → checkSecure item p
      ; replaceRoot r _ → perform (ledger (updateRoot r))
      ; replaceFlags (f , t) _ → perform (ledger (updateFlags f t)) } }

module M = Interpreter merkleContract (ExactCommunication.scheme merkleContract) 31
open M

ctx : Context
ctx = context 31 0

initial : State
initial = Fixture.initial

changed : State
changed = record initial { root = merkleLeaf 9 }

oldJournal : Journal
oldJournal = operated (checkRoot fixtureRoot) true ∷ []

old-success : eval (checkSecure 1 (findItem a)) initial ≡ inj₂ (finished tt initial oldJournal)
old-success = refl

oldTx : Tx
oldTx = makeTx membership 1 (findItem a) 0 initial tt initial oldJournal old-success

updateRootJournal : Journal
updateRootJournal = operated (updateRoot (merkleLeaf 9)) tt ∷ []

root-success : eval (perform (ledger (updateRoot (merkleLeaf 9)))) initial ≡
  inj₂ (finished tt changed updateRootJournal)
root-success = refl

rootTx : Tx
rootTx = makeTx replaceRoot (merkleLeaf 9) tt 1 initial tt changed updateRootJournal root-success

freshPath : Path
freshPath = path 9 []

freshJournal : Journal
freshJournal = operated (checkRoot (merkleLeaf 9)) true ∷ []

fresh-success : eval (checkSecure 9 freshPath) changed ≡ inj₂ (finished tt changed freshJournal)
fresh-success = matching-success 9 freshPath changed refl refl

freshTx : Tx
freshTx = makeTx membership 9 freshPath 2 changed tt changed freshJournal fresh-success

matching-admitted : admission ctx initial oldTx ≡ (initial , accepted)
matching-admitted = refl

root-updated : admission ctx initial rootTx ≡ (changed , accepted)
root-updated = refl

-- Old certificates remain valid about their preparation view. Admission
-- rejects their recorded true observation against the current changed root.
old-proof-valid : verified oldTx ≡ true
old-proof-valid = refl

old-evaluation-rejected : eval (checkSecure 1 (findItem a)) changed ≡
  inj₁ (assertionError assertionFailed)
old-evaluation-rejected = refl

old-replay-rejected : replay ctx oldJournal changed ≡ nothing
old-replay-rejected = refl

old-admission-rejected : admission ctx changed oldTx ≡ (changed , rejected)
old-admission-rejected = refl

fresh-admitted : admission ctx changed freshTx ≡ (changed , accepted)
fresh-admitted = refl

noFalseFlag : State
noFalseFlag = record initial { falseFlag = false }

flags-updated : eval (perform (ledger (updateFlags false true))) initial ≡
  inj₂ (finished tt noFalseFlag (operated (updateFlags false true) tt ∷ []))
flags-updated = refl

removed-flag-rejected : eval (program insecure a false) noFalseFlag ≡
  inj₁ (assertionError assertionFailed)
removed-flag-rejected = refl

removed-flag-replay-rejected : replay ctx (programJournal insecure a false) noFalseFlag ≡ nothing
removed-flag-replay-rejected = refl

assembled : Upstream.Protocol unitᴵ ClientIf
assembled = system ctx initial

rootChangeStrategy : Strat ClientQuery ClientAnswer
rootChangeStrategy = ask (build membership 1 (findItem a) 0) λ
  { (built membership tt _ _) → ask (submitOther oldTx) λ
      { (submitted accepted) → ask (submitOther rootTx) λ
          { (submitted accepted) → ask submit λ
              { (submitted rejected) → ask (build membership 9 freshPath 2) λ
                  { (built membership tt _ _) → ask submit λ
                      { (submitted accepted) → out true ; _ → out false }
                  ; _ → out false }
              ; _ → out false }
          ; _ → out false }
      ; _ → out false }
  ; _ → out false }

{-# OPTIONS --safe --without-K #-}

-- Manual source reference: language 0.16 lock clear/set in
-- https://docs.midnight.network/compact/reference/writing.md
-- Hashes and communication are explicit mathematical ideals; no compiler,
-- witness privacy, hash preimage, or source-byte-encoding theorem is asserted.
module Midnight.ContractDSL.Lock where

open import Data.Bool.Base hiding (_≤_; _<_)
open import Data.Empty
open import Data.List.Base
open import Data.Maybe.Base hiding (_>>=_)
open import Data.Nat.Base
open import Data.Nat.Properties using (_≤?_)
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable using (does; toWitness)

import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol using (St; init; ret)
import CategoricalCrypto.Protocol as Upstream
open import CategoricalCrypto.Strategy using (Strat; ask; out)
open import Midnight.ContractDSL.FixtureLedger
open import Midnight.ContractDSL.Ledger
open import Midnight.ContractDSL.MidnightLedger
open import Midnight.ContractDSL.Program midnight Assertion
open import Midnight.ContractDSL.Protocol midnight Assertion
open import Midnight.ContractDSL.SymbolicDigest
open Execution midnight

read : {k : Kind} → FieldRef k → Program (El k)
read f = perform (ledger (readField f))

write : {k : Kind} → FieldRef k → El k → Program ⊤
write f v = perform (ledger (writeField f v))

increment : ℕ → Program ⊤
increment d = perform (ledger (incrementCounter lockRound d))

clear : ℕ → Program ⊤
clear sk = do
  st ← read lockState
  assert st uninitialised
  r ← perform (ledger (readRound lockRound))
  a ← read lockAuthority
  assert (does (digestEq a (publicKey r sk))) unauthorised
  write lockState false
  increment 1

setLock : ℕ → ℕ → Program ⊤
setLock v sk = do
  st ← read lockState
  assert (not st) assertionFailed
  r ← perform (ledger (readRound lockRound))
  write lockAuthority (publicKey r sk)
  write lockValue v
  write lockState true

cleared : State → ℕ → State
cleared s n = record s { locked = false ; round = n }

ClearPost : State → State → ℕ → Set
ClearPost s t sk = locked s ≡ true × authority s ≡ publicKey (round s) sk ×
  Σ ℕ (λ n → addCounter (round s) 1 ≡ just n × t ≡ cleared s n)

clear-safety : (sk : ℕ) (s : State) {t : State} {j : Journal} →
  eval (clear sk) s ≡ inj₂ (finished tt t j) → ClearPost s t sk
clear-safety sk s eq with locked s
... | false with eq
...   | ()
clear-safety sk s eq | true with digestEq (authority s) (publicKey (round s) sk)
...   | no _ with eq
...     | ()
clear-safety sk s eq | true | yes auth with addCounter (round s) 1
...     | nothing with eq
...       | ()
clear-safety sk s eq | true | yes auth | just n with eq
...       | refl = refl , auth , n , refl , refl

clear-wrong-key : (sk : ℕ) (s : State) → locked s ≡ true →
  authority s ≢ publicKey (round s) sk → eval (clear sk) s ≡ inj₁ (assertionError unauthorised)
clear-wrong-key sk s flag wrong rewrite flag with digestEq (authority s) (publicKey (round s) sk)
... | no _ = refl
... | yes auth = ⊥-elim (wrong auth)

clear-round : {sk : ℕ} {s t : State} → ClearPost s t sk → round t ≡ round s + 1
clear-round {s = s} (_ , _ , n , added , refl) = proj₁ (addCounter-spec (round s) 1 added)

clear-frames : {sk : ℕ} {s t : State} → ClearPost s t sk →
  authority t ≡ authority s × value t ≡ value s × locked t ≡ false
clear-frames (_ , _ , n , added , refl) = refl , refl , refl

set-round : (v sk : ℕ) (s : State) {t : State} {j : Journal} →
  eval (setLock v sk) s ≡ inj₂ (finished tt t j) → round t ≡ round s
set-round v sk s eq with locked s
... | true with eq
...   | ()
set-round v sk s eq | false with eq
...   | refl = refl

data Entry : Set where
  clearEntry setEntry : Entry

Input : Entry → Set
Input clearEntry = ⊤
Input setEntry = Σ ℕ (λ v → v ≤ maxCounter)

lockContract : Contract
lockContract = record
  { Name = Entry ; Input = Input ; PublicArgs = λ _ → ⊤ ; Result = λ _ → ⊤
  ; Witness = λ _ _ → ℕ ; publicArgs = λ _ _ → tt
  ; body = λ self → λ { clearEntry tt sk → clear sk
                      ; setEntry (v , bound) sk → setLock v sk } }

module Lock = Interpreter lockContract (ExactCommunication.scheme lockContract) 7
open Lock

RoundBound : State → Set
RoundBound s = round s ≤ maxCounter

lock-preserves : Preserves RoundBound
lock-preserves acc clearEntry tt sk s tt t j pre eq
  with clear-safety sk s eq
... | _ , _ , n , added , refl = proj₂ (proj₂ (addCounter-spec (round s) 1 added))
lock-preserves acc setEntry (v , bound) sk s tt t j pre eq =
  subst (λ n → n ≤ maxCounter) (sym (set-round v sk s eq)) pre

accepted-clear : (ctx : Context) (s : State) (tx : Tx) {t : State} →
  Statement.name (Tx.claim tx) ≡ clearEntry → admission ctx s tx ≡ (t , accepted) →
  Σ ℕ (ClearPost s t)
accepted-clear ctx s (transaction (statement acc clearEntry pa binding j) proof) refl admitted
  with accepted-refinement ctx s (transaction (statement acc clearEntry pa binding j) proof) admitted
... | evidence view tt sk tt opening , rel , ev = sk , clear-safety sk s ev
accepted-clear ctx s (transaction (statement acc setEntry pa binding j) proof) () admitted

ctx : Context
ctx = context 7 0

initial : State
initial = fixtureState true (publicKey 0 42) 99 0

afterClear : State
afterClear = fixtureState false (publicKey 0 42) 99 1

afterSet : State
afterSet = fixtureState true (publicKey 1 42) 100 1

clearJournal : Journal
clearJournal = operated (readField lockState) true ∷
  operated (readRound lockRound) 0 ∷
  operated (readField lockAuthority) (publicKey 0 42) ∷
  operated (writeField lockState false) tt ∷
  operated (incrementCounter lockRound 1) tt ∷ []

valid-eval : eval (clear 42) initial ≡ inj₂ (finished tt afterClear clearJournal)
valid-eval = refl

validTx : Tx
validTx = makeTx clearEntry tt 42 0 initial tt afterClear clearJournal valid-eval

valid-proof : verified validTx ≡ true
valid-proof = refl

valid-admission : admission ctx initial validTx ≡ (afterClear , accepted)
valid-admission = refl

wrong-key : eval (clear 43) initial ≡ inj₁ (assertionError unauthorised)
wrong-key = refl

rawWrong : Tx
rawWrong = transaction (makeStatement clearEntry tt tt 0 clearJournal) invalid

raw-rejected : admission ctx initial rawWrong ≡ (initial , rejected)
raw-rejected = refl

setJournal : Journal
setJournal = operated (readField lockState) false ∷
  operated (readRound lockRound) 1 ∷
  operated (writeField lockAuthority (publicKey 1 42)) tt ∷
  operated (writeField lockValue 100) tt ∷
  operated (writeField lockState true) tt ∷ []

set-eval : eval (setLock 100 42) afterClear ≡ inj₂ (finished tt afterSet setJournal)
set-eval = refl

setTx : Tx
setTx = makeTx setEntry (100 , ≤-step100) 42 1 afterClear tt afterSet setJournal set-eval
  where
  ≤-step100 : 100 ≤ maxCounter
  ≤-step100 = toWitness {a? = 100 ≤? maxCounter} tt

intervening-set : admission ctx afterClear setTx ≡ (afterSet , accepted)
intervening-set = refl

-- State is SET again, but the old exact counter dependency is still stale.
stale-rejected : admission ctx afterSet validTx ≡ (afterSet , rejected)
stale-rejected = refl

zeroCounter : State
zeroCounter = fixtureState false (publicKey 0 42) 99 0

oneCounter : State
oneCounter = record zeroCounter { round = 1 }

twoCounter : State
twoCounter = record zeroCounter { round = 2 }

blindJournal : Journal
blindJournal = operated (incrementCounter lockRound 1) tt ∷ []

two-blind-increments : replay ctx blindJournal zeroCounter ≡ just oneCounter ×
  replay ctx blindJournal oneCounter ≡ just twoCounter
two-blind-increments = refl , refl

predicate-rebases : apply (counterLessThan lockRound 3) true twoCounter ≡ just twoCounter
predicate-rebases = refl

exact-read-conflicts : apply (readRound lockRound) 0 oneCounter ≡ nothing
exact-read-conflicts = refl

read-after-write : replay ctx
  (operated (writeField lockValue 100) tt ∷ operated (readField lockValue) 100 ∷ []) initial
  ≡ just (record initial { value = 100 })
read-after-write = refl

lateFailure : Program ⊤
lateFailure = write lockState false >> increment 1 >> assert false assertionFailed

late-failure : eval lateFailure initial ≡ inj₁ (assertionError assertionFailed)
late-failure = refl

time-rejected : replay ctx (operated (writeField lockState false) tt ∷ required (timeAtLeast 1) ∷ []) initial ≡ nothing
time-rejected = refl

assembled : Upstream.Protocol CategoricalCrypto.Iface.unitᴵ ClientIf
assembled = system ctx initial

assembled-round-safety : ∀ {st} → Reachable ctx initial st → RoundBound (chainState st)
assembled-round-safety = reachable-invariant lock-preserves ctx initial z≤n

validStrategy : Strat ClientQuery ClientAnswer
validStrategy = ask (build clearEntry tt 42 0) λ
  { (built clearEntry tt _ _) → ask submit λ { (submitted accepted) → out true ; _ → out false }
  ; _ → out false }

wrongKeyStrategy : Strat ClientQuery ClientAnswer
wrongKeyStrategy = ask (build clearEntry tt 43 0) λ
  { (buildFailed (assertionError unauthorised) _) → ask (submitOther rawWrong) λ
      { (submitted rejected) → out true ; _ → out false }
  ; _ → out false }

staleStrategy : Strat ClientQuery ClientAnswer
staleStrategy = ask (build clearEntry tt 42 0) λ
  { (built clearEntry tt _ _) → ask (submitOther validTx) λ
      { (submitted accepted) → ask (submitOther setTx) λ
          { (submitted accepted) → ask submit λ { (submitted rejected) → out true ; _ → out false }
          ; _ → out false }
      ; _ → out false }
  ; _ → out false }

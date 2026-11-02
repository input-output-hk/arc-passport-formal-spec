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
import CategoricalCrypto.Protocol.Reachability as Reach
open import CategoricalCrypto.Strategy using (Strat; ask; out)
open import Midnight.ContractDSL.FixtureLedger
open import Midnight.ContractDSL.Ledger
open import Midnight.ContractDSL.MidnightLedger
open import Midnight.ContractDSL.Program midnight Assertion
import Midnight.ContractDSL.Contract as Contracts
import Midnight.ContractDSL.Protocol as Protocols
import Midnight.ContractDSL.AdmissionProperties as Admissions
import Midnight.ContractDSL.Experiment as Experiments
import Midnight.ContractDSL.Experiment.Properties as ExperimentProperties
open import Midnight.ContractDSL.SymbolicDigest
open Execution midnight

read : {k : Kind} → FieldRef k → Program (Res k)
read f = perform (ledger (readField f))

write : {k : Kind} → FieldRef k → Res k → Program ⊤
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
Input clearEntry = ℕ
Input setEntry = Σ ℕ (λ v → v ≤ maxCounter) × ℕ

lockContract : Contracts.Contract midnight Assertion
lockContract = record
  { self = 7 ; EntryPoint = Entry ; Input = Input ; Result = λ _ → ⊤
  ; body = λ self → λ { clearEntry sk → clear sk
                      ; setEntry ((v , bound) , sk) → setLock v sk } }

module C = Contracts.Contract lockContract
module P = Protocols midnight Assertion lockContract
module A = Admissions midnight Assertion lockContract
open C hiding (Input)
module Client = Experiments.Runtime midnight Assertion lockContract (λ _ → ⊤) (λ _ _ → tt)
module ClientProof = ExperimentProperties midnight Assertion lockContract (λ _ → ⊤) (λ _ _ → tt)

RoundBound : State → Set
RoundBound s = round s ≤ maxCounter

lock-preserves : A.Preserves RoundBound
lock-preserves clearEntry sk s pre with eval (clear sk) s in evaluated
... | inj₁ err = tt
... | inj₂ (finished tt t j) with clear-safety sk s evaluated
... | _ , _ , n , added , refl = proj₂ (proj₂ (addCounter-spec (round s) 1 added))
lock-preserves setEntry ((v , bound) , sk) s pre with eval (setLock v sk) s in evaluated
... | inj₁ err = tt
... | inj₂ (finished tt t j) =
  subst (λ n → n ≤ maxCounter) (sym (set-round v sk s evaluated)) pre

accepted-clear : (now : ℕ) (s : State) (tx : Transaction) {t : State} →
  Transaction.entry tx ≡ clearEntry → admit s (submit now tx) ≡ (t , accepted) →
  Σ ℕ (ClearPost s t)
accepted-clear now s tx@(record { entry = clearEntry ; input = sk }) refl admitted =
  sk , clear-safety sk s (proj₂ (A.accepted-execution (submit now tx) s _ admitted))
accepted-clear now s (record { entry = setEntry }) () admitted

slot : ℕ
slot = 0

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

validTx : Transaction
validTx = record
  { target = 7 ; entry = clearEntry ; input = 42 ; view = initial
  ; execution = finished tt afterClear clearJournal ; certified = valid-eval }

valid-admission : admit initial (submit slot validTx) ≡ (afterClear , accepted)
valid-admission = refl

wrong-key : eval (clear 43) initial ≡ inj₁ (assertionError unauthorised)
wrong-key = refl
rawWrong : Client.Envelope
rawWrong = Client.invalidEnvelope

raw-rejected :
  Upstream.step (Client.system slot initial) (init (Client.system slot initial))
    (Client.sendEnvelope rawWrong) ≡
  ret ((nothing , initial , tt) , Client.transportInvalid)
raw-rejected = refl


setJournal : Journal
setJournal = operated (readField lockState) false ∷
  operated (readRound lockRound) 1 ∷
  operated (writeField lockAuthority (publicKey 1 42)) tt ∷
  operated (writeField lockValue 100) tt ∷
  operated (writeField lockState true) tt ∷ []

set-eval : eval (setLock 100 42) afterClear ≡ inj₂ (finished tt afterSet setJournal)
set-eval = refl

setTx : Transaction
setTx = record
  { target = 7 ; entry = setEntry ; input = (100 , ≤-step100) , 42 ; view = afterClear
  ; execution = finished tt afterSet setJournal ; certified = set-eval }
  where
  ≤-step100 : 100 ≤ maxCounter
  ≤-step100 = toWitness {a? = 100 ≤? maxCounter} tt

intervening-set : admit afterClear (submit slot setTx) ≡ (afterSet , accepted)
intervening-set = refl

-- State is SET again, but the old exact counter dependency is still stale.
stale-rejected : admit afterSet (submit slot validTx) ≡ (afterSet , rejected)
stale-rejected = refl

zeroCounter : State
zeroCounter = fixtureState false (publicKey 0 42) 99 0

oneCounter : State
oneCounter = record zeroCounter { round = 1 }

twoCounter : State
twoCounter = record zeroCounter { round = 2 }

blindJournal : Journal
blindJournal = operated (incrementCounter lockRound 1) tt ∷ []

two-blind-increments : replay slot blindJournal zeroCounter ≡ just oneCounter ×
  replay slot blindJournal oneCounter ≡ just twoCounter
two-blind-increments = refl , refl

predicate-rebases : apply (counterLessThan lockRound 3) true twoCounter ≡ just twoCounter
predicate-rebases = refl

exact-read-conflicts : apply (readRound lockRound) 0 oneCounter ≡ nothing
exact-read-conflicts = refl

read-after-write : replay slot
  (operated (writeField lockValue 100) tt ∷ operated (readField lockValue) 100 ∷ []) initial
  ≡ just (record initial { value = 100 })
read-after-write = refl

lateFailure : Program ⊤
lateFailure = write lockState false >> increment 1 >> assert false assertionFailed

late-failure : eval lateFailure initial ≡ inj₁ (assertionError assertionFailed)
late-failure = refl

time-rejected : replay slot (operated (writeField lockState false) tt ∷ required (timeAtLeast 1) ∷ []) initial ≡ nothing
time-rejected = refl

assembled : Upstream.Protocol CategoricalCrypto.Iface.unitᴵ P.ContractIf
assembled = P.toProtocol initial

assembled-round-safety : ∀ {s} → Reach.Reachable assembled s → RoundBound s
assembled-round-safety reached =
  A.admissions-preserve lock-preserves (P.reachable-admissions initial reached) z≤n

clientSystem : Upstream.Protocol CategoricalCrypto.Iface.unitᴵ Client.ClientIf
clientSystem = Client.system slot initial
client-system-round-safety : ∀ {st} → Reach.Reachable clientSystem st →
  RoundBound (Client.ledgerState st)
client-system-round-safety reached =
  A.admissions-preserve lock-preserves (ClientProof.system-admissions slot initial reached) z≤n


validStrategy : Strat Client.ClientQuery Client.ClientAnswer
validStrategy = ask (Client.prepareDraft clearEntry 42 Client.neutralArtifact) λ
  { (Client.preparedAnswer clearEntry tt _ _) → ask Client.submitDraft λ
      { (Client.admitted accepted) → out true ; _ → out false }
  ; _ → out false }

wrongKeyStrategy : Strat Client.ClientQuery Client.ClientAnswer
wrongKeyStrategy = ask (Client.prepareDraft clearEntry 43 Client.neutralArtifact) λ
  { (Client.failed (assertionError unauthorised) _) → ask (Client.sendEnvelope rawWrong) λ
      { Client.transportInvalid → out true ; _ → out false }
  ; _ → out false }

staleStrategy : Strat Client.ClientQuery Client.ClientAnswer
staleStrategy = ask (Client.prepareDraft clearEntry 42 Client.neutralArtifact) λ
  { (Client.preparedAnswer clearEntry tt _ _) →
      ask (Client.sendEnvelope (Client.certifiedEnvelope (Client.certifiedDraft validTx Client.neutralArtifact))) λ
      { (Client.submitted accepted) →
          ask (Client.sendEnvelope (Client.certifiedEnvelope (Client.certifiedDraft setTx Client.neutralArtifact))) λ
          { (Client.submitted accepted) → ask Client.submitDraft λ
              { (Client.admitted rejected) → out true ; _ → out false }
          ; _ → out false }
      ; _ → out false }
  ; _ → out false }

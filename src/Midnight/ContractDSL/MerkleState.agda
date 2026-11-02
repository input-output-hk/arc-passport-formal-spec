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
import Midnight.ContractDSL.Contract as Contracts
import Midnight.ContractDSL.Protocol as Protocols
import Midnight.ContractDSL.Experiment as Experiments
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
Input membership = FieldValue × Path
Input replaceRoot = Digest
Input replaceFlags = Bool × Bool

PublicInput : Entry → Set
PublicInput membership = FieldValue
PublicInput replaceRoot = Digest
PublicInput replaceFlags = Bool × Bool

projectInput : (n : Entry) → Input n → PublicInput n
projectInput membership = proj₁
projectInput replaceRoot r = r
projectInput replaceFlags flags = flags

-- Root/flag maintenance is deliberately unrestricted in this regression
-- contract; it makes no source-level access-control correspondence claim.
merkleContract : Contracts.Contract midnight Assertion
merkleContract = record
  { self = 31 ; EntryPoint = Entry ; Input = Input ; Result = λ _ → ⊤
  ; body = λ _ → λ
      { membership (item , p) → checkSecure item p
      ; replaceRoot r → perform (ledger (updateRoot r))
      ; replaceFlags (f , t) → perform (ledger (updateFlags f t)) } }

module C = Contracts.Contract merkleContract
module P = Protocols midnight Assertion merkleContract
module M = Experiments.Runtime midnight Assertion merkleContract PublicInput projectInput
open C hiding (Input)

slot : ℕ
slot = 0

initial : State
initial = Fixture.initial

changed : State
changed = record initial { root = merkleLeaf 9 }

oldJournal : Journal
oldJournal = operated (checkRoot fixtureRoot) true ∷ []

old-success : eval (checkSecure 1 (findItem a)) initial ≡ inj₂ (finished tt initial oldJournal)
old-success = refl

oldTx : Transaction
oldTx = record
  { target = 31 ; entry = membership ; input = 1 , findItem a ; view = initial
  ; execution = finished tt initial oldJournal ; certified = old-success }

updateRootJournal : Journal
updateRootJournal = operated (updateRoot (merkleLeaf 9)) tt ∷ []

root-success : eval (perform (ledger (updateRoot (merkleLeaf 9)))) initial ≡
  inj₂ (finished tt changed updateRootJournal)
root-success = refl

rootTx : Transaction
rootTx = record
  { target = 31 ; entry = replaceRoot ; input = merkleLeaf 9 ; view = initial
  ; execution = finished tt changed updateRootJournal ; certified = root-success }

freshPath : Path
freshPath = path 9 []

freshJournal : Journal
freshJournal = operated (checkRoot (merkleLeaf 9)) true ∷ []

fresh-success : eval (checkSecure 9 freshPath) changed ≡ inj₂ (finished tt changed freshJournal)
fresh-success = matching-success 9 freshPath changed refl refl

freshTx : Transaction
freshTx = record
  { target = 31 ; entry = membership ; input = 9 , freshPath ; view = changed
  ; execution = finished tt changed freshJournal ; certified = fresh-success }

matching-admitted : admit initial (submit slot oldTx) ≡ (initial , accepted)
matching-admitted = refl

root-updated : admit initial (submit slot rootTx) ≡ (changed , accepted)
root-updated = refl

-- Old certificates remain valid about their preparation view. Admission
-- rejects their recorded true observation against the current changed root.
old-certificate-execution :
  eval (C.body (Transaction.target oldTx) (Transaction.entry oldTx) (Transaction.input oldTx))
    (Transaction.view oldTx) ≡ inj₂ (Transaction.execution oldTx)
old-certificate-execution = Transaction.certified oldTx
old-evaluation-rejected : eval (checkSecure 1 (findItem a)) changed ≡
  inj₁ (assertionError assertionFailed)
old-evaluation-rejected = refl

old-replay-rejected : replay slot oldJournal changed ≡ nothing
old-replay-rejected = refl

old-admission-rejected : admit changed (submit slot oldTx) ≡ (changed , rejected)
old-admission-rejected = refl

fresh-admitted : admit changed (submit slot freshTx) ≡ (changed , accepted)
fresh-admitted = refl

noFalseFlag : State
noFalseFlag = record initial { falseFlag = false }

flags-updated : eval (perform (ledger (updateFlags false true))) initial ≡
  inj₂ (finished tt noFalseFlag (operated (updateFlags false true) tt ∷ []))
flags-updated = refl

removed-flag-rejected : eval (program insecure a false) noFalseFlag ≡
  inj₁ (assertionError assertionFailed)
removed-flag-rejected = refl

removed-flag-replay-rejected : replay slot (programJournal insecure a false) noFalseFlag ≡ nothing
removed-flag-replay-rejected = refl

assembled : Upstream.Protocol unitᴵ P.ContractIf
assembled = P.toProtocol initial

clientSystem : Upstream.Protocol unitᴵ M.ClientIf
clientSystem = M.system slot initial

rootChangeStrategy : Strat M.ClientQuery M.ClientAnswer
rootChangeStrategy = ask (M.prepareDraft membership (1 , findItem a) M.neutralArtifact) λ
  { (M.preparedAnswer membership tt _ _) →
      ask (M.sendEnvelope (M.certifiedEnvelope (M.certifiedDraft oldTx M.neutralArtifact))) λ
      { (M.submitted accepted) → ask (M.sendEnvelope (M.certifiedEnvelope (M.certifiedDraft rootTx M.neutralArtifact))) λ
          { (M.submitted accepted) → ask M.submitDraft λ
              { (M.admitted rejected) → ask (M.prepareDraft membership (9 , freshPath) M.neutralArtifact) λ
                  { (M.preparedAnswer membership tt _ _) → ask M.submitDraft λ
                      { (M.admitted accepted) → out true ; _ → out false }
                  ; _ → out false }
              ; _ → out false }
          ; _ → out false }
      ; _ → out false }
  ; _ → out false }

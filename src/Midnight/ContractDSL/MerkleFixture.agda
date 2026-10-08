{-# OPTIONS --safe --without-K #-}

module Midnight.ContractDSL.MerkleFixture where

open import Data.Bool.Base
open import Data.List.Base
open import Data.Maybe.Base hiding (_>>=_)
open import Data.Nat.Base
open import Data.Nat.Properties using (_≟_)
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Midnight.ContractDSL.FixtureLedger
open import Midnight.ContractDSL.MidnightLedger
open import Midnight.ContractDSL.Merkle
open import Midnight.ContractDSL.Program midnight Assertion
open import Midnight.ContractDSL.SymbolicDigest

-- Publicly known example members, NOT the circuit's input domain.
data Item : Set where
  a b c d : Item

fieldValue : Item → FieldValue
fieldValue a = 1
fieldValue b = 2
fieldValue c = 3
fieldValue d = 4

-- Experiment choice, not a predicate taken from the Midnight membership source.
classify : FieldValue → Bool
classify item = ⌊ item ≟ 3 ⌋ ∨ ⌊ item ≟ 4 ⌋

padding : ℕ → ℕ → List Sibling
padding zero h = []
padding (suc n) h = sibling false (emptyRoot h) ∷ padding n (suc h)

findItem : Item → Path
findItem a = path 1 (sibling false (merkleLeaf 2) ∷
  sibling false (merkleBranch (merkleLeaf 3) (merkleLeaf 4)) ∷ padding 8 2)
findItem b = path 2 (sibling true (merkleLeaf 1) ∷
  sibling false (merkleBranch (merkleLeaf 3) (merkleLeaf 4)) ∷ padding 8 2)
findItem c = path 3 (sibling false (merkleLeaf 4) ∷
  sibling true (merkleBranch (merkleLeaf 1) (merkleLeaf 2)) ∷ padding 8 2)
findItem d = path 4 (sibling true (merkleLeaf 3) ∷
  sibling true (merkleBranch (merkleLeaf 1) (merkleLeaf 2)) ∷ padding 8 2)

member-root : (i : Item) → pathRoot (findItem i) ≡ fixtureRoot
member-root a = refl
member-root b = refl
member-root c = refl
member-root d = refl

program : Variant → Item → Bool → Program ⊤
program v i mask = executionProgram classify v (fieldValue i) (findItem i) mask

initial : State
initial = fixtureState false (lockKey 0 0) 0 0

rootJournal : Journal
rootJournal = operated (checkRoot fixtureRoot) true ∷ []

programJournal : Variant → Item → Bool → Journal
programJournal secure i mask = rootJournal
programJournal insecure i mask = rootJournal ++
  (operated (flagMember (classify (fieldValue i) xor mask)) true ∷ [])

Compatible : State → Set
Compatible s = root s ≡ fixtureRoot × falseFlag s ≡ true × trueFlag s ≡ true

fixture-compatible : Compatible initial
fixture-compatible = refl , refl , refl

-- The former arbitrary-state claim relied on global root/flag constants.
-- Mutable state requires these explicit premises; fixture runs satisfy them.
successful : (v : Variant) (i : Item) (mask : Bool) (s : State) → Compatible s →
  eval (program v i mask) s ≡ inj₂ (finished tt s (programJournal v i mask))
successful secure a mask s (r , f , t) rewrite r = refl
successful secure b mask s (r , f , t) rewrite r = refl
successful secure c mask s (r , f , t) rewrite r = refl
successful secure d mask s (r , f , t) rewrite r = refl
successful insecure a false s (r , f , t) rewrite r | f = refl
successful insecure a true s (r , f , t) rewrite r | t = refl
successful insecure b false s (r , f , t) rewrite r | f = refl
successful insecure b true s (r , f , t) rewrite r | t = refl
successful insecure c false s (r , f , t) rewrite r | t = refl
successful insecure c true s (r , f , t) rewrite r | f = refl
successful insecure d false s (r , f , t) rewrite r | t = refl
successful insecure d true s (r , f , t) rewrite r | f = refl

fixture-successful : (v : Variant) (i : Item) (mask : Bool) →
  eval (program v i mask) initial ≡ inj₂ (finished tt initial (programJournal v i mask))
fixture-successful v i mask = successful v i mask initial fixture-compatible

wrong-leaf-rejected : eval (checkSecure 1 (findItem b)) initial ≡ inj₁ (assertionError assertionFailed)
wrong-leaf-rejected = refl

wrong-root-rejected : eval (checkSecure 1 (path 1 [])) initial ≡ inj₁ (assertionError assertionFailed)
wrong-root-rejected = refl

root-read-only : (r : Digest) (s : State) →
  prepare (checkRoot r) s ≡ inj₂ (⌊ digestEq r (root s) ⌋ , s)
root-read-only r s = refl

flags-read-only : (tag : Bool) (s : State) →
  prepare (flagMember tag) s ≡ inj₂ ((if tag then trueFlag s else falseFlag s) , s)
flags-read-only false s = refl
flags-read-only true s = refl

eligible : (v : Variant) (i : Item) (mask : Bool) (ctx : Context) →
  Eligible ctx (programJournal v i mask)
eligible secure i mask ctx = tt
eligible insecure i mask ctx = tt

admitted : (v : Variant) (i : Item) (mask : Bool) (s : State) (ctx : Context) →
  Compatible s → replay ctx (programJournal v i mask) s ≡ just s
admitted v i mask s ctx compatible = same-view-replay (program v i mask) ctx
  (successful v i mask s compatible) (eligible v i mask ctx)

second : Bool → Item
second false = b
second true = c

paired-tags : (x y mask : Bool) → (x xor mask) xor (y xor mask) ≡ x xor y
paired-tags false false false = refl
paired-tags false false true = refl
paired-tags false true false = refl
paired-tags false true true = refl
paired-tags true false false = refl
paired-tags true false true = refl
paired-tags true true false = refl
paired-tags true true true = refl

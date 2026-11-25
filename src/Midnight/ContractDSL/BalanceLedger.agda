{-# OPTIONS --safe --without-K #-}

module Midnight.ContractDSL.BalanceLedger where

open import Class.DecEq using (DecEq; DecEq-⊤)
open import Data.Nat.Base
open import Data.Nat.Properties using (_≟_; _≤?_; +-assoc; +-comm; m∸n+n≡m; m+[n∸m]≡n)
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Midnight.ContractDSL.Ledger

data Account : Set where
  alice bob : Account

other : Account → Account
other alice = bob
other bob = alice

-- A finite two-account balance map; it has no Midnight fields or digests.
record State : Set where
  constructor balances
  field aliceBalance bobBalance : ℕ
open State public

balanceOf : Account → State → ℕ
balanceOf alice = aliceBalance
balanceOf bob = bobBalance

total : State → ℕ
total s = aliceBalance s + bobBalance s

move : Account → ℕ → State → State
move alice n s = balances (aliceBalance s ∸ n) (bobBalance s + n)
move bob n s = balances (aliceBalance s + n) (bobBalance s ∸ n)

move-conserves : (a : Account) (n : ℕ) (s : State) →
  n ≤ balanceOf a s → total (move a n s) ≡ total s
move-conserves alice n (balances l r) enough = trans
  (cong ((l ∸ n) +_) (+-comm r n))
  (trans (sym (+-assoc (l ∸ n) n r)) (cong (_+ r) (m∸n+n≡m enough)))
move-conserves bob n (balances l r) enough = trans
  (+-assoc l n (r ∸ n)) (cong (l +_) (m+[n∸m]≡n enough))

data Kind : Set where
  amount unit : Kind

Res : Kind → Set
Res amount = ℕ
Res unit = ⊤

data Op : Kind → Set where
  readBalance : Account → Op amount
  transfer : Account → ℕ → Op unit

data Failure : Set where
  insufficientFunds : Failure

data Assertion : Set where
  emptyTransfer : Assertion

prepare : {k : Kind} → Op k → State → Failure ⊎ (Res k × State)
prepare (readBalance a) s = inj₂ (balanceOf a s , s)
prepare (transfer a n) s with n ≤? balanceOf a s
... | no _ = inj₁ insufficientFunds
... | yes _ = inj₂ (tt , move a n s)

resultEquality : (k : Kind) → DecEq (Res k)
resultEquality amount = record { _≟_ = _≟_ }
resultEquality unit = DecEq-⊤

balanceLedger : Semantics
balanceLedger = record
  { State = State ; Kind = Kind ; Res = Res ; Op = Op ; Failure = λ _ → Failure
  ; prepare = prepare ; DecEq-Res = λ {k} → resultEquality k }

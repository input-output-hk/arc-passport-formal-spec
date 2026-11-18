{-# OPTIONS --safe --without-K #-}

module Passport.FinalizedLedgerExamples where

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.List.Base
open import Data.Nat using (ℕ; _≟_; _≤_; _≤?_)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.String.Base using (String)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable using (⌊_⌋; _×-dec_)

import Passport.FinalizedLedger

open Passport.FinalizedLedger ℕ ℕ ℕ _≟_ _≟_ _≟_

-- Accounts 0, 1, 2 are Alice, Bob, Carol; assets 0, 1 are coin, token.
-- The illustrative policy is deliberately not a signature/custody policy.
Authorized : State → Transaction → Set
Authorized s t = txId t ≤ 20 × feeAmount (feeCharge t) ≤ balance s 2 1

authorized? : ∀ s t → Dec (Authorized s t)
authorized? s t = (txId t ≤? 20) ×-dec (feeAmount (feeCharge t) ≤? balance s 2 1)

open Execution Authorized authorized?

initialBalances : ℕ → ℕ → ℕ
initialBalances 0 0 = 10
initialBalances 0 1 = 7
initialBalances 1 0 = 3
initialBalances 2 1 = 2
initialBalances _ _ = 0

initialFees : ℕ → ℕ
initialFees 0 = 4
initialFees 1 = 5
initialFees _ = 0

initial : State
initial = state initialBalances initialFees []

payment repeated-debit overlapping-fee self-funded self-unfunded incoming-credit
  distinct-cells unauthorized policy-bound intervening retry topup : Transaction
payment = transaction 1 (transfer 0 1 0 4 ∷ []) (fee 0 0 1)
repeated-debit = transaction 3 (transfer 0 1 0 6 ∷ transfer 0 2 0 6 ∷ []) (fee 0 0 0)
overlapping-fee = transaction 4 (transfer 0 1 0 9 ∷ []) (fee 0 0 2)
self-funded = transaction 5 (transfer 0 0 0 10 ∷ []) (fee 0 0 0)
self-unfunded = transaction 6 (transfer 0 0 0 11 ∷ []) (fee 0 0 0)
incoming-credit = transaction 7 (transfer 1 0 0 3 ∷ transfer 0 1 0 11 ∷ []) (fee 0 0 0)
distinct-cells = transaction 2 (transfer 0 1 1 3 ∷ transfer 1 2 0 2 ∷ []) (fee 0 0 1)
unauthorized = transaction 99 (transfer 0 1 0 4 ∷ []) (fee 0 0 1)
policy-bound = transaction 8 (transfer 0 1 0 1 ∷ []) (fee 0 0 3)
intervening = transaction 9 (transfer 1 0 0 1 ∷ []) (fee 1 0 1)
retry = transaction 10 (transfer 0 1 0 11 ∷ []) (fee 0 0 0)
topup = transaction 11 (transfer 1 0 0 2 ∷ []) (fee 1 0 0)

after-payment after-intervening after-topup after-retry : State
after-payment = resultState (finalize initial payment)
after-intervening = resultState (finalize after-payment intervening)
after-topup = resultState (finalize initial topup)
after-retry = resultState (finalize after-topup retry)

isAccepted : Result → Bool
isAccepted (accepted _) = true
isAccepted (rejected _) = false

-- These equalities pin actual observations, not just validity of test fixtures.
payment-accepted : isAccepted (finalize initial payment) ≡ true
payment-accepted = refl

payment-accounting :
  _≡_ {A = ℕ × ℕ × ℕ × ℕ × List ℕ}
    (balance after-payment 0 0 , balance after-payment 1 0 , fees after-payment 0 ,
      fees after-payment 1 , acceptedIds after-payment)
    (5 , 7 , 5 , 5 , 1 ∷ [])
payment-accounting = refl

repeated-debit-rejected : finalize initial repeated-debit ≡ rejected initial
repeated-debit-rejected = refl

overlapping-fee-rejected : finalize initial overlapping-fee ≡ rejected initial
overlapping-fee-rejected = refl

self-transfer-accepted : isAccepted (finalize initial self-funded) ≡ true
self-transfer-accepted = refl

self-transfer-no-mint : balance (resultState (finalize initial self-funded)) 0 0 ≡ 10
self-transfer-no-mint = refl

self-transfer-needs-prefunding : finalize initial self-unfunded ≡ rejected initial
self-transfer-needs-prefunding = refl

incoming-credit-cannot-fund : finalize initial incoming-credit ≡ rejected initial
incoming-credit-cannot-fund = refl

distinct-cells-accepted : isAccepted (finalize initial distinct-cells) ≡ true
distinct-cells-accepted = refl

distinct-cells-accounting :
  let s = resultState (finalize initial distinct-cells) in
  _≡_ {A = ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ}
    (balance s 0 0 , balance s 0 1 , balance s 1 0 , balance s 1 1 ,
      balance s 2 0 , balance s 2 1 , balance s 3 0 , fees s 0 , fees s 1)
    (9 , 4 , 1 , 3 , 2 , 2 , 0 , 5 , 5)
distinct-cells-accounting = refl

unauthorized-preserves-entire-state : finalize initial unauthorized ≡ rejected initial
unauthorized-preserves-entire-state = refl

policy-inspects-prestate : finalize initial policy-bound ≡ rejected initial
policy-inspects-prestate = refl

changedPolicyBalances : ℕ → ℕ → ℕ
changedPolicyBalances 2 1 = 3
changedPolicyBalances a c = initialBalances a c

changed-policy-state : State
changed-policy-state = state changedPolicyBalances initialFees []

same-transaction-new-policy-state :
  isAccepted (finalize changed-policy-state policy-bound) ≡ true
same-transaction-new-policy-state = refl

accepted-id-rejected : finalize after-payment payment ≡ rejected after-payment
accepted-id-rejected = refl

intervening-accepted : isAccepted (finalize after-payment intervening) ≡ true
intervening-accepted = refl

history-survives-intervening : acceptedIds after-intervening ≡ 9 ∷ 1 ∷ []
history-survives-intervening = refl

replay-after-intervening-rejected :
  finalize after-intervening payment ≡ rejected after-intervening
replay-after-intervening-rejected = refl

failed-retry-preserves-entire-state : finalize initial retry ≡ rejected initial
failed-retry-preserves-entire-state = refl

topup-accepted : isAccepted (finalize initial topup) ≡ true
topup-accepted = refl

rejected-id-retry-accepted : isAccepted (finalize after-topup retry) ≡ true
rejected-id-retry-accepted = refl

retry-accounting :
  _≡_ {A = ℕ × ℕ × ℕ × List ℕ}
    (balance after-retry 0 0 , balance after-retry 1 0 , fees after-retry 0 ,
      acceptedIds after-retry)
    (1 , 12 , 4 , 10 ∷ 11 ∷ [])
retry-accounting = refl

-- The smoke runner prints these computed checks; it does not print canned PASS lines.
smokeChecks : List (String × Bool)
smokeChecks =
  ("accepted transfer and fee" , isAccepted (finalize initial payment) ∧
    ⌊ balance after-payment 0 0 ≟ 5 ⌋ ∧ ⌊ balance after-payment 1 0 ≟ 7 ⌋ ∧
    ⌊ fees after-payment 0 ≟ 5 ⌋ ∧ ⌊ fees after-payment 1 ≟ 5 ⌋) ∷
  ("aggregate repeated debit rejected" , rejected? (finalize initial repeated-debit)) ∷
  ("transfer and fee overlap rejected" , rejected? (finalize initial overlapping-fee)) ∷
  ("funded self-transfer does not mint" , isAccepted (finalize initial self-funded) ∧
    ⌊ balance (resultState (finalize initial self-funded)) 0 0 ≟ 10 ⌋) ∷
  ("unfunded self-transfer rejected" , rejected? (finalize initial self-unfunded)) ∷
  ("incoming credit cannot fund debit" , rejected? (finalize initial incoming-credit)) ∷
  ("distinct accounts and assets" , isAccepted (finalize initial distinct-cells) ∧
    let s = resultState (finalize initial distinct-cells) in
    ⌊ balance s 0 0 ≟ 9 ⌋ ∧ ⌊ balance s 0 1 ≟ 4 ⌋ ∧ ⌊ balance s 1 0 ≟ 1 ⌋ ∧
    ⌊ balance s 1 1 ≟ 3 ⌋ ∧ ⌊ balance s 2 0 ≟ 2 ⌋ ∧ ⌊ balance s 2 1 ≟ 2 ⌋ ∧
    ⌊ balance s 3 0 ≟ 0 ⌋ ∧ ⌊ fees s 0 ≟ 5 ⌋ ∧ ⌊ fees s 1 ≟ 5 ⌋) ∷
  ("unauthorized transaction rejected" , rejected? (finalize initial unauthorized)) ∷
  ("authorization inspects prestate" , rejected? (finalize initial policy-bound) ∧
    isAccepted (finalize changed-policy-state policy-bound)) ∷
  ("duplicate accepted ID rejected" , rejected? (finalize after-payment payment)) ∷
  ("intervening transaction accepted" , isAccepted (finalize after-payment intervening)) ∷
  ("replay after intervening transaction rejected" , rejected? (finalize after-intervening payment)) ∷
  ("initial retry rejected" , rejected? (finalize initial retry)) ∷
  ("topup accepted" , isAccepted (finalize initial topup)) ∷
  ("rejected ID retry accepted" , isAccepted (finalize after-topup retry) ∧
    ⌊ balance after-retry 0 0 ≟ 1 ⌋ ∧ ⌊ balance after-retry 1 0 ≟ 12 ⌋ ∧
    ⌊ fees after-retry 0 ≟ 4 ⌋) ∷ []
  where
  rejected? : Result → Bool
  rejected? (accepted _) = false
  rejected? (rejected _) = true

smoke-checks-pass : map proj₂ smokeChecks ≡ replicate 15 true
smoke-checks-pass = refl

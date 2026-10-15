{-# OPTIONS --safe --without-K #-}

module Midnight.ContractDSL.Balance where

open import Data.Bool.Base hiding (_≤_; _<_)
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Nat.Properties using (_≤?_)
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import CategoricalCrypto.Iface
import CategoricalCrypto.Protocol as Upstream
open import CategoricalCrypto.Strategy using (Strat; ask; out)
open import Midnight.ContractDSL.BalanceLedger
open import Midnight.ContractDSL.Program balanceLedger Assertion
open import Midnight.ContractDSL.Protocol balanceLedger Assertion

send : Account → ℕ → Program ⊤
send a n = assert (0 <ᵇ n) emptyTransfer >> perform (ledger (transfer a n))

private
  transfer-result : (a : Account) (n : ℕ) (s : State) {t : State} →
    prepare (transfer a n) s ≡ inj₂ (tt , t) →
    n ≤ balanceOf a s × t ≡ move a n s
  transfer-result a n s prepared with n ≤? balanceOf a s
  ... | no _ with prepared
  ...   | ()
  transfer-result a n s refl | yes enough = enough , refl

send-details : (a : Account) (n : ℕ) (s : State) {t : State} {j : Journal} →
  eval (send a n) s ≡ inj₂ (finished tt t j) →
  (0 <ᵇ n) ≡ true × n ≤ balanceOf a s × t ≡ move a n s ×
  j ≡ operated (transfer a n) tt ∷ []
send-details a n s {t} {j} ev =
  hoare-bind {P = λ u → u ≡ s}
    {R = λ _ u js → u ≡ s × (0 <ᵇ n) ≡ true × js ≡ []}
    {Q = λ _ v js → (0 <ᵇ n) ≡ true × n ≤ balanceOf a s × v ≡ move a n s ×
      js ≡ operated (transfer a n) tt ∷ []}
    (assert (0 <ᵇ n) emptyTransfer) (λ _ → perform (ledger (transfer a n)))
    (hoare-assert (0 <ᵇ n) emptyTransfer (λ u pre positive → pre , positive , refl))
    (λ _ js → hoare-ledger (transfer a n) λ
      { u tt v (refl , positive , refl) prepared →
        let enough , moved = transfer-result a n s prepared in
        positive , enough , moved , refl })
    s tt t j refl ev

send-conserves : (a : Account) (n : ℕ) (s : State) {t : State} {j : Journal} →
  eval (send a n) s ≡ inj₂ (finished tt t j) → total t ≡ total s
send-conserves a n s ev with send-details a n s ev
... | positive , enough , refl , recorded = move-conserves a n s enough

balanceContract : Contract
balanceContract = record
  { Name = Account ; Input = λ _ → ℕ ; PublicArgs = λ _ → ℕ
  ; Result = λ _ → ⊤ ; Witness = λ _ _ → ⊤
  ; publicArgs = λ _ n → n ; body = λ _ a n _ → send a n }

module B = Interpreter balanceContract (ExactCommunication.scheme balanceContract) 23
open B

Conserved : State → Set
Conserved s = total s ≡ 12

preserves : Preserves Conserved
preserves acc a n w s tt t j pre ev = trans (send-conserves a n s ev) pre

initial afterFirst afterSecond : State
initial = balances 10 2
afterFirst = balances 7 5
afterSecond = balances 4 8

ctx : Context
ctx = context 23 0

transferJournal : Journal
transferJournal = operated (transfer alice 3) tt ∷ []

successful : eval (send alice 3) initial ≡ inj₂ (finished tt afterFirst transferJournal)
successful = refl

validTx : Tx
validTx = makeTx alice 3 tt 0 initial tt afterFirst transferJournal successful

accepted-first : admission ctx initial validTx ≡ (afterFirst , accepted)
accepted-first = makeTx-admitted alice 3 tt 0 initial tt afterFirst transferJournal successful ctx tt refl

-- Unit-result transfers rebase while funds remain; replay is not banned.
accepted-again : admission ctx afterFirst validTx ≡ (afterSecond , accepted)
accepted-again = refl

insufficient-evaluation : eval (send alice 11) initial ≡ inj₁ (operationError insufficientFunds)
insufficient-evaluation = refl

empty-evaluation : eval (send alice 0) initial ≡ inj₁ (assertionError emptyTransfer)
empty-evaluation = refl

spent : State
spent = balances 1 11

spent-rejected : admission ctx spent validTx ≡ (spent , rejected)
spent-rejected = refl

exact-balance-conflicts : replay ctx (operated (readBalance alice) 10 ∷ []) afterFirst ≡ nothing
exact-balance-conflicts = refl

accepted-conserves : (s : State) (tx : Tx) → Conserved s →
  Conserved (proj₁ (admission ctx s tx))
accepted-conserves = admission-invariant preserves ctx

assembled : Upstream.Protocol unitᴵ ClientIf
assembled = system ctx initial

assembled-conserves : ∀ {st} → Reachable ctx initial st → Conserved (chainState st)
assembled-conserves = reachable-invariant preserves ctx initial refl

successStrategy : Strat ClientQuery ClientAnswer
successStrategy = ask (build alice 3 tt 0) λ
  { (built alice tt _ _) → ask submit λ
      { (submitted accepted) → ask (submitOther validTx) λ
          { (submitted accepted) → out true ; _ → out false }
      ; _ → out false }
  ; _ → out false }

errorStrategy : Strat ClientQuery ClientAnswer
errorStrategy = ask (build alice 11 tt 0) λ
  { (buildFailed (operationError insufficientFunds) _) → ask (build alice 0 tt 0) λ
      { (buildFailed (assertionError emptyTransfer) _) → out true ; _ → out false }
  ; _ → out false }

fundsStrategy : Strat ClientQuery ClientAnswer
fundsStrategy = ask (submitOther validTx) λ
  { (submitted accepted) → ask (submitOther validTx) λ
      { (submitted accepted) → ask (submitOther validTx) λ
          { (submitted accepted) → ask (submitOther validTx) λ
              { (submitted rejected) → out true ; _ → out false }
          ; _ → out false }
      ; _ → out false }
  ; _ → out false }

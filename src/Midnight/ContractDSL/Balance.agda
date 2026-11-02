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
import CategoricalCrypto.Protocol.Reachability as Reach
open import Midnight.ContractDSL.BalanceLedger
open import Midnight.ContractDSL.Program balanceLedger Assertion
import Midnight.ContractDSL.Contract as Contracts
import Midnight.ContractDSL.Protocol as Protocols
import Midnight.ContractDSL.AdmissionProperties as Admissions
open import Midnight.ContractDSL.Hoare balanceLedger Assertion
import Midnight.ContractDSL.Experiment as Experiments
import Midnight.ContractDSL.Experiment.Properties as ExperimentProperties

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
send-details a n s ev with 0 <ᵇ n
... | false with ev
... | ()
send-details a n s ev | true with n ≤? balanceOf a s
... | no _ with ev
... | ()
send-details a n s refl | true | yes enough = refl , enough , refl , refl

send-conserves : (a : Account) (n : ℕ) (s : State) {t : State} {j : Journal} →
  eval (send a n) s ≡ inj₂ (finished tt t j) → total t ≡ total s
send-conserves a n s ev with send-details a n s ev
... | positive , enough , refl , recorded = move-conserves a n s enough

balanceContract : Contracts.Contract balanceLedger Assertion
balanceContract = record
  { self = 23 ; EntryPoint = Account ; Input = λ _ → ℕ
  ; Result = λ _ → ⊤ ; body = λ _ a n → send a n }

module C = Contracts.Contract balanceContract
module P = Protocols balanceLedger Assertion balanceContract
module A = Admissions balanceLedger Assertion balanceContract
open C
module B = Experiments.Runtime balanceLedger Assertion balanceContract (λ _ → ℕ) (λ _ n → n)
module BProof = ExperimentProperties balanceLedger Assertion balanceContract (λ _ → ℕ) (λ _ n → n)

Conserved : State → Set
Conserved s = total s ≡ 12

preserves : A.Preserves Conserved
preserves a n s pre with eval (send a n) s in evaluated
... | inj₁ err = tt
... | inj₂ (finished x t j) with x
... | tt = trans (send-conserves a n s evaluated) pre

initial afterFirst afterSecond : State
initial = balances 10 2
afterFirst = balances 7 5
afterSecond = balances 4 8

slot : ℕ
slot = 0

transferJournal : Journal
transferJournal = operated (transfer alice 3) tt ∷ []

successful : eval (send alice 3) initial ≡ inj₂ (finished tt afterFirst transferJournal)
successful = refl

validTx : Transaction
validTx = record
  { target = 23 ; entry = alice ; input = 3 ; view = initial
  ; execution = finished tt afterFirst transferJournal ; certified = successful }

accepted-first : admit initial (submit slot validTx) ≡ (afterFirst , accepted)
accepted-first = refl

-- Unit-result transfers rebase while funds remain; replay is not banned.
accepted-again : admit afterFirst (submit slot validTx) ≡ (afterSecond , accepted)
accepted-again = refl

insufficient-evaluation : eval (send alice 11) initial ≡ inj₁ (operationError insufficientFunds)
insufficient-evaluation = refl

empty-evaluation : eval (send alice 0) initial ≡ inj₁ (assertionError emptyTransfer)
empty-evaluation = refl

spent : State
spent = balances 1 11

spent-rejected : admit spent (submit slot validTx) ≡ (spent , rejected)
spent-rejected = refl

exact-balance-conflicts : replay slot (operated (readBalance alice) 10 ∷ []) afterFirst ≡ nothing
exact-balance-conflicts = refl

accepted-conserves : (s : State) (q : Submission) → Conserved s →
  Conserved (proj₁ (admit s q))
accepted-conserves s q pre with admit s q in admitted
... | t , v = A.admit-preserves preserves q admitted pre

assembled : Upstream.Protocol unitᴵ P.ContractIf
assembled = P.toProtocol initial

assembled-conserves : ∀ {s} → Reach.Reachable assembled s → Conserved s
assembled-conserves reached = A.admissions-preserve preserves (P.reachable-admissions initial reached) refl

clientSystem : Upstream.Protocol unitᴵ B.ClientIf
clientSystem = B.system slot initial
client-system-conserves : ∀ {st} → Reach.Reachable clientSystem st →
  Conserved (B.ledgerState st)
client-system-conserves reached =
  A.admissions-preserve preserves (BProof.system-admissions slot initial reached) refl


successStrategy : Strat B.ClientQuery B.ClientAnswer
successStrategy = ask (B.prepareDraft alice 3 B.neutralArtifact) λ
  { (B.preparedAnswer alice tt _ _) → ask B.submitDraft λ
      { (B.admitted accepted) → ask (B.sendEnvelope (B.certifiedEnvelope (B.certifiedDraft validTx B.neutralArtifact))) λ
          { (B.submitted accepted) → out true ; _ → out false }
      ; _ → out false }
  ; _ → out false }

errorStrategy : Strat B.ClientQuery B.ClientAnswer
errorStrategy = ask (B.prepareDraft alice 11 B.neutralArtifact) λ
  { (B.failed (operationError insufficientFunds) _) → ask (B.prepareDraft alice 0 B.neutralArtifact) λ
      { (B.failed (assertionError emptyTransfer) _) → out true ; _ → out false }
  ; _ → out false }

fundsStrategy : Strat B.ClientQuery B.ClientAnswer
fundsStrategy = ask (B.sendEnvelope (B.certifiedEnvelope (B.certifiedDraft validTx B.neutralArtifact))) λ
  { (B.submitted accepted) → ask (B.sendEnvelope (B.certifiedEnvelope (B.certifiedDraft validTx B.neutralArtifact))) λ
      { (B.submitted accepted) → ask (B.sendEnvelope (B.certifiedEnvelope (B.certifiedDraft validTx B.neutralArtifact))) λ
          { (B.submitted accepted) → ask (B.sendEnvelope (B.certifiedEnvelope (B.certifiedDraft validTx B.neutralArtifact))) λ
              { (B.submitted rejected) → out true ; _ → out false }
          ; _ → out false }
      ; _ → out false }
  ; _ → out false }

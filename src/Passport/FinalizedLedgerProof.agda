{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Passport.FinalizedLedgerProof
  (Account Asset TxId : Set)
  (_≟Account_ : DecidableEquality Account)
  (_≟Asset_ : DecidableEquality Asset)
  (_≟Id_ : DecidableEquality TxId) where

open import Data.Empty using (⊥-elim)
open import Data.Integer.Base using (_⊖_; +_)
import Data.Integer.Properties as ℤ
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (ℕ; _+_; _∸_; _≤_; z≤n)
import Data.Nat.Properties as ℕ
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; module ≡-Reasoning)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

import Passport.FinalizedLedger as Ledger

module L = Ledger Account Asset TxId _≟Account_ _≟Asset_ _≟Id_
open L hiding (module Execution)

private
  variable
    s s′ s₁ s₂ : State
    t u : Transaction
    a : Account
    x : Asset
    i : TxId

funding-or-zero : (D B : Key → ℕ) (ps : List Posting) →
  All (λ p → D (proj₁ p) ≤ B (proj₁ p)) ps →
  ∀ q → (D q ≤ B q) ⊎ (total ps q ≡ 0)
funding-or-zero D B [] [] q = inj₂ refl
funding-or-zero D B ((k , n) ∷ ps) (p ∷ funded) q with q ≟Key k
... | yes refl = inj₁ p
... | no _ = funding-or-zero D B ps funded q

funded-at : Funded s t → ∀ a x → debit t a x ≤ balance s a x
funded-at {s = s} {t = t} funded a x with funding-or-zero
  (total (charges t)) (λ q → balance s (proj₁ q) (proj₂ q))
  (charges t) funded (a , x)
... | inj₁ enough = enough
... | inj₂ zero = subst (_≤ balance s a x) (sym zero) z≤n

accounting-arithmetic : ∀ b d c → d ≤ b → ((b ∸ d) + c) + d ≡ b + c
accounting-arithmetic b d c enough = begin
  ((b ∸ d) + c) + d ≡⟨ ℕ.+-assoc (b ∸ d) c d ⟩
  (b ∸ d) + (c + d) ≡⟨ cong (λ n → (b ∸ d) + n) (ℕ.+-comm c d) ⟩
  (b ∸ d) + (d + c) ≡⟨ sym (ℕ.+-assoc (b ∸ d) d c) ⟩
  ((b ∸ d) + d) + c ≡⟨ cong (_+ c) (ℕ.m∸n+n≡m enough) ⟩
  b + c ∎
  where open ≡-Reasoning

signed-arithmetic : ∀ b b′ d c → b′ + d ≡ b + c → b′ ⊖ b ≡ c ⊖ d
signed-arithmetic b b′ d c equation = begin
  b′ ⊖ b ≡⟨ sym (ℤ.+-cancelˡ-⊖ d b′ b) ⟩
  (d + b′) ⊖ (d + b) ≡⟨ cong (λ n → n ⊖ (d + b)) (ℕ.+-comm d b′) ⟩
  (b′ + d) ⊖ (d + b) ≡⟨ cong (λ n → n ⊖ (d + b)) equation ⟩
  (b + c) ⊖ (d + b) ≡⟨ cong ((b + c) ⊖_) (ℕ.+-comm d b) ⟩
  (b + c) ⊖ (b + d) ≡⟨ ℤ.+-cancelˡ-⊖ b c d ⟩
  c ⊖ d ∎
  where open ≡-Reasoning

fee-arithmetic : ∀ b f → (b + f) ⊖ b ≡ + f
fee-arithmetic b f = begin
  (b + f) ⊖ b ≡⟨ cong ((b + f) ⊖_) (sym (ℕ.+-identityʳ b)) ⟩
  (b + f) ⊖ (b + 0) ≡⟨ ℤ.+-cancelˡ-⊖ b f 0 ⟩
  f ⊖ 0 ≡⟨ ℤ.⊖-≥ z≤n ⟩
  + f ∎
  where open ≡-Reasoning

total-cons-same : ∀ k n ps → total ((k , n) ∷ ps) k ≡ n + total ps k
total-cons-same k n ps with k ≟Key k
... | yes _ = refl
... | no unequal = ⊥-elim (unequal refl)

total-singleton : ∀ k n → total ((k , n) ∷ []) k ≡ n
total-singleton k n = trans (total-cons-same k n []) (ℕ.+-identityʳ n)

self-charges : ∀ i a x n f →
  debit (transaction i (transfer a a x n ∷ []) (fee a x f)) a x ≡ f + n
self-charges i a x n f = trans
  (total-cons-same (a , x) f (((a , x) , n) ∷ []))
  (cong (λ k → f + k) (total-singleton (a , x) n))

self-receipts : ∀ i a x n f →
  credit (transaction i (transfer a a x n ∷ []) (fee a x f)) a x ≡ n
self-receipts i a x n f = total-singleton (a , x) n

module Execution
  (Authorized : State → Transaction → Set)
  (authorized? : ∀ s t → Dec (Authorized s t)) where

  open L.Execution Authorized authorized?

  accepted-valid : finalize s t ≡ accepted s′ → Valid s t
  accepted-valid {s = s} {t = t} eq with decideValid s t
  ... | yes valid = valid
  ... | no _ with eq
  ...   | ()

  accepted-state : finalize s t ≡ accepted s′ → s′ ≡ apply s t
  accepted-state {s = s} {t = t} eq with decideValid s t
  ... | yes _ with eq
  ...   | refl = refl
  accepted-state {s = s} {t = t} eq | no _ with eq
  ...   | ()

  valid-accepted : Valid s t → finalize s t ≡ accepted (apply s t)
  valid-accepted {s = s} {t = t} valid with decideValid s t
  ... | yes _ = refl
  ... | no invalid = ⊥-elim (invalid valid)
  invalid-rejected : ¬ Valid s t → finalize s t ≡ rejected s
  invalid-rejected {s = s} {t = t} invalid with decideValid s t
  ... | yes valid = ⊥-elim (invalid valid)
  ... | no _ = refl

  rejected-invalid : finalize s t ≡ rejected s′ → ¬ Valid s t
  rejected-invalid {s = s} {t = t} eq with decideValid s t
  ... | no invalid = invalid
  ... | yes _ with eq
  ...   | ()

  rejected-state : finalize s t ≡ rejected s′ → s′ ≡ s
  rejected-state {s = s} {t = t} eq with decideValid s t
  ... | no _ with eq
  ...   | refl = refl
  rejected-state {s = s} {t = t} eq | yes _ with eq
  ...   | ()

  accepted-authorized : finalize s t ≡ accepted s′ → Authorized s t
  accepted-authorized eq = proj₁ (proj₂ (accepted-valid eq))

  accepted-funded : finalize s t ≡ accepted s′ → ∀ a x → debit t a x ≤ balance s a x
  accepted-funded {s = s} {t = t} eq =
    funded-at {s = s} {t = t} (proj₂ (proj₂ (accepted-valid eq)))

  insufficient-rejected : ¬ (debit t a x ≤ balance s a x) → finalize s t ≡ rejected s
  insufficient-rejected {t = t} {a = a} {x = x} {s = s} insufficient =
    invalid-rejected (λ v → insufficient (funded-at {s = s} {t = t} (proj₂ (proj₂ v)) a x))

  duplicate-rejected : txId t ∈ acceptedIds s → finalize s t ≡ rejected s
  duplicate-rejected seen = invalid-rejected (λ v → proj₁ v seen)

  unauthorized-rejected : ¬ Authorized s t → finalize s t ≡ rejected s
  unauthorized-rejected denied = invalid-rejected (λ v → denied (proj₁ (proj₂ v)))

  accepted-accounting : finalize s t ≡ accepted s′ → ∀ a x →
    balance s′ a x + debit t a x ≡ balance s a x + credit t a x
  accepted-accounting {s = s} {t = t} {s′ = s′} eq a x = trans
    (cong (λ q → balance q a x + debit t a x) (accepted-state eq))
    (accounting-arithmetic (balance s a x) (debit t a x) (credit t a x)
      (accepted-funded eq a x))

  accepted-signed-effect : finalize s t ≡ accepted s′ → ∀ a x →
    balance s′ a x ⊖ balance s a x ≡ credit t a x ⊖ debit t a x
  accepted-signed-effect {s = s} {t = t} {s′ = s′} eq a x =
    signed-arithmetic (balance s a x) (balance s′ a x) (debit t a x) (credit t a x)
      (accepted-accounting eq a x)

  accepted-fees : finalize s t ≡ accepted s′ → ∀ x → fees s′ x ≡ fees s x + feeFor t x
  accepted-fees eq x = cong (λ q → fees q x) (accepted-state eq)

  accepted-signed-fees : finalize s t ≡ accepted s′ → ∀ x →
    fees s′ x ⊖ fees s x ≡ + feeFor t x
  accepted-signed-fees {s = s} {t = t} eq x = trans
    (cong (_⊖ fees s x) (accepted-fees eq x)) (fee-arithmetic (fees s x) (feeFor t x))

  irrelevant-balance : finalize s t ≡ accepted s′ →
    debit t a x ≡ 0 → credit t a x ≡ 0 → balance s′ a x ≡ balance s a x
  irrelevant-balance {s = s} {t = t} {s′ = s′} {a = a} {x = x} eq no-debit no-credit = trans
    (cong (λ q → balance q a x) (accepted-state eq)) unchanged
    where
    unchanged : (balance s a x ∸ debit t a x) + credit t a x ≡ balance s a x
    unchanged rewrite no-debit | no-credit = ℕ.+-identityʳ (balance s a x)
  irrelevant-fees : finalize s t ≡ accepted s′ → feeFor t x ≡ 0 → fees s′ x ≡ fees s x
  irrelevant-fees {s = s} {x = x} eq no-fee = trans (accepted-fees eq x)
    (trans (cong (λ n → fees s x + n) no-fee) (ℕ.+-identityʳ (fees s x)))

  accepted-id : finalize s t ≡ accepted s′ → txId t ∈ acceptedIds s′
  accepted-id {t = t} eq = subst (λ q → txId t ∈ acceptedIds q)
    (sym (accepted-state eq)) (here refl)

  accepted-fresh : finalize s t ≡ accepted s′ → ¬ (txId t ∈ acceptedIds s)
  accepted-fresh eq = proj₁ (accepted-valid eq)

  step-preserves-id : i ∈ acceptedIds s → i ∈ acceptedIds (resultState (finalize s t))
  step-preserves-id {s = s} {t = t} seen with decideValid s t
  ... | yes _ = there seen
  ... | no _ = seen

  history-preserves-id : Finalized s s′ → i ∈ acceptedIds s → i ∈ acceptedIds s′
  history-preserves-id done seen = seen
  history-preserves-id (step t rest) seen = history-preserves-id rest (step-preserves-id seen)

  accepted-id-persists : finalize s t ≡ accepted s₁ → Finalized s₁ s₂ → txId t ∈ acceptedIds s₂
  accepted-id-persists eq history = history-preserves-id history (accepted-id eq)

  historical-no-replay : finalize s t ≡ accepted s₁ → Finalized s₁ s₂ →
    txId u ≡ txId t → finalize s₂ u ≡ rejected s₂
  historical-no-replay {s₂ = s₂} eq history same = duplicate-rejected
    (subst (_∈ acceptedIds s₂) (sym same) (accepted-id-persists eq history))

  self-transfer-gross-funding : ∀ {s s′} i a x n f →
    finalize s (transaction i (transfer a a x n ∷ []) (fee a x f)) ≡ accepted s′ →
    f + n ≤ balance s a x
  self-transfer-gross-funding i a x n f eq =
    subst (_≤ _) (self-charges i a x n f) (accepted-funded eq a x)

  self-transfer-net-fee : ∀ {s s′} i a x n f →
    finalize s (transaction i (transfer a a x n ∷ []) (fee a x f)) ≡ accepted s′ →
    balance s′ a x + f ≡ balance s a x
  self-transfer-net-fee {s} {s′} i a x n f eq = ℕ.+-cancelʳ-≡ n _ _ equation
    where
    accounting : balance s′ a x + (f + n) ≡ balance s a x + n
    accounting = subst
      (λ d → balance s′ a x + d ≡ balance s a x + n)
      (self-charges i a x n f)
      (trans (accepted-accounting eq a x) (cong (λ k → balance s a x + k) (self-receipts i a x n f)))
    equation : (balance s′ a x + f) + n ≡ balance s a x + n
    equation = trans (ℕ.+-assoc (balance s′ a x) f n) accounting

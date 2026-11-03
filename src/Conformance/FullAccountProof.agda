{-# OPTIONS --safe --without-K #-}

module Conformance.FullAccountProof where

open import Data.Bool.Base
open import Data.Nat.Base hiding (equal)
open import Data.Product.Base
open import Data.Maybe.Base using (nothing; just)
import Conformance.FullAccount as Model
import Passport.Account as Account
open import Relation.Binary.PropositionalEquality
open import Conformance.FullAccountTypes
open import Conformance.FullAccountLayouts
import Conformance.FullAccountGrant as Grant

private
  next-distinct : ∀ n → (n ≡ᵇ suc n) ≡ false
  next-distinct zero = refl
  next-distinct (suc n) = next-distinct n

old-epoch-grant-rejected : ∀ P s g n →
  grantEpoch g ≡ nat n → lookupCell "device_epoch" (ledger s) ≡ just (nat (suc n)) →
  ∃ λ e → Grant.validateGrantRecord P g s ≡ rejected e
old-epoch-grant-rejected P s g n old current with flag (grantActive g)
... | false = assertion "grant revoked" , refl
... | true rewrite old | current | next-distinct n =
  assertion "grant epoch stale" , refl

old-generation-grant-rejected : ∀ P s g n →
  grantGeneration g ≡ nat n → lookupCell "grant_generation" (ledger s) ≡ just (nat (suc n)) →
  ∃ λ e → Grant.validateGrantRecord P g s ≡ rejected e
old-generation-grant-rejected P s g n old current with flag (grantActive g)
... | false = assertion "grant revoked" , refl
... | true with lookupCell "device_epoch" (ledger s)
...   | nothing = decoding "missing ledger field: device_epoch" , refl
...   | just epoch with equal (grantEpoch g) epoch
...     | false = assertion "grant epoch stale" , refl
...     | true rewrite old | current | next-distinct n =
  assertion "grant generation stale" , refl

rejection-is-atomic : ∀ P ctx call before e →
  Model.dispatch P ctx call before ≡ rejected e →
  Account.step P ctx call before ≡ (Account.reverted e , before)
rejection-is-atomic P ctx call before e rejected-call =
  cong (Account.transaction before) rejected-call

transition-deterministic : ∀ P ctx call before observation₁ observation₂ after₁ after₂ →
  Account.Transition P ctx call before observation₁ after₁ →
  Account.Transition P ctx call before observation₂ after₂ →
  (observation₁ , after₁) ≡ (observation₂ , after₂)
transition-deterministic P ctx call before observation₁ observation₂ after₁ after₂ left right =
  trans (sym (Account.execution left)) (Account.execution right)

{-# OPTIONS --safe --without-K #-}

-- Grant-authenticated withdrawal security, read from the actual evaluator.
-- Predicates: Conformance.FullAccountGrantSecurity. These are local contract
-- facts about one accepted grantCall; they make no claim that a signature or
-- commitment is unforgeable, and none that a transaction was admitted.

open import Conformance.FullAccountTypes

module Conformance.FullAccountGrantSecurityProperties (P : Primitives) where

open import Conformance.FullAccountBody P
open import Conformance.FullAccountExecution using (Run)
open import Conformance.FullAccountGrant P
open import Conformance.FullAccountGrantSecurity P
open import Conformance.FullAccountLayouts
open import Data.Bool.Base using (true)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base hiding (equal)
open import Data.Product.Base using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Conformance.FullAccountGrantSecurityProof P as Proof

-- Any accepted grantCall, for every curve and operation, ran its full guard
-- sequence in the before-state s: live record, scope, caller, object, caps,
-- spent opening, recipient pin, coin bound, operation challenge, signature
-- verification, and the settlement that the withdrawal body then runs after.
grant-call-evidence : ∀ c op ctx ga xs {s v t es} →
  grantCall c op ctx ga xs s ≡ accepted v t es → GrantCallEvidence c op ctx ga xs s
grant-call-evidence = Proof.grant-call-evidence

-- After settlement the grants map holds the updated record under the grant id.
settled-grant : ∀ {ga s identifier g spent settled} (S : Settlement ga s identifier g spent settled) →
  lookupMap identifier (fields (cell "grants" settled)) ≡
    just (settledGrant g (suc (number (grantNonce g))) (Settlement.commitment S))
settled-grant = Proof.settled-grant

-- For a record with its active flag set, settlement changes only the nonce
-- and spent commitment; epoch, generation, issue time, window, activity and
-- scope are kept.
settled-record : ∀ g nonce commitment → grantActive g ≡ bool true →
  SettledRecord g nonce commitment (settledGrant g nonce commitment)
settled-record = Proof.settled-record

-- For the three runtime withdrawals, the accepted call's final state stores
-- that settled record under the grant id: neither the withdrawal body nor the
-- change-entry append writes the grants cell.
grant-final-state : ∀ c op ctx ga xs → Withdrawal op → ∀ {s v t es} →
  grantCall c op ctx ga xs s ≡ accepted v t es → GrantFinalState c op ctx ga xs s t
grant-final-state = Proof.grant-final-state

-- Cumulative cap for one stored opening. Given explicit agreement of the
-- call's spent opening with a claimed opening (salt′, total) of the record's
-- commitment — a premise for that pair only, not proven SHA-256 binding —
-- the salt and previous spend are that opening's, the new spend is
-- total + amount, and it is within the scope cap. Settlement commits to the
-- new spend under the same salt.
cumulative-spend : ∀ {c op ctx ga xs s} (E : GrantCallEvidence c op ctx ga xs s) {salt′ total} →
  SpentOpeningsAgree (salt ga) (spentPrev ga) salt′ total →
  Run (spentCommit salt′ total) s (grantSpentCommitment (grantRecord E)) s →
  salt ga ≡ salt′ × spentPrev ga ≡ total × spent E ≡ total + amountOf op xs ×
  total + amountOf op xs ≤ number (scopeCap (grantScope (grantRecord E)))
cumulative-spend = Proof.cumulative-spend

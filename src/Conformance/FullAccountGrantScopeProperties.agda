{-# OPTIONS --safe --without-K #-}

-- Semantic grant scope, for every curve and each runtime withdrawal.
-- Read IntendedPolicy, IntendedGrant, RelevantOpeningsAgree and SemanticScope
-- in FullAccountGrantScope: policy openings are witnesses for the stored
-- digests; pair-local opening agreement is an explicit cryptographic premise.
-- Zero caller commitment means unrestricted, not a pinned zero address;
-- recipient kind zero means unrestricted, not a promise about the recipient.
-- The coin maximum bounds the whole held shielded coin. This is a local
-- source-runtime result, not ledger admission or native hash/signature soundness.
-- Proofs: FullAccountGrantScopeProof; source guards: FullAccountGrantSecurity.
open import Conformance.FullAccountTypes

module Conformance.FullAccountGrantScopeProperties (P : Primitives) where

import Conformance.FullAccount as Account
open import Conformance.FullAccountGrant P
open import Conformance.FullAccountGrantScope P
open import Conformance.FullAccountGrantSecurity P
open import Data.List.Base using (take)
open import Data.Product.Base
open import Relation.Binary.PropositionalEquality
import Conformance.FullAccountGrantScopeProof P as Proof

module Runtime = Account.AccountSemantics P

-- The typed runtime entry point includes ABI, context, held-coin and state
-- validation. All three withdrawals and all three schemes are quantified.
runtime-grant-scope : ∀ c op ctx xs → Withdrawal op → ∀ {s v t es p} →
  Runtime.checked (Runtime.grant c op) ctx xs s ≡ accepted v t es →
  IntendedGrant c ctx (runtimeGrantAuth c op xs) s p →
  RelevantOpeningsAgree op ctx (runtimeGrantAuth c op xs) (take 3 xs) p →
  GrantCallEvidence c op ctx (runtimeGrantAuth c op xs) (take 3 xs) s ×
  SemanticScope op ctx (runtimeGrantAuth c op xs) (take 3 xs) p
runtime-grant-scope = Proof.runtime-grant-scope

-- Useful conjunction: all operational guard/settlement evidence remains
-- available, together with the intended asset, caller, recipient and coin bound.
-- The witness is connected to the actual record by deterministic id and lookup
-- executions, not by assuming equality of a final scope and the intended policy.
accepted-grant-scope : ∀ c op ctx ga xs {s v t es p} →
  grantCall c op ctx ga xs s ≡ accepted v t es → IntendedGrant c ctx ga s p →
  RelevantOpeningsAgree op ctx ga xs p →
  GrantCallEvidence c op ctx ga xs s × SemanticScope op ctx ga xs p
accepted-grant-scope = Proof.accepted-grant-scope

scope-enforced : ∀ {op ctx ga xs s g spent p} →
  ScopeAdmitted op ctx ga xs (grantCoin op ctx) s g spent →
  CoinAdmitted op ga (grantCoin op ctx) s → PolicyCommitted p s g →
  RelevantOpeningsAgree op ctx ga xs p → SemanticScope op ctx ga xs p
scope-enforced = Proof.scope-enforced

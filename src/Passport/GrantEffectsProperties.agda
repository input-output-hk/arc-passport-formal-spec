{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

-- issue-result and revoke-result extract the installed record and map update;
-- spend-mutation extracts the withdrawal's whole-map settlement update.
-- execute-effect classifies every public runtime arm as preserving, issuing,
-- revoking, clearing or spending grants (see GrantEffects.GrantEffect).
-- GrantSecurityProperties.grant-final-state instead exposes the settled record's
-- lookup and fields; SpendMutation also fixes the surrounding map.
-- RuntimeEntrypoint excludes constructor and internal-only grant arms.
module Passport.GrantEffectsProperties (P : Primitives) where

import Conformance.FullAccount as Model
open import Conformance.FullAccountBody P
open import Conformance.FullAccountExecution
open import Conformance.FullAccountGrant P
open import Conformance.FullAccountGrantSecurity P
open import Passport.GrantEffects P
import Passport.GrantEffectsProof P as Proof

issue-result : ∀ xs {s v t} → Run (issue xs) s v t → IssueResult xs s t
issue-result = Proof.issue-result

revoke-result : ∀ id {s v t} → Run (revoke id) s v t → RevokeResult id s t
revoke-result = Proof.revoke-result

spend-mutation : ∀ c op ctx ga xs → Withdrawal op → ∀ {s v t} →
  Run (grantCall c op ctx ga xs) s v t → SpendMutation c op ctx ga xs s t
spend-mutation = Proof.spend-mutation

execute-effect : ∀ {e} → RuntimeEntrypoint e → ∀ ctx xs {s v t} →
  Run (Model.AccountSemantics.execute P e ctx xs) s v t → GrantEffect s t
execute-effect = Proof.execute-effect

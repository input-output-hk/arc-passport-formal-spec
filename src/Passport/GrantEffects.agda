{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

-- Source-derived grants-map mutations, shared by spending and revocation.
module Passport.GrantEffects (P : Primitives) where

import Conformance.FullAccount as Model

open import Conformance.FullAccountBody P
open import Conformance.FullAccountCrypto P
open import Conformance.FullAccountExecution
open import Conformance.FullAccountGrant P
open import Conformance.FullAccountGrantSecurity P
open import Conformance.FullAccountLayouts
open import Data.Bool.Base using (true; false)
open import Data.List.Base using (List; []; _∷_; _++_; take)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base hiding (equal)
open import Relation.Binary.PropositionalEquality using (_≡_)

record Issuance : Set where
  constructor issuance
  field identifier epoch generation issuedAt : Value

issuanceOf : Value → Value → Issuance
issuanceOf id g = issuance id (grantEpoch g) (grantGeneration g) (grantIssuedAt g)

issueRecord : List Value → Value → Value → Value → Value → Value → Value → Value → Value
issueRecord xs epoch generation issued spent object rp caller =
  tuple (epoch ∷ generation ∷ issued ∷ nat 0 ∷ spent ∷ nat 0 ∷ nat 0 ∷ bool true ∷
    tuple (A.withdrawUnshielded ∷ A.withdrawShielded ∷ A.withdrawToContract ∷ A.readFlag ∷
      object ∷ A.perCallCap ∷ A.cap ∷ A.expiresAt ∷ rp ∷ A.readKeyHash ∷ nat 0 ∷ nat 0 ∷ caller ∷ []) ∷ [])
  where module A = IssueArguments xs

record IssueResult (xs : List Value) (before after : State) : Set where
  field epoch generation issued spent object rp caller : Value
        epochRead : lookupCell "device_epoch" (ledger before) ≡ just epoch
        generationRead : lookupCell "grant_generation" (ledger before) ≡ just generation
        issuedRead : lookupCell "auth_nonce" (ledger before) ≡ just issued
        zeroOpening : Run (spentCommit (IssueArguments.salt xs) 0) before spent before
        installed : cell "grants" after ≡ tuple (insertMap (IssueArguments.id xs)
          (issueRecord xs epoch generation issued spent object rp caller) (fields (cell "grants" before)))

issuedRecord : ∀ {xs s t} → IssueResult xs s t → Value
issuedRecord {xs} r = issueRecord xs (IssueResult.epoch r) (IssueResult.generation r)
  (IssueResult.issued r) (IssueResult.spent r) (IssueResult.object r) (IssueResult.rp r) (IssueResult.caller r)

revokedRecord : Value → Value
revokedRecord old = tuple (take 7 (fields old) ++ (bool false ∷ grantScope old ∷ []))

record RevokeResult (identifier : Value) (before after : State) : Set where
  field old : Value
        recorded : lookupMap identifier (fields (cell "grants" before)) ≡ just old
        active : grantActive old ≡ bool true
        installed : cell "grants" after ≡
          tuple (insertMap identifier (revokedRecord old) (fields (cell "grants" before)))

record SpendMutation (c : Curve) (op : Operation) (ctx : Context) (ga : GrantAuth)
    (xs : List Value) (before after : State) : Set where
  field evidence : GrantCallEvidence c op ctx ga xs before
        installed : cell "grants" after ≡ tuple (insertMap (GrantCallEvidence.identifier evidence)
          (settledGrant (GrantCallEvidence.grantRecord evidence)
            (suc (number (grantNonce (GrantCallEvidence.grantRecord evidence))))
            (Settlement.commitment (GrantCallEvidence.settlement evidence)))
          (fields (cell "grants" before)))

data GrantEffect (before after : State) : Set where
  kept : cell "grants" after ≡ cell "grants" before → GrantEffect before after
  grantIssued : ∀ xs source → cell "grants" source ≡ cell "grants" before →
    IssueResult xs source after → GrantEffect before after
  grantRevoked : ∀ identifier source → cell "grants" source ≡ cell "grants" before →
    RevokeResult identifier source after → GrantEffect before after
  cleared : cell "grants" after ≡ tuple [] → GrantEffect before after
  grantSpent : ∀ c op ctx ga xs → Withdrawal op → SpendMutation c op ctx ga xs before after →
    GrantEffect before after

open Model.AccountSemantics P using (Entrypoint; activation; device; grant;
  depositPublic; depositPrivate; submitRecovery; finaliseRecovery)

data RuntimeEntrypoint : Entrypoint → Set where
  activationEntry : ∀ c → RuntimeEntrypoint (activation c)
  deviceEntry : ∀ c op → RuntimeEntrypoint (device c op)
  grantEntry : ∀ c op → Withdrawal op → RuntimeEntrypoint (grant c op)
  publicDepositEntry : RuntimeEntrypoint depositPublic
  privateDepositEntry : RuntimeEntrypoint depositPrivate
  submissionEntry : RuntimeEntrypoint submitRecovery
  finalisationEntry : RuntimeEntrypoint finaliseRecovery

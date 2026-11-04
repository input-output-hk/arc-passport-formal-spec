{-# OPTIONS --safe --without-K #-}

-- Intended meanings of the stored commitments, separate from their digests.
-- Reading route: FullAccountGrantScopeProperties → this module →
-- FullAccountGrantSecurity (ScopeAdmitted, RecipientAdmitted, CoinAdmitted).
-- The opening-agreement premises concern only the compared openings, not
-- global hash injectivity. Native typed encoding and hash binding are external.
open import Conformance.FullAccountTypes

module Conformance.FullAccountGrantScope (P : Primitives) where

import Conformance.FullAccount as Account
open import Conformance.FullAccountBody P
open import Conformance.FullAccountExecution
open import Conformance.FullAccountGrant P
open import Conformance.FullAccountGrantSecurity P
open import Conformance.FullAccountLayouts
open import Data.Bool.Base hiding (_≤_)
open import Data.List.Base using (List; []; _∷_; drop)
open import Data.Nat.Base hiding (equal)
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

-- The runtime ABI splits operation arguments from the grant opening; the
-- shielded twins additionally carry the change entry and encryption key.
runtimeGrantAuth : Curve → Operation → List Value → GrantAuth
runtimeGrantAuth c withdrawUnshielded xs = Account.AccountSemantics.parseGrant P c (drop 3 xs) none none
runtimeGrantAuth c op xs = Account.AccountSemantics.parseGrant P c (drop 5 xs) (get 3 xs) (get 4 xs)

data CallerPolicy : Set where
  unrestricted : CallerPolicy
  pinned : Value → CallerPolicy

record IntendedPolicy : Set where
  constructor intendedPolicy
  field policySalt asset : Value
        recipientTag : ℕ
        recipientAddress : Value
        coinMaximum : ℕ
        callerPolicy : CallerPolicy
open IntendedPolicy public

callAsset : Operation → Context → List Value → Value
callAsset op ctx xs = if shielded op then at 1 (grantCoin op ctx) else get 0 xs

-- Both maximums are encoded as nat, as grantCall does after ABI normalization.
-- Recipient kind agreement is numeric: policy tags use the source's number.
ObjectOpeningsAgree : Value → Value → Value → Value → ℕ → IntendedPolicy → Set
ObjectOpeningsAgree callSalt color kind recipient maximum p = ∀ {v s₁ s₂} →
  Run (objectCommit callSalt color kind recipient (nat maximum)) s₁ v s₁ →
  Run (objectCommit (policySalt p) (asset p) (nat (recipientTag p))
    (recipientAddress p) (nat (coinMaximum p))) s₂ v s₂ →
  callSalt ≡ policySalt p × color ≡ asset p × number kind ≡ recipientTag p ×
  recipient ≡ recipientAddress p × maximum ≡ coinMaximum p

CallerOpeningsAgree : Value → Value → Value → Value → Set
CallerOpeningsAgree callSalt address intendedSalt intendedAddress = ∀ {v s₁ s₂} →
  Run (callerCommit callSalt (some address)) s₁ v s₁ →
  Run (callerCommit intendedSalt (some intendedAddress)) s₂ v s₂ →
  callSalt ≡ intendedSalt × address ≡ intendedAddress

CallerCommitted : IntendedPolicy → State → Value → Set
CallerCommitted p s scope with callerPolicy p
... | unrestricted = scopeCallerCommitment scope ≡ zero32
... | pinned address = Run (callerCommit (policySalt p) (some address)) s
  (scopeCallerCommitment scope) s

record PolicyCommitted (p : IntendedPolicy) (s : State) (g : Value) : Set where
  field objectOpening : Run (objectCommit (policySalt p) (asset p) (nat (recipientTag p))
          (recipientAddress p) (nat (coinMaximum p))) s (scopeObjectCommitment (grantScope g)) s
        callerOpening : CallerCommitted p s (grantScope g)

-- A policy witness is attached to the actual lookup, not an arbitrary record
-- whose final scope is assumed equal to the intended one.
record IntendedGrant (c : Curve) (ctx : Context) (ga : GrantAuth)
    (s : State) (p : IntendedPolicy) : Set where
  field grantIdentifier storedRecord : Value
        identifierRun : Run (grantId c ctx ga) s grantIdentifier s
        recordRun : Run (lookup "grants" grantIdentifier) s storedRecord s
        committedPolicy : PolicyCommitted p s storedRecord

-- Only an address actually observed as the contract caller needs agreement.
-- The unrestricted branch has no caller-opening premise and no caller promise.
CallerAgreement : Context → GrantAuth → IntendedPolicy → Set
CallerAgreement ctx ga p with callerPolicy p
... | unrestricted = ⊤
... | pinned intended = ∀ address →
  caller ctx ≡ some (tuple (bool true ∷ address ∷ [])) →
  CallerOpeningsAgree (salt ga) address (policySalt p) intended

record RelevantOpeningsAgree (op : Operation) (ctx : Context) (ga : GrantAuth)
    (xs : List Value) (p : IntendedPolicy) : Set where
  field objectAgreement : ObjectOpeningsAgree (salt ga) (callAsset op ctx xs)
          (recipientKind ga) (pinnedRecipient ga) (maxCoinValue ga) p
        callerAgreement : CallerAgreement ctx ga p

CallerEnforced : Context → CallerPolicy → Set
CallerEnforced ctx unrestricted = ⊤
CallerEnforced ctx (pinned address) = caller ctx ≡ some (tuple (bool true ∷ address ∷ []))

RecipientEnforced : Operation → List Value → IntendedPolicy → Set
RecipientEnforced op xs p = recipientTag p ≡ 0 ⊎
  (recipientTag p ≡ thisKind op × recipientAddress p ≡ recipientOf op xs)

-- The whole held coin, not just the withdrawal amount, is bounded when shielded.
record SemanticScope (op : Operation) (ctx : Context) (ga : GrantAuth)
    (xs : List Value) (p : IntendedPolicy) : Set where
  field saltBound : salt ga ≡ policySalt p
        assetBound : callAsset op ctx xs ≡ asset p
        recipientKindBound : number (recipientKind ga) ≡ recipientTag p
        recipientAddressBound : pinnedRecipient ga ≡ recipientAddress p
        maximumBound : maxCoinValue ga ≡ coinMaximum p
        callerEnforced : CallerEnforced ctx (callerPolicy p)
        recipientEnforced : RecipientEnforced op xs p
        shieldedCoinBound : shielded op ≡ true → number (at 2 (grantCoin op ctx)) ≤ coinMaximum p

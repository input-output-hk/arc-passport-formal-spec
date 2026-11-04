{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

module Conformance.FullAccountGrantScopeProof (P : Primitives) where

import Conformance.FullAccount as Account
open import Conformance.FullAccountBody P
open import Conformance.FullAccountCrypto P
open import Conformance.FullAccountExecution
open import Conformance.FullAccountGrant P
open import Conformance.FullAccountGrantScope P
open import Conformance.FullAccountGrantSecurity P
open import Conformance.FullAccountLayouts
open import Data.Bool.Base hiding (_≤_)
open import Data.Empty
open import Data.List.Base using (List; []; _∷_; take)
open import Data.Nat.Base hiding (equal)
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
import Conformance.FullAccountGrantSecurityProof P as Security

private
  variable
    c : Curve
    op : Operation
    ctx : Context
    ga : GrantAuth
    xs : List Value
    s : State
    g : Value
    total : ℕ
    p : IntendedPolicy

  answer-injective : ∀ {A : Set} {x y : A} {s t es fs} →
    accepted x s es ≡ accepted y t fs → x ≡ y
  answer-injective refl = refl

  same-answer : ∀ {A : Set} {m : M A} {s x y t u} → Run m s x t → Run m s y u → x ≡ y
  same-answer (run _ first) (run _ second) = answer-injective (trans (sym first) second)

  returned-answer : ∀ {A : Set} {x y : A} {s t} → Run (return x) s y t → x ≡ y
  returned-answer (run _ refl) = refl

  false-assert : ∀ {message s x t} → Run (assert false message) s x t → ⊥
  false-assert (run _ ())

  rejected≠accepted : ∀ {A : Set} {e : Error} {v : A} {t es} →
    rejected e ≡ accepted v t es → ⊥
  rejected≠accepted ()

-- callerCommit rejects zero for a present caller. This distinguishes the
-- unrestricted sentinel without assuming separation as a cryptographic axiom.
caller-commit-nonzero : ∀ salt′ address {s v} →
  Run (callerCommit salt′ (some address)) s v s → v ≢ zero32
caller-commit-nonzero salt′ address r same
  with then (hash (b32 (pad 32 "midnight:account:grant:caller:v1") ∷ b32 salt′ ∷ contract address ∷ [])) r
... | digest , t , hashed , rest
  with then (assert (not (equal digest zero32)) "reserved caller commitment") rest
... | _ , u , checked , returned with trans (returned-answer returned) same
... | refl = false-assert checked

caller-enforced : CallerAdmitted ctx ga s (grantScope g) →
  CallerCommitted p s (grantScope g) → CallerAgreement ctx ga p → CallerEnforced ctx (callerPolicy p)
caller-enforced {p = p} admitted committed agree with callerPolicy p
... | unrestricted = tt
... | pinned intended with admitted
...   | inj₁ isZero = ⊥-elim (caller-commit-nonzero (policySalt p) intended committed isZero)
...   | inj₂ (address , observed , opened) =
  trans observed (cong (λ a → some (tuple (bool true ∷ a ∷ [])))
    (proj₂ (agree address observed opened committed)))

recipient-enforced : RecipientAdmitted op ga xs → number (recipientKind ga) ≡ recipientTag p →
  pinnedRecipient ga ≡ recipientAddress p → RecipientEnforced op xs p
recipient-enforced (inj₁ unpinned) kind address = inj₁ (trans (sym kind) unpinned)
recipient-enforced (inj₂ (tag , pin)) kind address = inj₂ (trans (sym kind) tag , trans (sym address) pin)

coin-bound : CoinAdmitted op ga (grantCoin op ctx) s → maxCoinValue ga ≡ coinMaximum p →
  shielded op ≡ true → number (at 2 (grantCoin op ctx)) ≤ coinMaximum p
coin-bound (inj₁ unshielded) maximum shielded with trans (sym unshielded) shielded
... | ()
coin-bound (inj₂ (_ , bound , encryption)) refl shielded = bound

scope-enforced : ScopeAdmitted op ctx ga xs (grantCoin op ctx) s g total →
  CoinAdmitted op ga (grantCoin op ctx) s → PolicyCommitted p s g →
  RelevantOpeningsAgree op ctx ga xs p → SemanticScope op ctx ga xs p
scope-enforced {op = op} {ctx = ctx} {ga = ga} {xs = xs} {s = s} {g = g} {p = p}
    scoped coin committed agreement
  with RelevantOpeningsAgree.objectAgreement agreement
    (ScopeAdmitted.objectCommitted scoped) (PolicyCommitted.objectOpening committed)
... | sameSalt , sameAsset , sameKind , sameRecipient , sameMaximum = record
  { saltBound = sameSalt
  ; assetBound = sameAsset
  ; recipientKindBound = sameKind
  ; recipientAddressBound = sameRecipient
  ; maximumBound = sameMaximum
  ; callerEnforced = caller-enforced {g = g} (ScopeAdmitted.callerAdmitted scoped)
      (PolicyCommitted.callerOpening committed) (RelevantOpeningsAgree.callerAgreement agreement)
  ; recipientEnforced = recipient-enforced {op = op} {ga = ga} {xs = xs} {p = p}
      (ScopeAdmitted.recipientAdmitted scoped) sameKind sameRecipient
  ; shieldedCoinBound = coin-bound {op = op} {ga = ga} {ctx = ctx} {s = s} {p = p} coin sameMaximum
  }

-- Determinism connects the intended witness to the record actually read.
evidence-scope : (E : GrantCallEvidence c op ctx ga xs s) → IntendedGrant c ctx ga s p →
  RelevantOpeningsAgree op ctx ga xs p → SemanticScope op ctx ga xs p
evidence-scope E intended agreement
  with same-answer (identified E) (IntendedGrant.identifierRun intended)
... | refl with same-answer (recorded E) (IntendedGrant.recordRun intended)
... | refl = scope-enforced (scoped E) (coinAdmitted E) (IntendedGrant.committedPolicy intended) agreement

accepted-grant-scope : ∀ c op ctx ga xs {s v t es p} →
  grantCall c op ctx ga xs s ≡ accepted v t es → IntendedGrant c ctx ga s p →
  RelevantOpeningsAgree op ctx ga xs p →
  GrantCallEvidence c op ctx ga xs s × SemanticScope op ctx ga xs p
accepted-grant-scope c op ctx ga xs execution intended agreement =
  E , evidence-scope E intended agreement
  where E = Security.grant-call-evidence c op ctx ga xs execution

module Runtime = Account.AccountSemantics P

private
  checked-grant-run : ∀ c op ctx xs {s v t es} →
    Runtime.checked (Runtime.grant c op) ctx xs s ≡ accepted v t es →
    Runtime.execute (Runtime.grant c op) ctx xs s ≡ accepted v t es
  checked-grant-run c op ctx xs {s} execution
    with Account.validArguments (Runtime.schema (Runtime.grant c op)) xs
  ... | false = ⊥-elim (rejected≠accepted execution)
  ... | true with Account.validContext ctx
  ...   | false = ⊥-elim (rejected≠accepted execution)
  ...   | true with Runtime.needsCoin (Runtime.grant c op) ∧
                    not (Account.valid Account.qualifiedCoinT (heldCoin ctx))
  ...     | true = ⊥-elim (rejected≠accepted execution)
  ...     | false with Account.validState s
  ...       | false = ⊥-elim (rejected≠accepted execution)
  ...       | true = execution

  execute-grant-run : ∀ c op ctx xs → Withdrawal op → ∀ {s v t es} →
    Runtime.execute (Runtime.grant c op) ctx xs s ≡ accepted v t es →
    grantCall c op ctx (runtimeGrantAuth c op xs) (take 3 xs) s ≡ accepted v t es
  execute-grant-run c .withdrawUnshielded ctx xs unshieldedWithdrawal execution = execution
  execute-grant-run c .withdrawShielded ctx xs shieldedWithdrawal execution = execution
  execute-grant-run c .withdrawToContract ctx xs contractWithdrawal execution = execution

runtime-grant-scope : ∀ c op ctx xs → Withdrawal op → ∀ {s v t es p} →
  Runtime.checked (Runtime.grant c op) ctx xs s ≡ accepted v t es →
  IntendedGrant c ctx (runtimeGrantAuth c op xs) s p →
  RelevantOpeningsAgree op ctx (runtimeGrantAuth c op xs) (take 3 xs) p →
  GrantCallEvidence c op ctx (runtimeGrantAuth c op xs) (take 3 xs) s ×
  SemanticScope op ctx (runtimeGrantAuth c op xs) (take 3 xs) p
runtime-grant-scope c op ctx xs withdrawal execution =
  accepted-grant-scope c op ctx (runtimeGrantAuth c op xs) (take 3 xs)
    (execute-grant-run c op ctx xs withdrawal (checked-grant-run c op ctx xs execution))

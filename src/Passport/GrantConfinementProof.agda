{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

module Passport.GrantConfinementProof (P : Primitives) (address : Value) where

import Conformance.FullAccount as Model
open import Conformance.FullAccountBody P
open import Conformance.FullAccountCrypto P
open import Conformance.FullAccountDeviceSecurity P using (Preserves)
import Conformance.FullAccountDeviceSecurityProof P as Device
open import Conformance.FullAccountExecution using (Run; run; then)
open import Conformance.FullAccountGrant P
open import Conformance.FullAccountGrantSecurity P
import Conformance.FullAccountGrantSecurityProof P as Grant
open import Conformance.FullAccountLayouts
open import Data.Bool.Base using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.List.Base using (List; []; _∷_; take)
import Data.List.Relation.Unary.All as All
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.PropositionalEquality
import Passport.Account as Account
open import Passport.AccountLifecycle P hiding (run)
open import Passport.GrantConfinement P address
open import Passport.GrantEffects P
import Passport.GrantEffectsProof P as Effects
open import Passport.GrantSpending P using (parseGrantAuth)

private
  settlement-frame : ∀ k → Protected k → ∀ {ga s id g spent t} → Settlement ga s id g spent t →
    lookupCell k (ledger t) ≡ lookupCell k (ledger s)
  settlement-frame k p {s = s} {id} {g} S = trans
    (Device.bump-preserves "round" 64 (Protected.notRound p) (Settlement.roundAdvanced S))
    (Device.lookup-insert-other k "grants" _ (ledger s) (Protected.notGrants p))

-- All pre-settlement computations are proved state-free by their source-run
-- decompositions; only the actual insert/bump/body/change tail need a frame.
source-frame : ∀ c op ctx ga xs → Withdrawal op → ∀ {s v t} →
  Run (grantCall c op ctx ga xs) s v t → Frame s t
source-frame c op ctx ga xs withdrawal r k p
  with then (if shielded op then held ctx (get 1 xs) else return none) r
... | coin , _ , coinRun , r₁ with Grant.coin-run op ctx xs coinRun
... | refl , refl with then (authenticateGrant c ctx ga) r₁
... | (id , g) , _ , authenticated , r₂ with Grant.authenticate-run c ctx ga authenticated
... | refl , identified , recorded , live with then (scopeCheck op ctx ga xs (grantCoin op ctx) g) r₂
... | spent , _ , scopedRun , r₃ with Grant.scope-run op ctx ga xs (grantCoin op ctx) g scopedRun
... | refl , scoped with then (Grant.coinCheck op ga (grantCoin op ctx)) r₃
... | _ , _ , coinGuard , r₄ with Grant.coinCheck-run op ga (grantCoin op ctx) coinGuard
... | refl , admitted with then (challenge c true (operationName op) ctx (authorisation ga)
  (grantChallengeAtoms op xs (grantCoin op ctx) ga id g) (number (grantNonce g))) r₄
... | h , _ , challengeRun , r₅ with Grant.challenge-run c true (operationName op) ctx (authorisation ga)
  (grantChallengeAtoms op xs (grantCoin op ctx) ga id g) (number (grantNonce g)) challengeRun
... | challenged , refl with then (settle c ga id g h spent) r₅
... | _ , settled , settleRun , r₆ with Grant.settle-run c ga id g h spent settleRun
... | verified , settlement with then (body op ctx xs (grantCoin op ctx) none) r₆
... | result , afterBody , bodyRun , tailRun with withdrawal
... | unshieldedWithdrawal = trans (Grant.unshielded-tail result tailRun)
  (trans (Device.body-frame k withdrawUnshielded ctx xs (grantCoin withdrawUnshielded ctx) none
    (Protected.notBalance p All.∷ All.[]) bodyRun) (settlement-frame k p settlement))
... | shieldedWithdrawal = trans
  (Grant.change-tail (flag (at 0 result)) (changeEntry ga) result
    (Protected.notInbox p) (Protected.notInboxCount p) tailRun)
  (trans (Device.body-frame k withdrawShielded ctx xs (grantCoin withdrawShielded ctx) none All.[] bodyRun)
    (settlement-frame k p settlement))
... | contractWithdrawal = trans
  (Grant.change-tail (flag (at 0 (at 1 result))) (changeEntry ga) result
    (Protected.notInbox p) (Protected.notInboxCount p) tailRun)
  (trans (Device.body-frame k withdrawToContract ctx xs (grantCoin withdrawToContract ctx) none All.[] bodyRun)
    (settlement-frame k p settlement))

private
  lookup-insert-same : ∀ id g entries → lookupMap id (insertMap id g entries) ≡ just g
  lookup-insert-same id g [] rewrite Grant.equal-refl id = refl
  lookup-insert-same id g (tuple (key ∷ value ∷ []) ∷ rest) with equal id key in same
  ... | true rewrite Grant.equal-refl id = refl
  ... | false rewrite same = lookup-insert-same id g rest
  lookup-insert-same id g (nat _ ∷ rest) = lookup-insert-same id g rest
  lookup-insert-same id g (bool _ ∷ rest) = lookup-insert-same id g rest
  lookup-insert-same id g (bytes _ ∷ rest) = lookup-insert-same id g rest
  lookup-insert-same id g (none ∷ rest) = lookup-insert-same id g rest
  lookup-insert-same id g (some _ ∷ rest) = lookup-insert-same id g rest
  lookup-insert-same id g (tuple [] ∷ rest) = lookup-insert-same id g rest
  lookup-insert-same id g (tuple (_ ∷ []) ∷ rest) = lookup-insert-same id g rest
  lookup-insert-same id g (tuple (_ ∷ _ ∷ _ ∷ _) ∷ rest) = lookup-insert-same id g rest

  lookup-insert-other : ∀ other id g entries → equal other id ≡ false →
    lookupMap other (insertMap id g entries) ≡ lookupMap other entries
  lookup-insert-other other id g [] distinct rewrite distinct = refl
  lookup-insert-other other id g (tuple (key ∷ value ∷ []) ∷ rest) distinct with equal id key in same
  ... | true rewrite distinct | subst (λ x → equal other x ≡ false) (Grant.equal-sound id key same) distinct = refl
  ... | false with equal other key
  ... | true = refl
  ... | false = lookup-insert-other other id g rest distinct
  lookup-insert-other other id g (nat _ ∷ rest) distinct = lookup-insert-other other id g rest distinct
  lookup-insert-other other id g (bool _ ∷ rest) distinct = lookup-insert-other other id g rest distinct
  lookup-insert-other other id g (bytes _ ∷ rest) distinct = lookup-insert-other other id g rest distinct
  lookup-insert-other other id g (none ∷ rest) distinct = lookup-insert-other other id g rest distinct
  lookup-insert-other other id g (some _ ∷ rest) distinct = lookup-insert-other other id g rest distinct
  lookup-insert-other other id g (tuple [] ∷ rest) distinct = lookup-insert-other other id g rest distinct
  lookup-insert-other other id g (tuple (_ ∷ []) ∷ rest) distinct = lookup-insert-other other id g rest distinct
  lookup-insert-other other id g (tuple (_ ∷ _ ∷ _ ∷ _) ∷ rest) distinct = lookup-insert-other other id g rest distinct

source-confinement : ∀ c op ctx ga xs → Withdrawal op → ∀ {s v t} →
  Run (grantCall c op ctx ga xs) s v t → Confinement c op ctx ga xs s t
source-confinement c op ctx ga xs w {s} r = record
  { mutation = mutation
  ; authorityFrame = source-frame c op ctx ga xs w r
  ; ownFields = Grant.settled-record E.grantRecord (suc (number (grantNonce E.grantRecord)))
      (Settlement.commitment E.settlement) (LiveGrant.active E.live)
  ; ownStored = trans (cong (λ v → lookupMap E.identifier (fields v)) M.installed)
      (lookup-insert-same E.identifier M.settledValue (fields (cell "grants" s)))
  ; otherGrant = λ other distinct → trans (cong (λ v → lookupMap other (fields v)) M.installed)
      (lookup-insert-other other E.identifier M.settledValue (fields (cell "grants" s)) distinct) }
  where
  mutation = Effects.spend-mutation c op ctx ga xs w r
  module M = SpendMutation mutation
  module E = GrantCallEvidence M.evidence

private
  accepted-branch : ∀ b {good : Execution Value} {error v t es} →
    (if b then good else rejected error) ≡ accepted v t es → good ≡ accepted v t es
  accepted-branch true ok = ok
  accepted-branch false ()

  else-branch : ∀ b {good : Execution Value} {error v t es} →
    (if b then rejected error else good) ≡ accepted v t es → good ≡ accepted v t es
  else-branch false ok = ok
  else-branch true ()

  committed : ∀ s r {v es t} → Account.transaction s r ≡ (Account.committed v es , t) →
    r ≡ accepted v t es
  committed s (rejected _) ()
  committed s (accepted _ _ _) refl = refl

  reverted : ∀ s r {e t} → Account.transaction s r ≡ (Account.reverted e , t) → t ≡ s
  reverted s (rejected _) refl = refl
  reverted s (accepted _ _ _) ()

  dispatch-via : ∀ ctx call s {c op} → resolve call ≡ just (Semantics.grant c op) →
    Model.dispatch P ctx (RuntimeCall.request call) s ≡
      Semantics.checked (Semantics.grant c op) ctx (arguments (RuntimeCall.request call)) s
  dispatch-via ctx call s found rewrite found = refl

  checked-execute : ∀ c op ctx xs s {v t es} →
    Semantics.checked (Semantics.grant c op) ctx xs s ≡ accepted v t es →
    Semantics.execute (Semantics.grant c op) ctx xs s ≡ accepted v t es
  checked-execute c op ctx xs s ok = accepted-branch (Model.validState s)
    (else-branch (Semantics.needsCoin (Semantics.grant c op) ∧ not (Model.valid Model.qualifiedCoinT (heldCoin ctx)))
      (accepted-branch (Model.validContext ctx)
        (accepted-branch (Model.validArguments (Semantics.schema (Semantics.grant c op)) xs) ok)))

  execute-confinement : ∀ c op ctx xs → Withdrawal op → ∀ {s v t} →
    Run (Semantics.execute (Semantics.grant c op) ctx xs) s v t →
    Confinement c op ctx (parseGrantAuth c op xs) (take 3 xs) s t
  execute-confinement c .withdrawUnshielded ctx xs unshieldedWithdrawal =
    source-confinement c withdrawUnshielded ctx (parseGrantAuth c withdrawUnshielded xs) (take 3 xs) unshieldedWithdrawal
  execute-confinement c .withdrawShielded ctx xs shieldedWithdrawal =
    source-confinement c withdrawShielded ctx (parseGrantAuth c withdrawShielded xs) (take 3 xs) shieldedWithdrawal
  execute-confinement c .withdrawToContract ctx xs contractWithdrawal =
    source-confinement c withdrawToContract ctx (parseGrantAuth c withdrawToContract xs) (take 3 xs) contractWithdrawal

runtime-confinement : ∀ {s t} (step : Runs.Step s t) c op → Withdrawal op → ∀ {v es} →
  Runs.Step.outcome step ≡ Account.committed v es →
  resolve (Runs.Step.call step) ≡ just (Semantics.grant c op) → RuntimeConfinement step c op
runtime-confinement {s} step c op w refl found =
  execute-confinement c op (stepContext step) (stepArguments step) w
    (run _ (checked-execute c op (stepContext step) (stepArguments step) s
      (trans (sym (dispatch-via (stepContext step) (Runs.Step.call step) s found))
        (committed s _ (Account.execution (Runs.Step.executed step))))))

step-frame : ∀ {s t} (step : Runs.Step s t) →
  GrantAction (Runs.Step.call step) (Runs.Step.outcome step) → Frame s t
step-frame step (grantWithdrawal c op w found) =
  Confinement.authorityFrame (runtime-confinement step c op w refl found)
step-frame {s} step (refused _) k p = cong (λ t → lookupCell k (ledger t))
  (reverted s _ (Account.execution (Runs.Step.executed step)))

trace-frame : ∀ {s t} → GrantTrace s t → Frame s t
trace-frame idle k p = refl
trace-frame (attempt step kind rest) k p = trans (trace-frame rest k p) (step-frame step kind k p)

private
  protected-authority : All.All Protected authorityCells
  protected-authority =
    protected refl refl refl refl refl All.∷ protected refl refl refl refl refl All.∷
    protected refl refl refl refl refl All.∷ protected refl refl refl refl refl All.∷
    protected refl refl refl refl refl All.∷ protected refl refl refl refl refl All.∷
    protected refl refl refl refl refl All.∷ protected refl refl refl refl refl All.∷
    protected refl refl refl refl refl All.∷ protected refl refl refl refl refl All.∷
    protected refl refl refl refl refl All.∷ protected refl refl refl refl refl All.∷
    protected refl refl refl refl refl All.∷ protected refl refl refl refl refl All.∷
    protected refl refl refl refl refl All.∷ protected refl refl refl refl refl All.∷
    protected refl refl refl refl refl All.∷ protected refl refl refl refl refl All.∷
    protected refl refl refl refl refl All.∷ All.[]

frame-authority : ∀ {s t} → Frame s t → AuthorityPreserved s t
frame-authority frame member = frame _ (All.lookup protected-authority member)

trace-authority : ∀ {s t} → GrantTrace s t → AuthorityPreserved s t
trace-authority {s} {t} trace = frame-authority {s} {t} (trace-frame trace)

trace-enrolled : ∀ {s t} → GrantTrace s t → ∀ entry → Enrolled entry s → Enrolled entry t
trace-enrolled {s} {t} trace entry enrolled = subst (λ v → member entry (fields v) ≡ true)
  (sym (Effects.cell-frame "devices" s t (trace-frame trace "devices" (protected refl refl refl refl refl)))) enrolled

underlying : ∀ {s t} → GrantTrace s t → Runs.Trace s t
underlying idle = ε
underlying (attempt step _ rest) = step ◅ underlying rest

history-confinement : ∀ {s t} → Runs.History s → GrantTrace s t →
  Runs.History t × Frame s t × AuthorityPreserved s t × (∀ entry → Enrolled entry s → Enrolled entry t)
history-confinement h trace = Runs.extend h (underlying trace) , trace-frame trace ,
  trace-authority trace , trace-enrolled trace

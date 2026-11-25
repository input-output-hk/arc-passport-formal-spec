{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

-- Pending-cell frames over all full-account entrypoints.
module Conformance.FullAccountRecoverySecurityPendingProof (P : Primitives) where

import Conformance.FullAccount as Model
open import Conformance.FullAccountBody P
import Conformance.FullAccountDeviceSecurity P as Device
import Conformance.FullAccountDeviceSecurityProperties P as DeviceProperties
open import Conformance.FullAccountExecution using (Run; run) renaming (then to split)
open import Conformance.FullAccountGrant P
import Conformance.FullAccountGrantSecurityProof P as GrantProof
open import Conformance.FullAccountLayouts
open import Conformance.FullAccountRecoverySecurity P
open import Conformance.FullAccountRecoverySecurityHelpers P
open import Conformance.FullAccountRecoverySecurityStages P
open import Data.Bool.Base using (false; if_then_else_; T)
open import Data.List.Base using (take; drop)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open Model.AccountSemantics P using (construct; activation; device; grant;
  depositPublic; depositPrivate; submitRecovery; finaliseRecovery; execute; deviceCall; parseActivation; parseGrant)
open OperationRun using (cancel-body)
open GrantPrefix using (grant-change; GrantReady; grant-prefix; grant-program-equal)

private
  authorised-same : ∀ {c ctx a h before e after′} → Device.Authorisation c ctx a h before e after′ →
    SamePending before after′
  authorised-same authority = samePending λ k pend →
    Device.Authorisation.unchanged authority k
      (pending-away pend "devices" _) (pending-away pend "auth_nonce" _) (pending-away pend "round" _)

  device-same : ∀ c op ctx xs {s v t} → T (separate pendingCells (Device.bodyWrites op)) →
    Run (deviceCall c op ctx xs) s v t → SamePending s t
  device-same c op ctx xs ok r =
    same-trans (authorised-same (Device.DeviceCall.authorised call)) (samePending λ k pend →
      DeviceProperties.body-frame k op ctx _ _ _ (away-all pend ok) (Device.DeviceCall.bodyRun call))
    where call = DeviceProperties.device-call-evidence c op ctx xs r

  cleared-after : ∀ {s s′ s″ t} → SamePending s s′ → Cancellation s′ s″ → SamePending s″ t → Cleared s t
  cleared-after before cancelled tail = record
    { pendingFlag = Cancellation.pendingFlag cancelled
    ; wasPending = same-stores-back before (here refl) (Cancellation.pending cancelled)
    ; isPending = Cancellation.isPending cancelled
    ; clearsFlag = same-stores tail (here refl) (Cancellation.clearsFlag cancelled)
    }

  device-cleared : ∀ c ctx xs {s v t} → Run (deviceCall c cancelRecovery ctx xs) s v t → Cleared s t
  device-cleared c ctx xs r =
    cleared-after (authorised-same (Device.DeviceCall.authorised call))
      (cancel-body (Device.DeviceCall.bodyRun call)) same-refl
    where call = DeviceProperties.device-call-evidence c cancelRecovery ctx xs r

  activation-same : ∀ c ctx a salt {s v t} → Run (activate c ctx a salt) s v t → SamePending s t
  activation-same c ctx a salt r = samePending λ k pend →
    Device.Activation.unchanged (DeviceProperties.activation-evidence c ctx a salt r) k
      (pending-away pend "devices" _) (pending-away pend "device_count" _) (pending-away pend "booted" _)
      (pending-away pend "boot" _) (pending-away pend "round" _)

  -- The tail after a grant-authorised body: grantCall's appendChange, then
  -- return (frames from FullAccountGrantSecurityProof).
  plain-tail : ∀ {x s v t} → Run (return tt >> return x) s v t → SamePending s t
  plain-tail {x} r = samePending λ k _ → GrantProof.unshielded-tail x r

  change-tail : ∀ b e {x s v t} → Run ((if b then inboxAppend e else return tt) >> return x) s v t →
    SamePending s t
  change-tail b e {x} r = samePending λ k pend →
    GrantProof.change-tail b e x (pending-away pend "inbox" _) (pending-away pend "inbox_count" _) r


  body-same : ∀ op ctx xs coin e {s v t} → T (separate pendingCells (Device.bodyWrites op)) →
    Run (body op ctx xs coin e) s v t → SamePending s t
  body-same op ctx xs coin e ok r = samePending λ k pend →
    DeviceProperties.body-frame k op ctx xs coin e (away-all pend ok) r


  grant-tail : ∀ op ga result {s v t} → Run (grant-change op ga result >> return result) s v t → SamePending s t
  grant-tail withdrawUnshielded ga result = plain-tail
  grant-tail withdrawShielded ga result = change-tail (flag (at 0 result)) (changeEntry ga)
  grant-tail withdrawToContract ga result = change-tail (flag (at 0 (at 1 result))) (changeEntry ga)
  grant-tail appendInbox ga result = plain-tail
  grant-tail rotateEncKey ga result = plain-tail
  grant-tail addDevice ga result = plain-tail
  grant-tail removeDevice ga result = plain-tail
  grant-tail issueGrant ga result = plain-tail
  grant-tail revokeGrant ga result = plain-tail
  grant-tail revokeAllGrants ga result = plain-tail
  grant-tail publishRecovery ga result = plain-tail
  grant-tail cancelRecovery ga result = plain-tail

  abstract
    grant-kept-body : ∀ op ctx ga xs coin {s v t} → T (separate pendingCells (Device.bodyWrites op)) →
      Run (body op ctx xs coin none >>= λ result → grant-change op ga result >> return result) s v t →
      SamePending s t
    grant-kept-body op ctx ga xs coin distinct r
      with split (body op ctx xs coin none) {f = λ result → grant-change op ga result >> return result} r
    ... | result , after , bodyRun , rest =
      same-trans (body-same op ctx xs coin none distinct bodyRun) (grant-tail op ga result rest)

    grant-cancel-body : ∀ ctx ga xs coin {s v t} →
      Run (body cancelRecovery ctx xs coin none >>= λ result → grant-change cancelRecovery ga result >> return result) s v t →
      Cleared s t
    grant-cancel-body ctx ga xs coin r
      with split (body cancelRecovery ctx xs coin none) {f = λ result → return tt >> return result} r
    ... | result , after , bodyRun , rest = cleared-after same-refl (cancel-body bodyRun) (plain-tail rest)

  grant-body : ∀ op ctx ga xs coin {s v t} →
    Run (body op ctx xs coin none >>= λ result → grant-change op ga result >> return result) s v t →
    OperationEffect op s t
  grant-body withdrawUnshielded ctx ga xs coin = grant-kept-body withdrawUnshielded ctx ga xs coin _
  grant-body withdrawShielded ctx ga xs coin = grant-kept-body withdrawShielded ctx ga xs coin _
  grant-body withdrawToContract ctx ga xs coin = grant-kept-body withdrawToContract ctx ga xs coin _
  grant-body appendInbox ctx ga xs coin = grant-kept-body appendInbox ctx ga xs coin _
  grant-body rotateEncKey ctx ga xs coin = grant-kept-body rotateEncKey ctx ga xs coin _
  grant-body addDevice ctx ga xs coin = grant-kept-body addDevice ctx ga xs coin _
  grant-body removeDevice ctx ga xs coin = grant-kept-body removeDevice ctx ga xs coin _
  grant-body issueGrant ctx ga xs coin = grant-kept-body issueGrant ctx ga xs coin _
  grant-body revokeGrant ctx ga xs coin = grant-kept-body revokeGrant ctx ga xs coin _
  grant-body revokeAllGrants ctx ga xs coin = grant-kept-body revokeAllGrants ctx ga xs coin _
  grant-body publishRecovery ctx ga xs coin = grant-kept-body publishRecovery ctx ga xs coin _
  grant-body cancelRecovery ctx ga xs coin = grant-cancel-body ctx ga xs coin

  operation-before : ∀ op {s s′ t} → SamePending s s′ → OperationEffect op s′ t → OperationEffect op s t
  operation-before withdrawUnshielded = same-trans
  operation-before withdrawShielded = same-trans
  operation-before withdrawToContract = same-trans
  operation-before appendInbox = same-trans
  operation-before rotateEncKey = same-trans
  operation-before addDevice = same-trans
  operation-before removeDevice = same-trans
  operation-before issueGrant = same-trans
  operation-before revokeGrant = same-trans
  operation-before revokeAllGrants = same-trans
  operation-before publishRecovery = same-trans
  operation-before cancelRecovery before cleared = record
    { pendingFlag = Cleared.pendingFlag cleared
    ; wasPending = same-stores-back before (here refl) (Cleared.wasPending cleared)
    ; isPending = Cleared.isPending cleared
    ; clearsFlag = Cleared.clearsFlag cleared
    }

  grant-call : ∀ c op ctx ga xs {s v t} → Run (grantCall c op ctx ga xs) s v t → OperationEffect op s t
  grant-call c op ctx ga xs {s} {v} {t} r = operation-before op (GrantReady.unchanged ready)
    (grant-body op ctx ga xs (GrantReady.coin ready) (GrantReady.remaining ready))
    where ready = grant-prefix c op ctx ga xs (subst (λ m → Run m s v t) (grant-program-equal c op ctx ga xs) r)

abstract
  pending-effect : ∀ e ctx xs {s v t es} → execute e ctx xs s ≡ accepted v t es → PendingEffect e ctx xs s t
  pending-effect construct ctx xs ok =
    subst (λ t → Stores t "pending_recovery" (bool false)) (proj₁ (proj₂ (accepted-injective ok))) (stored refl)
  pending-effect submitRecovery ctx xs ok = SubmitRun.evidence ctx xs (run _ ok)
  pending-effect finaliseRecovery ctx xs ok = FinaliseRun.evidence ctx (run _ ok)
  pending-effect (activation c) ctx xs ok = activation-same c ctx (parseActivation c xs) (get 1 xs) (run _ ok)
  pending-effect (device c withdrawUnshielded) ctx xs ok = device-same c withdrawUnshielded ctx xs _ (run _ ok)
  pending-effect (device c withdrawShielded) ctx xs ok = device-same c withdrawShielded ctx xs _ (run _ ok)
  pending-effect (device c withdrawToContract) ctx xs ok = device-same c withdrawToContract ctx xs _ (run _ ok)
  pending-effect (device c appendInbox) ctx xs ok = device-same c appendInbox ctx xs _ (run _ ok)
  pending-effect (device c rotateEncKey) ctx xs ok = device-same c rotateEncKey ctx xs _ (run _ ok)
  pending-effect (device c addDevice) ctx xs ok = device-same c addDevice ctx xs _ (run _ ok)
  pending-effect (device c removeDevice) ctx xs ok = device-same c removeDevice ctx xs _ (run _ ok)
  pending-effect (device c issueGrant) ctx xs ok = device-same c issueGrant ctx xs _ (run _ ok)
  pending-effect (device c revokeGrant) ctx xs ok = device-same c revokeGrant ctx xs _ (run _ ok)
  pending-effect (device c revokeAllGrants) ctx xs ok = device-same c revokeAllGrants ctx xs _ (run _ ok)
  pending-effect (device c publishRecovery) ctx xs ok = device-same c publishRecovery ctx xs _ (run _ ok)
  pending-effect (device c cancelRecovery) ctx xs ok = device-cleared c ctx xs (run _ ok)
  pending-effect (grant c withdrawUnshielded) ctx xs ok =
    grant-call c withdrawUnshielded ctx (parseGrant c (drop 3 xs) none none) (take 3 xs) (run _ ok)
  pending-effect (grant c withdrawShielded) ctx xs ok =
    grant-call c withdrawShielded ctx (parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) (run _ ok)
  pending-effect (grant c withdrawToContract) ctx xs ok =
    grant-call c withdrawToContract ctx (parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) (run _ ok)
  pending-effect (grant c appendInbox) ctx xs ok =
    grant-call c appendInbox ctx (parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) (run _ ok)
  pending-effect (grant c rotateEncKey) ctx xs ok =
    grant-call c rotateEncKey ctx (parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) (run _ ok)
  pending-effect (grant c addDevice) ctx xs ok =
    grant-call c addDevice ctx (parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) (run _ ok)
  pending-effect (grant c removeDevice) ctx xs ok =
    grant-call c removeDevice ctx (parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) (run _ ok)
  pending-effect (grant c issueGrant) ctx xs ok =
    grant-call c issueGrant ctx (parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) (run _ ok)
  pending-effect (grant c revokeGrant) ctx xs ok =
    grant-call c revokeGrant ctx (parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) (run _ ok)
  pending-effect (grant c revokeAllGrants) ctx xs ok =
    grant-call c revokeAllGrants ctx (parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) (run _ ok)
  pending-effect (grant c publishRecovery) ctx xs ok =
    grant-call c publishRecovery ctx (parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) (run _ ok)
  pending-effect (grant c cancelRecovery) ctx xs ok =
    grant-call c cancelRecovery ctx (parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) (run _ ok)
  pending-effect depositPublic ctx xs ok = deposit-public ctx xs (run _ ok)
  pending-effect depositPrivate ctx xs ok = deposit-private ctx xs (run _ ok)

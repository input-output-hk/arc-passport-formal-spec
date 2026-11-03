{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes using (Primitives; Value)

module Passport.OutsiderPreservationProof (P : Primitives) (address : Value) where

open import Conformance.FullAccountTypes
import Conformance.FullAccount as Model
open import Conformance.FullAccountBody P
open import Conformance.FullAccountDeviceSecurity P using (Preserves)
open import Conformance.FullAccountDeviceSecurityProof P
  using (preserves-bind; if-preserves; emit-preserves; return-preserves;
    memberMap-preserves; lookup-preserves; cast-preserves; insert-preserves;
    bump-preserves; readSelf-preserves; createCoin-preserves; inboxAppend-preserves;
    return-run; bump-run; cell-lookup; cell-insert-same)
open import Conformance.FullAccountExecution using (Run; run; then)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat.Base using (ℕ; suc; _+_; _^_; _<ᵇ_)
open import Data.Nat.Properties using (+-suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
import Passport.Account as Account
open import Passport.AccountLifecycle P using (RuntimeCall; executionContext)
open import Passport.OutsiderPreservation P address

open Semantics using (execute; checked; schema; depositPublic; depositPrivate)

credit-frame : ∀ {k} color amount → stringEqual k "unshielded_balances" ≡ false →
  Preserves k (credit color amount)
credit-frame color amount distinct =
  preserves-bind (memberMap-preserves "unshielded_balances" color) λ present →
  if-preserves present
    (preserves-bind (lookup-preserves "unshielded_balances" color) λ old →
     preserves-bind (cast-preserves "unshielded_balances" 128 (number old + amount)) λ n →
     insert-preserves "unshielded_balances" color (nat n) distinct)
    (insert-preserves "unshielded_balances" color (nat amount) distinct)

receive-frame : ∀ {k} ctx coin → Preserves k (receiveCoin ctx coin)
receive-frame ctx coin =
  preserves-bind (readSelf-preserves ctx) λ addr →
  preserves-bind (createCoin-preserves coin (tuple (bool false ∷ addr ∷ []))) λ _ →
  emit-preserves (receiveShielded coin)

public-frame : ∀ k → Protected k → ∀ ctx xs → Preserves k (execute depositPublic ctx xs)
public-frame k p ctx xs =
  preserves-bind (emit-preserves (receiveUnshielded (get 0 xs) (number (get 1 xs)))) λ _ →
  preserves-bind (credit-frame (get 0 xs) (number (get 1 xs)) (Protected.notBalance p)) λ _ →
  preserves-bind (bump-preserves "round" 64 (Protected.notRound p)) λ _ →
  return-preserves unit

private-frame : ∀ k → Protected k → ∀ ctx xs → Preserves k (execute depositPrivate ctx xs)
private-frame k p ctx xs =
  preserves-bind (receive-frame ctx (get 0 xs)) λ _ →
  preserves-bind (inboxAppend-preserves (get 1 xs) (Protected.notInbox p) (Protected.notInboxCount p)) λ _ →
  preserves-bind (bump-preserves "round" 64 (Protected.notRound p)) λ _ →
  return-preserves unit

private
  step-context : ∀ {s t} → Runs.Step s t → Context
  step-context step = executionContext address (Runs.Step.environment step)

  step-arguments : ∀ {s t} → Runs.Step s t → List Value
  step-arguments step = arguments (RuntimeCall.request (Runs.Step.call step))

  accepted-branch : ∀ {A : Set} b {good : Execution A} {error v t es} →
    (if b then good else rejected error) ≡ accepted v t es → good ≡ accepted v t es
  accepted-branch true ok = ok
  accepted-branch false ()

  committed : ∀ s r {v es t} → Account.transaction s r ≡ (Account.committed v es , t) →
    r ≡ accepted v t es
  committed s (rejected _) ()
  committed s (accepted _ _ _) refl = refl

  reverted : ∀ s r {e t} → Account.transaction s r ≡ (Account.reverted e , t) → t ≡ s
  reverted s (rejected _) refl = refl
  reverted s (accepted _ _ _) ()

  dispatch-via : ∀ ctx call s {e} → resolve call ≡ just e →
    Model.dispatch P ctx (RuntimeCall.request call) s ≡
      checked e ctx (arguments (RuntimeCall.request call)) s
  dispatch-via ctx call s found rewrite found = refl

  public-execute : ∀ ctx xs s {v t es} → checked depositPublic ctx xs s ≡ accepted v t es →
    execute depositPublic ctx xs s ≡ accepted v t es
  public-execute ctx xs s ok = accepted-branch (Model.validState s)
    (accepted-branch (Model.validContext ctx)
      (accepted-branch (Model.validArguments (schema depositPublic) xs) ok))

  private-execute : ∀ ctx xs s {v t es} → checked depositPrivate ctx xs s ≡ accepted v t es →
    execute depositPrivate ctx xs s ≡ accepted v t es
  private-execute ctx xs s ok = accepted-branch (Model.validState s)
    (accepted-branch (Model.validContext ctx)
      (accepted-branch (Model.validArguments (schema depositPrivate) xs) ok))

  public-run : ∀ {s t} (step : Runs.Step s t) {v es} →
    Runs.Step.outcome step ≡ Account.committed v es → resolve (Runs.Step.call step) ≡ just depositPublic →
    Run (execute depositPublic (executionContext address (Runs.Step.environment step))
      (arguments (RuntimeCall.request (Runs.Step.call step)))) s v t
  public-run {s} step refl found = run _ (public-execute (step-context step) (step-arguments step) s
    (trans (sym (dispatch-via (step-context step) (Runs.Step.call step) s found))
      (committed s (Model.dispatch P (step-context step) (RuntimeCall.request (Runs.Step.call step)) s)
        (Account.execution (Runs.Step.executed step)))))

  private-run : ∀ {s t} (step : Runs.Step s t) {v es} →
    Runs.Step.outcome step ≡ Account.committed v es → resolve (Runs.Step.call step) ≡ just depositPrivate →
    Run (execute depositPrivate (executionContext address (Runs.Step.environment step))
      (arguments (RuntimeCall.request (Runs.Step.call step)))) s v t
  private-run {s} step refl found = run _ (private-execute (step-context step) (step-arguments step) s
    (trans (sym (dispatch-via (step-context step) (Runs.Step.call step) s found))
      (committed s (Model.dispatch P (step-context step) (RuntimeCall.request (Runs.Step.call step)) s)
        (Account.execution (Runs.Step.executed step)))))

step-frame : ∀ {s t} (step : Runs.Step s t) →
  OutsiderAction (Runs.Step.call step) (Runs.Step.outcome step) → Frame s t
step-frame step (publicDeposit found) k p =
  public-frame k p (step-context step) (step-arguments step) (public-run step refl found)
step-frame step (privateDeposit found) k p =
  private-frame k p (step-context step) (step-arguments step) (private-run step refl found)
step-frame {s} step (refused _) k p = cong (λ t → lookupCell k (ledger t))
  (reverted s _ (Account.execution (Runs.Step.executed step)))

trace-frame : ∀ {s t} → OutsiderTrace s t → Frame s t
trace-frame idle k p = refl
trace-frame (attempt step kind rest) k p = trans (trace-frame rest k p) (step-frame step kind k p)

private
  protected-resources : All Protected resources
  protected-resources =
    protected refl refl refl refl ∷ protected refl refl refl refl ∷
    protected refl refl refl refl ∷ protected refl refl refl refl ∷
    protected refl refl refl refl ∷ protected refl refl refl refl ∷
    protected refl refl refl refl ∷ protected refl refl refl refl ∷
    protected refl refl refl refl ∷ protected refl refl refl refl ∷
    protected refl refl refl refl ∷ protected refl refl refl refl ∷
    protected refl refl refl refl ∷ protected refl refl refl refl ∷
    protected refl refl refl refl ∷ protected refl refl refl refl ∷
    protected refl refl refl refl ∷ protected refl refl refl refl ∷
    protected refl refl refl refl ∷ protected refl refl refl refl ∷ []

resources-preserved : ∀ {s t} → OutsiderTrace s t → ResourcesPreserved s t
resources-preserved trace member = trace-frame trace _ (All.lookup protected-resources member)

private
  cell-frame : ∀ k s t → lookupCell k (ledger t) ≡ lookupCell k (ledger s) → cell k t ≡ cell k s
  cell-frame k s t eq with lookupCell k (ledger t) | lookupCell k (ledger s) | eq
  ... | nothing | .nothing | refl = refl
  ... | just v | .(just v) | refl = refl

enrolled-preserved : ∀ {s t} → OutsiderTrace s t → ∀ entry → Enrolled entry s → Enrolled entry t
enrolled-preserved {s} {t} trace entry enrolled = subst
  (λ v → member entry (fields v) ≡ true)
  (sym (cell-frame "devices" s t
    (trace-frame trace "devices" (protected refl refl refl refl)))) enrolled

underlying : ∀ {s t} → OutsiderTrace s t → Runs.Trace s t
underlying idle = ε
underlying (attempt step _ rest) = step ◅ underlying rest

rooted-extension : ∀ {s t} → Runs.History s → OutsiderTrace s t → Runs.History t
rooted-extension h trace = Runs.extend h (underlying trace)

private
  RoundStep : State → State → Set
  RoundStep s t = roundValue t ≡ suc (roundValue s) × RoundFits t

  bump-round : ∀ {s x t} → Run (bump "round" 64) s x t → RoundStep s t
  bump-round {s} r with bump-run "round" 64 r
  ... | v , found , bounded , refl
    rewrite cell-lookup "round" s found
          | cell-insert-same "round" (nat (suc (number v))) (ledger s) = refl , bounded

  round-frame : ∀ {s t} → lookupCell "round" (ledger t) ≡ lookupCell "round" (ledger s) →
    roundValue t ≡ roundValue s
  round-frame {s} {t} eq = cong number (cell-frame "round" s t eq)

  public-round : ∀ ctx xs {s v t} → Run (execute depositPublic ctx xs) s v t → RoundStep s t
  public-round ctx xs {s} r
    with then (emit (receiveUnshielded (get 0 xs) (number (get 1 xs))))
      {f = λ _ → credit (get 0 xs) (number (get 1 xs)) >> (bump "round" 64 >> return unit)} r
  ... | _ , u , first , rest
    with then (credit (get 0 xs) (number (get 1 xs)))
      {f = λ _ → bump "round" 64 >> return unit} rest
  ... | _ , w , credited , rest′
    with then (bump "round" 64) {f = λ _ → return unit} rest′
  ... | _ , z , bumped , returned with return-run unit returned
  ... | _ , refl with bump-round bumped
  ... | cost , fits = trans cost (cong suc (trans
    (round-frame {s = u} {t = w}
      (credit-frame {k = "round"} (get 0 xs) (number (get 1 xs)) refl credited))
    (round-frame {s = s} {t = u}
      (emit-preserves {k = "round"} (receiveUnshielded (get 0 xs) (number (get 1 xs))) first)))) , fits

  private-round : ∀ ctx xs {s v t} → Run (execute depositPrivate ctx xs) s v t → RoundStep s t
  private-round ctx xs {s} r
    with then (receiveCoin ctx (get 0 xs))
      {f = λ _ → inboxAppend (get 1 xs) >> (bump "round" 64 >> return unit)} r
  ... | _ , u , first , rest
    with then (inboxAppend (get 1 xs)) {f = λ _ → bump "round" 64 >> return unit} rest
  ... | _ , w , appended , rest′
    with then (bump "round" 64) {f = λ _ → return unit} rest′
  ... | _ , z , bumped , returned with return-run unit returned
  ... | _ , refl with bump-round bumped
  ... | cost , fits = trans cost (cong suc (trans
    (round-frame {s = u} {t = w}
      (inboxAppend-preserves {k = "round"} (get 1 xs) refl refl appended))
    (round-frame {s = s} {t = u} (receive-frame {k = "round"} ctx (get 0 xs) first)))) , fits

round-cost : ∀ {s t} (trace : OutsiderTrace s t) → RoundCost trace
round-cost idle = refl
round-cost (attempt step (publicDeposit found) rest) =
  trans (round-cost rest) (trans
    (cong (successfulDeposits rest +_)
      (proj₁ (public-round (step-context step) (step-arguments step) (public-run step refl found))))
    (+-suc (successfulDeposits rest) _))
round-cost (attempt step (privateDeposit found) rest) =
  trans (round-cost rest) (trans
    (cong (successfulDeposits rest +_)
      (proj₁ (private-round (step-context step) (step-arguments step) (private-run step refl found))))
    (+-suc (successfulDeposits rest) _))
round-cost {s} (attempt step (refused _) rest) = trans (round-cost rest)
  (cong (λ t → successfulDeposits rest + roundValue t)
    (reverted s _ (Account.execution (Runs.Step.executed step))))

round-fits : ∀ {s t} → OutsiderTrace s t → RoundFits s → RoundFits t
round-fits idle fits = fits
round-fits (attempt step (publicDeposit found) rest) fits =
  round-fits rest (proj₂ (public-round (step-context step) (step-arguments step) (public-run step refl found)))
round-fits (attempt step (privateDeposit found) rest) fits =
  round-fits rest (proj₂ (private-round (step-context step) (step-arguments step) (private-run step refl found)))
round-fits {s} (attempt step (refused _) rest) fits = round-fits rest
  (subst RoundFits (sym (reverted s _ (Account.execution (Runs.Step.executed step)))) fits)

round-budget : ∀ {s t} (trace : OutsiderTrace s t) → RoundFits s →
  ((successfulDeposits trace + roundValue s) <ᵇ 2 ^ 64) ≡ true
round-budget trace fits = subst (λ n → (n <ᵇ 2 ^ 64) ≡ true)
  (round-cost trace) (round-fits trace fits)

-- Successful bootstrap/finalisation cannot enter the restricted class. Refused
-- attempts to either entrypoint can, and are covered by transaction rollback.
activation-excluded : ∀ call c {v es} → resolve call ≡ just (Semantics.activation c) →
  OutsiderAction call (Account.committed v es) → ⊥
activation-excluded call c found (publicDeposit deposit) with trans (sym found) deposit
... | ()
activation-excluded call c found (privateDeposit deposit) with trans (sym found) deposit
... | ()

finalisation-excluded : ∀ call {v es} → resolve call ≡ just Semantics.finaliseRecovery →
  OutsiderAction call (Account.committed v es) → ⊥
finalisation-excluded call found (publicDeposit deposit) with trans (sym found) deposit
... | ()
finalisation-excluded call found (privateDeposit deposit) with trans (sym found) deposit
... | ()

history-preserved : ∀ {s t} → Runs.History s → (trace : OutsiderTrace s t) →
  Runs.History t × Frame s t × ResourcesPreserved s t ×
  (∀ entry → Enrolled entry s → Enrolled entry t)
history-preserved h trace = rooted-extension h trace , trace-frame trace ,
  resources-preserved trace , enrolled-preserved trace

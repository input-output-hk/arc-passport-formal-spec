{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes
open import Midnight.ContractDSL.SymbolicSigning using (Ownership)
import Conformance.FullAccountSignatureBinding as SignatureBinding

module Passport.TransactionSafetyProof (P : Primitives) (address : Value)
  (ownership : SignatureBinding.Key P → Ownership) where

open import Conformance.FullAccountBody P
open import Conformance.FullAccountCrypto P
import Conformance.FullAccountDeviceSecurity P as Device
import Conformance.FullAccountDeviceSecurityProperties P as DeviceFacts
import Conformance.FullAccountDeviceSecurityProof P as DeviceProof
open import Conformance.FullAccountExecution
open import Conformance.FullAccountGrant P
open import Conformance.FullAccountGrantScope P
import Conformance.FullAccountGrantScopeProperties P as ScopeFacts
open import Conformance.FullAccountGrantSecurity P
import Conformance.FullAccountGrantSecurityProperties P as GrantFacts
import Conformance.FullAccountGrantSecurityProof P as GrantProof
open import Conformance.FullAccountLayouts
import Conformance.FullAccountSignatureBindingProof P as BindingProof
open import Data.Bool.Base using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using ([]; _∷_; take)
import Data.List.Relation.Unary.All as All
open import Data.Maybe.Base using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat.Base using (_≤_)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
import Passport.AccountSecurity P address ownership as Security
import Passport.AccountSecurityProof P address ownership as SecurityProof
open import Passport.AccountLifecycle P hiding (run; environment)
open import Passport.GrantEffects P using (issuanceOf)
import Passport.GrantReplayProperties P address as ReplayFacts
open import Passport.GrantSpending P
import Passport.GrantSpendingProperties P address as SpendingFacts
open Histories address
open import Passport.RevocationExclusion P address hiding (module Runs)
open import Passport.TransactionSafety P address ownership
open import Relation.Binary.PropositionalEquality

private
  accepted-value : ∀ {A : Set} {x y : A} {s t es fs} →
    accepted x s es ≡ accepted y t fs → x ≡ y
  accepted-value refl = refl

  lookup-recorded : ∀ id {s g} → Run (lookup "grants" id) s g s →
    lookupMap id (fields (cell "grants" s)) ≡ just g
  lookup-recorded id {s} (run _ execution) with lookupMap id (fields (cell "grants" s))
  ... | nothing with execution
  ... | ()
  lookup-recorded id (run _ execution) | just _ = cong just (accepted-value execution)

  find-opening : ∀ id g {eps entries} → Corresponds eps entries → lookupMap id entries ≡ just g →
    Σ Episode λ ep → findEpisode id eps ≡ just ep × episodeKey ep ≡ id × Opens ep g
  find-opening id g empty ()
  find-opening id g (mapEntry {ep = ep} {g = old} O rest) found
    with equal id (episodeKey ep) in same
  ... | false = find-opening id g rest found
  ... | true with GrantProof.equal-sound id (episodeKey ep) same | just-injective found
  ... | refl | refl = ep , refl , refl , O

  historical-cap : ∀ {s c op ctx xs} (h : Runs.History s) → HistoryAgreement h →
    CallAgreement (Runtime.grant c op) ctx xs s (historyBook h) →
    (E : GrantCallEvidence c op ctx (parseGrantAuth c op xs) (take 3 xs) s) → HistoricalCap h E
  historical-cap {s} {c} {op} {ctx} {xs} h agreed current E
    with find-opening (identifier E) (grantRecord E)
      (Accounted.correspondence (SpendingFacts.whole-history-stored-openings h agreed))
      (lookup-recorded (identifier E) (recorded E))
  ... | ep , found , key , O = ep , found ,
    trans (cong (λ id → issuanceOf id (grantRecord E)) (sym key)) (Opens.identityKept O) ,
    subst (_ ≤_) (Opens.scopeCapKept O) (proj₂ (proj₂ (proj₂ cap)))
    where
    opening = run [] (BindingProof.pure-runs (DeviceProof.spentCommit-pure (Episode.saltValue ep) (total ep))
      (Run.execution (Opens.spentOpening O)) s)
    cap = GrantFacts.cumulative-spend E
      (current ep (subst (λ id → findEpisode id (Book.current (historyBook h)) ≡ just ep) (sym key) found)
        (subst (λ id → Run (grantId c ctx (parseGrantAuth c op xs)) s id s) (sym key) (identified E))) opening

  withdrawal-cap : ∀ {s c op ctx xs} → Withdrawal op → (h : Runs.History s) → HistoryAgreement h →
    CallAgreement (Runtime.grant c op) ctx xs s (historyBook h) →
    (E : GrantCallEvidence c op ctx (Security.grantAuthorisation c op xs) (take 3 xs) s) → HistoricalCap h E
  withdrawal-cap unshieldedWithdrawal = historical-cap
  withdrawal-cap shieldedWithdrawal = historical-cap
  withdrawal-cap contractWithdrawal = historical-cap

  withdrawal-frame : ∀ {op} → Withdrawal op →
    All.All (λ label → stringEqual "devices" label ≡ false) (Device.bodyWrites op)
  withdrawal-frame unshieldedWithdrawal = refl All.∷ All.[]
  withdrawal-frame shieldedWithdrawal = All.[]
  withdrawal-frame contractWithdrawal = All.[]

transaction-safety : ∀ {s t} (h : Runs.History s) (event : CommittedOccurrence s t)
  (policy : IntendedPolicy) → WithdrawalCall event → HistoryAgreement h →
  IntendedOpening h event policy → ScopeAgreement h event policy → SpendAgreement h event policy →
  TransactionSafety h event policy
transaction-safety {s} {t} h event policy withdrawal historyAgreed intended scopeAgreed spentAgreed
  with SecurityProof.accepted-call (CommittedOccurrence.environment event) (CommittedOccurrence.call event)
    (CommittedOccurrence.executed event)
... | requests , classifiedCall , actual = classify classifiedCall actual
  where
  open CommittedOccurrence event
  ctx = occurrenceContext event
  xs = occurrenceArguments event

  selected : ∀ {e} → Security.Dispatched e environment call s answer t effects → withdrawalEntry (just e)
  selected d = subst withdrawalEntry (Security.Dispatched.resolved d) withdrawal

  classify : ∀ {requests} → Security.AcceptedCall environment call s answer t effects requests →
    Security.signedRequests s environment call ≡ requests → TransactionSafety h event policy
  classify (Security.activated c d _) _ = ⊥-elim (selected d)
  classify (Security.deviceAuthorised c op d E checked encoded) actual = record
    { request = Security.calledRequest E
    ; classified = deviceWithdrawal c op (selected d) (Security.Dispatched.resolved d) E checked encoded
        (DeviceFacts.consumed-credentials-refused c op E (withdrawal-frame (selected d)))
    ; actualRequest = actual }
  classify (Security.grantAuthorised c op d w final checked encoded) actual = record
    { request = Security.grantedRequest E
    ; classified = grantWithdrawal c op w resolved final checked encoded
        (ScopeFacts.scope-enforced (scoped E) (coinAdmitted E) committed (scopeAgreed c op resolved))
        (withdrawal-cap w h historyAgreed (spentAgreed c op resolved) E)
        (ReplayFacts.SymbolicReplay.historical-token-replay-excluded ownership (replaySpend event c op w resolved final))
    ; actualRequest = actual }
    where
    resolved = Security.Dispatched.resolved d
    E = GrantFinalState.callEvidence final
    policyOpening = intended c op resolved
    -- Deterministic source id and lookup executions identify the policy witness
    -- with this accepted call's actual record.
    same-result : ∀ {A : Set} {m : M A} {s x y t u} → Run m s x t → Run m s y u → x ≡ y
    same-result (run _ first) (run _ second) = accepted-value (trans (sym first) second)
    same-id = same-result (IntendedGrant.identifierRun policyOpening) (identified E)
    same-record = same-result
      (subst (λ id → Run (lookup "grants" id) s (IntendedGrant.storedRecord policyOpening) s)
        same-id (IntendedGrant.recordRun policyOpening)) (recorded E)
    committed = subst (PolicyCommitted policy s) same-record (IntendedGrant.committedPolicy policyOpening)
  classify (Security.depositedUnshielded d) _ = ⊥-elim (selected d)
  classify (Security.depositedShielded d) _ = ⊥-elim (selected d)
  classify (Security.recoverySubmitted d _ _ _ _) _ = ⊥-elim (selected d)
  classify (Security.recoveryFinalised d _) _ = ⊥-elim (selected d)

safe-request-provenance : ∀ {s t knowledge} {event : CommittedOccurrence s t} {policy}
  (joint : Security.Histories.History (s , knowledge))
  (safe : TransactionSafety (Security.Histories.contractHistory joint) event policy) →
  All.All (Security.Symbolic.Signatures.Available knowledge)
    (Security.requiredTokens s (CommittedOccurrence.environment event) (CommittedOccurrence.call event)) →
  Security.AgreesIn (λ r → r) joint (TransactionSafety.request safe) →
  Security.RequestProvenance (λ r → r) joint (TransactionSafety.request safe)
safe-request-provenance {knowledge = knowledge} joint safe available agreed =
  BindingProof.Provenance.request-provenance ownership (λ r → r) encoded (Security.Histories.signingHistory joint)
    (agreed digest encoded) tokenAvailable
  where
  request = TransactionSafety.request safe
  encoding : ∀ {s t h event policy request} →
    SafeWithdrawal {s} {t} h event policy request → Σ Value (Security.Encodes request)
  encoding (deviceWithdrawal _ _ _ _ _ checked encoded _) = Binding.signedDigest checked , encoded
  encoding (grantWithdrawal _ _ _ _ _ checked encoded _ _ _) = Binding.signedDigest checked , encoded
  digest = proj₁ (encoding (TransactionSafety.classified safe))
  encoded = proj₂ (encoding (TransactionSafety.classified safe))
  singleton : ∀ {A : Set} {Q : A → Set} {x} → All.All Q (x ∷ []) → Q x
  singleton (proof All.∷ All.[]) = proof
  tokenAvailable = singleton (subst
    (λ requests → All.All (Security.Symbolic.Signatures.Available knowledge)
      (Data.List.Base.map (Data.Product.Base.uncurry′ Security.Symbolic.token) requests))
    (TransactionSafety.actualRequest safe) available)

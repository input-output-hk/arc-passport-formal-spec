{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes using (Primitives; Value)

module Passport.RevocationExclusionProof (P : Primitives) (address : Value) where

open import Conformance.FullAccountTypes
open import Conformance.FullAccountBody P
open import Conformance.FullAccountCrypto P
open import Conformance.FullAccountExecution
open import Conformance.FullAccountGrant P
open import Conformance.FullAccountGrantSecurity P
open import Conformance.FullAccountDeviceSecurity P
open import Conformance.FullAccount using (module AccountSemantics)
open import Conformance.FullAccountLayouts
import Passport.GrantEffects as GrantEffects
import Passport.GrantEffectsProof as GrantEffectsProof
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; take)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Base using (_++_)
open import Data.Bool.Base using (not; _∨_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; <-≤-trans)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂)
import Conformance.FullAccountDeviceSecurityProof as DeviceProof
import Conformance.FullAccountGrantSecurityProof as GrantProof
import Conformance.FullAccountRecoverySecurity as Recovery
import Passport.Account as Account
open import Passport.AccountLifecycle P hiding (run)
open import Passport.RevocationExclusion P address
import Passport.AccountSecurity as Security
import Passport.AccountSecurityProof as SecurityProof
open import Midnight.ContractDSL.SymbolicSigning using (attacker)

module D = DeviceProof P
module G = GrantProof P
module R = Recovery P
module S = Security P address (λ _ → attacker)
module SP = SecurityProof P address (λ _ → attacker)
module Semantics = AccountSemantics P
module GE = GrantEffects P
module EP = GrantEffectsProof P
open S using (AcceptedCall; activated; deviceAuthorised; grantAuthorised;
  depositedUnshielded; depositedShielded; recoverySubmitted; recoveryFinalised)

-- Proof-only certificates. Advertised statements take the committed occurrence
-- and neutral dispatcher resolution; constructors below extract these guards.
record RecoveryBoundary (s recovered : State) : Set where
  field history : Runs.History s
        event : CommittedOccurrence s recovered
        finaliseResolved : Resolved event Runtime.finaliseRecovery
        evidence : R.Finalisation.Evidence (occurrenceContext event) s recovered

record DeviceBoundary (c : Curve) (op : Operation) (s after : State) : Set where
  field history : Runs.History s
        event : CommittedOccurrence s after
        deviceResolved : Resolved event (Runtime.device c op)
        evidence : DeviceCall c op (occurrenceContext event) (occurrenceArguments event)
          s (CommittedOccurrence.answer event) after

revokedIdentifier : ∀ {c s t} → DeviceBoundary c revokeGrant s t → Value
revokedIdentifier boundary = revocationIdentifier (DeviceBoundary.event boundary)

-- The installed issue result connects the history occurrence to the actual
-- grant record; it is extracted by issue-boundary, not assumed by a headline.
record IssueBoundary (c : Curve) (s t : State) : Set where
  field device : DeviceBoundary c issueGrant s t
        issued : GE.IssueResult (deviceArguments issueGrant (occurrenceArguments (DeviceBoundary.event device)))
          (DeviceCall.authorisedState (DeviceBoundary.evidence device)) t

issueIdentity : ∀ {c s t} → IssueBoundary c s t → GE.Issuance
issueIdentity boundary = GE.issuanceOf (issuedIdentifier (DeviceBoundary.event (IssueBoundary.device boundary)))
  (GE.issuedRecord (IssueBoundary.issued boundary))

enrolledSeeds : Operation → List Value → List Value
enrolledSeeds addDevice xs = get 0 xs ∷ []
enrolledSeeds _ xs = []

deviceSeeds : Operation → List Value → Value → List Value
deviceSeeds op xs next = next ∷ enrolledSeeds op xs

introducedEntries : ∀ {env call s x t es requests} →
  AcceptedCall env call s x t es requests → List Value
introducedEntries (activated c _ E) = Activation.initial E ∷ []
introducedEntries {call = call} (deviceAuthorised c op _ E _ _) =
  deviceSeeds op (deviceArguments op (callArguments call)) (DeviceCall.rolledEntry E)
introducedEntries (grantAuthorised _ _ _ _ _ _ _) = []
introducedEntries (depositedUnshielded _) = []
introducedEntries (depositedShielded _) = []
introducedEntries (recoverySubmitted _ _ _ _ _) = []
introducedEntries (recoveryFinalised _ E) = R.Finalisation.Evidence.successor E ∷ []

cell-number : ∀ k s {v} → lookupCell k (ledger s) ≡ just v → counterValue k s ≡ number v
cell-number k s found = cong number (D.cell-lookup k s found)

frame-number : ∀ k {s t} → lookupCell k (ledger t) ≡ lookupCell k (ledger s) →
  counterValue k t ≡ counterValue k s
frame-number k {s} {t} same with lookupCell k (ledger t) | lookupCell k (ledger s) | same
... | just v | .(just v) | refl = refl
... | Data.Maybe.Base.nothing | .Data.Maybe.Base.nothing | refl = refl

frame-≤ : ∀ k {s t} → lookupCell k (ledger t) ≡ lookupCell k (ledger s) →
  counterValue k s ≤ counterValue k t
frame-≤ k {s} {t} same = subst (λ n → counterValue k s ≤ n) (sym (frame-number k {s} {t} same)) ≤-refl

advanced-< : ∀ {k bits v s t} → Advanced k bits v s t → counterValue k s < counterValue k t
advanced-< {k} {v = v} {s} {t} A rewrite cell-number k s (Advanced.previousCell A) |
  cell-number k t (Advanced.advanced A) = ≤-refl
bump-≤ : ∀ k bits {s x t} → Run (bump k bits) s x t → counterValue k s ≤ counterValue k t
bump-≤ k bits {s} r with D.bump-run k bits r
... | v , found , bounded , refl rewrite cell-number k s found |
  D.cell-insert-same k (nat (suc (number v))) (ledger s) = n≤1+n (number v)


epoch-outside : ∀ op → All (λ k → stringEqual "device_epoch" k ≡ false) (bodyWrites op)
epoch-outside withdrawUnshielded = refl ∷ []
epoch-outside withdrawShielded = []
epoch-outside withdrawToContract = []
epoch-outside appendInbox = refl ∷ refl ∷ []
epoch-outside rotateEncKey = refl ∷ []
epoch-outside addDevice = refl ∷ refl ∷ []
epoch-outside removeDevice = refl ∷ refl ∷ []
epoch-outside issueGrant = refl ∷ []
epoch-outside revokeGrant = refl ∷ []
epoch-outside revokeAllGrants = refl ∷ refl ∷ []
epoch-outside publishRecovery = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []
epoch-outside cancelRecovery = refl ∷ refl ∷ refl ∷ refl ∷ []

-- The only device body that changes the generation runs the source bounded
-- increment before clearing grants. All other bodies frame it.
generation-body : ∀ op ctx xs coin entry {s x t} → Run (body op ctx xs coin entry) s x t →
  counterValue "grant_generation" s ≤ counterValue "grant_generation" t
generation-body withdrawUnshielded ctx xs coin entry {s} {t = t} r = frame-≤ "grant_generation" {s = s} {t = t} (D.body-frame "grant_generation" withdrawUnshielded ctx xs coin entry (refl ∷ []) r)
generation-body withdrawShielded ctx xs coin entry {s} {t = t} r = frame-≤ "grant_generation" {s = s} {t = t} (D.body-frame "grant_generation" withdrawShielded ctx xs coin entry [] r)
generation-body withdrawToContract ctx xs coin entry {s} {t = t} r = frame-≤ "grant_generation" {s = s} {t = t} (D.body-frame "grant_generation" withdrawToContract ctx xs coin entry [] r)
generation-body appendInbox ctx xs coin entry {s} {t = t} r = frame-≤ "grant_generation" {s = s} {t = t} (D.body-frame "grant_generation" appendInbox ctx xs coin entry (refl ∷ refl ∷ []) r)
generation-body rotateEncKey ctx xs coin entry {s} {t = t} r = frame-≤ "grant_generation" {s = s} {t = t} (D.body-frame "grant_generation" rotateEncKey ctx xs coin entry (refl ∷ []) r)
generation-body addDevice ctx xs coin entry {s} {t = t} r = frame-≤ "grant_generation" {s = s} {t = t} (D.body-frame "grant_generation" addDevice ctx xs coin entry (refl ∷ refl ∷ []) r)
generation-body removeDevice ctx xs coin entry {s} {t = t} r = frame-≤ "grant_generation" {s = s} {t = t} (D.body-frame "grant_generation" removeDevice ctx xs coin entry (refl ∷ refl ∷ []) r)
generation-body issueGrant ctx xs coin entry {s} {t = t} r = frame-≤ "grant_generation" {s = s} {t = t} (D.body-frame "grant_generation" issueGrant ctx xs coin entry (refl ∷ []) r)
generation-body revokeGrant ctx xs coin entry {s} {t = t} r = frame-≤ "grant_generation" {s = s} {t = t} (D.body-frame "grant_generation" revokeGrant ctx xs coin entry (refl ∷ []) r)
generation-body revokeAllGrants ctx xs coin entry r with then (bump "grant_generation" 32 >> clear "grants") r
... | _ , u , prefix , returned with D.return-run unit returned
... | refl , refl with then (bump "grant_generation" 32) prefix
... | _ , middle , bumped , cleared = ≤-trans (bump-≤ "grant_generation" 32 bumped)
  (frame-≤ "grant_generation" {s = middle} {t = u} (D.clear-preserves {k = "grant_generation"} "grants" refl cleared))
generation-body publishRecovery ctx xs coin entry {s} {t = t} r = frame-≤ "grant_generation" {s = s} {t = t} (D.body-frame "grant_generation" publishRecovery ctx xs coin entry (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []) r)
generation-body cancelRecovery ctx xs coin entry {s} {t = t} r = frame-≤ "grant_generation" {s = s} {t = t} (D.body-frame "grant_generation" cancelRecovery ctx xs coin entry (refl ∷ refl ∷ refl ∷ refl ∷ []) r)

credit-frame : ∀ k color amount → stringEqual k "unshielded_balances" ≡ false → Preserves k (credit color amount)
credit-frame k color amount different =
  D.preserves-bind (D.memberMap-preserves "unshielded_balances" color) λ present →
  D.if-preserves present
    (D.preserves-bind (D.lookup-preserves "unshielded_balances" color) λ old →
     D.preserves-bind (D.cast-preserves "unshielded_balances" 128 (number old Data.Nat.Base.+ amount)) λ n →
     D.insert-preserves "unshielded_balances" color (nat n) different)
    (D.insert-preserves "unshielded_balances" color (nat amount) different)

public-frame : ∀ k ctx xs → stringEqual k "unshielded_balances" ≡ false → stringEqual k "round" ≡ false →
  Preserves k (Semantics.execute Semantics.depositPublic ctx xs)
public-frame k ctx xs balances round =
  D.preserves-bind (D.emit-preserves (receiveUnshielded (get 0 xs) (number (get 1 xs)))) λ _ →
  D.preserves-bind (credit-frame k (get 0 xs) (number (get 1 xs)) balances) λ _ →
  D.preserves-bind (D.bump-preserves "round" 64 round) λ _ → D.return-preserves unit

private-frame : ∀ k ctx xs → stringEqual k "inbox" ≡ false → stringEqual k "inbox_count" ≡ false →
  stringEqual k "round" ≡ false → Preserves k (Semantics.execute Semantics.depositPrivate ctx xs)
private-frame k ctx xs inbox count round =
  D.preserves-bind
    (D.preserves-bind (D.readSelf-preserves ctx) λ addr →
     D.preserves-bind (D.createCoin-preserves (get 0 xs) (tuple (bool false ∷ addr ∷ []))) λ _ →
     D.emit-preserves (receiveShielded (get 0 xs))) λ _ →
  D.preserves-bind (D.inboxAppend-preserves (get 1 xs) inbox count) λ _ →
  D.preserves-bind (D.bump-preserves "round" 64 round) λ _ → D.return-preserves unit

settle-frame : ∀ k c ga identifier g h spent → stringEqual k "grants" ≡ false → stringEqual k "round" ≡ false →
  Preserves k (settle c ga identifier g h spent)
settle-frame k c ga identifier g h spent grants round {s} r with G.settle-run c ga identifier g h spent r
... | _ , settlement = trans (D.bump-preserves {k = k} "round" 64 round (Settlement.roundAdvanced settlement))
  (D.lookup-insert-other k "grants"
    (tuple (insertMap identifier (settledGrant g (suc (number (grantNonce g))) (Settlement.commitment settlement))
      (fields (cell "grants" s)))) (ledger s) grants)

withdrawal-frame : ∀ k op ctx xs coin → Withdrawal op → stringEqual k "unshielded_balances" ≡ false →
  Preserves k (body op ctx xs coin none)
withdrawal-frame k withdrawUnshielded ctx xs coin unshieldedWithdrawal balances = D.body-frame k withdrawUnshielded ctx xs coin none (balances ∷ [])
withdrawal-frame k withdrawShielded ctx xs coin shieldedWithdrawal balances = D.body-frame k withdrawShielded ctx xs coin none []
withdrawal-frame k withdrawToContract ctx xs coin contractWithdrawal balances = D.body-frame k withdrawToContract ctx xs coin none []

grant-frame : ∀ k c op ctx ga xs → Withdrawal op → stringEqual k "grants" ≡ false →
  stringEqual k "round" ≡ false → stringEqual k "unshielded_balances" ≡ false →
  stringEqual k "inbox" ≡ false → stringEqual k "inbox_count" ≡ false → Preserves k (grantCall c op ctx ga xs)
grant-frame k c op ctx ga xs w grants round balances inbox count r
  with then (if shielded op then held ctx (get 1 xs) else return none) r
... | coin , t₁ , coinRun , rest₁ with G.coin-run op ctx xs coinRun
... | refl , refl with then (authenticateGrant c ctx ga) rest₁
... | (identifier , g) , t₂ , authenticated , rest₂ with G.authenticate-run c ctx ga authenticated
... | refl , _ , _ , _ with then (scopeCheck op ctx ga xs (grantCoin op ctx) g) rest₂
... | spent , t₃ , scoped , rest₃ with G.scope-run op ctx ga xs (grantCoin op ctx) g scoped
... | refl , _ with then (G.coinCheck op ga (grantCoin op ctx)) rest₃
... | _ , t₄ , guarded , rest₄ with G.coinCheck-run op ga (grantCoin op ctx) guarded
... | refl , _ with then (challenge c true (operationName op) ctx (authorisation ga)
  (grantChallengeAtoms op xs (grantCoin op ctx) ga identifier g) (number (Conformance.FullAccountLayouts.grantNonce g))) rest₄
... | h , t₅ , challenged , rest₅ with G.challenge-run c true (operationName op) ctx (authorisation ga)
  (grantChallengeAtoms op xs (grantCoin op ctx) ga identifier g) (number (Conformance.FullAccountLayouts.grantNonce g)) challenged
... | _ , refl with then (settle c ga identifier g h spent) rest₅
... | _ , settled , settlement , rest₆ with then (body op ctx xs (grantCoin op ctx) none) rest₆
... | result , after , withdrawn , tailRun with w
... | unshieldedWithdrawal = trans (G.unshielded-tail result tailRun)
  (trans (withdrawal-frame k withdrawUnshielded ctx xs (grantCoin withdrawUnshielded ctx) unshieldedWithdrawal balances withdrawn)
    (settle-frame k c ga identifier g h spent grants round settlement))
... | shieldedWithdrawal = trans (G.change-tail (flag (at 0 result)) (changeEntry ga) result inbox count tailRun)
  (trans (withdrawal-frame k _ ctx xs _ shieldedWithdrawal balances withdrawn)
    (settle-frame k c ga identifier g h spent grants round settlement))
... | contractWithdrawal = trans (G.change-tail (flag (at 0 (at 1 result))) (changeEntry ga) result inbox count tailRun)
  (trans (withdrawal-frame k _ ctx xs _ contractWithdrawal balances withdrawn)
    (settle-frame k c ga identifier g h spent grants round settlement))

device-counters : ∀ c op ctx xs {s x t} → DeviceCall c op ctx xs s x t → CountersAdvance s t
device-counters c op ctx xs {s} {t = t} E = record
  { nonce = ≤-trans (n≤1+n _) (advanced-< (DeviceCall.nonceAdvanced E))
  ; epoch = frame-≤ "device_epoch" {s = s} {t = t} (trans
      (D.body-frame "device_epoch" op ctx (deviceArguments op xs) (deviceCoin op ctx)
        (DeviceCall.callerEntry E) (epoch-outside op) (DeviceCall.bodyRun E))
      (Authorisation.unchanged (DeviceCall.authorised E) "device_epoch" refl refl refl))
  ; generation = ≤-trans
      (frame-≤ "grant_generation" {s = s} {t = DeviceCall.authorisedState E}
        (Authorisation.unchanged (DeviceCall.authorised E) "grant_generation" refl refl refl))
      (generation-body op ctx (deviceArguments op xs) (deviceCoin op ctx)
        (DeviceCall.callerEntry E) (DeviceCall.bodyRun E)) }

-- The grant branch is restricted to the dispatcher's three withdrawals.
execute-grant-frame : ∀ k c op ctx xs → Withdrawal op →
  stringEqual k "grants" ≡ false → stringEqual k "round" ≡ false →
  stringEqual k "unshielded_balances" ≡ false → stringEqual k "inbox" ≡ false →
  stringEqual k "inbox_count" ≡ false → Preserves k (Semantics.execute (Semantics.grant c op) ctx xs)
execute-grant-frame k c withdrawUnshielded ctx xs unshieldedWithdrawal =
  grant-frame k c withdrawUnshielded ctx (S.grantAuthorisation c withdrawUnshielded xs) (take 3 xs) unshieldedWithdrawal
execute-grant-frame k c withdrawShielded ctx xs shieldedWithdrawal =
  grant-frame k c withdrawShielded ctx (S.grantAuthorisation c withdrawShielded xs) (take 3 xs) shieldedWithdrawal
execute-grant-frame k c withdrawToContract ctx xs contractWithdrawal =
  grant-frame k c withdrawToContract ctx (S.grantAuthorisation c withdrawToContract xs) (take 3 xs) contractWithdrawal

not-listed : ∀ {label labels} → All (λ k → stringEqual label k ≡ false) labels → label ∉ labels
not-listed [] ()
not-listed {label = label} (different ∷ rest) (Any.here refl) with trans (sym (D.stringEqual-refl label)) different
... | ()
not-listed (different ∷ rest) (Any.there p) = not-listed rest p

accepted-counters : ∀ env call {s x t es requests} →
  AcceptedCall env call s x t es requests → CountersAdvance s t
accepted-counters env call {s} {t = t} (activated c dispatchWitness E) = record
  { nonce = frame-≤ "auth_nonce" {s = s} {t = t} (Activation.unchanged E "auth_nonce" refl refl refl refl refl)
  ; epoch = frame-≤ "device_epoch" {s = s} {t = t} (Activation.unchanged E "device_epoch" refl refl refl refl refl)
  ; generation = frame-≤ "grant_generation" {s = s} {t = t} (Activation.unchanged E "grant_generation" refl refl refl refl refl) }
accepted-counters env call {s} {t = t} (deviceAuthorised c op dispatchWitness E checked encoded) =
  device-counters c op (executionContext address env) (callArguments call) E
accepted-counters env call {s} {t = t} (grantAuthorised c op dispatchWitness w E checked encoded) = record
  { nonce = frame-≤ "auth_nonce" {s = s} {t = t} (execute-grant-frame "auth_nonce" c op (executionContext address env) (callArguments call) w refl refl refl refl refl r)
  ; epoch = frame-≤ "device_epoch" {s = s} {t = t} (execute-grant-frame "device_epoch" c op (executionContext address env) (callArguments call) w refl refl refl refl refl r)
  ; generation = frame-≤ "grant_generation" {s = s} {t = t} (execute-grant-frame "grant_generation" c op (executionContext address env) (callArguments call) w refl refl refl refl refl r) }
  where r = run _ (S.Dispatched.executed dispatchWitness)
accepted-counters env call {s} {t = t} (depositedUnshielded dispatchWitness) = record
  { nonce = frame-≤ "auth_nonce" {s = s} {t = t} (public-frame "auth_nonce" (executionContext address env) (callArguments call) refl refl {s = s} {t = t} r)
  ; epoch = frame-≤ "device_epoch" {s = s} {t = t} (public-frame "device_epoch" (executionContext address env) (callArguments call) refl refl {s = s} {t = t} r)
  ; generation = frame-≤ "grant_generation" {s = s} {t = t} (public-frame "grant_generation" (executionContext address env) (callArguments call) refl refl {s = s} {t = t} r) }
  where r = run _ (S.Dispatched.executed dispatchWitness)
accepted-counters env call {s} {t = t} (depositedShielded dispatchWitness) = record
  { nonce = frame-≤ "auth_nonce" {s = s} {t = t} (private-frame "auth_nonce" (executionContext address env) (callArguments call) refl refl refl r)
  ; epoch = frame-≤ "device_epoch" {s = s} {t = t} (private-frame "device_epoch" (executionContext address env) (callArguments call) refl refl refl r)
  ; generation = frame-≤ "grant_generation" {s = s} {t = t} (private-frame "grant_generation" (executionContext address env) (callArguments call) refl refl refl r) }
  where r = run _ (S.Dispatched.executed dispatchWitness)
accepted-counters env call {s} {t = t} (recoverySubmitted dispatchWitness E recoverySig successorSig encoded) = record
  { nonce = frame-≤ "auth_nonce" {s = s} {t = t} (R.Frames.unwritten (R.Submission.Evidence.frame E) "auth_nonce"
      (not-listed (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ [])))
  ; epoch = frame-≤ "device_epoch" {s = s} {t = t} (R.Frames.unwritten (R.Submission.Evidence.frame E) "device_epoch"
      (not-listed (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ [])))
  ; generation = frame-≤ "grant_generation" {s = s} {t = t} (R.Frames.unwritten (R.Submission.Evidence.frame E) "grant_generation"
      (not-listed (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []))) }
accepted-counters env call {s} {t = t} (recoveryFinalised dispatchWitness E) = record
  { nonce = increases "auth_nonce" (R.Finalisation.Evidence.nonceCell E) (R.Finalisation.Evidence.advancesNonce E)
  ; epoch = increases "device_epoch" (R.Finalisation.Evidence.epochCell E) (R.Finalisation.Evidence.advancesEpoch E)
  ; generation = frame-≤ "grant_generation" {s = s} {t = t} (R.Frames.unwritten (R.Finalisation.Evidence.frame E) "grant_generation"
      (not-listed (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []))) }
  where
  increases : ∀ k {v} → R.Stores s k v → R.Stores t k (nat (suc (number v))) →
    counterValue k s ≤ counterValue k t
  increases k before after rewrite cell-number k s (R.Stores.observed before) |
    cell-number k t (R.Stores.observed after) = n≤1+n _

reverted-state : ∀ {ctx call s e t} →
  Account.Transition P ctx call s (Account.reverted e) t → t ≡ s
reverted-state {ctx} {call} {s} (Account.transition execution)
  with Conformance.FullAccount.dispatch P ctx call s
... | rejected _ with execution
... | refl = refl
reverted-state (Account.transition ()) | accepted _ _ _

step-counters : ∀ {s t} → Runs.Step s t → CountersAdvance s t
step-counters (Runs.event env call (Account.reverted e) executed) with reverted-state executed
... | refl = record { nonce = ≤-refl ; epoch = ≤-refl ; generation = ≤-refl }
step-counters (Runs.event env call (Account.committed answer es) executed)
  with SP.accepted-call env call executed
... | _ , evidence , _ = accepted-counters env call evidence

history-counters : ∀ {s t} → Runs.Trace s t → CountersAdvance s t
history-counters ε = record { nonce = ≤-refl ; epoch = ≤-refl ; generation = ≤-refl }
history-counters (step ◅ trace) = record
  { nonce = ≤-trans (CountersAdvance.nonce (step-counters step)) (CountersAdvance.nonce (history-counters trace))
  ; epoch = ≤-trans (CountersAdvance.epoch (step-counters step)) (CountersAdvance.epoch (history-counters trace))
  ; generation = ≤-trans (CountersAdvance.generation (step-counters step)) (CountersAdvance.generation (history-counters trace)) }

-- A stale epoch/generation cannot become current again along any real trace,
-- including traces containing failed calls and arbitrary later recoveries.
stale-epoch-excluded : ∀ {s t c ctx ga g} → Runs.Trace s t →
  number (Conformance.FullAccountLayouts.grantEpoch g) < counterValue "device_epoch" s →
  LiveGrant c ctx ga t g → ⊥
stale-epoch-excluded {t = t} {g = g} trace stale live =
  Data.Nat.Properties.<-irrefl refl
    (subst (λ n → number (Conformance.FullAccountLayouts.grantEpoch g) < n)
      (cell-number "device_epoch" t (LiveGrant.currentEpoch live))
      (<-≤-trans stale (CountersAdvance.epoch (history-counters trace))))

stale-generation-excluded : ∀ {s t c ctx ga g} → Runs.Trace s t →
  number (Conformance.FullAccountLayouts.grantGeneration g) < counterValue "grant_generation" s →
  LiveGrant c ctx ga t g → ⊥
stale-generation-excluded {t = t} {g = g} trace stale live =
  Data.Nat.Properties.<-irrefl refl
    (subst (λ n → number (Conformance.FullAccountLayouts.grantGeneration g) < n)
      (cell-number "grant_generation" t (LiveGrant.currentGeneration live))
      (<-≤-trans stale (CountersAdvance.generation (history-counters trace))))

recovery-epoch-strict : ∀ {ctx s t} → R.Finalisation.Evidence ctx s t →
  counterValue "device_epoch" s < counterValue "device_epoch" t
recovery-epoch-strict {s = s} {t} E rewrite
  cell-number "device_epoch" s (R.Stores.observed (R.Finalisation.Evidence.epochCell E)) |
  cell-number "device_epoch" t (R.Stores.observed (R.Finalisation.Evidence.advancesEpoch E)) = ≤-refl

post-recovery-epoch : ∀ {ctx s recovered later} → R.Finalisation.Evidence ctx s recovered →
  Runs.Trace recovered later → counterValue "device_epoch" s < counterValue "device_epoch" later
post-recovery-epoch E trace = <-≤-trans (recovery-epoch-strict E) (CountersAdvance.epoch (history-counters trace))

post-device-nonce : ∀ {c op ctx xs s t later x} → DeviceCall c op ctx xs s x t →
  Runs.Trace t later → counterValue "auth_nonce" s < counterValue "auth_nonce" later
post-device-nonce E trace = <-≤-trans (advanced-< (DeviceCall.nonceAdvanced E))
  (CountersAdvance.nonce (history-counters trace))

member-witness : ∀ entry entries → member entry entries ≡ true → entry ∈ entries
member-witness entry [] ()
member-witness entry (x ∷ xs) live with equal entry x in same
... | true = Any.here (G.equal-sound entry x same)
... | false = Any.there (member-witness entry xs live)

witness-member : ∀ {entry entries} → entry ∈ entries → member entry entries ≡ true
witness-member {entry = entry} (Any.here {xs = xs} refl) =
  cong (λ b → b ∨ member entry xs) (G.equal-refl entry)
witness-member {entry = entry} (Any.there {x = x} p) with equal entry x
... | true = refl
... | false = witness-member p

append-witness : ∀ {entry : Value} (xs ys : List Value) → entry ∈ (xs ++ ys) → (entry ∈ xs) ⊎ (entry ∈ ys)
append-witness [] ys p = inj₂ p
append-witness (x ∷ xs) ys (Any.here p) = inj₁ (Any.here p)
append-witness (x ∷ xs) ys (Any.there p) with append-witness xs ys p
... | inj₁ q = inj₁ (Any.there q)
... | inj₂ q = inj₂ q

insert-origin : ∀ {entry} next xs → entry ∈ insertSet next xs → (entry ∈ xs) ⊎ (entry ≡ next)
insert-origin next xs p with member next xs
... | true = inj₁ p
... | false with append-witness xs (next ∷ []) p
... | inj₁ q = inj₁ q
... | inj₂ (Any.here same) = inj₂ same
... | inj₂ (Any.there ())

remove-origin : ∀ {entry} old xs → entry ∈ removeSet old xs → entry ∈ xs
remove-origin old [] ()
remove-origin old (x ∷ xs) p with equal old x
... | true = Any.there (remove-origin old xs p)
... | false with p
... | Any.here q = Any.here q
... | Any.there q = Any.there (remove-origin old xs q)

inserted-membership : ∀ entry next entries value →
  value ≡ tuple (insertSet next entries) → member entry (fields value) ≡ true →
  (member entry entries ≡ true) ⊎ (entry ≡ next)
inserted-membership entry next entries value installed live with insert-origin next entries
  (member-witness entry (insertSet next entries)
    (subst (λ v → member entry (fields v) ≡ true) installed live))
... | inj₁ old = inj₁ (witness-member {entry = entry} {entries = entries} old)
... | inj₂ same = inj₂ same

removed-membership : ∀ entry old entries value →
  value ≡ tuple (removeSet old entries) → member entry (fields value) ≡ true →
  member entry entries ≡ true
removed-membership entry old entries value installed live =
  witness-member {entry = entry} {entries = entries}
    (remove-origin old entries (member-witness entry (removeSet old entries)
      (subst (λ v → member entry (fields v) ≡ true) installed live)))

devices-frame : ∀ {s t entry} → lookupCell "devices" (ledger t) ≡ lookupCell "devices" (ledger s) →
  member entry (fields (cell "devices" t)) ≡ true → member entry (fields (cell "devices" s)) ≡ true
devices-frame {s} {t} same live with lookupCell "devices" (ledger t) | lookupCell "devices" (ledger s) | same
... | just v | .(just v) | refl = live
... | Data.Maybe.Base.nothing | .Data.Maybe.Base.nothing | refl = live

-- Only addDevice can insert an entry in an operation body. removeDevice is
-- deliberately a subset argument, not a false frame assertion.
body-device-origin : ∀ op ctx xs coin callerEntry {s x t entry} →
  Run (body op ctx xs coin callerEntry) s x t →
  member entry (fields (cell "devices" t)) ≡ true →
  (member entry (fields (cell "devices" s)) ≡ true) ⊎ (entry ≡ get 0 xs × op ≡ addDevice)
body-device-origin addDevice ctx xs coin callerEntry {s} {t = t} {entry = entry} r live
  with then (has "devices" (get 0 xs)) r
... | present , s₁ , tested , rest with D.has-run "devices" (get 0 xs) tested
... | _ , refl with then (assert (not present) "device entry already present") rest
... | _ , s₂ , asserted , rest₂ with D.assert-run (not present) "device entry already present" asserted
... | _ , refl with then (include "devices" (get 0 xs)) rest₂
... | _ , s₃ , included , rest₃ with D.include-run "devices" (get 0 xs) included
... | refl with inserted-membership entry (get 0 xs) (fields (cell "devices" s)) (cell "devices" s₃)
  (D.cell-insert-same "devices" (tuple (insertSet (get 0 xs) (fields (cell "devices" s)))) (ledger s))
  (devices-frame {s = s₃} {t = t}
    (D.preserves-bind (D.bump-preserves {k = "devices"} "device_count" 8 refl)
      (λ _ → D.return-preserves unit) rest₃) live)
... | inj₁ old = inj₁ old
... | inj₂ same = inj₂ (same , refl)
body-device-origin removeDevice ctx xs coin callerEntry {s} {t = t} {entry = entry} r live
  with then (readCount "device_count") r
... | count , s₁ , counted , rest with D.readCount-run "device_count" counted
... | _ , _ , _ , refl with then (assert (1 Data.Nat.Base.<ᵇ count) "cannot remove last device") rest
... | _ , s₂ , asserted , rest₂ with D.assert-run (1 Data.Nat.Base.<ᵇ count) "cannot remove last device" asserted
... | _ , refl with then (assert (not (equal (get 0 xs) callerEntry)) "cannot remove the authorising device") rest₂
... | _ , s₃ , asserted₂ , rest₃ with D.assert-run (not (equal (get 0 xs) callerEntry)) "cannot remove the authorising device" asserted₂
... | _ , refl with then (has "devices" (get 0 xs)) rest₃
... | present , s₄ , tested , rest₄ with D.has-run _ _ tested
... | _ , refl with then (assert present "unknown device entry") rest₄
... | _ , s₅ , asserted₃ , rest₅ with D.assert-run present "unknown device entry" asserted₃
... | _ , refl with then (exclude "devices" (get 0 xs)) rest₅
... | _ , s₆ , excluded , rest₆ with D.exclude-run _ _ excluded
... | refl = inj₁ (removed-membership entry (get 0 xs) (fields (cell "devices" s)) (cell "devices" s₆)
  (D.cell-insert-same "devices" (tuple (removeSet (get 0 xs) (fields (cell "devices" s)))) (ledger s))
  (devices-frame {s = s₆} {t = t}
    (D.preserves-bind (D.readCount-preserves {k = "devices"} "device_count")
      (λ current → D.preserves-bind
        (D.writeCount-preserves {k = "devices"} "device_count" 8 (current Data.Nat.Base.∸ 1) refl)
        (λ _ → D.return-preserves unit)) rest₆) live))
body-device-origin withdrawUnshielded ctx xs coin e {s} {t = t} r live = inj₁ (devices-frame {s = s} {t = t} (D.body-frame "devices" withdrawUnshielded ctx xs coin e (refl ∷ []) r) live)
body-device-origin withdrawShielded ctx xs coin e {s} {t = t} r live = inj₁ (devices-frame {s = s} {t = t} (D.body-frame "devices" withdrawShielded ctx xs coin e [] r) live)
body-device-origin withdrawToContract ctx xs coin e {s} {t = t} r live = inj₁ (devices-frame {s = s} {t = t} (D.body-frame "devices" withdrawToContract ctx xs coin e [] r) live)
body-device-origin appendInbox ctx xs coin e {s} {t = t} r live = inj₁ (devices-frame {s = s} {t = t} (D.body-frame "devices" appendInbox ctx xs coin e (refl ∷ refl ∷ []) r) live)
body-device-origin rotateEncKey ctx xs coin e {s} {t = t} r live = inj₁ (devices-frame {s = s} {t = t} (D.body-frame "devices" rotateEncKey ctx xs coin e (refl ∷ []) r) live)
body-device-origin issueGrant ctx xs coin e {s} {t = t} r live = inj₁ (devices-frame {s = s} {t = t} (D.body-frame "devices" issueGrant ctx xs coin e (refl ∷ []) r) live)
body-device-origin revokeGrant ctx xs coin e {s} {t = t} r live = inj₁ (devices-frame {s = s} {t = t} (D.body-frame "devices" revokeGrant ctx xs coin e (refl ∷ []) r) live)
body-device-origin revokeAllGrants ctx xs coin e {s} {t = t} r live = inj₁ (devices-frame {s = s} {t = t} (D.body-frame "devices" revokeAllGrants ctx xs coin e (refl ∷ refl ∷ []) r) live)
body-device-origin publishRecovery ctx xs coin e {s} {t = t} r live = inj₁ (devices-frame {s = s} {t = t} (D.body-frame "devices" publishRecovery ctx xs coin e (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []) r) live)
body-device-origin cancelRecovery ctx xs coin e {s} {t = t} r live = inj₁ (devices-frame {s = s} {t = t} (D.body-frame "devices" cancelRecovery ctx xs coin e (refl ∷ refl ∷ refl ∷ refl ∷ []) r) live)

device-origin : ∀ c op ctx xs {s x t entry} → (E : DeviceCall c op ctx xs s x t) →
  member entry (fields (cell "devices" t)) ≡ true →
  (member entry (fields (cell "devices" s)) ≡ true) ⊎
  (member entry (deviceSeeds op (deviceArguments op xs) (DeviceCall.rolledEntry E)) ≡ true)
device-origin c op ctx xs {s} {entry = entry} E live with body-device-origin op ctx
  (deviceArguments op xs) (deviceCoin op ctx) (DeviceCall.callerEntry E) (DeviceCall.bodyRun E) live
... | inj₂ (same , refl) = inj₂ (witness-member
  {entries = deviceSeeds addDevice (deviceArguments addDevice xs) (DeviceCall.rolledEntry E)}
  (Any.there (Any.here same)))
... | inj₁ rolledLive with inserted-membership entry (DeviceCall.rolledEntry E)
  (removeSet (Authorisation.current (DeviceCall.authorised E)) (fields (cell "devices" s)))
  (cell "devices" (DeviceCall.authorisedState E))
  (Authorisation.devicesRolled (DeviceCall.authorised E)) rolledLive
... | inj₁ old = inj₁ (witness-member {entries = fields (cell "devices" s)} (remove-origin
  (Authorisation.current (DeviceCall.authorised E)) (fields (cell "devices" s))
  (member-witness entry
    (removeSet (Authorisation.current (DeviceCall.authorised E)) (fields (cell "devices" s))) old)))
... | inj₂ same = inj₂ (witness-member
  {entries = deviceSeeds op (deviceArguments op xs) (DeviceCall.rolledEntry E)} (Any.here same))

accepted-device-origin : ∀ env call {s x t es requests entry} →
  (E : AcceptedCall env call s x t es requests) →
  member entry (fields (cell "devices" t)) ≡ true →
  (member entry (fields (cell "devices" s)) ≡ true) ⊎ (member entry (introducedEntries E) ≡ true)
accepted-device-origin env call {s} {t = t} {entry = entry} (activated c dispatchWitness E) live
  with inserted-membership entry (Activation.initial E) (fields (cell "devices" s))
    (cell "devices" t) (Activation.installed E) live
... | inj₁ old = inj₁ old
... | inj₂ same = inj₂ (witness-member {entries = Activation.initial E ∷ []} (Any.here same))
accepted-device-origin env call {s} {t = t} (deviceAuthorised c op dispatchWitness E checked encoded) =
  device-origin c op _ _ E
accepted-device-origin env call {s} {t = t} (grantAuthorised c op dispatchWitness w E checked encoded) live =
  inj₁ (devices-frame {s = s} {t = t} (execute-grant-frame "devices" c op (executionContext address env) (callArguments call) w refl refl refl refl refl
    (run _ (S.Dispatched.executed dispatchWitness))) live)
accepted-device-origin env call {s} {t = t} (depositedUnshielded dispatchWitness) live =
  inj₁ (devices-frame {s = s} {t = t} (public-frame "devices" (executionContext address env) (callArguments call) refl refl {s = s} {t = t} (run _ (S.Dispatched.executed dispatchWitness))) live)
accepted-device-origin env call {s} {t = t} (depositedShielded dispatchWitness) live =
  inj₁ (devices-frame {s = s} {t = t} (private-frame "devices" (executionContext address env) (callArguments call) refl refl refl (run _ (S.Dispatched.executed dispatchWitness))) live)
accepted-device-origin env call {s} {t = t} (recoverySubmitted dispatchWitness E recoverySig successorSig encoded) live =
  inj₁ (devices-frame {s = s} {t = t} (R.Frames.unwritten (R.Submission.Evidence.frame E) "devices"
    (not-listed (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []))) live)
accepted-device-origin env call {t = t} {entry = entry} (recoveryFinalised dispatchWitness E) live =
  inj₂ (subst (λ ds → member entry (fields ds) ≡ true)
    (D.cell-lookup "devices" t (R.Stores.observed (R.Finalisation.Evidence.replacesDevices E))) live)

entry-reindex : ∀ {s c a count epoch entry} →
  lookupCell "device_epoch" (ledger s) ≡ just epoch →
  Run (entryAt c address a (number epoch) count) s entry s →
  Run (entryAt c address a (counterValue "device_epoch" s) count) s entry s
entry-reindex {s} {c} {a} {count} {entry = entry} found = subst
  (λ epoch → Run (entryAt c address a epoch count) s entry s)
  (sym (cell-number "device_epoch" s found))

enrolled-origin : ∀ {entry} op xs → entry ∈ enrolledSeeds op xs →
  entry ≡ get 0 xs × op ≡ addDevice
enrolled-origin addDevice xs (Any.here same) = same , refl
enrolled-origin addDevice xs (Any.there ())
enrolled-origin withdrawUnshielded xs ()
enrolled-origin withdrawShielded xs ()
enrolled-origin withdrawToContract xs ()
enrolled-origin appendInbox xs ()
enrolled-origin rotateEncKey xs ()
enrolled-origin removeDevice xs ()
enrolled-origin issueGrant xs ()
enrolled-origin revokeGrant xs ()
enrolled-origin revokeAllGrants xs ()
enrolled-origin publishRecovery xs ()
enrolled-origin cancelRecovery xs ()

introduction-sound : ∀ {env call s x t es requests entry}
  (E : AcceptedCall env call s x t es requests) →
  member entry (introducedEntries E) ≡ true → EntryIntroduction entry s env call
introduction-sound {call = call} {s = s} {entry = entry} (activated c dispatchWitness E) introduced
  with member-witness entry (Activation.initial E ∷ []) introduced
... | Any.here refl = bootstrapped c (S.Dispatched.resolved dispatchWitness)
  (entry-reindex {s = s} {c = c} {a = Semantics.parseActivation c (callArguments call)}
    {count = 0} (Activation.epochCell E) (Activation.initialEntry E))
... | Any.there ()
introduction-sound {call = call} {s = s} {entry = entry} (deviceAuthorised c op dispatchWitness E checked encoded) introduced
  with member-witness entry (deviceSeeds op (deviceArguments op (callArguments call))
    (DeviceCall.rolledEntry E)) introduced
... | Any.here refl = rolled c op (S.Dispatched.resolved dispatchWitness)
  (entry-reindex {s = s} {c = c} {a = deviceAuth c op (callArguments call)}
    {count = suc (counter (deviceAuth c op (callArguments call)))}
    (Authorisation.epochCell (DeviceCall.authorised E)) (Authorisation.nextEntry (DeviceCall.authorised E)))
... | Any.there p with enrolled-origin op (deviceArguments op (callArguments call)) p
... | same , refl = enrolled c (S.Dispatched.resolved dispatchWitness) (sym same)
introduction-sound (grantAuthorised _ _ _ _ _ _ _) ()
introduction-sound (depositedUnshielded _) ()
introduction-sound (depositedShielded _) ()
introduction-sound (recoverySubmitted _ _ _ _ _) ()
introduction-sound {s = s} {entry = entry} (recoveryFinalised dispatchWitness E) introduced
  with member-witness entry (R.Finalisation.Evidence.successor E ∷ []) introduced
... | Any.here refl = recoveredSuccessor (S.Dispatched.resolved dispatchWitness)
  (D.cell-lookup "pending_entry" s (R.Stores.observed (R.Finalisation.Evidence.successorCell E)))
... | Any.there ()

history-device-origin : ∀ {s t entry} (trace : Runs.Trace s t) →
  member entry (fields (cell "devices" t)) ≡ true →
  (member entry (fields (cell "devices" s)) ≡ true) ⊎ IntroducedIn entry trace
history-device-origin ε live = inj₁ live
history-device-origin (step ◅ trace) live with history-device-origin trace live
... | inj₂ origin = inj₂ (introducedLater origin)
history-device-origin (Runs.event env call (Account.reverted e) executed ◅ trace) live | inj₁ previous
  with reverted-state executed
... | refl = inj₁ previous
history-device-origin (Runs.event env call (Account.committed x es) executed ◅ trace) live | inj₁ previous
  with SP.accepted-call env call executed
... | requests , E , _ with accepted-device-origin env call E previous
... | inj₁ original = inj₁ original
... | inj₂ introduced = inj₂ (here (introduction-sound E introduced))

post-recovery-device-origin : ∀ {ctx s recovered later entry} →
  (E : R.Finalisation.Evidence ctx s recovered) → (trace : Runs.Trace recovered later) →
  member entry (fields (cell "devices" later)) ≡ true →
  (entry ≡ R.Finalisation.Evidence.successor E) ⊎ IntroducedIn entry trace
post-recovery-device-origin {recovered = recovered} {entry = entry} E trace live
  with history-device-origin trace live
... | inj₂ introduced = inj₂ introduced
... | inj₁ previous with member-witness entry (R.Finalisation.Evidence.successor E ∷ [])
  (subst (λ ds → member entry (fields ds) ≡ true)
    (D.cell-lookup "devices" recovered (R.Stores.observed (R.Finalisation.Evidence.replacesDevices E))) previous)
... | Any.here same = inj₁ same
... | Any.there ()

authorisation-opened : ∀ {env c a h s next t} →
  (A : Authorisation c (executionContext address env) a h s next t) →
  Run (entryAt c address a (counterValue "device_epoch" s) (counter a)) s (Authorisation.current A) s
authorisation-opened {c = c} {a = a} {s = s} A =
  subst (λ epoch → Run (entryAt c address a epoch (counter a)) s (Authorisation.current A) s)
    (sym (cell-number "device_epoch" s (Authorisation.epochCell A))) (Authorisation.currentEntry A)

protected-device-excluded : ∀ {ctx s recovered later env c op xs x after} →
  (recovery : R.Finalisation.Evidence ctx s recovered) →
  (trace : Runs.Trace recovered later) →
  RelevantEntrySeparation c (deviceAuth c op xs) (counterValue "device_epoch" later)
    (R.Finalisation.Evidence.successor recovery) trace →
  DeviceCall c op (executionContext address env) xs later x after → ⊥
protected-device-excluded {later = later} {c = c} {op} {xs} recovery trace separation call
  with post-recovery-device-origin recovery trace
    (Authorisation.currentLive (DeviceCall.authorised call))
... | inj₁ same = RelevantEntrySeparation.successorSeparated separation
  (authorisation-opened (DeviceCall.authorised call)) same
... | inj₂ introduced = RelevantEntrySeparation.insertionsSeparated separation
  (authorisation-opened (DeviceCall.authorised call)) introduced refl

rooted-counters : ∀ {s t} → Runs.History s → Runs.Trace s t → CountersAdvance s t
rooted-counters history = history-counters

recovery-boundary : ∀ {s recovered} → (history : Runs.History s) →
  (event : CommittedOccurrence s recovered) →
  S.resolve (RuntimeCall.request (CommittedOccurrence.call event)) ≡ just Semantics.finaliseRecovery →
  RecoveryBoundary s recovered
recovery-boundary history event resolved = record
  { history = history ; event = event ; finaliseResolved = resolved
  ; evidence = S.EnactsOccurrence.finalisation (SP.finalisation-enacts-occurrence
      (CommittedOccurrence.environment event) (CommittedOccurrence.call event) history resolved
      (CommittedOccurrence.executed event)) }

runtime-post-recovery-epoch : ∀ {s recovered later} → RecoveryBoundary s recovered →
  Runs.Trace recovered later → counterValue "device_epoch" s < counterValue "device_epoch" later
runtime-post-recovery-epoch boundary = post-recovery-epoch (RecoveryBoundary.evidence boundary)

runtime-post-device-nonce : ∀ {c op s t later} → DeviceBoundary c op s t →
  Runs.Trace t later → counterValue "auth_nonce" s < counterValue "auth_nonce" later
runtime-post-device-nonce boundary = post-device-nonce (DeviceBoundary.evidence boundary)

runtime-post-recovery-device-origin : ∀ {s recovered later entry} →
  (boundary : RecoveryBoundary s recovered) → (trace : Runs.Trace recovered later) →
  member entry (fields (cell "devices" later)) ≡ true →
  (entry ≡ R.Finalisation.Evidence.successor (RecoveryBoundary.evidence boundary)) ⊎ IntroducedIn entry trace
runtime-post-recovery-device-origin boundary = post-recovery-device-origin (RecoveryBoundary.evidence boundary)

runtime-protected-device-excluded : ∀ {s recovered later c op after} →
  (recovery : RecoveryBoundary s recovered) → (trace : Runs.Trace recovered later) →
  (device : DeviceBoundary c op later after) →
  RelevantEntrySeparation c
    (deviceAuth c op (occurrenceArguments (DeviceBoundary.event device)))
    (counterValue "device_epoch" later)
    (R.Finalisation.Evidence.successor (RecoveryBoundary.evidence recovery)) trace → ⊥
runtime-protected-device-excluded recovery trace device separation =
  protected-device-excluded (RecoveryBoundary.evidence recovery) trace separation (DeviceBoundary.evidence device)

bump-< : ∀ k bits {s x t} → Run (bump k bits) s x t → counterValue k s < counterValue k t
bump-< k bits {s} r with D.bump-run k bits r
... | v , found , bounded , refl rewrite cell-number k s found |
  D.cell-insert-same k (nat (suc (number v))) (ledger s) = ≤-refl

revoke-all-body-strict : ∀ ctx xs coin entry {s x t} →
  Run (body revokeAllGrants ctx xs coin entry) s x t →
  counterValue "grant_generation" s < counterValue "grant_generation" t
revoke-all-body-strict ctx xs coin entry r with then (bump "grant_generation" 32 >> clear "grants") r
... | _ , u , prefix , returned with D.return-run unit returned
... | refl , refl with then (bump "grant_generation" 32) prefix
... | _ , middle , bumped , cleared = <-≤-trans (bump-< "grant_generation" 32 bumped)
  (frame-≤ "grant_generation" {s = middle} {t = u} (D.clear-preserves {k = "grant_generation"} "grants" refl cleared))

post-revoke-all-generation : ∀ {c s t later} → DeviceBoundary c revokeAllGrants s t →
  Runs.Trace t later → counterValue "grant_generation" s < counterValue "grant_generation" later
post-revoke-all-generation {s = s} {t = t} boundary trace = <-≤-trans strict
  (CountersAdvance.generation (history-counters trace))
  where
  E = DeviceBoundary.evidence boundary
  boundaryEvent = DeviceBoundary.event boundary
  ctx = occurrenceContext boundaryEvent
  xs = occurrenceArguments boundaryEvent
  strict : counterValue "grant_generation" s < counterValue "grant_generation" t
  strict = subst (λ n → n < counterValue "grant_generation" t)
    (frame-number "grant_generation" {s = s} {t = DeviceCall.authorisedState E}
      (Authorisation.unchanged (DeviceCall.authorised E) "grant_generation" refl refl refl))
    (revoke-all-body-strict ctx (deviceArguments revokeAllGrants xs)
      (deviceCoin revokeAllGrants ctx) (DeviceCall.callerEntry E) (DeviceCall.bodyRun E))

just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

equal-false : ∀ {x y} → x ≢ y → equal x y ≡ false
equal-false {x} {y} different with equal x y in same
... | true = ⊥-elim (different (G.equal-sound x y same))
... | false = refl

map-insert-same : ∀ id updated entries → lookupMap id (insertMap id updated entries) ≡ just updated
map-insert-same id updated [] rewrite G.equal-refl id = refl
map-insert-same id updated (tuple (k ∷ v ∷ []) ∷ entries) with equal id k in same
... | true rewrite G.equal-refl id = refl
... | false rewrite same = map-insert-same id updated entries
map-insert-same id updated (nat _ ∷ entries) = map-insert-same id updated entries
map-insert-same id updated (bool _ ∷ entries) = map-insert-same id updated entries
map-insert-same id updated (bytes _ ∷ entries) = map-insert-same id updated entries
map-insert-same id updated (none ∷ entries) = map-insert-same id updated entries
map-insert-same id updated (some _ ∷ entries) = map-insert-same id updated entries
map-insert-same id updated (tuple [] ∷ entries) = map-insert-same id updated entries
map-insert-same id updated (tuple (_ ∷ []) ∷ entries) = map-insert-same id updated entries
map-insert-same id updated (tuple (_ ∷ _ ∷ _ ∷ _) ∷ entries) = map-insert-same id updated entries

map-insert-other : ∀ target id updated entries → target ≢ id →
  lookupMap target (insertMap id updated entries) ≡ lookupMap target entries
map-insert-other target id updated [] different rewrite equal-false different = refl
map-insert-other target id updated (tuple (k ∷ v ∷ []) ∷ entries) different with equal id k in same
... | true with G.equal-sound id k same
... | refl rewrite equal-false different = refl
map-insert-other target id updated (tuple (k ∷ v ∷ []) ∷ entries) different | false
  with equal target k
... | true = refl
... | false = map-insert-other target id updated entries different
map-insert-other target id updated (nat _ ∷ entries) different = map-insert-other target id updated entries different
map-insert-other target id updated (bool _ ∷ entries) different = map-insert-other target id updated entries different
map-insert-other target id updated (bytes _ ∷ entries) different = map-insert-other target id updated entries different
map-insert-other target id updated (none ∷ entries) different = map-insert-other target id updated entries different
map-insert-other target id updated (some _ ∷ entries) different = map-insert-other target id updated entries different
map-insert-other target id updated (tuple [] ∷ entries) different = map-insert-other target id updated entries different
map-insert-other target id updated (tuple (_ ∷ []) ∷ entries) different = map-insert-other target id updated entries different
map-insert-other target id updated (tuple (_ ∷ _ ∷ _ ∷ _) ∷ entries) different = map-insert-other target id updated entries different

revoked-inactive : ∀ old → grantActive old ≡ bool true → grantActive (GE.revokedRecord old) ≡ bool false
revoked-inactive old active with fields old
revoked-inactive old () | []
revoked-inactive old () | _ ∷ []
revoked-inactive old () | _ ∷ _ ∷ []
revoked-inactive old () | _ ∷ _ ∷ _ ∷ []
revoked-inactive old () | _ ∷ _ ∷ _ ∷ _ ∷ []
revoked-inactive old () | _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ []
revoked-inactive old () | _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ []
revoked-inactive old () | _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ []
revoked-inactive old active | _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ = refl

disabled-frame : ∀ {id s t} → cell "grants" t ≡ cell "grants" s → GrantDisabled id s → GrantDisabled id t
disabled-frame {id} frame disabled g found = disabled g
  (trans (sym (cong (λ v → lookupMap id (fields v)) frame)) found)

disabled-other-insert : ∀ {target id updated s t} →
  cell "grants" t ≡ tuple (insertMap id updated (fields (cell "grants" s))) →
  target ≢ id → GrantDisabled target s → GrantDisabled target t
disabled-other-insert {target} {id} {updated} {s} installed different disabled g found =
  disabled g (trans (sym (trans (cong (λ v → lookupMap target (fields v)) installed)
    (map-insert-other target id updated (fields (cell "grants" s)) different))) found)

disabled-inactive-insert : ∀ {id updated s t} →
  cell "grants" t ≡ tuple (insertMap id updated (fields (cell "grants" s))) →
  grantActive updated ≡ bool false → GrantDisabled id t
disabled-inactive-insert {id} {updated} {s} installed inactive g found active
  with just-injective (trans (sym found) (trans (cong (λ v → lookupMap id (fields v)) installed)
    (map-insert-same id updated (fields (cell "grants" s)))))
... | refl with trans (sym inactive) active
... | ()

NoMatchingIssue : ∀ {s t} → Value → GE.GrantEffect s t → Set
NoMatchingIssue target (GE.grantIssued xs _ _ _) = target ≢ IssueArguments.id xs
NoMatchingIssue target _ = ⊤

false-not-true : false ≢ true
false-not-true ()

false-equal-different : ∀ {x y} → equal x y ≡ false → x ≢ y
false-equal-different {x} same refl = false-not-true (trans (sym same) (G.equal-refl x))

effect-preserves-disabled : ∀ {s t target} (effect : GE.GrantEffect s t) →
  NoMatchingIssue target effect → GrantDisabled target s → GrantDisabled target t
effect-preserves-disabled {s} {t} {target} (GE.kept frame) noIssue =
  disabled-frame {id = target} {s = s} {t = t} frame
effect-preserves-disabled {s} {t} {target} (GE.grantIssued xs source frame issued) different disabled =
  disabled-other-insert {target = target} {id = IssueArguments.id xs} {updated = GE.issuedRecord issued}
    {s = source} {t = t} (GE.IssueResult.installed issued) different
    (disabled-frame {id = target} {s = s} {t = source} frame disabled)
effect-preserves-disabled {s} {t} {target} (GE.grantRevoked id source frame revoked) noIssue disabled
  with equal target id in same
... | true with G.equal-sound target id same
... | refl = disabled-inactive-insert {id = id} {updated = GE.revokedRecord (GE.RevokeResult.old revoked)}
  {s = source} {t = t} (GE.RevokeResult.installed revoked)
  (revoked-inactive (GE.RevokeResult.old revoked) (GE.RevokeResult.active revoked))
effect-preserves-disabled {s} {t} {target} (GE.grantRevoked id source frame revoked) noIssue disabled | false =
  disabled-other-insert {target = target} {id = id} {updated = GE.revokedRecord (GE.RevokeResult.old revoked)}
    {s = source} {t = t} (GE.RevokeResult.installed revoked) (false-equal-different same)
    (disabled-frame {id = target} {s = s} {t = source} frame disabled)
effect-preserves-disabled {target = target} (GE.cleared empty) noIssue disabled g found active
  with trans (sym (cong (λ v → lookupMap target (fields v)) empty)) found
... | ()
effect-preserves-disabled {s} {t} {target} (GE.grantSpent c op ctx ga xs w spent) noIssue disabled
  with equal target (identifier (GE.SpendMutation.evidence spent)) in same
... | true with G.equal-sound target (identifier (GE.SpendMutation.evidence spent)) same
... | refl = λ g found active → disabled (grantRecord (GE.SpendMutation.evidence spent))
  (EP.lookup-found "grants" (identifier (GE.SpendMutation.evidence spent)) (recorded (GE.SpendMutation.evidence spent)))
  (LiveGrant.active (live (GE.SpendMutation.evidence spent)))
effect-preserves-disabled {s} {t} {target} (GE.grantSpent c op ctx ga xs w spent) noIssue disabled | false =
  disabled-other-insert {target = target} {id = identifier (GE.SpendMutation.evidence spent)}
    {updated = settledGrant (grantRecord (GE.SpendMutation.evidence spent))
      (suc (number (Conformance.FullAccountLayouts.grantNonce (grantRecord (GE.SpendMutation.evidence spent)))))
      (Settlement.commitment (settlement (GE.SpendMutation.evidence spent)))}
    {s = s} {t = t} (GE.SpendMutation.installed spent) (false-equal-different same) disabled

accepted-grant-effect : ∀ env call {s x t es requests} →
  AcceptedCall env call s x t es requests → GE.GrantEffect s t
accepted-grant-effect env call {s} {t = t} (activated c dispatchWitness E) =
  EP.execute-effect (GE.activationEntry c) (executionContext address env)
    (callArguments call) {s = s} {t = t} (run _ (S.Dispatched.executed dispatchWitness))
accepted-grant-effect env call {s} {t = t} (deviceAuthorised c op dispatchWitness E checked encoded) =
  EP.body-effect op (executionContext address env)
    (deviceArguments op (callArguments call))
    (deviceCoin op (executionContext address env)) (DeviceCall.callerEntry E)
    {before = s} {source = DeviceCall.authorisedState E} {after = t}
    (EP.cell-frame "grants" s (DeviceCall.authorisedState E)
      (Authorisation.unchanged (DeviceCall.authorised E) "grants" refl refl refl))
    (DeviceCall.bodyRun E)
accepted-grant-effect env call {s} {t = t} (grantAuthorised c op dispatchWitness w E checked encoded) =
  EP.execute-effect (GE.grantEntry c op w) (executionContext address env)
    (callArguments call) {s = s} {t = t} (run _ (S.Dispatched.executed dispatchWitness))
accepted-grant-effect env call {s} {t = t} (depositedUnshielded dispatchWitness) =
  EP.execute-effect GE.publicDepositEntry (executionContext address env)
    (callArguments call) {s = s} {t = t} (run _ (S.Dispatched.executed dispatchWitness))
accepted-grant-effect env call {s} {t = t} (depositedShielded dispatchWitness) =
  EP.execute-effect GE.privateDepositEntry (executionContext address env)
    (callArguments call) {s = s} {t = t} (run _ (S.Dispatched.executed dispatchWitness))
accepted-grant-effect env call {s} {t = t} (recoverySubmitted dispatchWitness E recoverySig successorSig encoded) =
  GE.kept (EP.cell-frame "grants" s t (R.Frames.unwritten (R.Submission.Evidence.frame E) "grants"
    (not-listed (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []))))
accepted-grant-effect env call {s} {t = t} (recoveryFinalised dispatchWitness E) =
  GE.kept (EP.cell-frame "grants" s t (R.Frames.unwritten (R.Finalisation.Evidence.frame E) "grants"
    (not-listed (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []))))

accepted-disabled : ∀ env call {s x t u es requests target}
  {executed : Account.Transition P (executionContext address env) (RuntimeCall.request call)
    s (Account.committed x es) t} {rest : Runs.Trace t u} →
  AcceptedCall env call s x t es requests → GrantDisabled target s →
  GrantDisabled target t ⊎ ReissuedIn target (Runs.event env call (Account.committed x es) executed ◅ rest)
accepted-disabled env call (activated c dispatchWitness E) disabled =
  inj₁ (effect-preserves-disabled (accepted-grant-effect env call (activated c dispatchWitness E)) tt disabled)
accepted-disabled env call (deviceAuthorised c withdrawUnshielded dispatchWitness E checked encoded) disabled =
  inj₁ (effect-preserves-disabled (accepted-grant-effect env call (deviceAuthorised c withdrawUnshielded dispatchWitness E checked encoded)) tt disabled)
accepted-disabled env call (deviceAuthorised c withdrawShielded dispatchWitness E checked encoded) disabled =
  inj₁ (effect-preserves-disabled (accepted-grant-effect env call (deviceAuthorised c withdrawShielded dispatchWitness E checked encoded)) tt disabled)
accepted-disabled env call (deviceAuthorised c withdrawToContract dispatchWitness E checked encoded) disabled =
  inj₁ (effect-preserves-disabled (accepted-grant-effect env call (deviceAuthorised c withdrawToContract dispatchWitness E checked encoded)) tt disabled)
accepted-disabled env call (deviceAuthorised c appendInbox dispatchWitness E checked encoded) disabled =
  inj₁ (effect-preserves-disabled (accepted-grant-effect env call (deviceAuthorised c appendInbox dispatchWitness E checked encoded)) tt disabled)
accepted-disabled env call (deviceAuthorised c rotateEncKey dispatchWitness E checked encoded) disabled =
  inj₁ (effect-preserves-disabled (accepted-grant-effect env call (deviceAuthorised c rotateEncKey dispatchWitness E checked encoded)) tt disabled)
accepted-disabled env call (deviceAuthorised c addDevice dispatchWitness E checked encoded) disabled =
  inj₁ (effect-preserves-disabled (accepted-grant-effect env call (deviceAuthorised c addDevice dispatchWitness E checked encoded)) tt disabled)
accepted-disabled env call (deviceAuthorised c removeDevice dispatchWitness E checked encoded) disabled =
  inj₁ (effect-preserves-disabled (accepted-grant-effect env call (deviceAuthorised c removeDevice dispatchWitness E checked encoded)) tt disabled)
accepted-disabled env call {target = target} (deviceAuthorised c issueGrant dispatchWitness E checked encoded) disabled
  with equal target (IssueArguments.id (deviceArguments issueGrant (callArguments call))) in same
... | true = inj₂ (issuedHere (S.Dispatched.resolved dispatchWitness)
  (sym (G.equal-sound target (IssueArguments.id (deviceArguments issueGrant (callArguments call))) same)))
... | false = inj₁ (effect-preserves-disabled
  (accepted-grant-effect env call (deviceAuthorised c issueGrant dispatchWitness E checked encoded))
  (false-equal-different same) disabled)
accepted-disabled env call (deviceAuthorised c revokeGrant dispatchWitness E checked encoded) disabled =
  inj₁ (effect-preserves-disabled (accepted-grant-effect env call (deviceAuthorised c revokeGrant dispatchWitness E checked encoded)) tt disabled)
accepted-disabled env call (deviceAuthorised c revokeAllGrants dispatchWitness E checked encoded) disabled =
  inj₁ (effect-preserves-disabled (accepted-grant-effect env call (deviceAuthorised c revokeAllGrants dispatchWitness E checked encoded)) tt disabled)
accepted-disabled env call (deviceAuthorised c publishRecovery dispatchWitness E checked encoded) disabled =
  inj₁ (effect-preserves-disabled (accepted-grant-effect env call (deviceAuthorised c publishRecovery dispatchWitness E checked encoded)) tt disabled)
accepted-disabled env call (deviceAuthorised c cancelRecovery dispatchWitness E checked encoded) disabled =
  inj₁ (effect-preserves-disabled (accepted-grant-effect env call (deviceAuthorised c cancelRecovery dispatchWitness E checked encoded)) tt disabled)
accepted-disabled env call (grantAuthorised c withdrawUnshielded dispatchWitness unshieldedWithdrawal E checked encoded) disabled =
  inj₁ (effect-preserves-disabled (accepted-grant-effect env call
    (grantAuthorised c withdrawUnshielded dispatchWitness unshieldedWithdrawal E checked encoded)) tt disabled)
accepted-disabled env call (grantAuthorised c withdrawShielded dispatchWitness shieldedWithdrawal E checked encoded) disabled =
  inj₁ (effect-preserves-disabled (accepted-grant-effect env call
    (grantAuthorised c withdrawShielded dispatchWitness shieldedWithdrawal E checked encoded)) tt disabled)
accepted-disabled env call (grantAuthorised c withdrawToContract dispatchWitness contractWithdrawal E checked encoded) disabled =
  inj₁ (effect-preserves-disabled (accepted-grant-effect env call
    (grantAuthorised c withdrawToContract dispatchWitness contractWithdrawal E checked encoded)) tt disabled)
accepted-disabled env call (depositedUnshielded dispatchWitness) disabled =
  inj₁ (effect-preserves-disabled (accepted-grant-effect env call (depositedUnshielded dispatchWitness)) tt disabled)
accepted-disabled env call (depositedShielded dispatchWitness) disabled =
  inj₁ (effect-preserves-disabled (accepted-grant-effect env call (depositedShielded dispatchWitness)) tt disabled)
accepted-disabled env call (recoverySubmitted dispatchWitness E recoverySig successorSig encoded) disabled =
  inj₁ (effect-preserves-disabled (accepted-grant-effect env call
    (recoverySubmitted dispatchWitness E recoverySig successorSig encoded)) tt disabled)
accepted-disabled env call (recoveryFinalised dispatchWitness E) disabled =
  inj₁ (effect-preserves-disabled (accepted-grant-effect env call (recoveryFinalised dispatchWitness E)) tt disabled)

disabled-until-reissue : ∀ {s t target} (trace : Runs.Trace s t) →
  GrantDisabled target s → GrantDisabled target t ⊎ ReissuedIn target trace
disabled-until-reissue ε disabled = inj₁ disabled
disabled-until-reissue (Runs.event env call (Account.reverted e) executed ◅ rest) disabled
  with reverted-state executed
... | refl with disabled-until-reissue rest disabled
... | inj₁ final = inj₁ final
... | inj₂ origin = inj₂ (issuedLater origin)
disabled-until-reissue (Runs.event env call (Account.committed x es) executed ◅ rest) disabled
  with SP.accepted-call env call executed
... | requests , E , _ with accepted-disabled env call {executed = executed} {rest = rest} E disabled
... | inj₂ origin = inj₂ origin
... | inj₁ next with disabled-until-reissue rest next
... | inj₁ final = inj₁ final
... | inj₂ origin = inj₂ (issuedLater origin)

revocation-disables : ∀ {c s t} (boundary : DeviceBoundary c revokeGrant s t) →
  GrantDisabled
    (get 0 (deviceArguments revokeGrant
      (occurrenceArguments (DeviceBoundary.event boundary)))) t
revocation-disables {t = t} boundary =
  disabled-inactive-insert {id = get 0 (deviceArguments revokeGrant xs)}
    {updated = GE.revokedRecord (GE.RevokeResult.old result)}
    {s = DeviceCall.authorisedState E} {t = t} (GE.RevokeResult.installed result)
    (revoked-inactive (GE.RevokeResult.old result) (GE.RevokeResult.active result))
  where
  E = DeviceBoundary.evidence boundary
  boundaryEvent = DeviceBoundary.event boundary
  ctx = occurrenceContext boundaryEvent
  xs = occurrenceArguments boundaryEvent
  result = EP.revoke-body-result ctx (deviceArguments revokeGrant xs)
    (deviceCoin revokeGrant ctx) (DeviceCall.callerEntry E) (DeviceCall.bodyRun E)

revoked-grant-reactivation-origin : ∀ {c s revoked later g}
  (boundary : DeviceBoundary c revokeGrant s revoked) (trace : Runs.Trace revoked later) →
  lookupMap (get 0 (deviceArguments revokeGrant
    (occurrenceArguments (DeviceBoundary.event boundary))))
    (fields (cell "grants" later)) ≡ just g →
  grantActive g ≡ bool true →
  ReissuedIn (get 0 (deviceArguments revokeGrant
    (occurrenceArguments (DeviceBoundary.event boundary)))) trace
revoked-grant-reactivation-origin boundary trace found active
  with disabled-until-reissue trace (revocation-disables boundary)
... | inj₁ disabled = ⊥-elim (disabled _ found active)
... | inj₂ origin = origin

revoked-grant-excluded : ∀ {c s revoked later}
  (boundary : DeviceBoundary c revokeGrant s revoked) (trace : Runs.Trace revoked later) →
  (ReissuedIn (revokedIdentifier boundary) trace → ⊥) → GrantDisabled (revokedIdentifier boundary) later
revoked-grant-excluded boundary trace noReissue with disabled-until-reissue trace (revocation-disables boundary)
... | inj₁ disabled = disabled
... | inj₂ origin = ⊥-elim (noReissue origin)

same-answer : ∀ {A : Set} {m : M A} {s x t y u} → Run m s x t → Run m s y u → x ≡ y
same-answer (run _ first) (run _ second) = answer (trans (sym first) second)
  where
  answer : ∀ {A : Set} {x y : A} {t u es fs} → accepted x t es ≡ accepted y u fs → x ≡ y
  answer refl = refl

disabled-grant-call : ∀ {target c op ctx ga xs s x t} → GrantDisabled target s →
  Run (grantId c ctx ga) s target s → Run (grantCall c op ctx ga xs) s x t → ⊥
disabled-grant-call {c = c} {op} {ctx} {ga} {xs} disabled identified call
  with G.evidence c op ctx ga xs call
... | evidence with same-answer identified (GrantCallEvidence.identified evidence)
... | refl = disabled (grantRecord evidence)
  (EP.lookup-found "grants" _ (recorded evidence)) (LiveGrant.active (live evidence))

revoked-grant-call-excluded : ∀ {ownerCurve s revoked later c op ctx ga xs x after}
  (boundary : DeviceBoundary ownerCurve revokeGrant s revoked) (trace : Runs.Trace revoked later) →
  (ReissuedIn (revokedIdentifier boundary) trace → ⊥) →
  Run (grantId c ctx ga) later (revokedIdentifier boundary) later →
  Run (grantCall c op ctx ga xs) later x after → ⊥
revoked-grant-call-excluded {later = later} {c} {op} {ctx} {ga} {xs} {after = after} boundary trace noReissue =
  disabled-grant-call {c = c} {op = op} {ctx = ctx} {ga = ga} {xs = xs} {s = later} {t = after}
    (revoked-grant-excluded boundary trace noReissue)

issue-boundary : ∀ {c s t} → DeviceBoundary c issueGrant s t → IssueBoundary c s t
issue-boundary device = record
  { device = device
  ; issued = EP.issue-body-result ctx (deviceArguments issueGrant xs)
      (deviceCoin issueGrant ctx) (DeviceCall.callerEntry E) (DeviceCall.bodyRun E)
  }
  where
  E = DeviceBoundary.evidence device
  boundaryEvent = DeviceBoundary.event device
  ctx = occurrenceContext boundaryEvent
  xs = occurrenceArguments boundaryEvent

issued-at-number : ∀ {c s t} (boundary : IssueBoundary c s t) →
  number (GE.Issuance.issuedAt (issueIdentity boundary)) ≡ counterValue "auth_nonce" t
issued-at-number {t = t} boundary = trans
  (sym (cell-number "auth_nonce" (DeviceCall.authorisedState E)
    (GE.IssueResult.issuedRead (IssueBoundary.issued boundary))))
  (sym (frame-number "auth_nonce" {s = DeviceCall.authorisedState E} {t = t}
    (D.body-frame "auth_nonce" issueGrant ctx (deviceArguments issueGrant xs)
      (deviceCoin issueGrant ctx) (DeviceCall.callerEntry E) (refl ∷ []) (DeviceCall.bodyRun E))))
  where
  E = DeviceBoundary.evidence (IssueBoundary.device boundary)
  boundaryEvent = DeviceBoundary.event (IssueBoundary.device boundary)
  ctx = occurrenceContext boundaryEvent
  xs = occurrenceArguments boundaryEvent

issue-nonces-strict : ∀ {c₁ c₂ s first later final} →
  (issued₁ : IssueBoundary c₁ s first) → Runs.Trace first later →
  (issued₂ : IssueBoundary c₂ later final) →
  number (GE.Issuance.issuedAt (issueIdentity issued₁)) <
    number (GE.Issuance.issuedAt (issueIdentity issued₂))
issue-nonces-strict issued₁ trace issued₂ rewrite issued-at-number issued₁ | issued-at-number issued₂ =
  ≤-trans (s≤s (CountersAdvance.nonce (history-counters trace)))
    (advanced-< (DeviceCall.nonceAdvanced (DeviceBoundary.evidence (IssueBoundary.device issued₂))))

accepted-device-evidence : ∀ {env call s x t es requests c op} →
  AcceptedCall env call s x t es requests →
  S.resolve (RuntimeCall.request call) ≡ just (Semantics.device c op) →
  DeviceCall c op (executionContext address env) (callArguments call) s x t
accepted-device-evidence (activated _ dispatchWitness _) resolved
  with trans (sym (S.Dispatched.resolved dispatchWitness)) resolved
... | ()
accepted-device-evidence (deviceAuthorised _ _ dispatchWitness E _ _) resolved
  with trans (sym (S.Dispatched.resolved dispatchWitness)) resolved
... | refl = E
accepted-device-evidence (grantAuthorised _ _ dispatchWitness _ _ _ _) resolved
  with trans (sym (S.Dispatched.resolved dispatchWitness)) resolved
... | ()
accepted-device-evidence (depositedUnshielded dispatchWitness) resolved
  with trans (sym (S.Dispatched.resolved dispatchWitness)) resolved
... | ()
accepted-device-evidence (depositedShielded dispatchWitness) resolved
  with trans (sym (S.Dispatched.resolved dispatchWitness)) resolved
... | ()
accepted-device-evidence (recoverySubmitted dispatchWitness _ _ _ _) resolved
  with trans (sym (S.Dispatched.resolved dispatchWitness)) resolved
... | ()
accepted-device-evidence (recoveryFinalised dispatchWitness _) resolved
  with trans (sym (S.Dispatched.resolved dispatchWitness)) resolved
... | ()

device-boundary : ∀ {c op s t} → Runs.History s →
  (event : CommittedOccurrence s t) →
  S.resolve (RuntimeCall.request (CommittedOccurrence.call event)) ≡ just (Semantics.device c op) →
  DeviceBoundary c op s t
device-boundary history event resolved
  with SP.accepted-call (CommittedOccurrence.environment event) (CommittedOccurrence.call event)
    (CommittedOccurrence.executed event)
... | _ , E , _ = record
  { history = history ; event = event ; deviceResolved = resolved
  ; evidence = accepted-device-evidence E resolved }

rooted-stale-epoch-excluded : ∀ {s t c ctx ga g} → Runs.History s → Runs.Trace s t →
  number (grantEpoch g) < counterValue "device_epoch" s → LiveGrant c ctx ga t g → ⊥
rooted-stale-epoch-excluded history = stale-epoch-excluded

rooted-stale-generation-excluded : ∀ {s t c ctx ga g} → Runs.History s → Runs.Trace s t →
  number (grantGeneration g) < counterValue "grant_generation" s → LiveGrant c ctx ga t g → ⊥
rooted-stale-generation-excluded history = stale-generation-excluded

post-recovery-old-grant-excluded : ∀ {s recovered later c ctx ga g} →
  (boundary : RecoveryBoundary s recovered) → Runs.Trace recovered later →
  number (grantEpoch g) ≤ counterValue "device_epoch" s → LiveGrant c ctx ga later g → ⊥
post-recovery-old-grant-excluded boundary trace old live =
  stale-epoch-excluded trace
    (≤-trans (s≤s old) (recovery-epoch-strict (RecoveryBoundary.evidence boundary))) live

post-revoke-all-old-grant-excluded : ∀ {ownerCurve s revoked later c ctx ga g} →
  (boundary : DeviceBoundary ownerCurve revokeAllGrants s revoked) → Runs.Trace revoked later →
  number (grantGeneration g) ≤ counterValue "grant_generation" s → LiveGrant c ctx ga later g → ⊥
post-revoke-all-old-grant-excluded boundary trace old live =
  stale-generation-excluded trace
    (≤-trans (s≤s old) (post-revoke-all-generation boundary ε)) live

-- Occurrence-facing proofs ---------------------------------------------------
-- Certificates above remain strong supporting results, but their source guard
-- fields are derived here rather than imposed on the advertised statements.

history-after : ∀ {s t later} → Runs.History s → CommittedOccurrence s t →
  Runs.Trace t later → Runs.History later
history-after history event trace = Runs.extend history
  (Runs.event (CommittedOccurrence.environment event) (CommittedOccurrence.call event)
    (Account.committed (CommittedOccurrence.answer event) (CommittedOccurrence.effects event))
    (CommittedOccurrence.executed event) ◅ trace)

boundary-successor : ∀ {s recovered} (boundary : RecoveryBoundary s recovered) →
  recoverySuccessor (RecoveryBoundary.event boundary) ≡
    R.Finalisation.Evidence.successor (RecoveryBoundary.evidence boundary)
boundary-successor {s} boundary = D.cell-lookup "pending_entry" s
  (R.Stores.observed (R.Finalisation.Evidence.successorCell (RecoveryBoundary.evidence boundary)))

observed-grant-found : ∀ identifier s {g} →
  lookupMap identifier (fields (cell "grants" s)) ≡ just g → observedGrant identifier s ≡ g
observed-grant-found identifier s found with lookupMap identifier (fields (cell "grants" s)) | found
... | just g | refl = refl
... | nothing | ()

occurrence-issue-identity : ∀ {c s t} (boundary : IssueBoundary c s t) →
  issuedIdentity (DeviceBoundary.event (IssueBoundary.device boundary)) ≡ issueIdentity boundary
occurrence-issue-identity {t = t} boundary = cong (GE.issuanceOf issueId)
  (observed-grant-found issueId t
    (trans (cong (λ v → lookupMap issueId (fields v)) (GE.IssueResult.installed issued))
      (map-insert-same issueId (GE.issuedRecord issued) (fields (cell "grants" source)))))
  where
  device = IssueBoundary.device boundary
  issueId = issuedIdentifier (DeviceBoundary.event device)
  source = DeviceCall.authorisedState (DeviceBoundary.evidence device)
  issued = IssueBoundary.issued boundary

occurrence-post-recovery-epoch : ∀ {s recovered later} → Runs.History s →
  (event : CommittedOccurrence s recovered) → Resolved event Runtime.finaliseRecovery →
  Runs.Trace recovered later → counterValue "device_epoch" s < counterValue "device_epoch" later
occurrence-post-recovery-epoch history event resolved =
  runtime-post-recovery-epoch (recovery-boundary history event resolved)

occurrence-post-device-nonce : ∀ {c op s t later} → Runs.History s →
  (event : CommittedOccurrence s t) → Resolved event (Runtime.device c op) →
  Runs.Trace t later → counterValue "auth_nonce" s < counterValue "auth_nonce" later
occurrence-post-device-nonce history event resolved =
  runtime-post-device-nonce (device-boundary history event resolved)

occurrence-post-revoke-all-generation : ∀ {c s t later} → Runs.History s →
  (event : CommittedOccurrence s t) → Resolved event (Runtime.device c revokeAllGrants) →
  Runs.Trace t later → counterValue "grant_generation" s < counterValue "grant_generation" later
occurrence-post-revoke-all-generation history event resolved =
  post-revoke-all-generation (device-boundary history event resolved)

occurrence-post-recovery-device-origin : ∀ {s recovered later entry} → Runs.History s →
  (event : CommittedOccurrence s recovered) → Resolved event Runtime.finaliseRecovery →
  (trace : Runs.Trace recovered later) → member entry (fields (cell "devices" later)) ≡ true →
  (entry ≡ recoverySuccessor event) ⊎ IntroducedIn entry trace
occurrence-post-recovery-device-origin history event resolved trace live
  with runtime-post-recovery-device-origin (recovery-boundary history event resolved) trace live
... | inj₁ same = inj₁ (trans same (sym (boundary-successor (recovery-boundary history event resolved))))
... | inj₂ introduced = inj₂ introduced

occurrence-protected-device-excluded : ∀ {s recovered later c op after} → Runs.History s →
  (recovery : CommittedOccurrence s recovered) → Resolved recovery Runtime.finaliseRecovery →
  (trace : Runs.Trace recovered later) →
  (device : CommittedOccurrence later after) → Resolved device (Runtime.device c op) →
  RelevantEntrySeparation c (occurrenceAuth c op device) (counterValue "device_epoch" later)
    (recoverySuccessor recovery) trace → ⊥
occurrence-protected-device-excluded {later = later} {c} {op} history recovery resolved trace device deviceResolved separation =
  runtime-protected-device-excluded recoveryEvidence trace deviceEvidence
    (subst (λ successor → RelevantEntrySeparation c (occurrenceAuth c op device)
      (counterValue "device_epoch" later) successor trace)
      (boundary-successor recoveryEvidence) separation)
  where
  recoveryEvidence = recovery-boundary history recovery resolved
  deviceEvidence = device-boundary (history-after history recovery trace) device deviceResolved

occurrence-revoked-grant-excluded : ∀ {c s revoked later} → Runs.History s →
  (event : CommittedOccurrence s revoked) → Resolved event (Runtime.device c revokeGrant) →
  (trace : Runs.Trace revoked later) → (ReissuedIn (revocationIdentifier event) trace → ⊥) →
  GrantDisabled (revocationIdentifier event) later
occurrence-revoked-grant-excluded history event resolved =
  revoked-grant-excluded (device-boundary history event resolved)

occurrence-revoked-grant-call-excluded : ∀ {ownerCurve s revoked later c op ctx ga xs x after} →
  Runs.History s → (event : CommittedOccurrence s revoked) →
  Resolved event (Runtime.device ownerCurve revokeGrant) → (trace : Runs.Trace revoked later) →
  (ReissuedIn (revocationIdentifier event) trace → ⊥) →
  Run (grantId c ctx ga) later (revocationIdentifier event) later →
  Run (grantCall c op ctx ga xs) later x after → ⊥
occurrence-revoked-grant-call-excluded {c = c} {op} {ctx} {ga} {xs} history event resolved =
  revoked-grant-call-excluded {c = c} {op = op} {ctx = ctx} {ga = ga} {xs = xs}
    (device-boundary history event resolved)

occurrence-issue-nonces-strict : ∀ {c₁ c₂ s first later final} → Runs.History s →
  (issued₁ : CommittedOccurrence s first) → Resolved issued₁ (Runtime.device c₁ issueGrant) →
  Runs.Trace first later →
  (issued₂ : CommittedOccurrence later final) → Resolved issued₂ (Runtime.device c₂ issueGrant) →
  number (GE.Issuance.issuedAt (issuedIdentity issued₁)) <
    number (GE.Issuance.issuedAt (issuedIdentity issued₂))
occurrence-issue-nonces-strict history issued₁ resolved₁ trace issued₂ resolved₂ =
  subst₂ (λ first second → number (GE.Issuance.issuedAt first) < number (GE.Issuance.issuedAt second))
    (sym (occurrence-issue-identity firstIssue)) (sym (occurrence-issue-identity secondIssue))
    (issue-nonces-strict firstIssue trace secondIssue)
  where
  firstIssue = issue-boundary (device-boundary history issued₁ resolved₁)
  secondIssue = issue-boundary
    (device-boundary (history-after history issued₁ trace) issued₂ resolved₂)

occurrence-post-recovery-old-grant-excluded : ∀ {s recovered later c ctx ga g} →
  Runs.History s → (event : CommittedOccurrence s recovered) → Resolved event Runtime.finaliseRecovery →
  Runs.Trace recovered later → number (grantEpoch g) ≤ counterValue "device_epoch" s →
  LiveGrant c ctx ga later g → ⊥
occurrence-post-recovery-old-grant-excluded history event resolved =
  post-recovery-old-grant-excluded (recovery-boundary history event resolved)

occurrence-post-revoke-all-old-grant-excluded : ∀ {ownerCurve s revoked later c ctx ga g} →
  Runs.History s → (event : CommittedOccurrence s revoked) →
  Resolved event (Runtime.device ownerCurve revokeAllGrants) → Runs.Trace revoked later →
  number (grantGeneration g) ≤ counterValue "grant_generation" s → LiveGrant c ctx ga later g → ⊥
occurrence-post-revoke-all-old-grant-excluded history event resolved =
  post-revoke-all-old-grant-excluded (device-boundary history event resolved)

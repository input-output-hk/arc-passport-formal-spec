{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes using (Primitives; Value)
open import Midnight.ContractDSL.SymbolicSigning using (Ownership)
import Conformance.FullAccountSignatureBinding as SignatureBinding

module Passport.AccountSecurityProof (P : Primitives) (address : Value)
  (ownership : SignatureBinding.Key P → Ownership) where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; map; take)
import Data.List.Membership.DecPropositional as Membership
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.All as AllBase using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All.Properties as All
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; uncurry′)
import Data.String as String
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec; yes; no; does)
open import Relation.Nullary.Decidable using (toWitnessFalse)

open import Conformance.FullAccountTypes
import Conformance.FullAccount as Model
open import Conformance.FullAccountBody P using (Operation; withdrawUnshielded; withdrawShielded;
  withdrawToContract; appendInbox; rotateEncKey; addDevice; removeDevice; issueGrant; revokeGrant;
  revokeAllGrants; publishRecovery; cancelRecovery; operationAtoms; operationName)
open import Conformance.FullAccountCrypto P using (challengeAt; hash; hashTag; schnorr; verify)
import Conformance.FullAccountDeviceSecurityProperties as DeviceProperties
open import Conformance.FullAccountExecution using (Run; run; Succeeded; succeeded)
open import Conformance.FullAccountGrant P using (authorisation; grantCall; grantId)
import Conformance.FullAccountGrantSecurityProperties as GrantProperties
open import Conformance.FullAccountLayouts using (module SubmitArguments; grantNonce)
import Conformance.FullAccountRecoverySecurityProperties as RecoveryProperties
import Conformance.FullAccountSignatureBindingProperties as BindingProperties
import Midnight.ContractDSL.AdversarialLifecycleProperties as AdversarialProperties
import Passport.Account as Account
open import Passport.AccountLifecycle P using (Environment; RuntimeCall; executionContext; lifecycle)
open import Passport.AccountSecurity P address ownership
open Semantics using (Entrypoint; construct; activation; device; grant; depositPublic;
  depositPrivate; submitRecovery; finaliseRecovery; execute)
open Device using (deviceArguments; deviceAuth; deviceCoin; verificationMessage)
open Symbolic using (module Signatures)

module BindingFacts = BindingProperties P
module DeviceFacts = DeviceProperties P
module GrantFacts = GrantProperties P
module RecoveryFacts = RecoveryProperties P
module JointFacts = AdversarialProperties.Properties lifecycle address Symbolic.interface
  requiredTokens

------------------------------------------------------------------------
-- Dispatcher: a committed runtime transition resolved to a runtime entrypoint

private
  isConstructor : Entrypoint → Bool
  isConstructor construct = true
  isConstructor _ = false

  true≢false : true ≢ false
  true≢false ()

  rejected≢accepted : ∀ {e v t es} → rejected {Value} e ≢ accepted v t es
  rejected≢accepted ()

  ∧-true : ∀ a {b} → a ∧ b ≡ true → a ≡ true × b ≡ true
  ∧-true true eq = refl , eq
  ∧-true false ()

  -- One accepted conditional layer of `checked`.
  then-branch : ∀ b {err x v t es} →
    (if b then x else rejected err) ≡ accepted {Value} v t es → x ≡ accepted v t es
  then-branch true ok = ok
  then-branch false ()

  else-branch : ∀ b {err x v t es} →
    (if b then rejected err else x) ≡ accepted {Value} v t es → x ≡ accepted v t es
  else-branch false ok = ok
  else-branch true ()

  transaction-committed : ∀ s r {v es t} →
    Account.transaction s r ≡ (Account.committed v es , t) → r ≡ accepted v t es
  transaction-committed s (rejected e) ()
  transaction-committed s (accepted v t es) refl = refl

  -- A Boolean property of every entry of a name table holds of whatever
  -- lookupEntrypoint resolves from it.
  lookup-all : ∀ (p : Entrypoint → Bool) n es {e} → all (λ entry → p (proj₂ entry)) es ≡ true →
    Semantics.lookupEntrypoint n es ≡ just e → p e ≡ true
  lookup-all p n [] _ ()
  lookup-all p n ((k , e′) ∷ es) {e} holds found = choose (stringEqual n k) found
    where
    choose : ∀ b → (if b then just e′ else Semantics.lookupEntrypoint n es) ≡ just e → p e ≡ true
    choose true same = subst (λ x → p x ≡ true) (just-injective same) (proj₁ (∧-true (p e′) holds))
    choose false rest = lookup-all p n es (proj₂ (∧-true (p e′) holds)) rest

  runtime-entries : all (λ entry → not (isConstructor (proj₂ entry))) Semantics.runtimeEntrypoints ≡ true
  runtime-entries = refl

  resolved-constructor : ∀ n → Semantics.lookupEntrypoint n Semantics.entrypoints ≡ just construct →
    n ≡ "constructor"
  resolved-constructor n found = decide (n String.≟ "constructor") found
    where
    decide : (d : Dec (n ≡ "constructor")) →
      (if does d then just construct else Semantics.lookupEntrypoint n Semantics.runtimeEntrypoints)
        ≡ just construct → n ≡ "constructor"
    decide (yes same) _ = same
    decide (no _) rest = ⊥-elim (true≢false (sym
      (lookup-all (λ e → not (isConstructor e)) n Semantics.runtimeEntrypoints runtime-entries rest)))

  -- The dispatcher resolves grant authentication only for withdrawals.
  withdrawal : Operation → Bool
  withdrawal withdrawUnshielded = true
  withdrawal withdrawShielded = true
  withdrawal withdrawToContract = true
  withdrawal _ = false

  grantWithdrawal : Entrypoint → Bool
  grantWithdrawal (grant _ op) = withdrawal op
  grantWithdrawal _ = true

  grant-entries : all (λ entry → grantWithdrawal (proj₂ entry)) Semantics.entrypoints ≡ true
  grant-entries = refl

  withdrawal-sound : ∀ op → withdrawal op ≡ true → Grant.Withdrawal op
  withdrawal-sound withdrawUnshielded _ = Grant.unshieldedWithdrawal
  withdrawal-sound withdrawShielded _ = Grant.shieldedWithdrawal
  withdrawal-sound withdrawToContract _ = Grant.contractWithdrawal
  withdrawal-sound appendInbox ()
  withdrawal-sound rotateEncKey ()
  withdrawal-sound addDevice ()
  withdrawal-sound removeDevice ()
  withdrawal-sound issueGrant ()
  withdrawal-sound revokeGrant ()
  withdrawal-sound revokeAllGrants ()
  withdrawal-sound publishRecovery ()
  withdrawal-sound cancelRecovery ()

  resolved-withdrawal : ∀ call {c op} → resolve call ≡ just (grant c op) → Grant.Withdrawal op
  resolved-withdrawal call {op = op} found = withdrawal-sound op
    (lookup-all grantWithdrawal (name call) Semantics.entrypoints grant-entries found)

  -- Decided by evaluating the finite runtime name table.
  constructor-not-runtime : "constructor" ∉ Model.runtimeNames P
  constructor-not-runtime =
    toWitnessFalse {a? = Membership._∈?_ String._≟_ "constructor" (Model.runtimeNames P)} _

  runtime-not-constructor : (call : RuntimeCall) →
    resolve (RuntimeCall.request call) ≢ just construct
  runtime-not-constructor call found = constructor-not-runtime
    (subst (_∈ Model.runtimeNames P) (resolved-constructor (name (RuntimeCall.request call)) found)
      (RuntimeCall.runtime call))

  dispatch-resolves : ∀ ctx call s →
    Model.dispatch P ctx call s ≡ rejected (decoding "unknown runtime circuit") ⊎
    Σ Entrypoint λ e → resolve call ≡ just e ×
      Model.dispatch P ctx call s ≡ Semantics.checked e ctx (arguments call) s
  dispatch-resolves ctx call s with Semantics.lookupEntrypoint (name call) Semantics.entrypoints
  ... | nothing = inj₁ refl
  ... | just e = inj₂ (e , refl , refl)

  -- Every runtime entrypoint passes the same four validation layers before execute.
  checked-execute : ∀ e ctx xs s {v t es} → isConstructor e ≡ false →
    Semantics.checked e ctx xs s ≡ accepted v t es → execute e ctx xs s ≡ accepted v t es
  checked-execute construct ctx xs s () ok
  checked-execute (activation c) ctx xs s _ ok =
    then-branch (Model.validState s) (then-branch (Model.validContext ctx)
      (then-branch (Model.validArguments (Semantics.schema (activation c)) xs) ok))
  checked-execute (device c op) ctx xs s _ ok =
    then-branch (Model.validState s)
      (else-branch (Semantics.needsCoin (device c op) ∧
          not (Model.valid Model.qualifiedCoinT (heldCoin ctx)))
        (then-branch (Model.validContext ctx)
          (then-branch (Model.validArguments (Semantics.schema (device c op)) xs) ok)))
  checked-execute (grant c op) ctx xs s _ ok =
    then-branch (Model.validState s)
      (else-branch (Semantics.needsCoin (grant c op) ∧
          not (Model.valid Model.qualifiedCoinT (heldCoin ctx)))
        (then-branch (Model.validContext ctx)
          (then-branch (Model.validArguments (Semantics.schema (grant c op)) xs) ok)))
  checked-execute depositPublic ctx xs s _ ok =
    then-branch (Model.validState s) (then-branch (Model.validContext ctx)
      (then-branch (Model.validArguments (Semantics.schema depositPublic) xs) ok))
  checked-execute depositPrivate ctx xs s _ ok =
    then-branch (Model.validState s) (then-branch (Model.validContext ctx)
      (then-branch (Model.validArguments (Semantics.schema depositPrivate) xs) ok))
  checked-execute submitRecovery ctx xs s _ ok =
    then-branch (Model.validState s) (then-branch (Model.validContext ctx)
      (then-branch (Model.validArguments (Semantics.schema submitRecovery) xs) ok))
  checked-execute finaliseRecovery ctx xs s _ ok =
    then-branch (Model.validState s) (then-branch (Model.validContext ctx)
      (then-branch (Model.validArguments (Semantics.schema finaliseRecovery) xs) ok))

  constructor-resolution : ∀ e → isConstructor e ≡ true → e ≡ construct
  constructor-resolution construct _ = refl
  constructor-resolution (activation _) ()
  constructor-resolution (device _ _) ()
  constructor-resolution (grant _ _) ()
  constructor-resolution depositPublic ()
  constructor-resolution depositPrivate ()
  constructor-resolution submitRecovery ()
  constructor-resolution finaliseRecovery ()

  runtime-entrypoint : (call : RuntimeCall) → ∀ {e} →
    resolve (RuntimeCall.request call) ≡ just e → isConstructor e ≡ false
  runtime-entrypoint call {e} found = decide (isConstructor e) refl
    where
    decide : ∀ b → isConstructor e ≡ b → isConstructor e ≡ false
    decide false same = same
    decide true same = ⊥-elim (runtime-not-constructor call
      (trans found (cong just (constructor-resolution e same))))

  committed-dispatch : ∀ {ctx call before answer effects after} →
    Account.Transition P ctx call before (Account.committed answer effects) after →
    Model.dispatch P ctx call before ≡ accepted answer after effects
  committed-dispatch {ctx} {call} {before} committed =
    transaction-committed before (Model.dispatch P ctx call before) (Account.execution committed)

  accepted-dispatch : ∀ env (call : RuntimeCall) {before answer effects after} →
    Account.Transition P (executionContext address env) (RuntimeCall.request call) before
      (Account.committed answer effects) after →
    Σ Entrypoint λ e → isConstructor e ≡ false × Dispatched e env call before answer after effects
  accepted-dispatch env call {before} committed
    with dispatch-resolves (executionContext address env) (RuntimeCall.request call) before
  ... | inj₁ unknown =
    ⊥-elim (rejected≢accepted (trans (sym unknown) (committed-dispatch committed)))
  ... | inj₂ (e , found , via) = e , runtime-entrypoint call found , dispatched found
    (checked-execute e (executionContext address env) (arguments (RuntimeCall.request call)) before
      (runtime-entrypoint call found) (trans (sym via) (committed-dispatch committed)))

------------------------------------------------------------------------
-- Source paths: evaluator evidence and the requests the before state yields

private
  signed-resolved : ∀ s env call {e} → resolve (RuntimeCall.request call) ≡ just e →
    signedRequests s env call ≡
      entrypointRequests e (executionContext address env) (arguments (RuntimeCall.request call)) s
  signed-resolved s env call found = cong (maybe′ (λ e → entrypointRequests e
    (executionContext address env) (arguments (RuntimeCall.request call)) s) []) found

  -- execute's two grant clauses, as one equation for every operation.
  execute-grant : ∀ c op ctx xs s →
    execute (grant c op) ctx xs s ≡ grantCall c op ctx (grantAuthorisation c op xs) (take 3 xs) s
  execute-grant c withdrawUnshielded ctx xs s = refl
  execute-grant c withdrawShielded ctx xs s = refl
  execute-grant c withdrawToContract ctx xs s = refl
  execute-grant c appendInbox ctx xs s = refl
  execute-grant c rotateEncKey ctx xs s = refl
  execute-grant c addDevice ctx xs s = refl
  execute-grant c removeDevice ctx xs s = refl
  execute-grant c issueGrant ctx xs s = refl
  execute-grant c revokeGrant ctx xs s = refl
  execute-grant c revokeAllGrants ctx xs s = refl
  execute-grant c publishRecovery ctx xs s = refl
  execute-grant c cancelRecovery ctx xs s = refl

  grant-requests : ∀ c op ctx ga ys s {id g h d t₁ t₂ t₃ es₁ es₂ es₃} →
    grantId c ctx ga s ≡ accepted id t₁ es₁ →
    lookup "grants" id s ≡ accepted g t₂ es₂ →
    challengeAt c true (operationName op) (self ctx) (authorisation ga)
      (Grant.grantChallengeAtoms op ys (Grant.grantCoin op ctx) ga id g)
      (number (grantNonce g)) s ≡ accepted h t₃ es₃ →
    Binding.verifiedDigest c (authorisation ga) h "invalid grant signature" ≡ just d →
    grantRequests c op ctx ga ys s ≡ grantRequest c op ctx ga ys id g ∷ []
  grant-requests c op ctx ga ys s identified recorded challenged gate
    rewrite identified | recorded | challenged | gate = refl

  device-requests : ∀ c op ctx xs s {atoms nonce h d t₁ t₂ es₁ es₂} →
    operationAtoms op (deviceArguments op xs) (deviceCoin op ctx) s ≡ accepted atoms t₁ es₁ →
    lookupCell "auth_nonce" (ledger s) ≡ just nonce →
    challengeAt c false (operationName op) (self ctx) (deviceAuth c op xs) atoms (number nonce) s
      ≡ accepted h t₂ es₂ →
    Binding.verifiedDigest c (deviceAuth c op xs) h (verificationMessage c) ≡ just d →
    deviceRequests c op ctx xs s ≡ deviceRequest c op ctx xs atoms (number nonce) ∷ []
  device-requests c op ctx xs s encoded nonce challenged gate
    rewrite encoded | nonce | challenged | gate = refl

  recovery-requests : ∀ ctx xs s {storedEpoch storedNonce recoveryKey domain h t₁ t₂ es₁ es₂} →
    lookupCell "device_epoch" (ledger s) ≡ just storedEpoch →
    lookupCell "auth_nonce" (ledger s) ≡ just storedNonce →
    lookupCell "recovery_pk" (ledger s) ≡ just recoveryKey →
    hashTag Binding.recoverySubmitTag s ≡ accepted domain t₁ es₁ →
    hash (Binding.submitPreimage domain (submission ctx xs recoveryKey storedEpoch storedNonce)) s
      ≡ accepted h t₂ es₂ →
    Binding.schnorrAccepted recoveryKey (SubmitArguments.recoveryR xs)
      (SubmitArguments.recoveryS xs) h "invalid recovery signature" ≡ true →
    Binding.schnorrAccepted (SubmitArguments.successorKey xs) (SubmitArguments.successorR xs)
      (SubmitArguments.successorS xs) h "invalid successor co-signature" ≡ true →
    recoveryRequests ctx xs s ≡
      recoveryAuthority recoveryKey (submission ctx xs recoveryKey storedEpoch storedNonce) ∷
      successorPossession xs (submission ctx xs recoveryKey storedEpoch storedNonce) ∷ []
  recovery-requests ctx xs s epoch nonce key domain digest authority successor
    rewrite epoch | nonce | key | domain | digest | authority | successor = refl

  AcceptedWith : Environment → RuntimeCall → State → Value → State → List Effect → Set
  AcceptedWith env call before answer after effects =
    Σ (List SignedRequest) λ requests → AcceptedCall env call before answer after effects requests ×
      signedRequests before env call ≡ requests

  activation-call : ∀ env call c {before answer after effects} →
    Dispatched (activation c) env call before answer after effects →
    AcceptedWith env call before answer after effects
  activation-call env call c {before} {answer} {after} {effects} d =
    [] , activated c d (DeviceFacts.activation-evidence c ctx (Semantics.parseActivation c xs)
      (get 1 xs) {before} {answer} {after} (run effects (Dispatched.executed d))) ,
    signed-resolved before env call (Dispatched.resolved d)
    where
    ctx = executionContext address env
    xs = arguments (RuntimeCall.request call)

  device-call : ∀ env call c op {before answer after effects} →
    Dispatched (device c op) env call before answer after effects →
    AcceptedWith env call before answer after effects
  device-call env call c op {before} {answer} {after} {effects} d =
    calledRequest evidence ∷ [] , deviceAuthorised c op d evidence checked encodes ,
    trans (signed-resolved before env call (Dispatched.resolved d))
      (device-requests c op ctx xs before (Run.execution E.encoded)
        (Device.Advanced.previousCell E.nonceAdvanced) (Run.execution E.challengeComputed)
        (BindingFacts.verified-digest c a h (verificationMessage c) verification checked))
    where
    ctx = executionContext address env
    xs = arguments (RuntimeCall.request call)
    a = deviceAuth c op xs
    evidence = DeviceFacts.device-call-evidence c op ctx xs {before} {answer} {after}
      (run effects (Dispatched.executed d))
    module E = Device.DeviceCall evidence
    h = E.challengeValue
    verified = Device.Authorisation.verified E.authorised
    verification : Succeeded (verify c a h (verificationMessage c)) before
    verification = succeeded tt before (Run.journal verified) (Run.execution verified)
    checked = BindingFacts.verification-evidence c a h (verificationMessage c) verification
    encodes = BindingFacts.authorisation-message c false op (self ctx) a E.atoms (number E.nonce)
      (Run.execution E.challengeComputed) checked

  grant-call : ∀ env call c op {before answer after effects} →
    Dispatched (grant c op) env call before answer after effects →
    AcceptedWith env call before answer after effects
  grant-call env call c op {before} {answer} {after} {effects} d =
    grantedRequest evidence ∷ [] , grantAuthorised c op d spend final checked encodes ,
    trans (signed-resolved before env call (Dispatched.resolved d))
      (grant-requests c op ctx ga ys before (Run.execution (Granted.identified evidence))
        (Run.execution (Granted.recorded evidence)) (Run.execution (Granted.challenged evidence))
        (BindingFacts.verified-digest c a h "invalid grant signature" verification checked))
    where
    ctx = executionContext address env
    xs = arguments (RuntimeCall.request call)
    ga = grantAuthorisation c op xs
    ys = take 3 xs
    a = authorisation ga
    spend = resolved-withdrawal (RuntimeCall.request call) (Dispatched.resolved d)
    final : Grant.GrantFinalState c op ctx ga ys before after
    final = GrantFacts.grant-final-state c op ctx ga ys spend
      (trans (sym (execute-grant c op ctx xs before)) (Dispatched.executed d))
    evidence = Grant.GrantFinalState.callEvidence final
    h = Granted.challengeValue evidence
    verification : Succeeded (verify c a h "invalid grant signature") before
    verification = succeeded tt before (Run.journal (Granted.verified evidence))
      (Run.execution (Granted.verified evidence))
    checked = BindingFacts.verification-evidence c a h "invalid grant signature" verification
    encodes = BindingFacts.authorisation-message c true op (self ctx) a
      (Grant.grantChallengeAtoms op ys (Grant.grantCoin op ctx) ga
        (Granted.identifier evidence) (Granted.grantRecord evidence))
      (number (grantNonce (Granted.grantRecord evidence)))
      (Run.execution (Granted.challenged evidence)) checked

  recovery-call : ∀ env call {before answer after effects} →
    Dispatched submitRecovery env call before answer after effects →
    AcceptedWith env call before answer after effects
  recovery-call env call {before} d =
    submittedRequests evidence , recoverySubmitted d evidence authority successor encodings ,
    trans (signed-resolved before env call (Dispatched.resolved d))
      (recovery-requests ctx xs before (Recovery.Stores.observed E.epochCell)
        (Recovery.Stores.observed E.nonceCell) (Recovery.Stores.observed E.recoveryKeyCell)
        (Run.execution E.domainHash) (Run.execution E.challengeHash)
        (BindingFacts.schnorr-accepted E.recoveryKey A.recoveryR A.recoveryS E.digest
          "invalid recovery signature" authoritySignature)
        (BindingFacts.schnorr-accepted A.successorKey A.successorR A.successorS E.digest
          "invalid successor co-signature" successorSignature))
    where
    ctx = executionContext address env
    xs = arguments (RuntimeCall.request call)
    module A = SubmitArguments xs
    evidence = RecoveryFacts.submit-evidence ctx xs (Dispatched.executed d)
    module E = Recovery.Submission.Evidence evidence
    r = submission ctx xs E.recoveryKey E.storedEpoch E.storedNonce
    authoritySignature : Succeeded (schnorr E.recoveryKey A.recoveryR A.recoveryS E.digest
      "invalid recovery signature") before
    authoritySignature = succeeded tt before (Run.journal E.recoverySignature)
      (Run.execution E.recoverySignature)
    successorSignature : Succeeded (schnorr A.successorKey A.successorR A.successorS E.digest
      "invalid successor co-signature") before
    successorSignature = succeeded tt before (Run.journal E.successorSignature)
      (Run.execution E.successorSignature)
    authority = BindingFacts.schnorr-evidence E.recoveryKey A.recoveryR A.recoveryS E.digest
      "invalid recovery signature" authoritySignature
    successor = BindingFacts.schnorr-evidence A.successorKey A.successorR A.successorS E.digest
      "invalid successor co-signature" successorSignature
    encodings : All (λ request → Encodes request E.digest) (submittedRequests evidence)
    encodings =
      BindingFacts.recovery-message r E.recoveryKey (Run.execution E.domainHash)
        (Run.execution E.challengeHash) ∷
      BindingFacts.recovery-message r A.successorKey (Run.execution E.domainHash)
        (Run.execution E.challengeHash) ∷ []

------------------------------------------------------------------------
-- Every accepted runtime call, by dispatcher case analysis

accepted-call : ∀ env (call : RuntimeCall) {before answer effects after} →
  Account.Transition P (executionContext address env) (RuntimeCall.request call) before
    (Account.committed answer effects) after →
  Σ (List SignedRequest) λ requests → AcceptedCall env call before answer after effects requests ×
    signedRequests before env call ≡ requests
accepted-call env call {before} committed with accepted-dispatch env call committed
... | construct , () , _
... | activation c , _ , d = activation-call env call c d
... | device c op , _ , d = device-call env call c op d
... | grant c op , _ , d = grant-call env call c op d
... | depositPublic , _ , d =
  [] , depositedUnshielded d , signed-resolved before env call (Dispatched.resolved d)
... | depositPrivate , _ , d =
  [] , depositedShielded d , signed-resolved before env call (Dispatched.resolved d)
... | submitRecovery , _ , d = recovery-call env call d
... | finaliseRecovery , _ , d =
  [] , recoveryFinalised d
    (RecoveryFacts.finalise-evidence (executionContext address env) (Dispatched.executed d)) ,
  signed-resolved before env call (Dispatched.resolved d)

-- The invocation premise of a joint step makes every required token available;
-- AdversarialLifecycle's provenance then applies to each verified request.
accepted-call-provenance : ∀ {before knowledge after env call answer effects}
  (h : Histories.History (before , knowledge)) →
  All (Signatures.Available knowledge) (requiredTokens before env call) →
  Account.Transition P (executionContext address env) (RuntimeCall.request call) before
    (Account.committed answer effects) after →
  Σ (List SignedRequest) λ requests → AcceptedCall env call before answer after effects requests ×
    All (λ request → Provenance h (uncurry′ Symbolic.token request)) requests
accepted-call-provenance {env = env} {call} h available committed
  with accepted-call env call committed
... | requests , classified , signed = requests , classified , All.map⁻
  (subst (λ rs → All (Provenance h) (map (uncurry′ Symbolic.token) rs)) signed
    (JointFacts.required-provenance {environment = env} {call = call} h available))

------------------------------------------------------------------------
-- Request-level provenance under the trace-scoped agreement premise

private
  accepted-encodings : ∀ {env call before answer after effects requests} →
    AcceptedCall env call before answer after effects requests →
    All (λ request → Σ Value (Encodes request)) requests
  accepted-encodings (activated _ _ _) = []
  accepted-encodings (deviceAuthorised _ _ _ _ _ encodes) = (_ , encodes) ∷ []
  accepted-encodings (grantAuthorised _ _ _ _ _ _ encodes) = (_ , encodes) ∷ []
  accepted-encodings (depositedUnshielded _) = []
  accepted-encodings (depositedShielded _) = []
  accepted-encodings (recoverySubmitted _ _ _ _ encodings) =
    AllBase.map (λ encodes → _ , encodes) encodings
  accepted-encodings (recoveryFinalised _ _) = []

  requests-provenance : ∀ {X : Set} (view : Binding.Request → X) {contract knowledge}
    (h : Histories.History (contract , knowledge)) {requests} →
    All (λ request → Σ Value (Encodes request)) requests → All (AgreesIn view h) requests →
    All (λ request → Signatures.Available knowledge (uncurry′ Symbolic.token request)) requests →
    All (RequestProvenance view h) requests
  requests-provenance view h [] [] [] = []
  requests-provenance view h ((d , encodes) ∷ encodings) (agreement ∷ agreements)
    (available ∷ availables) =
    BindingFacts.request-provenance ownership view encodes (Histories.signingHistory h)
      (agreement d encodes) available ∷
    requests-provenance view h encodings agreements availables

accepted-call-requests : ∀ {X : Set} (view : Binding.Request → X)
  {before knowledge after env call answer effects}
  (h : Histories.History (before , knowledge)) →
  All (Signatures.Available knowledge) (requiredTokens before env call) →
  All (AgreesIn view h) (signedRequests before env call) →
  Account.Transition P (executionContext address env) (RuntimeCall.request call) before
    (Account.committed answer effects) after →
  Σ (List SignedRequest) λ requests → AcceptedCall env call before answer after effects requests ×
    All (RequestProvenance view h) requests
accepted-call-requests view {knowledge = knowledge} {env = env} {call} h available agreed
  committed with accepted-call env call committed
... | requests , classified , signed = requests , classified ,
  requests-provenance view h (accepted-encodings classified)
    (subst (All (AgreesIn view h)) signed agreed)
    (All.map⁻ (subst (λ rs → All (Signatures.Available knowledge)
      (map (uncurry′ Symbolic.token) rs)) signed available))

------------------------------------------------------------------------
-- Pending recovery records over rooted histories

private
  transaction-reverted : ∀ s r {e t} →
    Account.transaction s r ≡ (Account.reverted e , t) → t ≡ s
  transaction-reverted s (rejected e) refl = refl
  transaction-reverted s (accepted v t es) ()

  constructorArguments : Account.Deployment → List Value
  constructorArguments d = Account.initialDeviceBoot d ∷ Account.encryptionKey d ∷
    Account.initialRecoveryKey d ∷ Account.initialRecoveryWrap d ∷
    nat (Account.vetoWindowSeconds d) ∷ []

  -- Deployment dispatches the constructor name, which resolves to construct.
  deployment-executes : ∀ ctx d {v s es} → Account.deploy P ctx d ≡ accepted v s es →
    execute construct ctx (constructorArguments d) (state []) ≡ accepted v s es
  deployment-executes ctx d deployed = then-branch (Model.validContext ctx)
    (then-branch (Model.validArguments (Semantics.schema construct) (constructorArguments d)) deployed)

  Flagged : State → Set
  Flagged s = Σ Value λ p → Recovery.Stores s "pending_recovery" p × flag p ≡ true

  stores-unique : ∀ {s k v w} → Recovery.Stores s k v → Recovery.Stores s k w → v ≡ w
  stores-unique cell cell′ =
    just-injective (trans (sym (Recovery.Stores.observed cell)) (Recovery.Stores.observed cell′))

  cleared-flag : ∀ {s} → Recovery.Stores s "pending_recovery" (bool false) → Flagged s → ⊥
  cleared-flag cleared (p , cell , flagged) =
    true≢false (trans (sym flagged) (cong flag (stores-unique cell cleared)))

  same-refl : ∀ {s} → Recovery.SamePending s s
  same-refl = record { pendingKept = λ _ _ → refl }

  same-trans : ∀ {s m t} → Recovery.SamePending s m → Recovery.SamePending m t →
    Recovery.SamePending s t
  same-trans first second = record { pendingKept = λ k member →
    trans (Recovery.SamePending.pendingKept second k member)
      (Recovery.SamePending.pendingKept first k member) }

  same-stores : ∀ {s t k v} → Recovery.SamePending s t → k ∈ Recovery.pendingCells →
    Recovery.Stores s k v → Recovery.Stores t k v
  same-stores same member cell = record { observed =
    trans (Recovery.SamePending.pendingKept same _ member) (Recovery.Stores.observed cell) }

  flagged-before : ∀ {s t} → Recovery.SamePending s t → Flagged t → Flagged s
  flagged-before same (p , cell , flagged) = p , record { observed =
    trans (sym (Recovery.SamePending.pendingKept same "pending_recovery" (here refl)))
      (Recovery.Stores.observed cell) } , flagged

  retained-same : ∀ {s t} {trace : Runs.Trace s t} → Retained trace → Recovery.SamePending s t
  retained-same done = same-refl
  retained-same (kept (refused unchanged) retained) =
    subst (λ u → Recovery.SamePending u _) unchanged (retained-same retained)
  retained-same (kept (ordinary _ _ _ same) retained) = same-trans same (retained-same retained)

  occurrence-retained : ∀ {s t} {trace : Runs.Trace s t} (origin : SubmittedIn trace) →
    Recovery.SamePending (Occurrence.installedAt (occurrence origin)) t
  occurrence-retained (submitted _ _ _ _ _ _ _ retained) = retained-same retained
  occurrence-retained (later _ origin) = occurrence-retained origin

  operation-effect : ∀ op {s t} → Recovery.OperationEffect op s t →
    Recovery.Cleared s t ⊎ (op ≢ cancelRecovery × Recovery.SamePending s t)
  operation-effect withdrawUnshielded same = inj₂ ((λ ()) , same)
  operation-effect withdrawShielded same = inj₂ ((λ ()) , same)
  operation-effect withdrawToContract same = inj₂ ((λ ()) , same)
  operation-effect appendInbox same = inj₂ ((λ ()) , same)
  operation-effect rotateEncKey same = inj₂ ((λ ()) , same)
  operation-effect addDevice same = inj₂ ((λ ()) , same)
  operation-effect removeDevice same = inj₂ ((λ ()) , same)
  operation-effect issueGrant same = inj₂ ((λ ()) , same)
  operation-effect revokeGrant same = inj₂ ((λ ()) , same)
  operation-effect revokeAllGrants same = inj₂ ((λ ()) , same)
  operation-effect publishRecovery same = inj₂ ((λ ()) , same)
  operation-effect cancelRecovery cleared = inj₁ cleared

  -- Classifies an accepted step by its entrypoint's effect on a pending record
  -- that is flagged after the step (RecoverySecurity.pending-effect).
  classify : ∀ e env call answer effects {s m t}
    (executed : Account.Transition P (executionContext address env) (RuntimeCall.request call) s
      (Account.committed answer effects) m) {rest : Runs.Trace m t} →
    isConstructor e ≡ false → resolve (RuntimeCall.request call) ≡ just e →
    Recovery.PendingEffect e (executionContext address env) (arguments (RuntimeCall.request call)) s m →
    Retained rest → Flagged m →
    SubmittedIn (Runs.event env call (Account.committed answer effects) executed ◅ rest) ⊎
      Retained (Runs.event env call (Account.committed answer effects) executed ◅ rest) × Flagged s
  classify construct _ _ _ _ _ () _ _ _ _
  classify (activation c) _ _ _ _ _ _ resolved same retained flagged =
    inj₂ (kept (ordinary (activation c) resolved (ordinaryActivation c) same) retained ,
      flagged-before same flagged)
  classify (device c op) _ _ _ _ _ _ resolved effect retained flagged
    with operation-effect op effect
  ... | inj₁ cleared = ⊥-elim (cleared-flag (Recovery.Cleared.clearsFlag cleared) flagged)
  ... | inj₂ (other , same) =
    inj₂ (kept (ordinary (device c op) resolved (ordinaryDevice c op other) same) retained ,
      flagged-before same flagged)
  classify (grant c op) _ _ _ _ _ _ resolved effect retained flagged
    with operation-effect op effect
  ... | inj₁ cleared = ⊥-elim (cleared-flag (Recovery.Cleared.clearsFlag cleared) flagged)
  ... | inj₂ (other , same) =
    inj₂ (kept (ordinary (grant c op) resolved (ordinaryGrant c op other) same) retained ,
      flagged-before same flagged)
  classify depositPublic _ _ _ _ _ _ resolved same retained flagged =
    inj₂ (kept (ordinary depositPublic resolved ordinaryUnshieldedDeposit same) retained ,
      flagged-before same flagged)
  classify depositPrivate _ _ _ _ _ _ resolved same retained flagged =
    inj₂ (kept (ordinary depositPrivate resolved ordinaryShieldedDeposit same) retained ,
      flagged-before same flagged)
  classify submitRecovery env call answer effects executed _ resolved submission retained _ =
    inj₁ (submitted env call answer effects executed resolved submission retained)
  classify finaliseRecovery _ _ _ _ _ _ _ finalisation _ flagged =
    ⊥-elim (cleared-flag (Recovery.Finalisation.Evidence.clearsFlag finalisation) flagged)

  step-origin : ∀ {s m t} (x : Runs.Step s m) {rest : Runs.Trace m t} → Retained rest →
    Flagged m → SubmittedIn (x ◅ rest) ⊎ Retained (x ◅ rest) × Flagged s
  step-origin {s} (Runs.event env call (Account.reverted error) executed) retained flagged =
    inj₂ (kept (refused unchanged) retained , subst Flagged unchanged flagged)
    where
    unchanged = transaction-reverted s (Model.dispatch P (executionContext address env)
      (RuntimeCall.request call) s) (Account.execution executed)
  step-origin (Runs.event env call (Account.committed answer effects) executed) retained flagged
    with accepted-dispatch env call executed
  ... | e , notConstructor , d = classify e env call answer effects executed notConstructor
    (Dispatched.resolved d)
    (RecoveryFacts.pending-effect e (executionContext address env) (arguments (RuntimeCall.request call))
      (Dispatched.executed d))
    retained flagged

  -- A record flagged at the end of a trace was installed within it, or was
  -- already flagged at its start and retained throughout.
  trace-origin : ∀ {s t} (trace : Runs.Trace s t) → Flagged t →
    SubmittedIn trace ⊎ Retained trace × Flagged s
  trace-origin ε flagged = inj₂ (done , flagged)
  trace-origin (x ◅ rest) flagged with trace-origin rest flagged
  ... | inj₁ origin = inj₁ (later x origin)
  ... | inj₂ (retained , flaggedNext) = step-origin x retained flaggedNext

pending-origin : ∀ {s p} (h : Runs.History s) → Recovery.Stores s "pending_recovery" p →
  flag p ≡ true → SubmittedIn (Runs.History.execution h)
pending-origin (Runs.rooted env d (Account.committed v effects) initial deployed trace) cell flagged
  with trace-origin trace (_ , cell , flagged)
... | inj₁ origin = origin
... | inj₂ (_ , flaggedInitially) = ⊥-elim (cleared-flag
  (RecoveryFacts.pending-effect construct (executionContext address env) (constructorArguments d)
    {s = state []} {v = v} {t = initial} {es = effects}
    (deployment-executes (executionContext address env) d deployed))
  flaggedInitially)
pending-origin (Runs.rooted env d (Account.reverted e) initial () trace) cell flagged

joint-pending-origin : ∀ {s knowledge p} (h : Histories.History (s , knowledge)) →
  Recovery.Stores s "pending_recovery" p → flag p ≡ true →
  SubmittedIn (Histories.contractTrace (Histories.History.execution h))
joint-pending-origin h = pending-origin (Histories.contractHistory h)

private
  enacts : ∀ {ctx s t after} {trace : Runs.Trace s t} (origin : SubmittedIn trace) →
    Recovery.Finalisation.Evidence ctx t after → EnactsOccurrence ctx trace after
  enacts origin finalisation = record
    { origin = origin
    ; finalisation = finalisation
    ; sameSuccessor = stores-unique F.successorCell
        (same-stores retained (there (here refl)) S.installsEntry)
    ; sameRecoveryKey = stores-unique F.recoveryKeyCell
        (same-stores retained (there (there (here refl))) S.installsRecoveryKey)
    ; sameDeadline = stores-unique F.deadlineCell
        (same-stores retained (there (there (there (here refl)))) S.installsDeadline) }
    where
    module F = Recovery.Finalisation.Evidence finalisation
    module S = Recovery.Submission.Evidence (Occurrence.installation (occurrence origin))
    retained = occurrence-retained origin

finalisation-enacts-occurrence : ∀ env (call : RuntimeCall) {before answer effects after} →
  (h : Runs.History before) → resolve (RuntimeCall.request call) ≡ just finaliseRecovery →
  Account.Transition P (executionContext address env) (RuntimeCall.request call) before
    (Account.committed answer effects) after →
  EnactsOccurrence (executionContext address env) (Runs.History.execution h) after
finalisation-enacts-occurrence env call h finalising committed
  with accepted-dispatch env call committed
... | e , _ , dispatched found executed with trans (sym found) finalising
...   | refl = enacts (pending-origin h F.pending F.isPending) finalisation
  where
  finalisation = RecoveryFacts.finalise-evidence (executionContext address env) executed
  module F = Recovery.Finalisation.Evidence finalisation

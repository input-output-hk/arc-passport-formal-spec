{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes using (Primitives; Value)
open import Midnight.ContractDSL.SymbolicSigning using (Ownership)
import Conformance.FullAccountSignatureBinding as SignatureBinding

-- Concrete signing interpretation of full-account runtime calls, and the
-- account's deployment-rooted joint histories (AdversarialLifecycle.Joint).
-- signedRequests reruns, from a call's before state, the source steps that
-- compute the request its device, grant or recovery signatures are checked
-- against, and keeps each (key, request) whose actual source verification
-- succeeds; requiredTokens are their SignatureBinding tokens (key and source
-- encoding). A joint invocation needs those tokens available: the ideal
-- symbolic boundary for complete source hash-and-sign requests. Tokens are
-- never consumed, so obtained signatures may be replayed. A concrete
-- cryptographic realization must also account for effective challenge/digest
-- equivalence (Schnorr mod jubjubOrder, ECDSA digest reduction); neither raw
-- verification success nor this exact-digest tokenization proves it. Invalid
-- signatures require nothing, so their refusals remain steps. Activation,
-- deposits and finalisation verify no signature. The guard evidence in
-- AcceptedCall holds for every primitive backend P. Local source execution,
-- not ledger admission or adoption. Statements: Passport.AccountSecurityProperties.
module Passport.AccountSecurity (P : Primitives) (address : Value)
  (ownership : SignatureBinding.Key P → Ownership) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_; _++_; drop; map; take)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe.Base using (Maybe; just; nothing; fromMaybe; maybe′; _>>=_)
open import Data.Nat.Base using (ℕ; suc; _+_)
open import Data.Product using (Σ; _×_; _,_; uncurry′)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Conformance.FullAccountTypes hiding (_>>=_; _>>_)
import Conformance.FullAccount as Model
open import Conformance.FullAccountBody P using (Operation; withdrawUnshielded; cancelRecovery;
  operationAtoms; operationName)
open import Conformance.FullAccountCrypto P using (challengeAt; hash; hashTag)
import Conformance.FullAccountDeviceSecurity as DeviceSecurity
open import Conformance.FullAccountGrant P using (GrantAuth; authorisation; grantId)
import Conformance.FullAccountGrantSecurity as GrantSecurity
import Conformance.FullAccountRecoverySecurity as RecoverySecurity
open import Conformance.FullAccountLayouts using (module SubmitArguments; grantNonce)
import Midnight.ContractDSL.AdversarialLifecycle as Adversarial
import Midnight.ContractDSL.Lifecycle as Generic
import Midnight.ContractDSL.SymbolicSigning as Signing
import Passport.Account as Account
open import Passport.AccountLifecycle P

module Semantics = Model.AccountSemantics P
open Semantics using (Entrypoint; construct; activation; device; grant; depositPublic;
  depositPrivate; submitRecovery; finaliseRecovery; execute)
module Device = DeviceSecurity P
open Device using (deviceArguments; deviceAuth; deviceCoin; verificationMessage)
module Grant = GrantSecurity P
module Recovery = RecoverySecurity P
module Binding = SignatureBinding P
module Runs = Generic.Runs lifecycle address

------------------------------------------------------------------------
-- Dispatch: the entrypoint the dispatcher's name table resolves

resolve : RawCall → Maybe Entrypoint
resolve call = Semantics.lookupEntrypoint (name call) Semantics.entrypoints

-- execute's split of a grant call's arguments (spend arguments are take 3).
grantAuthorisation : Curve → Operation → List Value → GrantAuth
grantAuthorisation c withdrawUnshielded xs = Semantics.parseGrant c (drop 3 xs) none none
grantAuthorisation c _ xs = Semantics.parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)

-- The answer of a source computation run from state s; refusal gives nothing.
evaluateFrom : ∀ {A} → M A → State → Maybe A
evaluateFrom m s = Binding.outcome (m s)

-- An accepted call's dispatcher resolution, and the accepted execution of that
-- entrypoint after the dispatcher's argument, context, coin and state validation.
record Dispatched (e : Entrypoint) (env : Environment) (call : RuntimeCall)
    (before : State) (answer : Value) (after : State) (effects : List Effect) : Set where
  constructor dispatched
  field resolved : resolve (RuntimeCall.request call) ≡ just e
        executed : execute e (executionContext address env) (arguments (RuntimeCall.request call))
          before ≡ accepted answer after effects

------------------------------------------------------------------------
-- Signed requests a runtime call carries

module Symbolic = Binding.Symbolic ownership
open Symbolic using (module Signatures)
open Signatures using (Token)

-- A key and the source-computed request whose encoding its signature covers.
SignedRequest : Set
SignedRequest = Binding.Key × Binding.Request

-- Keep a request only when the actual source verification gate accepts.
whenVerified : Maybe Value → SignedRequest → List SignedRequest
whenVerified (just _) request = request ∷ []
whenVerified nothing _ = []

whenAccepted : Bool → SignedRequest → List SignedRequest
whenAccepted true request = request ∷ []
whenAccepted false _ = []

-- The request a device signature covers, for operation atoms and auth nonce.
deviceRequest : Curve → Operation → Context → List Value → List Atom → ℕ → SignedRequest
deviceRequest c op ctx xs atoms nonce =
  Binding.authorisingKey c a , Binding.authorisedRequest c false op (self ctx) a atoms nonce
  where a = deviceAuth c op xs

-- The request a grantee signature covers, for grant id and stored record g;
-- ga and ys are grantCall's authorisation and spend arguments.
grantRequest : Curve → Operation → Context → GrantAuth → List Value → Value → Value →
  SignedRequest
grantRequest c op ctx ga ys id g =
  Binding.authorisingKey c (authorisation ga) ,
  Binding.authorisedRequest c true op (self ctx) (authorisation ga)
    (Grant.grantChallengeAtoms op ys (Grant.grantCoin op ctx) ga id g) (number (grantNonce g))

-- recover_submit's request, over the stored recovery key, epoch and nonce.
-- The current recovery key's authorisation and the successor key's possession
-- proof both cover it.
submission : Context → List Value → Value → Value → Value → Binding.RecoveryChallenge
submission ctx xs recoveryKey storedEpoch storedNonce =
  Binding.submitChallenge (self ctx) recoveryKey xs (suc (number storedEpoch)) (number storedNonce)

recoveryAuthority : Value → Binding.RecoveryChallenge → SignedRequest
recoveryAuthority recoveryKey r = Binding.signingKey jubjub recoveryKey , Binding.recoveryRequest r

successorPossession : List Value → Binding.RecoveryChallenge → SignedRequest
successorPossession xs r =
  Binding.signingKey jubjub (SubmitArguments.successorKey xs) , Binding.recoveryRequest r

-- Each builder reruns, from the before state, the source steps deviceCall,
-- grantCall or submit use to compute the checked digest, then applies the gate.
deviceRequests : Curve → Operation → Context → List Value → State → List SignedRequest
deviceRequests c op ctx xs s = fromMaybe [] do
  atoms ← evaluateFrom (operationAtoms op (deviceArguments op xs) (deviceCoin op ctx)) s
  nonce ← lookupCell "auth_nonce" (ledger s)
  h ← evaluateFrom (challengeAt c false (operationName op) (self ctx) (deviceAuth c op xs) atoms
    (number nonce)) s
  just (whenVerified (Binding.verifiedDigest c (deviceAuth c op xs) h (verificationMessage c))
    (deviceRequest c op ctx xs atoms (number nonce)))

grantRequests : Curve → Operation → Context → GrantAuth → List Value → State →
  List SignedRequest
grantRequests c op ctx ga ys s = fromMaybe [] do
  id ← evaluateFrom (grantId c ctx ga) s
  g ← evaluateFrom (lookup "grants" id) s
  h ← evaluateFrom (challengeAt c true (operationName op) (self ctx) (authorisation ga)
    (Grant.grantChallengeAtoms op ys (Grant.grantCoin op ctx) ga id g)
    (number (grantNonce g))) s
  just (whenVerified (Binding.verifiedDigest c (authorisation ga) h "invalid grant signature")
    (grantRequest c op ctx ga ys id g))

recoveryRequests : Context → List Value → State → List SignedRequest
recoveryRequests ctx xs s = fromMaybe [] do
  storedEpoch ← lookupCell "device_epoch" (ledger s)
  storedNonce ← lookupCell "auth_nonce" (ledger s)
  recoveryKey ← lookupCell "recovery_pk" (ledger s)
  domain ← evaluateFrom (hashTag Binding.recoverySubmitTag) s
  h ← evaluateFrom (hash (Binding.submitPreimage domain
    (submission ctx xs recoveryKey storedEpoch storedNonce))) s
  just (whenAccepted (Binding.schnorrAccepted recoveryKey A.recoveryR A.recoveryS h
          "invalid recovery signature")
        (recoveryAuthority recoveryKey (submission ctx xs recoveryKey storedEpoch storedNonce)) ++
      whenAccepted (Binding.schnorrAccepted A.successorKey A.successorR A.successorS h
          "invalid successor co-signature")
        (successorPossession xs (submission ctx xs recoveryKey storedEpoch storedNonce)))
  where module A = SubmitArguments xs

-- Activation, deposits and finalisation verify no signature.
entrypointRequests : Entrypoint → Context → List Value → State → List SignedRequest
entrypointRequests (device c op) ctx xs s = deviceRequests c op ctx xs s
entrypointRequests (grant c op) ctx xs s =
  grantRequests c op ctx (grantAuthorisation c op xs) (take 3 xs) s
entrypointRequests submitRecovery ctx xs s = recoveryRequests ctx xs s
entrypointRequests _ _ _ _ = []

signedRequests : State → Environment → RuntimeCall → List SignedRequest
signedRequests s env call = maybe′
  (λ e → entrypointRequests e (executionContext address env) (arguments (RuntimeCall.request call)) s)
  [] (resolve (RuntimeCall.request call))

-- Token knowledge needed to construct the call: each verifying signature's key
-- and its request's source encoding (Binding.encode, a Maybe digest).
requiredTokens : State → Environment → RuntimeCall → List Token
requiredTokens s env call = map (uncurry′ Symbolic.token) (signedRequests s env call)

------------------------------------------------------------------------
-- Joint histories of this account and symbolic signing

module Histories = Adversarial.Joint lifecycle address Symbolic.interface requiredTokens

-- Message-level provenance of a token known at a reachable joint state: its key
-- is attacker-controlled there, or an approved honest signing in the history's
-- signing trace produced it (SymbolicSigning.HonestlyIssued).
Provenance : ∀ {contract knowledge} → Histories.History (contract , knowledge) → Token → Set
Provenance {knowledge = knowledge} h τ =
  Signatures.Controlled knowledge (Signatures.Token.key τ) ⊎
  Signatures.HonestlyIssued (Histories.signingHistory h) τ

------------------------------------------------------------------------
-- Accepted runtime calls by source path

-- The request's source encoding is the digest the signature primitive verified.
Encodes : SignedRequest → Value → Set
Encodes (k , r) d = Binding.encode k r ≡ just d

module DeviceCalled = Device.DeviceCall
module Granted = Grant.GrantCallEvidence
module Submitted = Recovery.Submission.Evidence

-- The request an accepted device call verified: its operation atoms and the
-- authorisation nonce it consumed.
calledRequest : ∀ {c op ctx xs s v t} → Device.DeviceCall c op ctx xs s v t → SignedRequest
calledRequest {c} {op} {ctx} {xs} evidence =
  deviceRequest c op ctx xs (DeviceCalled.atoms evidence) (number (DeviceCalled.nonce evidence))

-- The request an accepted grant call verified: its presented id and stored record.
grantedRequest : ∀ {c op ctx ga ys s} → Grant.GrantCallEvidence c op ctx ga ys s → SignedRequest
grantedRequest {c} {op} {ctx} {ga} {ys} evidence =
  grantRequest c op ctx ga ys (Granted.identifier evidence) (Granted.grantRecord evidence)

-- The recovery-key authorisation and successor possession an accepted
-- submission verified, over its stored recovery key, epoch and nonce.
submittedRequests : ∀ {ctx xs s t} → Recovery.Submission.Evidence ctx xs s t → List SignedRequest
submittedRequests {ctx} {xs} evidence =
  recoveryAuthority recoveryKey r ∷ successorPossession xs r ∷ []
  where
  open Recovery.Submission.Evidence evidence using (recoveryKey; storedEpoch; storedNonce)
  r = submission ctx xs recoveryKey storedEpoch storedNonce

module _ (env : Environment) (call : RuntimeCall) where
  private
    ctx = executionContext address env
    xs = arguments (RuntimeCall.request call)

  -- An accepted runtime call, by the entrypoint the dispatcher resolved: the
  -- guard evidence extracted from that entrypoint's actual evaluator, and the
  -- signed requests whose source verification the evaluator performed. There
  -- is no constructor case: no runtime call resolves to it.
  data AcceptedCall (before : State) (answer : Value) (after : State) (effects : List Effect) :
      List SignedRequest → Set where
    activated : ∀ c → Dispatched (activation c) env call before answer after effects →
      Device.Activation c ctx (Semantics.parseActivation c xs) (get 1 xs) before after →
      AcceptedCall before answer after effects []
    deviceAuthorised : ∀ c op → Dispatched (device c op) env call before answer after effects →
      (evidence : Device.DeviceCall c op ctx xs before answer after) →
      (checked : Binding.Verified c (deviceAuth c op xs) (DeviceCalled.challengeValue evidence)) →
      Encodes (calledRequest evidence) (Binding.signedDigest checked) →
      AcceptedCall before answer after effects (calledRequest evidence ∷ [])
    grantAuthorised : ∀ c op → Dispatched (grant c op) env call before answer after effects →
      Grant.Withdrawal op →
      (final : Grant.GrantFinalState c op ctx (grantAuthorisation c op xs) (take 3 xs) before after) →
      (checked : Binding.Verified c (authorisation (grantAuthorisation c op xs))
        (Granted.challengeValue (Grant.GrantFinalState.callEvidence final))) →
      Encodes (grantedRequest (Grant.GrantFinalState.callEvidence final)) (Binding.signedDigest checked) →
      AcceptedCall before answer after effects (grantedRequest (Grant.GrantFinalState.callEvidence final) ∷ [])
    depositedUnshielded : Dispatched depositPublic env call before answer after effects →
      AcceptedCall before answer after effects []
    depositedShielded : Dispatched depositPrivate env call before answer after effects →
      AcceptedCall before answer after effects []
    recoverySubmitted : Dispatched submitRecovery env call before answer after effects →
      (evidence : Recovery.Submission.Evidence ctx xs before after) →
      Binding.SchnorrAccepts (Submitted.recoveryKey evidence)
        (SubmitArguments.recoveryR xs) (SubmitArguments.recoveryS xs) (Submitted.digest evidence) →
      Binding.SchnorrAccepts (SubmitArguments.successorKey xs)
        (SubmitArguments.successorR xs) (SubmitArguments.successorS xs) (Submitted.digest evidence) →
      All (λ request → Encodes request (Submitted.digest evidence)) (submittedRequests evidence) →
      AcceptedCall before answer after effects (submittedRequests evidence)
    recoveryFinalised : Dispatched finaliseRecovery env call before answer after effects →
      Recovery.Finalisation.Evidence ctx before after →
      AcceptedCall before answer after effects []

------------------------------------------------------------------------
-- Request-level provenance

-- SignatureBinding's trace-scoped agreement premise, for the encoding of a
-- signed request, in a joint history's signing trace. view selects what must
-- agree (the identity for the whole request).
AgreesIn : ∀ {X : Set} → (Binding.Request → X) → ∀ {contract knowledge} →
  Histories.History (contract , knowledge) → SignedRequest → Set
AgreesIn view h (k , r) = ∀ d → Binding.encode k r ≡ just d →
  Symbolic.IssuedAgreement view (Histories.signingHistory h) k d r

-- A verified request's key is attacker-controlled at the invoking joint state,
-- or a request with the same view was approved and honestly signed with it.
RequestProvenance : ∀ {X : Set} → (Binding.Request → X) → ∀ {contract knowledge} →
  Histories.History (contract , knowledge) → SignedRequest → Set
RequestProvenance view {knowledge = knowledge} h (k , r) =
  Signatures.Controlled knowledge k ⊎
  Σ (Signatures.HonestlyIssued (Histories.signingHistory h) (Symbolic.token k r))
    λ issued → view (Signatures.HonestlyIssued.request issued) ≡ view r

------------------------------------------------------------------------
-- Pending recovery records in account histories

-- Entrypoints that neither install, enact nor cancel a pending recovery.
data Ordinary : Entrypoint → Set where
  ordinaryActivation : ∀ c → Ordinary (activation c)
  ordinaryDevice : ∀ c op → op ≢ cancelRecovery → Ordinary (device c op)
  ordinaryGrant : ∀ c op → op ≢ cancelRecovery → Ordinary (grant c op)
  ordinaryUnshieldedDeposit : Ordinary depositPublic
  ordinaryShieldedDeposit : Ordinary depositPrivate

-- A history step that keeps a pending record: a refused attempt, which keeps
-- the whole state, or an accepted call of an ordinary entrypoint, which keeps
-- the pending cells.
data Retains {s t : State} : Runs.Step s t → Set where
  refused : ∀ {env call error executed} → t ≡ s →
    Retains (Runs.event env call (Account.reverted error) executed)
  ordinary : ∀ {env call answer effects executed} e →
    resolve (RuntimeCall.request call) ≡ just e → Ordinary e → Recovery.SamePending s t →
    Retains (Runs.event env call (Account.committed answer effects) executed)

data Retained : ∀ {s t} → Runs.Trace s t → Set where
  done : ∀ {s} → Retained {s} {s} ε
  kept : ∀ {s m t} {x : Runs.Step s m} {rest : Runs.Trace m t} →
    Retains x → Retained rest → Retained (x ◅ rest)

-- An actual accepted recover_submit step of a trace, after which every step
-- retains the record it installed: there is no later accepted submission,
-- cancellation or finalisation; refused attempts remain allowed.
data SubmittedIn : ∀ {s t} → Runs.Trace s t → Set where
  submitted : ∀ {s m t} env call answer effects
    (executed : Account.Transition P (executionContext address env) (RuntimeCall.request call) s
      (Account.committed answer effects) m) {rest : Runs.Trace m t} →
    resolve (RuntimeCall.request call) ≡ just submitRecovery →
    Recovery.Submission.Evidence (executionContext address env) (arguments (RuntimeCall.request call))
      s m →
    Retained rest →
    SubmittedIn (Runs.event env call (Account.committed answer effects) executed ◅ rest)
  later : ∀ {s m t} (x : Runs.Step s m) {rest : Runs.Trace m t} →
    SubmittedIn rest → SubmittedIn (x ◅ rest)

-- The submission evidence such an occurrence carries.
record Occurrence : Set where
  field submissionContext : Context
        submissionArguments : List Value
        submittedFrom installedAt : State
        installation : Recovery.Submission.Evidence submissionContext submissionArguments
          submittedFrom installedAt

occurrence : ∀ {s t} {trace : Runs.Trace s t} → SubmittedIn trace → Occurrence
occurrence (submitted {s} {m} env call _ _ _ _ installation _) = record
  { submissionContext = executionContext address env
  ; submissionArguments = arguments (RuntimeCall.request call)
  ; submittedFrom = s ; installedAt = m ; installation = installation }
occurrence (later _ origin) = occurrence origin

-- A finalisation from the end of a trace enacts the successor entry, recovery
-- key and deadline that the trace's submission occurrence installed.
record EnactsOccurrence (ctx : Context) {s t} (trace : Runs.Trace s t) (after : State) : Set where
  field
    origin : SubmittedIn trace
    finalisation : Recovery.Finalisation.Evidence ctx t after
    sameSuccessor : Recovery.Finalisation.Evidence.successor finalisation ≡
      Recovery.Submission.Evidence.successor (Occurrence.installation (occurrence origin))
    sameRecoveryKey : Recovery.Finalisation.Evidence.recoveryKey finalisation ≡
      SubmitArguments.nextRecoveryKey (Occurrence.submissionArguments (occurrence origin))
    sameDeadline : Recovery.Finalisation.Evidence.deadline finalisation ≡
      nat (number (SubmitArguments.nowBound (Occurrence.submissionArguments (occurrence origin))) +
        number (Recovery.Submission.Evidence.vetoWindow (Occurrence.installation (occurrence origin))))

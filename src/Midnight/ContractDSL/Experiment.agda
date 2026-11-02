{-# OPTIONS --safe --without-K #-}

-- Experimental off-chain evaluation and proof transport for safety fixtures and
-- privacy experiments. Admission delegates to Protocol.toProtocol and Contract.admit.
-- Artifacts, resource responses and Commitment are simulator stand-ins, not
-- cryptographic commitments or proof verification; certification comes from the core.
-- See docs/contract-specification-dsl.md#ideal-resource-merkle-history-experiment.

open import Midnight.ContractDSL.Ledger

module Midnight.ContractDSL.Experiment (L : Semantics) (Assertion : Set) where

open import Data.Bool.Base
open import Data.Maybe hiding (_>>=_)
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality
open import CategoricalCrypto.GamePlaying.Partial
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol hiding (serve)
import Midnight.ContractDSL.Contract as Core
import Midnight.ContractDSL.Protocol as MainProtocol
open import Midnight.ContractDSL.Program L Assertion hiding (step)
open import Midnight.ContractDSL.ObservedExecution L Assertion
open Semantics L

-- Closed main-protocol activations can be embedded under a proof resource.
closedCalls : ∀ {A X} → Calls unitᴵ X → Calls A X
closedCalls (ret x) = ret x
closedCalls (call () k)
closedCalls (coin μ k) = coin μ (λ b → closedCalls (k b))
closedCalls dead = dead

module Runtime (C : Core.Contract L Assertion)
  (PublicInput : Core.Contract.EntryPoint C → Set)
  (projectInput : ∀ n → Core.Contract.Input C n → PublicInput n) where

  open Core.Contract C public
  module Main = MainProtocol L Assertion C

  SimulatorArtifact : Set
  SimulatorArtifact = Bool

  neutralArtifact : SimulatorArtifact
  neutralArtifact = false

  record Claim : Set where
    constructor claim
    field target : ℕ
          entry : EntryPoint
          input : PublicInput entry
          artifact : SimulatorArtifact
          journal : Journal

  record CertifiedDraft : Set where
    constructor certifiedDraft
    field transaction : Transaction
          artifact : SimulatorArtifact
  open CertifiedDraft public

  publicClaim : CertifiedDraft → Claim
  publicClaim (certifiedDraft tx token) = claim (Transaction.target tx) (Transaction.entry tx)
    (projectInput (Transaction.entry tx) (Transaction.input tx)) token
    (journal (Transaction.execution tx))

  makeCertifiedDraft : (n : EntryPoint) (a : Input n) (token : SimulatorArtifact) (s : State)
    (r : Result n) (t : State) (j : Journal) →
    eval (body self n a) s ≡ inj₂ (finished r t j) → CertifiedDraft
  makeCertifiedDraft n a token s r t j certified = certifiedDraft record
    { target = self ; entry = n ; input = a ; view = s
    ; execution = finished r t j ; certified = certified } token

  -- Simulator artifacts intentionally do not bind a private opening.
  Commitment : SimulatorArtifact → ℕ → (n : EntryPoint) → Input n → Bool → Set
  Commitment token target n a opening = ⊤

  CommitmentBinding : Set
  CommitmentBinding = ∀ token target n (a b : Input n) opening opening′ →
    Commitment token target n a opening → Commitment token target n b opening′ →
    a ≡ b × opening ≡ opening′

  Draft = Maybe CertifiedDraft

  data Envelope : Set where
    invalidEnvelope : Envelope
    certifiedEnvelope : CertifiedDraft → Envelope

  data ProofQuery : Set where
    certifyRequest verifyRequest : CertifiedDraft → ProofQuery
    invalidVerifyRequest : ProofQuery

  ProofIf = Bool ⇿ ProofQuery

  proofResource : Protocol unitᴵ ProofIf
  -- Explicit simulator responses; CertifiedDraft already carries core certification.
  proofResource = record
    { St = ⊤ ; init = tt ; step = λ _ → λ
        { (certifyRequest p) → ret (tt , true)
        ; (verifyRequest p) → ret (tt , true)
        ; invalidVerifyRequest → ret (tt , false) } }

  data ServiceQuery : Set where
    snapshotRequest : ServiceQuery
    certifyDraft : CertifiedDraft → ServiceQuery
    deliverEnvelope : Envelope → ServiceQuery

  data ServiceAnswer : Set where
    snapshotAnswer : State → ServiceAnswer
    certificationAnswer : Bool → ServiceAnswer
    submissionAnswer : Verdict → ServiceAnswer
    invalidTransport : ServiceAnswer

  ServiceIf = ServiceAnswer ⇿ ServiceQuery

  bridge : ℕ → State → Protocol ProofIf ServiceIf
  bridge now initial = record { St = State ; init = initial ; step = serve }
    where
    serve : State → ServiceQuery → Calls ProofIf (State × ServiceAnswer)
    serve s snapshotRequest = ret (s , snapshotAnswer s)
    serve s (certifyDraft p) = call (certifyRequest p) λ ok → ret (s , certificationAnswer ok)
    serve s (deliverEnvelope invalidEnvelope) = ret (s , invalidTransport)
    serve s (deliverEnvelope (certifiedEnvelope p)) = call (verifyRequest p) λ where
      false → ret (s , submissionAnswer rejected)
      true → closedCalls (step (Main.toProtocol initial) s (submit now (transaction p))) >>=ᶜ λ
        { (t , response) → ret (t , submissionAnswer (Main.Receipt.verdict response)) }

  data ClientQuery : Set where
    prepareDraft : (n : EntryPoint) → Input n → SimulatorArtifact → ClientQuery
    submitDraft : ClientQuery
    sendEnvelope : Envelope → ClientQuery

  data ClientAnswer : Set where
    preparedAnswer : (n : EntryPoint) → Result n → Claim → Trace → ClientAnswer
    failed : Error → Trace → ClientAnswer
    provingFailed : Trace → ClientAnswer
    admitted submitted : Verdict → ClientAnswer
    occupied absentDraft transportInvalid : ClientAnswer

  ClientIf = ClientAnswer ⇿ ClientQuery

  afterEvaluation : (n : EntryPoint) (a : Input n) (token : SimulatorArtifact) (s : State)
    (observed : Trace) (outcome : Outcome (Result n)) →
    eval (body self n a) s ≡ outcome → Calls ServiceIf (Draft × ClientAnswer)
  afterEvaluation n a token s observed (inj₁ err) ev = ret (nothing , failed err observed)
  afterEvaluation n a token s observed (inj₂ (finished r t j)) ev =
    let p = makeCertifiedDraft n a token s r t j ev in
    call (certifyDraft p) λ where
      (certificationAnswer true) → ret (just p , preparedAnswer n r (publicClaim p) observed)
      (certificationAnswer false) → ret (nothing , provingFailed observed)
      _ → dead

  client : Protocol ServiceIf ClientIf
  client = record { St = Draft ; init = nothing ; step = activate }
    where
    deliver : Draft → Envelope → (Verdict → ClientAnswer) → Calls ServiceIf (Draft × ClientAnswer)
    deliver d envelope answer = call (deliverEnvelope envelope) λ where
      (submissionAnswer v) → ret (d , answer v)
      invalidTransport → ret (d , transportInvalid)
      _ → dead

    activate : Draft → ClientQuery → Calls ServiceIf (Draft × ClientAnswer)
    activate (just p) (prepareDraft n a token) = ret (just p , occupied)
    activate nothing (prepareDraft n a token) = call snapshotRequest λ where
      (snapshotAnswer s) → afterEvaluation n a token s
        (trace (execute (body self n a) s)) (evaluation (execute (body self n a) s))
        (execute-correct (body self n a) s)
      _ → dead
    activate nothing submitDraft = ret (nothing , absentDraft)
    activate (just p) submitDraft = deliver nothing (certifiedEnvelope p) admitted
    activate d (sendEnvelope envelope) = deliver d envelope submitted

  services : ℕ → State → Protocol unitᴵ ServiceIf
  services now initial = bridge now initial ∘ᵖ proofResource

  system : ℕ → State → Protocol unitᴵ ClientIf
  system now initial = client ∘ᵖ services now initial

  -- The composed state is client draft × (ledger state × resource state).
  ledgerState : Draft × (State × ⊤) → State
  ledgerState st = proj₁ (proj₂ st)

  module PublicProjection (PublicResult : EntryPoint → Set)
    (disclose : ∀ n → Result n → PublicResult n) where

    data PublicAnswer : Set where
      prepared : (n : EntryPoint) → PublicResult n → Claim → Trace → PublicAnswer
      failed : Error → Trace → PublicAnswer
      provingFailed : Trace → PublicAnswer
      admitted submitted : Verdict → PublicAnswer
      occupied absentDraft transportInvalid : PublicAnswer

    publicAnswer : ClientAnswer → PublicAnswer
    publicAnswer (preparedAnswer n r statement observed) = prepared n (disclose n r) statement observed
    publicAnswer (failed err observed) = failed err observed
    publicAnswer (provingFailed observed) = provingFailed observed
    publicAnswer (admitted v) = admitted v
    publicAnswer (submitted v) = submitted v
    publicAnswer occupied = occupied
    publicAnswer absentDraft = absentDraft
    publicAnswer transportInvalid = transportInvalid

    recipientAnswer : ClientAnswer → Maybe (Σ EntryPoint Result)
    recipientAnswer (preparedAnswer n r statement observed) = just (n , r)
    recipientAnswer _ = nothing

    wrapper : ∀ {Action : Set} → (Action → ClientQuery) → Protocol ServiceIf (PublicAnswer ⇿ Action)
    wrapper request = record
      { St = Draft ; init = nothing ; step = λ d action →
          step client d (request action) >>=ᶜ λ
            { (d′ , answer) → ret (d′ , publicAnswer answer) } }

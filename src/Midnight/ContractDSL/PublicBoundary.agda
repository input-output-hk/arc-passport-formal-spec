{-# OPTIONS --safe --without-K --guardedness #-}

module Midnight.ContractDSL.PublicBoundary where

open import Data.Bool.Base
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Function.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Observe
import Midnight.ContractDSL.Balance as Balance
import Midnight.ContractDSL.BalanceLedger as BL
import Midnight.ContractDSL.Program as Programs
open import Midnight.ContractDSL.MidnightLedger hiding (prepare)
open import Midnight.ContractDSL.MerkleFixture using (initial)
open import Midnight.ContractDSL.Program midnight Assertion hiding (step)
open import Midnight.ContractDSL.Smoke using () renaming (readDet to deterministic)
open import Midnight.ContractDSL.Protocol midnight Assertion

-- Result declassification is fixed per entry, not chosen by the challenge bit.
data Entry : Set where
  silent echo publicEcho publishInput queryInput abortAfter chainGate : Entry

Result : Entry → Set
Result echo = Bool
Result publicEcho = Bool
Result _ = ⊤

bit : Bool → ℕ
bit false = 0
bit true = 1

boundaryContract : Contract
boundaryContract = record
  { Name = Entry ; Input = λ _ → Bool ; PublicArgs = λ _ → ⊤ ; Result = Result
  ; Witness = λ _ _ → ⊤ ; publicArgs = λ _ _ → tt
  ; body = λ _ → λ
      { silent b _ → pure tt
      ; echo b _ → pure b
      ; publicEcho b _ → pure b
      ; publishInput b _ → perform (publish (bit b))
      ; queryInput b _ → perform (ledger (flagMember b)) >> pure tt
      ; abortAfter b _ → perform (publish (bit b)) >> perform (ledger (flagMember b)) >> assert false assertionFailed
      ; chainGate b _ → perform (atChain (timeAtLeast 1)) } }

module I = Interpreter boundaryContract (SimulatorCommunication.scheme boundaryContract) 0

simulator-not-binding : ¬ CommunicationObligations.Binding boundaryContract (SimulatorCommunication.scheme boundaryContract)
simulator-not-binding binding with proj₁ (proj₂ (binding false 0 silent false tt false 0 silent true tt false refl refl))
... | ()

PublicResult : Entry → Set
PublicResult publicEcho = Bool
PublicResult _ = ⊤

disclose : (n : Entry) → Result n → PublicResult n
disclose publicEcho b = b
disclose silent _ = tt
disclose echo _ = tt
disclose publishInput _ = tt
disclose queryInput _ = tt
disclose abortAfter _ = tt
disclose chainGate _ = tt

module O = I.Observation PublicResult disclose

data Action : Set where
  prepare commit : Action

request : Entry → Bool → Action → I.ClientQuery
request n b prepare = I.build n b tt false
request n b commit = I.submit

publicSystem : Entry → Bool → Protocol unitᴵ (O.PublicAnswer ⇿ Action)
publicSystem n b = O.wrapper (request n b) ∘ᵖ I.services (context 0 0) initial

publicResponse : Entry → Bool → Calls unitᴵ O.PublicAnswer
publicResponse n b = step (publicSystem n b) (init (publicSystem n b)) prepare >>=ᶜ λ sr → ret (proj₂ sr)

callerResponse : Entry → Bool → Calls unitᴵ I.ClientAnswer
callerResponse n b = step (I.system (context 0 0) initial) (init (I.system (context 0 0) initial))
  (I.build n b tt false) >>=ᶜ λ sr → ret (proj₂ sr)

recipientResponse : Entry → Bool → Calls unitᴵ (Maybe (Σ Entry Result))
recipientResponse n b = callerResponse n b >>=ᶜ λ answer → ret (O.recipientAnswer answer)

private-booleans-distinct : false ≢ true
private-booleans-distinct ()

silent-public-response-equal : publicResponse silent false ≡ publicResponse silent true
silent-public-response-equal = refl

echo-public-response-equal : publicResponse echo false ≡ publicResponse echo true
echo-public-response-equal = refl

recipient-false : recipientResponse echo false ≡ ret (just (echo , false))
recipient-false = refl
recipient-true : recipientResponse echo true ≡ ret (just (echo , true))
recipient-true = refl

public-result-policy-false : publicResponse publicEcho false ≡
  ret (O.prepared publicEcho false (I.makeStatement publicEcho false false false []) [])
public-result-policy-false = refl
public-result-policy-true : publicResponse publicEcho true ≡
  ret (O.prepared publicEcho true (I.makeStatement publicEcho true true false []) [])
public-result-policy-true = refl

publicTrace : O.PublicAnswer → Trace
publicTrace (O.prepared n r claim observed) = observed
publicTrace (O.failed e observed) = observed
publicTrace (O.provingFailed observed) = observed
publicTrace _ = []

publicationBit : Trace → Maybe Bool
publicationBit [] = nothing
publicationBit (publication 0 ∷ _) = just false
publicationBit (publication 1 ∷ _) = just true
publicationBit (_ ∷ rest) = publicationBit rest

queryBit : Trace → Maybe Bool
queryBit [] = nothing
queryBit (queried (flagMember b) _ ∷ _) = just b
queryBit (_ ∷ rest) = queryBit rest

readPublication : Entry → Bool → Calls unitᴵ (Maybe Bool)
readPublication n b = publicResponse n b >>=ᶜ λ answer → ret (publicationBit (publicTrace answer))
readQuery : Entry → Bool → Calls unitᴵ (Maybe Bool)
readQuery n b = publicResponse n b >>=ᶜ λ answer → ret (queryBit (publicTrace answer))

publication-false-visible : readPublication publishInput false ≡ ret (just false)
publication-false-visible = refl
publication-true-visible : readPublication publishInput true ≡ ret (just true)
publication-true-visible = refl
query-false-visible : readQuery queryInput false ≡ ret (just false)
query-false-visible = refl
query-true-visible : readQuery queryInput true ≡ ret (just true)
query-true-visible = refl

publication-leaks : publicResponse publishInput false ≢ publicResponse publishInput true
publication-leaks ()
query-leaks : publicResponse queryInput false ≢ publicResponse queryInput true
query-leaks ()

abort-projection : (b : Bool) → publicResponse abortAfter b ≡ ret
  (O.failed (assertionError assertionFailed)
    (publication (bit b) ∷ queried (flagMember b) (inj₂ true) ∷ []))
abort-projection false = refl
abort-projection true = refl

abort-publication-survives : (b : Bool) → readPublication abortAfter b ≡ ret (just b)
abort-publication-survives false = refl
abort-publication-survives true = refl
abort-query-survives : (b : Bool) → readQuery abortAfter b ≡ ret (just b)
abort-query-survives false = refl
abort-query-survives true = refl

admissionResponse : Entry → Bool → Calls unitᴵ O.PublicAnswer
admissionResponse n b = step P (init P) prepare >>=ᶜ λ
  { (st , answer) → step P st commit >>=ᶜ λ next → ret (proj₂ next) }
  where P = publicSystem n b

accepted-projection : admissionResponse silent false ≡ ret (O.admitted I.accepted)
accepted-projection = refl
rejected-projection : admissionResponse chainGate false ≡ ret (O.admitted I.rejected)
rejected-projection = refl
no-draft-after-failure : admissionResponse abortAfter true ≡ ret O.absentDraft
no-draft-after-failure = refl

wrongAccountSystem : Protocol unitᴵ (O.PublicAnswer ⇿ Action)
wrongAccountSystem = O.wrapper (request silent false) ∘ᵖ I.services (context 1 0) initial

wrong-account-rejected :
  (step wrongAccountSystem (init wrongAccountSystem) prepare >>=ᶜ λ sr →
    step wrongAccountSystem (proj₁ sr) commit >>=ᶜ λ tr → ret (proj₂ tr)) ≡ ret (O.admitted I.rejected)
wrong-account-rejected = refl

proofFailureServices : Protocol unitᴵ I.ServiceIf
proofFailureServices = record
  { St = ⊤ ; init = tt ; step = λ _ → λ
      { I.snapshotRequest → ret (tt , I.snapshotAnswer initial)
      ; (I.proofRequest tx) → ret (tt , I.proofAnswer false)
      ; (I.submitRequest tx) → ret (tt , I.submitAnswer I.rejected) } }

proof-failure-projection :
  (step (O.wrapper (request publishInput true) ∘ᵖ proofFailureServices) (nothing , tt) prepare >>=ᶜ λ sr →
    ret (proj₂ sr)) ≡ ret (O.provingFailed (publication 1 ∷ []))
proof-failure-projection = refl

occupiedResponse : Calls unitᴵ O.PublicAnswer
occupiedResponse = step P (init P) prepare >>=ᶜ λ sr →
  step P (proj₁ sr) prepare >>=ᶜ λ tr → ret (proj₂ tr)
  where P = publicSystem silent false

occupied-projection : occupiedResponse ≡ ret O.occupied
occupied-projection = refl

absent-projection : step (publicSystem silent false) (init (publicSystem silent false)) commit ≡
  ret ((nothing , initial , tt) , O.absentDraft)
absent-projection = refl

module BP = Programs BL.balanceLedger BL.Assertion
module BO = Balance.B.Observation (λ _ → ⊤) (λ _ _ → tt)

balanceResponse : ℕ → Calls unitᴵ BO.PublicAnswer
balanceResponse amount = step P (init P) tt >>=ᶜ λ sr → ret (proj₂ sr)
  where
  P = BO.wrapper (λ _ → Balance.B.build BL.alice amount tt 0) ∘ᵖ
    Balance.B.services Balance.ctx Balance.initial

operation-failure-projection : balanceResponse 11 ≡ ret
  (BO.failed (BP.operationError BL.insufficientFunds)
    (BP.queried (BL.transfer BL.alice 11) (inj₁ BL.insufficientFunds) ∷ []))
operation-failure-projection = refl

empty-assertion-projection : balanceResponse 0 ≡ ret (BO.failed (BP.assertionError BL.emptyTransfer) [])
empty-assertion-projection = refl

-- Runtime readers use the changed assembled wrapper, not theorem constants.
publicBooleanBoundary : Bool
publicBooleanBoundary = case deterministic (publicResponse silent false) of λ
  { (just (O.prepared silent tt claim [])) → case deterministic (publicResponse silent true) of λ
      { (just (O.prepared silent tt claim′ [])) → true ; _ → false }
  ; _ → false }

privateRecipientBoundary : Bool
privateRecipientBoundary = case deterministic (recipientResponse echo false) of λ
  { (just (just (echo , false))) → case deterministic (recipientResponse echo true) of λ
      { (just (just (echo , true))) → true ; _ → false }
  ; _ → false }

publicationBoundary : Bool
publicationBoundary = case deterministic (readPublication publishInput true) of λ
  { (just (just true)) → case deterministic (readPublication publishInput false) of λ
      { (just (just false)) → true ; _ → false }
  ; _ → false }

queryBoundary : Bool
queryBoundary = case deterministic (readQuery queryInput true) of λ
  { (just (just true)) → case deterministic (readQuery queryInput false) of λ
      { (just (just false)) → true ; _ → false }
  ; _ → false }

abortBoundary : Bool
abortBoundary = case deterministic (readPublication abortAfter true) of λ
  { (just (just true)) → case deterministic (readQuery abortAfter true) of λ
      { (just (just true)) → true ; _ → false }
  ; _ → false }

publicResultBoundary : Bool
publicResultBoundary = case deterministic (publicResponse publicEcho true) of λ
  { (just (O.prepared publicEcho true claim [])) → case deterministic (publicResponse publicEcho false) of λ
      { (just (O.prepared publicEcho false claim′ [])) → true ; _ → false }
  ; _ → false }

admissionBoundary : Bool
admissionBoundary = case deterministic (admissionResponse silent false) of λ
  { (just (O.admitted I.accepted)) → case deterministic (admissionResponse chainGate false) of λ
      { (just (O.admitted I.rejected)) → true ; _ → false }
  ; _ → false }

operationFailureBoundary : Bool
operationFailureBoundary = case deterministic (balanceResponse 11) of λ
  { (just (BO.failed (BP.operationError BL.insufficientFunds) _)) →
      case deterministic (balanceResponse 0) of λ
        { (just (BO.failed (BP.assertionError BL.emptyTransfer) [])) → true ; _ → false }
  ; _ → false }

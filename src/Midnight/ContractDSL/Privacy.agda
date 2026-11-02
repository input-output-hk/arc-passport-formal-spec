{-# OPTIONS --safe --without-K --guardedness #-}

module Midnight.ContractDSL.Privacy where

open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base hiding (_≤_; _<_)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; _/_; _≤_; _<_)
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

import Data.Nat.Properties as ℕP
import Data.Rational.Properties as ℚP
open import Data.Rational.Properties.Ext using (p≤p+q)
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Setoid
open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp.Advantage
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Agree
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy using (Strat; ask; out)
open import CategoricalCrypto.Machines.Run
import CategoricalCrypto.UC.Model.Setup as UC
open import CategoricalCrypto.UC.Model.Seal
open import Midnight.ContractDSL.MidnightLedger
open import Midnight.ContractDSL.Observation
open import Midnight.ContractDSL.Merkle
open import Midnight.ContractDSL.MerkleFixture as Fixture hiding (a; b; c; d)
open import Midnight.ContractDSL.Program midnight Assertion hiding (step; ledger)
open import Midnight.ContractDSL.ObservedExecution midnight Assertion
import Midnight.ContractDSL.Contract as Contracts
import Midnight.ContractDSL.Experiment as Experiments
import Midnight.ContractDSL.Experiment.Properties as ExperimentProperties

contract : Contracts.Contract midnight Assertion
contract = record
  { self = 0 ; EntryPoint = Variant
  ; Input = λ _ → FieldValue × Path × Bool ; Result = λ _ → ⊤
  ; body = λ _ v → λ { (i , p , mask) → executionProgram classify v i p mask } }

module I = Experiments.Runtime midnight Assertion contract (λ _ → ⊤) (λ _ _ → tt)
module IP = ExperimentProperties midnight Assertion contract (λ _ → ⊤) (λ _ _ → tt)
module O = I.PublicProjection (λ _ → ⊤) (λ _ _ → tt)
open I using (Verdict; accepted; rejected)

-- Membership inputs remain private in this experiment's projected claim;
-- certification still witnesses the complete core contract input.
record PrivateExecution : Set where
  constructor execution
  field variant : Variant
        item : FieldValue
        mask : Bool
        pathWitness : Path
        executionJournal : Journal
        successfulRun : eval (executionProgram classify variant item pathWitness mask) initial
          ≡ inj₂ (finished tt initial executionJournal)
open PrivateExecution

evaluatedJournal : Outcome ⊤ → Journal
evaluatedJournal (inj₁ err) = []
evaluatedJournal (inj₂ f) = Finished.journal f

makeExecution : (v : Variant) (i : Item) (m : Bool) → PrivateExecution
makeExecution v i m = execution v (fieldValue i) m (findItem i)
  (evaluatedJournal (eval (program v i m) initial))
  (trans success (cong (λ j → inj₂ (finished tt initial j))
    (sym (cong evaluatedJournal success))))
  where
  success : eval (program v i m) initial ≡ inj₂ (finished tt initial (programJournal v i m))
  success = fixture-successful v i m

data PrivateQuery : Set where
  proveAndHide verify : I.CertifiedDraft → PrivateQuery
  invalidVerify : PrivateQuery

data ResourceAnswer : Set where
  sealed : Bool → Bool → ResourceAnswer
  checked : Bool → ResourceAnswer

ResourceIf = ResourceAnswer ⇿ PrivateQuery

idealStep : PrivateQuery → Calls unitᴵ (⊤ × ResourceAnswer)
idealStep (proveAndHide tx) = coin uniform-Bool λ proofToken →
  ret (tt , sealed proofToken (I.Claim.artifact (I.publicClaim tx)))
idealStep (verify tx) = ret (tt , checked true)
idealStep invalidVerify = ret (tt , checked false)

idealZKAndHiding : Protocol unitᴵ ResourceIf
idealZKAndHiding = record { St = ⊤ ; init = tt ; step = λ _ → idealStep }

ideal-soundness : (e : PrivateExecution) →
  eval (executionProgram classify (variant e) (item e) (pathWitness e) (mask e)) initial
    ≡ inj₂ (finished tt initial (executionJournal e))
ideal-soundness = successfulRun

-- A local, joint-composable resource premise: every fresh activation samples
-- independent simulator tokens, and verification exposes only validity.
record PrivacyResources : Set₁ where
  field seal : PrivateQuery → Calls unitᴵ (⊤ × ResourceAnswer)
        seal-law : (q : PrivateQuery) → seal q ≡ idealStep q
open PrivacyResources

idealResources : PrivacyResources
idealResources = record { seal = idealStep ; seal-law = λ _ → refl }

resource : PrivacyResources → Protocol unitᴵ ResourceIf
resource r = record { St = ⊤ ; init = tt ; step = λ _ → seal r }

History : Set
History = Bool → PrivateExecution × PrivateExecution

history : Variant → Bool → History
history v world m = makeExecution v Fixture.a m , makeExecution v (second world) m

record PublicDraft : Set where
  constructor publicDraft
  field publicClaim : I.Claim
        proofInterface : Bool
        publicTrace : Trace
open PublicDraft

data SessionQuery : Set where
  beginSession prepareFirst submitFirst prepareSecond submitSecond : SessionQuery

data SessionAnswer : Set where
  ready : SessionAnswer
  draft : PublicDraft → SessionAnswer
  outcome : Verdict → ⊤ → SessionAnswer
  refused : SessionAnswer
  diagnostic : O.PublicAnswer → SessionAnswer

SessionIf = SessionAnswer ⇿ SessionQuery

data Phase : Set where
  firstUnprepared firstPrepared secondUnprepared secondPrepared finishedSession : Phase

data Session : Set where
  unopened : Session
  active : Bool → Phase → Session

-- The simulator token is an experiment resource; the bridge delegates replay
-- and admission to the certified core contract.
backend : Protocol ResourceIf I.ProofIf
backend = record
  { St = Bool ; init = false ; step = λ token → λ
      { (I.certifyRequest tx) → call (proveAndHide tx) λ
          { (sealed p c) → ret (p , true) ; _ → dead }
      ; (I.verifyRequest tx) → call (verify tx) λ
          { (checked ok) → ret (token , ok) ; _ → dead }
      ; I.invalidVerifyRequest → call invalidVerify λ
          { (checked ok) → ret (token , ok) ; _ → dead } } }

core : Protocol ResourceIf I.ClientIf
core = I.client ∘ᵖ (I.bridge 0 initial ∘ᵖ backend)

ClientState : Set
ClientState = Session × St core

sessionAnswer : Bool → O.PublicAnswer → SessionAnswer
sessionAnswer token (O.prepared n r statement observed) = draft (publicDraft statement token observed)
sessionAnswer token (O.admitted v) = outcome v tt
sessionAnswer token answer = diagnostic answer

respond : Bool → Phase → St core × I.ClientAnswer → Calls ResourceIf (ClientState × SessionAnswer)
respond m next (st′ , answer) = ret ((active m next , st′) ,
  sessionAnswer (proj₂ (proj₂ st′)) (O.publicAnswer answer))

prepareExecution : PrivateExecution → Bool → Phase → St core → Calls ResourceIf (ClientState × SessionAnswer)
prepareExecution e m next st = coin uniform-Bool λ c →
  step core st (I.prepareDraft (variant e) (item e , pathWitness e , mask e) c) >>=ᶜ respond m next

prepareCall : History → Bool → Bool → Phase → St core → Calls ResourceIf (ClientState × SessionAnswer)
prepareCall H m which = prepareExecution (if which then proj₂ (H m) else proj₁ (H m)) m

submitCall : Bool → Phase → St core → Calls ResourceIf (ClientState × SessionAnswer)
submitCall m next st = step core st I.submitDraft >>=ᶜ respond m next

client : History → Protocol ResourceIf SessionIf
client H = record { St = ClientState ; init = unopened , init core ; step = clientStep }
  where
  clientStep : ClientState → SessionQuery → Calls ResourceIf (ClientState × SessionAnswer)
  clientStep (session , st) beginSession = coin uniform-Bool λ m → ret ((active m firstUnprepared , st) , ready)
  clientStep (active m firstUnprepared , st) prepareFirst = prepareCall H m false firstPrepared st
  clientStep (active m firstPrepared , st) submitFirst = submitCall m secondUnprepared st
  clientStep (active m secondUnprepared , st) prepareSecond = prepareCall H m true secondPrepared st
  clientStep (active m secondPrepared , st) submitSecond = submitCall m finishedSession st
  clientStep st q = ret (st , refused)

assembled : PrivacyResources → History → Protocol unitᴵ SessionIf
assembled r H = client H ∘ᵖ resource r

record View : Set where
  constructor view
  field firstDraft : PublicDraft
        firstOutcome : Verdict
        firstResult : ⊤
        secondDraft : PublicDraft
        secondOutcome : Verdict
        secondResult : ⊤
open View

observer : (View → Bool) → Strat SessionQuery SessionAnswer
observer D = ask beginSession λ
  { ready → ask prepareFirst λ
      { (draft p) → ask submitFirst λ
          { (outcome v x) → ask prepareSecond λ
              { (draft q) → ask submitSecond λ
                  { (outcome w y) → out (D (view p v x q w y))
                  ; _ → out false }
              ; _ → out false }
          ; _ → out false }
      ; _ → out false }
  ; _ → out false }

HistoryPrivacy : PrivacyResources → History → History → Set
HistoryPrivacy r H K = (d : Strat SessionQuery SessionAnswer) →
  UC.S._≈_ (runᴹ (morphism (assembled r H)) d) (runᴹ (morphism (assembled r K)) d)

ExecutionAgreement : PrivateExecution → PrivateExecution → Set
ExecutionAgreement e f = variant e ≡ variant f ×
  executionProgram classify (variant e) (item e) (pathWitness e) (mask e) ≡
    executionProgram classify (variant f) (item f) (pathWitness f) (mask f)

ProgramHistoryPrivacy : History → History → Set
ProgramHistoryPrivacy H K = (m : Bool) →
  ExecutionAgreement (proj₁ (H m)) (proj₁ (K m)) × ExecutionAgreement (proj₂ (H m)) (proj₂ (K m))

data DraftRelated : I.Draft → I.Draft → Set where
  empty : DraftRelated nothing nothing
  pending : {tx ty : I.CertifiedDraft} → I.publicClaim tx ≡ I.publicClaim ty →
    DraftRelated (just tx) (just ty)

data StateRelated : St (assembled idealResources (history secure false)) →
  St (assembled idealResources (history secure true)) → Set where
  related : ∀ session s p {d e} → DraftRelated d e →
    StateRelated ((session , d , s , p) , tt) ((session , e , s , p) , tt)

module Coupling (r : PrivacyResources) (H K : History) where
  module R = Relational (assembled r H) (assembled r K) StateRelated

  prepare-coupled : (e f : PrivateExecution) → ExecutionAgreement e f →
    ∀ m next s p →
    Coupled R.Answers
      (graft (client H) (resource r) (prepareExecution e m next (nothing , s , p)) tt)
      (graft (client K) (resource r) (prepareExecution f m next (nothing , s , p)) tt)
  prepare-coupled e f eq m next s p = flipped λ c →
    reports c _ _ (cong (λ program → execute program s) (proj₂ eq))
      (execute-correct (executionProgram classify (variant e) (item e) (pathWitness e) (mask e)) s)
      (execute-correct (executionProgram classify (variant f) (item f) (pathWitness f) (mask f)) s)
    where
    evaluatedPreparation : (e : PrivateExecution) (c : Bool) (run : ExecutionReport ⊤) →
      eval (executionProgram classify (variant e) (item e) (pathWitness e) (mask e)) s ≡ evaluation run →
      Calls ResourceIf (ClientState × SessionAnswer)
    evaluatedPreparation e c run ev =
      graft I.client (I.bridge 0 initial ∘ᵖ backend)
        (I.afterEvaluation (variant e) (item e , pathWitness e , mask e) c s (trace run) (evaluation run) ev)
        (s , p) >>=ᶜ respond m next

    reports : (c : Bool) (run run′ : ExecutionReport ⊤) → run ≡ run′ →
      (ev : eval (executionProgram classify (variant e) (item e) (pathWitness e) (mask e)) s ≡ evaluation run) →
      (ev′ : eval (executionProgram classify (variant f) (item f) (pathWitness f) (mask f)) s ≡ evaluation run′) →
      Coupled R.Answers
        (graft (client H) (resource r) (evaluatedPreparation e c run ev) tt)
        (graft (client K) (resource r) (evaluatedPreparation f c run′ ev′) tt)
    reports c (report observed (inj₁ err)) ._ refl ev ev′ =
      returned (related _ _ _ empty , refl)
    reports c (report observed (inj₂ (finished tt t j))) ._ refl ev ev′
      rewrite seal-law r (proveAndHide (I.makeCertifiedDraft (variant e) (item e , pathWitness e , mask e) c s tt t j ev))
            | seal-law r (proveAndHide (I.makeCertifiedDraft (variant f) (item f , pathWitness f , mask f) c s tt t j ev′)) =
      flipped λ proofToken → returned
        (related _ _ _ (pending (cong (λ n → I.claim 0 n tt c j) (proj₁ eq))) ,
          cong (λ claim → draft (publicDraft claim proofToken observed))
            (cong (λ n → I.claim 0 n tt c j) (proj₁ eq)))

  step-public : ProgramHistoryPrivacy H K →
    ∀ s t → StateRelated s t → ∀ q →
    Coupled R.Answers (step (assembled r H) s q) (step (assembled r K) t q)
  step-public h s t (related session ledger token rel) beginSession =
    flipped (λ _ → returned (related _ _ _ rel , refl))
  step-public h s t (related (active m firstUnprepared) ledger token empty) prepareFirst =
    prepare-coupled (proj₁ (H m)) (proj₁ (K m)) (proj₁ (h m)) m firstPrepared ledger token
  step-public h s t (related (active m secondUnprepared) ledger token empty) prepareSecond =
    prepare-coupled (proj₂ (H m)) (proj₂ (K m)) (proj₂ (h m)) m secondPrepared ledger token
  step-public h s t (related (active m firstUnprepared) ledger token rel@(pending eq)) prepareFirst =
    flipped λ _ → returned (related _ _ _ rel , refl)
  step-public h s t (related (active m secondUnprepared) ledger token rel@(pending eq)) prepareSecond =
    flipped λ _ → returned (related _ _ _ rel , refl)
  step-public h s t (related (active m firstPrepared) ledger token empty) submitFirst =
    returned (related _ _ _ empty , refl)
  step-public h s t (related (active m secondPrepared) ledger token empty) submitSecond =
    returned (related _ _ _ empty , refl)
  step-public h s t (related (active m firstPrepared) ledger token (pending {tx} {ty} eq)) submitFirst
    rewrite seal-law r (verify tx) | seal-law r (verify ty)
          | IP.admissionAfterVerification-public 0 ledger tx ty eq true
    with IP.admissionAfterVerification 0 ledger ty true
  ... | ledger′ , accepted = returned (related _ ledger′ _ empty , refl)
  ... | ledger′ , rejected = returned (related _ ledger′ _ empty , refl)
  step-public h s t (related (active m secondPrepared) ledger token (pending {tx} {ty} eq)) submitSecond
    rewrite seal-law r (verify tx) | seal-law r (verify ty)
          | IP.admissionAfterVerification-public 0 ledger tx ty eq true
    with IP.admissionAfterVerification 0 ledger ty true
  ... | ledger′ , accepted = returned (related _ ledger′ _ empty , refl)
  ... | ledger′ , rejected = returned (related _ ledger′ _ empty , refl)
  step-public h s t (related unopened ledger token rel) prepareFirst = returned (related _ _ _ rel , refl)
  step-public h s t (related unopened ledger token rel) submitFirst = returned (related _ _ _ rel , refl)
  step-public h s t (related unopened ledger token rel) prepareSecond = returned (related _ _ _ rel , refl)
  step-public h s t (related unopened ledger token rel) submitSecond = returned (related _ _ _ rel , refl)
  step-public h s t (related (active m firstUnprepared) ledger token rel) submitFirst = returned (related _ _ _ rel , refl)
  step-public h s t (related (active m firstUnprepared) ledger token rel) prepareSecond = returned (related _ _ _ rel , refl)
  step-public h s t (related (active m firstUnprepared) ledger token rel) submitSecond = returned (related _ _ _ rel , refl)
  step-public h s t (related (active m firstPrepared) ledger token rel) prepareFirst = returned (related _ _ _ rel , refl)
  step-public h s t (related (active m firstPrepared) ledger token rel) prepareSecond = returned (related _ _ _ rel , refl)
  step-public h s t (related (active m firstPrepared) ledger token rel) submitSecond = returned (related _ _ _ rel , refl)
  step-public h s t (related (active m secondUnprepared) ledger token rel) prepareFirst = returned (related _ _ _ rel , refl)
  step-public h s t (related (active m secondUnprepared) ledger token rel) submitFirst = returned (related _ _ _ rel , refl)
  step-public h s t (related (active m secondUnprepared) ledger token rel) submitSecond = returned (related _ _ _ rel , refl)
  step-public h s t (related (active m secondPrepared) ledger token rel) prepareFirst = returned (related _ _ _ rel , refl)
  step-public h s t (related (active m secondPrepared) ledger token rel) submitFirst = returned (related _ _ _ rel , refl)
  step-public h s t (related (active m secondPrepared) ledger token rel) prepareSecond = returned (related _ _ _ rel , refl)
  step-public h s t (related (active m finishedSession) ledger token rel) prepareFirst = returned (related _ _ _ rel , refl)
  step-public h s t (related (active m finishedSession) ledger token rel) submitFirst = returned (related _ _ _ rel , refl)
  step-public h s t (related (active m finishedSession) ledger token rel) prepareSecond = returned (related _ _ _ rel , refl)
  step-public h s t (related (active m finishedSession) ledger token rel) submitSecond = returned (related _ _ _ rel , refl)

run-public : (r : PrivacyResources) (H K : History) → ProgramHistoryPrivacy H K →
  (d : Strat SessionQuery SessionAnswer) →
  runFrom (assembled r H) (init (assembled r H)) d ≈Mℚ
    runFrom (assembled r K) (init (assembled r K)) d
run-public r H K h d = Coupling.R.observations r H K (Coupling.step-public r H K h)
  _ _ (related unopened initial false empty) d

-- A concrete settling-budget derivation is large; retain its existential
-- witness behind opacity instead of normalising the compiled machine in users.
opaque
  history-observation-settles : (r : PrivacyResources) (H : History) (b : Bool)
    (d : Strat SessionQuery SessionAnswer) (value : ℚ) →
    Prᵇ (assembled r H) b d ≡ value →
    Σ ℕ (λ n → (m : ℕ) →
      Pr≤[ b ] (n + m) (runᴹ (morphism (assembled r H)) d) ≡ value)
  history-observation-settles r H b d value eq = change-value (prAgree b (assembled r H) d)
    where
    change-value : Σ ℕ (λ n → (m : ℕ) →
      Pr≤[ b ] (n + m) (runᴹ (morphism (assembled r H)) d) ≡ Prᵇ (assembled r H) b d) →
      Σ ℕ (λ n → (m : ℕ) →
        Pr≤[ b ] (n + m) (runᴹ (morphism (assembled r H)) d) ≡ value)
    change-value (n , hp) = n , λ m → trans (hp m) eq

  history-observation-upper : (r : PrivacyResources) (H : History)
    (d : Strat SessionQuery SessionAnswer) (value : ℚ) →
    Pr (assembled r H) d ℚ.≤ value → Upper (runᴹ (morphism (assembled r H)) d) value
  history-observation-upper r H d value = upper-run (assembled r H) d

-- This is exactly the existing UCSetup readout equivalence, obtained by
-- relating its finite machine approximants to upstream Protocol observations.
lift-privacy : (r : PrivacyResources) (H K : History) → ProgramHistoryPrivacy H K → HistoryPrivacy r H K
lift-privacy r H K h d ε positive = direction H K h , direction K H (λ m →
  (sym (proj₁ (proj₁ (h m))) , sym (proj₂ (proj₁ (h m)))) ,
  (sym (proj₁ (proj₂ (h m))) , sym (proj₂ (proj₂ (h m)))))
  where
  direction : (H K : History) → ProgramHistoryPrivacy H K →
    runᴹ (morphism (assembled r H)) d ≼ₚ[ ε ] runᴹ (morphism (assembled r K)) d
  direction H K h b k =
    let n , hp = prAgree b (assembled r H) d
        m , hq = prAgree b (assembled r K) d
        eq = run-public r H K h d (maybeℚ (indᵇ b))
    in m + 0 , ℚP.≤-trans
      (ℚP.≤-trans (Pr≤-mono b (runᴹ (morphism (assembled r H)) d) (ℕP.m≤n+m k n))
        (ℚP.≤-reflexive (trans (hp k) (trans eq (sym (hq 0))))))
      (p≤p+q (Pr≤[ b ] (m + 0) (runᴹ (morphism (assembled r K)) d)) (ℚP.<⇒≤ positive))

secure-program-history : ProgramHistoryPrivacy (history secure false) (history secure true)
secure-program-history m = (refl , refl) , (refl , refl)

secure-history-private : HistoryPrivacy idealResources (history secure false) (history secure true)
secure-history-private = lift-privacy idealResources _ _ secure-program-history

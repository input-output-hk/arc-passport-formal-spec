{-# OPTIONS --safe --without-K #-}

open import Midnight.ContractDSL.Ledger
import Midnight.ContractDSL.Contract as Core

module Midnight.ContractDSL.Experiment.Properties
  (L : Semantics) (Assertion : Set) (C : Core.Contract L Assertion)
  (PublicInput : Core.Contract.EntryPoint C → Set)
  (projectInput : ∀ n → Core.Contract.Input C n → PublicInput n) where

open import Data.Bool.Base
open import Data.Maybe hiding (_>>=_)
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Unit hiding (_≟_)
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import ProbabilisticLogic.Distribution.RationalDist
open import CategoricalCrypto.GamePlaying.Partial
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Observe
import CategoricalCrypto.Protocol.Reachability as Reach
open import Midnight.ContractDSL.Program L Assertion hiding (step)
open import Midnight.ContractDSL.ObservedExecution L Assertion
import Midnight.ContractDSL.Experiment L Assertion as Experiment
open Experiment.Runtime C PublicInput projectInput hiding (admitted)
open Semantics L

-- Proof-only description of the bridge's response to the simulator resource.
-- Runtime delivery itself always uses the native Protocol.toProtocol route.
admissionAfterVerification : ℕ → State → CertifiedDraft → Bool → State × Verdict
admissionAfterVerification now s p false = s , rejected
admissionAfterVerification now s p true = admit s (submit now (transaction p))

-- The successful native call and receipt projection reduce to this description.
native-admission : ∀ now initial s p →
  (Experiment.closedCalls {A = ProofIf} (step (Main.toProtocol initial) s (submit now (transaction p))) >>=ᶜ λ
    { (t , response) → ret (t , submissionAnswer (Main.Receipt.verdict response)) }) ≡
  (let t , v = admissionAfterVerification now s p true in ret (t , submissionAnswer v))
native-admission now initial s p with admit s (submit now (transaction p))
... | t , accepted = refl
... | t , rejected = refl

-- Only target and journal enter main admission. Neither certificates nor
-- dependent inputs are compared, so proof irrelevance is not required.
admissionAfterVerification-public : (now : ℕ) (s : State) (p q : CertifiedDraft) →
  publicClaim p ≡ publicClaim q → (ok : Bool) →
  admissionAfterVerification now s p ok ≡ admissionAfterVerification now s q ok
admissionAfterVerification-public now s p q same false = refl
admissionAfterVerification-public now s p q same true =
  trans (projected (transaction p))
    (trans (cong₂ decide (cong Claim.target same) (cong Claim.journal same))
      (sym (projected (transaction q))))
  where
  decide : ℕ → Journal → State × Verdict
  decide target events with target ≟ self
  ... | no _ = s , rejected
  ... | yes _ with replay now events s
  ...   | nothing = s , rejected
  ...   | just t = t , accepted

  projected : (tx : Transaction) →
    admit s (submit now tx) ≡ decide (Transaction.target tx) (journal (Transaction.execution tx))
  projected tx with Transaction.target tx ≟ self
  ... | no _ = refl
  ... | yes _ with replay now (journal (Transaction.execution tx)) s
  ...   | nothing = refl
  ...   | just t = refl

appendAdmissions : ∀ {s u t} → Admissions s u → Admissions u t → Admissions s t
appendAdmissions done suffix = suffix
appendAdmissions (next q v admitted rest) suffix =
  next q v admitted (appendAdmissions rest suffix)

system-step-admissions : ∀ now initial (st : St (system now initial)) q {nextState response} →
  InSupport (just (nextState , response)) (kernel (system now initial) st q) →
  Admissions (ledgerState st) (ledgerState nextState)
system-step-admissions now initial (just p , s , tt) (prepareDraft n a token) supported
  with support-return supported
... | refl = done
system-step-admissions now initial (nothing , s , tt) (prepareDraft n a token) supported
  with execute (body self n a) s | execute-correct (body self n a) s
... | report observed (inj₁ err) | ev with support-return supported
... | refl = done
system-step-admissions now initial (nothing , s , tt) (prepareDraft n a token) supported
  | report observed (inj₂ (finished r t j)) | ev with support-return supported
... | refl = done
system-step-admissions now initial (nothing , s , tt) submitDraft supported
  with support-return supported
... | refl = done
system-step-admissions now initial (just p , s , tt) submitDraft supported
  with admit s (submit now (transaction p)) in admitted
... | t , v with support-return supported
... | refl = next (submit now (transaction p)) v admitted done
system-step-admissions now initial (nothing , s , tt) (sendEnvelope invalidEnvelope) supported
  with support-return supported
... | refl = done
system-step-admissions now initial (just p , s , tt) (sendEnvelope invalidEnvelope) supported
  with support-return supported
... | refl = done
system-step-admissions now initial (nothing , s , tt) (sendEnvelope (certifiedEnvelope p)) supported
  with admit s (submit now (transaction p)) in admitted
... | t , v with support-return supported
... | refl = next (submit now (transaction p)) v admitted done
system-step-admissions now initial (just draft , s , tt) (sendEnvelope (certifiedEnvelope p)) supported
  with admit s (submit now (transaction p)) in admitted
... | t , v with support-return supported
... | refl = next (submit now (transaction p)) v admitted done

system-admissions : ∀ now initial {st} → Reach.Reachable (system now initial) st →
  Admissions initial (ledgerState st)
system-admissions now initial Reach.start = done
system-admissions now initial (Reach.advance {s = s} {q = q} reached executed) =
  appendAdmissions (system-admissions now initial reached)
    (system-step-admissions now initial s q executed)

{-# OPTIONS --safe --without-K #-}

open import Midnight.ContractDSL.Ledger
open import Midnight.ContractDSL.Contract

module Midnight.ContractDSL.Protocol (L : Semantics) (Assertion : Set)
  (C : Contract L Assertion) where

open import Data.List
import Data.Maybe as Maybe
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.GamePlaying.Partial
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Observe
import CategoricalCrypto.Protocol.Reachability as Reach
open import ProbabilisticLogic.Distribution.RationalDist
open Semantics L
open Contract C
open Transaction
open import Midnight.ContractDSL.Program L Assertion hiding (step)
import Midnight.ContractDSL.AdmissionProperties L Assertion C as Admission

record Receipt : Set where
  constructor receipt
  field verdict      : Verdict
        publications : List ℕ
open Receipt public

ContractIf : Iface
ContractIf = Receipt ⇿ Submission

publishedValues : Journal → List ℕ
publishedValues [] = []
publishedValues (published n ∷ events) = n ∷ publishedValues events
publishedValues (_ ∷ events)           = publishedValues events

receiptFor : Transaction → Verdict → Receipt
receiptFor tx accepted = receipt accepted (publishedValues (journal (execution tx)))
receiptFor tx rejected = receipt rejected []

module _ (initial : State) where
  toProtocol : Protocol unitᴵ ContractIf
  toProtocol = record
    { St = State ; init = initial
    ; step = λ s q →
        let t , v = admit s q in ret (t , receiptFor (Submission.transaction q) v)
    }

  step-admission : ∀ s (q : Submission) {t response} →
    InSupport (Maybe.just (t , response)) (kernel toProtocol s q) →
    admit s q ≡ (t , verdict response)
  step-admission s q supported with admit s q
  ... | u , accepted with support-return supported
  ... | refl = refl
  step-admission s q supported | u , rejected with support-return supported
  ... | refl = refl

  reachable-admissions : ∀ {t} → Reach.Reachable toProtocol t → Admissions initial t
  reachable-admissions reached = extend reached done
    where
    extend : ∀ {s t} → Reach.Reachable toProtocol s → Admissions s t → Admissions initial t
    extend Reach.start suffix = suffix
    extend (Reach.advance {q = q} {response} reached executed) suffix =
      extend reached (next q (verdict response) (step-admission _ q executed) suffix)

  step-invariant : {I : State → Set} → Admission.Preserves I →
    ∀ s q → I s → AllLeaves (λ next → I (proj₁ next)) (step toProtocol s q)
  step-invariant preserves s q pre with admit s q in admitted
  ... | t , v = Admission.admit-preserves preserves q admitted pre

  kernel-invariant : {I : State → Set} → Admission.Preserves I → Preserved⊥ I (kernel toProtocol)
  kernel-invariant preserves s q pre =
    evalC-support (step toProtocol s q) (step-invariant preserves s q pre)

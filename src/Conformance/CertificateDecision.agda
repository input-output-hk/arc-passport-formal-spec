{-# OPTIONS --safe --without-K #-}

open import Conformance.Primitives
import Conformance.AccountLedger as AccountLedger

-- Decides whether an external candidate's journal is an actual circuit run.
-- Only a successful decision can construct a core certified transaction.
module Conformance.CertificateDecision (P : Primitives) (self : Primitives.Bytes32 P)
  (variant : AccountLedger.Finalisation P) where

import Data.List.Properties as List
open import Data.Maybe.Base using (just)
open import Data.Nat.Base
open import Data.Nat.Properties using (_≟_)
open import Data.Product.Base
open import Data.Sum.Base
import Data.Sum.Properties as ⊎P
open import Data.Unit.Base
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Conformance.AccountLedger P
open import Conformance.Custody P self
open import Conformance.Decidable
open import Passport.AccountRecovery P self

open import Midnight.ContractDSL.Program accountLedger Assertion

decCondition : DecidableEquality Condition
decCondition = via
  (λ { (timeAtLeast t) → inj₁ t ; (timeAtMost t) → inj₂ t })
  (λ { (inj₁ t) → just (timeAtLeast t) ; (inj₂ t) → just (timeAtMost t) })
  (λ { (timeAtLeast _) → refl ; (timeAtMost _) → refl })
  (⊎P.≡-dec _≟_ _≟_)

decEvent : DecidableEquality Event
decEvent = via
  (λ { (operated o x) → inj₁ (_ , o , x) ; (published v) → inj₂ (inj₁ v) ; (required c) → inj₂ (inj₂ c) })
  (λ { (inj₁ (_ , o , x)) → just (operated o x) ; (inj₂ (inj₁ v)) → just (published v) ; (inj₂ (inj₂ c)) → just (required c) })
  (λ { (operated _ _) → refl ; (published _) → refl ; (required _) → refl })
  (⊎P.≡-dec decOperated (⊎P.≡-dec _≟_ decCondition))

_≟ᴶ_ : DecidableEquality Journal
_≟ᴶ_ = List.≡-dec decEvent

decRun : (p : Program ⊤) (s : State) (j : Journal) → Dec (Σ State λ t → eval p s ≡ inj₂ (finished tt t j))
decRun p s j with eval p s
... | inj₁ _ = no λ { (_ , ()) }
... | inj₂ (finished _ t j′) = map′ (λ { refl → t , refl }) (λ { (_ , refl) → refl }) (j′ ≟ᴶ j)

decExecution : (n : Name) (a : Input n) (s : State) (j : Journal) →
  Dec (Σ State λ t → eval (circuit variant n a) s ≡ inj₂ (finished tt t j))
decExecution n a = decRun (circuit variant n a)

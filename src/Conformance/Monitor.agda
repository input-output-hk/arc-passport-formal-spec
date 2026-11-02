{-# OPTIONS --safe --without-K #-}

open import Conformance.Primitives
import Conformance.AccountLedger as AccountLedger

-- External validation boundary: a Candidate becomes a certified Transaction only
-- after its execution is checked. The logical account identity is a natural:
-- Context.account selects Contract.self; Candidate.transactionAccount is the target.
-- The Bytes32 module parameter self is the challenge domain, not that identity.
module Conformance.Monitor (P : Primitives) (self : Primitives.Bytes32 P)
  (variant : AccountLedger.Finalisation P) where

open import Data.Bool.Base
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base
open import Data.Product.Base
open import Data.String.Base using (String)
open import Data.String.Properties using (_==_)
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Conformance.AccountLedger P
import Conformance.CertificateDecision
open import Conformance.Custody P self
open import Conformance.Recovery P self
open import Passport.AccountRecovery P self hiding (module Chain)

open import Midnight.ContractDSL.Program accountLedger Assertion
import Midnight.ContractDSL.Contract accountLedger Assertion as DSL

module Certificate = Conformance.CertificateDecision P self variant

RawCall : Set
RawCall = Σ Name Input

-- Transport context supplies the logical account identity and chain time.
record Context : Set where
  constructor context
  field account : ℕ
        time : ℕ
open Context

data Observed : Set where
  -- Host Outcome: accepted/rejected/aborted (Haskell Accepted/Rejected/Aborted);
  -- wire tokens: ok/refused/fail. Distinct from the DSL evaluation Outcome.
  accepted rejected : Observed
  aborted : String → Observed

record Candidate : Set where
  constructor candidate
  -- The claimed target is checked against the receiving contract's self.
  field transactionAccount : ℕ
        buildState : State
        rawCall : RawCall
        claimedJournal : Journal
open Candidate

data Transition : Set where
  invocation : Context → RawCall → Observed → Transition
  admission : Context → Candidate → Observed → Transition

module Instance (recipient : ℕ) where
  -- Monitor instance: selected finalisation variant and receiving logical account identity.
  module Chain = DSL.Contract (record (assemble variant) { self = recipient })

  -- No admission state is used to reconstruct the claimed effects. Failure is
  -- external validation rejection; the core has no invalid Transaction value.
  validate : Candidate → Maybe Chain.Transaction
  validate (candidate acc s (n , a) j) with Certificate.decExecution n a s j
  ... | no _ = nothing
  ... | yes (t , proof) = just record
    { target = acc ; entry = n ; input = a ; view = s
    ; execution = finished tt t j ; certified = proof }

  matches : State × Chain.Verdict → State → Observed → Bool
  matches (u , Chain.accepted) t accepted = t ≈ᵇ u
  matches (u , Chain.rejected) t rejected = t ≈ᵇ u
  matches _ _ _ = false

  checkAdmission : ℕ → State → Candidate → Observed → State → Bool
  checkAdmission now s c observed t with validate c
  ... | nothing = matches (s , Chain.rejected) t observed
  ... | just tx = matches (Chain.admit s (Chain.submit now tx)) t observed

  checkInvocation : ℕ → State → RawCall → Observed → State → Bool
  checkInvocation now s (n , a) observed t with Chain.build n a s
  ... | inj₁ err with observed
  ...   | aborted code = (code == errorCode err) ∧ (t ≈ᵇ s)
  ...   | _ = false
  checkInvocation now s (n , a) observed t | inj₂ tx =
    matches (Chain.admit s (Chain.submit now tx)) t observed

prepareCandidate : ℕ → State → RawCall → Error ⊎ Candidate
prepareCandidate acc s (n , a) with eval (circuit variant n a) s
... | inj₁ err = inj₁ err
... | inj₂ (finished _ _ j) = inj₂ (candidate acc s (n , a) j)


-- True confirms the observed outcome AND final state, including an accurately
-- observed rejection or abort; it does not mean the transaction was accepted.
acceptable : State → Transition → State → Bool
acceptable s (admission (context acc now) c observed) t =
  Instance.checkAdmission acc now s c observed t
acceptable s (invocation (context acc now) call observed) t =
  Instance.checkInvocation acc now s call observed t

record Observation : Set where
  constructor observation
  field initialState : State
        transition : Transition
        finalState : State

check : Observation → Bool
check (observation s tr t) = acceptable s tr t

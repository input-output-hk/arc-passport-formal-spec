{-# OPTIONS --safe #-}

open import Relation.Binary.Definitions using (DecidableEquality)

-- Local conclusions are proved for every genesis ledger and every qualified
-- key. No accounting or query-serving hypothesis is supplied by a caller.
module Passport.AccountCustodyProperties
  (Account Asset TxId : Set)
  (_≟Account_ : DecidableEquality Account)
  (_≟Asset_ : DecidableEquality Asset)
  (_≟Id_ : DecidableEquality TxId) where

open import Data.Integer.Base using (+_; _+_)
open import Data.Maybe.Base using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary.Decidable using (Dec)
open import Relation.Nullary.Negation using (¬_)

open import CategoricalCrypto.Channel.Core using (Channel)
open import CategoricalCrypto.Machine.Core using (Trace)
open import CategoricalCrypto.Machine.Relay using (AnswersOnly; CanAnswer)
open import CategoricalCrypto.Machine.Valuation using (flow)
open import Midnight.Passport.BalanceAccounting using (module BalanceAccounting)
import Passport.AccountCustody
import Passport.AccountCustodyProof

module C = Passport.AccountCustody Account Asset TxId _≟Account_ _≟Asset_ _≟Id_
module Proof = Passport.AccountCustodyProof Account Asset TxId _≟Account_ _≟Asset_ _≟Id_
open C hiding (module Execution)

private
  variable
    s s′ s₀ : State
    t : Transaction
    k : Key

module Execution
  (Authorized : State → Transaction → Set)
  (authorized? : ∀ s t → Dec (Authorized s t)) where

  module E = C.Execution Authorized authorized?
  module P = Proof.Execution Authorized authorized?
  open E hiding (module MachineInterface)
  open E.Finalize

  receive-adopted : finalize s t ≡ Ledger.accepted (apply s t) →
    receive s (adopted t) ≡ just (apply s t)
  receive-adopted = P.receive-adopted

  receive-rejected : finalize s t ≡ Ledger.rejected s → receive s (rejected t) ≡ just s
  receive-rejected = P.receive-rejected

  invalid-adoption-refused : ¬ Valid s t → receive s (adopted t) ≡ nothing
  invalid-adoption-refused = P.invalid-adoption-refused

  valid-rejection-refused : Valid s t → receive s (rejected t) ≡ nothing
  valid-rejection-refused = P.valid-rejection-refused

  module MachineInterface (TBD : Channel) (SignRequest Signature LedgerWrite : Set) where
    module M = E.MachineInterface TBD SignRequest Signature LedgerWrite
    module Pᴹ = P.MachineInterface TBD SignRequest Signature LedgerWrite
    open M

    module Local (k : Key) (s₀ : State) =
      BalanceAccounting accountCustody (acPort k) (txValue k) s₀ (report s₀ k)

    trace-accounting : (k : Key) (run : Trace accountCustody s₀ s) →
      + report s k ≡ + report s₀ k + flow (txValue k) run
    trace-accounting = Pᴹ.trace-accounting

    sound : ∀ k s₀ → Local.Sound k s₀
    sound = Pᴹ.sound

    promptlyAccurate : ∀ k s₀ → Local.PromptlyAccurate k s₀
    promptlyAccurate = Pᴹ.promptlyAccurate

    query-preserves-state : ∀ {o} → Step s (queryInput k) o s′ → s′ ≡ s
    query-preserves-state = Pᴹ.query-preserves-state

    answer-exact : ∀ {n} → Step s (queryInput k) (just (answerOutput k n)) s′ →
      n ≡ report s k
    answer-exact = Pᴹ.answer-exact

    answersOnly : ∀ k → AnswersOnly (acPort k)
    answersOnly = Pᴹ.answersOnly

    canAnswer : ∀ k → CanAnswer (acPort k)
    canAnswer = Pᴹ.canAnswer

    receive-step : ∀ {e} → receive s e ≡ just s′ → Step s (chainInput e) nothing s′
    receive-step = Pᴹ.receive-step

    step-receive : ∀ {e} → Step s (chainInput e) nothing s′ → receive s e ≡ just s′
    step-receive = Pᴹ.step-receive

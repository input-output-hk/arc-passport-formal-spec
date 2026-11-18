{-# OPTIONS --safe #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Passport.AccountCustodyProof
  (Account Asset TxId : Set)
  (_≟Account_ : DecidableEquality Account)
  (_≟Asset_ : DecidableEquality Asset)
  (_≟Id_ : DecidableEquality TxId) where

open import Data.Empty using (⊥-elim)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; _+_; _⊖_)
import Data.Integer.Properties as ℤ
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ; z≤n)
import Data.Nat.Properties as ℕ
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; module ≡-Reasoning)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Relay using (Answers; AnswersOnly; CanAnswer)
open import CategoricalCrypto.Machine.Valuation using (flow)
open import Midnight.Passport.BalanceAccounting using (module BalanceAccounting)
import Passport.AccountCustody
import Passport.FinalizedLedgerProof

module C = Passport.AccountCustody Account Asset TxId _≟Account_ _≟Asset_ _≟Id_
module LP = Passport.FinalizedLedgerProof Account Asset TxId _≟Account_ _≟Asset_ _≟Id_
open C hiding (module Execution)

private
  variable
    s s′ s₀ : State
    t : Transaction
    k : Key

restore-difference : ∀ b b′ → + b + (b′ ⊖ b) ≡ + b′
restore-difference b b′ = begin
  + b + (b′ ⊖ b) ≡⟨ ℤ.distribʳ-⊖-+-pos b b′ b ⟩
  (b Data.Nat.Base.+ b′) ⊖ b ≡⟨ cong ((b Data.Nat.Base.+ b′) ⊖_) (sym (ℕ.+-identityʳ b)) ⟩
  (b Data.Nat.Base.+ b′) ⊖ (b Data.Nat.Base.+ 0) ≡⟨ ℤ.+-cancelˡ-⊖ b b′ 0 ⟩
  b′ ⊖ 0 ≡⟨ ℤ.⊖-≥ z≤n ⟩
  + b′ ∎
  where open ≡-Reasoning

module Execution
  (Authorized : State → Transaction → Set)
  (authorized? : ∀ s t → Dec (Authorized s t)) where

  module E = C.Execution Authorized authorized?
  module L = LP.Execution Authorized authorized?
  open E hiding (module MachineInterface)
  open E.Finalize

  receive-adopted : finalize s t ≡ Ledger.accepted (apply s t) →
    receive s (adopted t) ≡ just (apply s t)
  receive-adopted {s = s} {t = t} eq with decideValid s t
  ... | yes _ = refl
  ... | no _ with eq
  ...   | ()

  receive-rejected : finalize s t ≡ Ledger.rejected s →
    receive s (rejected t) ≡ just s
  receive-rejected {s = s} {t = t} eq with decideValid s t
  ... | no _ = refl
  ... | yes _ with eq
  ...   | ()

  invalid-adoption-refused : ¬ Valid s t → receive s (adopted t) ≡ nothing
  invalid-adoption-refused {s = s} {t = t} invalid with decideValid s t
  ... | no _ = refl
  ... | yes valid = ⊥-elim (invalid valid)

  valid-rejection-refused : Valid s t → receive s (rejected t) ≡ nothing
  valid-rejection-refused {s = s} {t = t} valid with decideValid s t
  ... | yes _ = refl
  ... | no invalid = ⊥-elim (invalid valid)

  module MachineInterface (TBD : Channel) (SignRequest Signature LedgerWrite : Set) where
    module M = E.MachineInterface TBD SignRequest Signature LedgerWrite
    open M

    module Local (k : Key) (s₀ : State) =
      BalanceAccounting accountCustody (acPort k) (txValue k) s₀ (report s₀ k)

    opaque
      unfolding _⊗₀_ destruct-⊗ ⊗-right-intro ⊗-sym

      step-accounting : ∀ {i o} → Step s i o s′ → ∀ k →
        + report s′ k ≡ + report s k + txValue k i o
      step-accounting {s = s} (adopt {t = t} accepted) (a , x) = trans
        (sym (restore-difference (balance s a x) (balance (apply s t) a x)))
        (cong (λ delta → (+ balance s a x) + delta) (L.accepted-signed-effect accepted a x))
      step-accounting {s = s} (reject _) k = sym (ℤ.+-identityʳ (+ report s k))
      step-accounting {s = s} query k = sym (ℤ.+-identityʳ (+ report s k))

      query-preserves-state : ∀ {o} → Step s (queryInput k) o s′ → s′ ≡ s
      query-preserves-state query = refl

      answer-exact : ∀ {n} → Step s (queryInput k) (just (answerOutput k n)) s′ →
        n ≡ report s k
      answer-exact query = refl

      answersOnly : ∀ k → AnswersOnly (acPort k)
      answersOnly k {s = s} query = report s k , refl

      receive-step : ∀ {e} → receive s e ≡ just s′ →
        Step s (chainInput e) nothing s′
      receive-step {s = s} {s′ = s′} {e = adopted t} eq with decideValid s t
      ... | yes valid with eq
      ...   | refl = adopt (L.valid-accepted valid)
      receive-step {s = s} {s′ = s′} {e = adopted t} eq | no _ with eq
      ...   | ()
      receive-step {s = s} {s′ = s′} {e = rejected t} eq with decideValid s t
      ... | no invalid with eq
      ...   | refl = reject (L.invalid-rejected invalid)
      receive-step {s = s} {s′ = s′} {e = rejected t} eq | yes _ with eq
      ...   | ()

      step-receive : ∀ {e} → Step s (chainInput e) nothing s′ → receive s e ≡ just s′
      step-receive (adopt accepted) = receive-adopted accepted
      step-receive (reject refusal) = receive-rejected refusal

    canAnswer : ∀ k → CanAnswer (acPort k)
    canAnswer k s _ = report s k , s , query

    trace-accounting : (k : Key) (run : Trace accountCustody s₀ s) →
      + report s k ≡ + report s₀ k + flow (txValue k) run
    trace-accounting {s₀ = s₀} k [] = sym (ℤ.+-identityʳ (+ report s₀ k))
    trace-accounting {s₀ = s₀} k (run ∷ʳ⟨ i , o , st ⟩) = trans
      (step-accounting st k)
      (trans (cong (_+ txValue k i o) (trace-accounting k run))
        (ℤ.+-assoc (+ report s₀ k) (flow (txValue k) run) (txValue k i o)))

    sound : ∀ k s₀ → Local.Sound k s₀
    sound k s₀ run (_ , answer) = ℤ.≤-reflexive
      (trans (cong +_ (answer-exact answer)) (trace-accounting k run))

    promptlyAccurate : ∀ k s₀ → Local.PromptlyAccurate k s₀
    promptlyAccurate k s₀ {s = s} run = report s k , trace-accounting k run , s , query

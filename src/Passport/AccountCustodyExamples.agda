{-# OPTIONS --safe #-}

module Passport.AccountCustodyExamples where

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (ℤ; +_; -[1+_])
open import Data.List.Base using (List; []; _∷_; map; replicate)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.String.Base using (String)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (⌊_⌋)

import CategoricalCrypto.Channel.Core as Ch
import CategoricalCrypto.Machine.Core as Machine
import Passport.AccountCustody as Custody
import Passport.FinalizedLedgerExamples as F

module C = Custody ℕ ℕ ℕ _≟_ _≟_ _≟_
module E = C.Execution F.Authorized F.authorized?
module M = E.MachineInterface Ch.I ⊥ ⊥ ⊥

paid : C.Ledger.State
paid = C.Ledger.apply F.initial F.payment

payment-received : E.receive F.initial (C.adopted F.payment) ≡ just paid
payment-received = refl

replay-received-as-rejection : E.receive paid (C.rejected F.payment) ≡ just paid
replay-received-as-rejection = refl

forged-replay-adoption-refused : E.receive paid (C.adopted F.payment) ≡ nothing
forged-replay-adoption-refused = refl

forged-rejection-refused : E.receive F.initial (C.rejected F.payment) ≡ nothing
forged-rejection-refused = refl

unauthorized-adoption-refused : E.receive F.initial (C.adopted F.unauthorized) ≡ nothing
unauthorized-adoption-refused = refl

unfunded-adoption-refused : E.receive F.initial (C.adopted F.repeated-debit) ≡ nothing
unfunded-adoption-refused = refl

qualified-balances :
  (C.report paid (0 , 0) ∷ C.report paid (1 , 0) ∷
   C.report paid (0 , 1) ∷ C.report paid (1 , 1) ∷ []) ≡ (5 ∷ 7 ∷ 7 ∷ 0 ∷ [])
qualified-balances = refl

payment-effects :
  (C.effect (0 , 0) (C.adopted F.payment) ∷ C.effect (1 , 0) (C.adopted F.payment) ∷
   C.effect (0 , 1) (C.adopted F.payment) ∷ C.effect (0 , 0) (C.rejected F.payment) ∷ [])
    ≡ (-[1+ 4 ] ∷ + 4 ∷ + 0 ∷ + 0 ∷ [])
payment-effects = refl

-- The actual machine trace includes adoption, a qualified query, and replay rejection.
payment-trace : Machine.Trace M.accountCustody F.initial paid
payment-trace = Machine.[] Machine.∷ʳ⟨ _ , _ , M.adopt refl ⟩

queried-and-replayed : Machine.Trace M.accountCustody F.initial paid
queried-and-replayed =
  (payment-trace Machine.∷ʳ⟨ M.queryInput (0 , 0) , just (M.answerOutput (0 , 0) 5) , M.query ⟩)
    Machine.∷ʳ⟨ M.chainInput (C.rejected F.payment) , nothing , M.reject refl ⟩

received : Maybe C.Ledger.State → Bool
received (just _) = true
received nothing = false

refused : Maybe C.Ledger.State → Bool
refused (just _) = false
refused nothing = true

observedBalance : Maybe C.Ledger.State → C.Key → ℕ → Bool
observedBalance nothing _ _ = false
observedBalance (just s) q expected = ⌊ C.report s q ≟ expected ⌋

smokeChecks : List (String × Bool)
smokeChecks =
  ("adopted transfer reports payer after fee" , observedBalance (E.receive F.initial (C.adopted F.payment)) (0 , 0) 5) ∷
  ("adopted transfer reports recipient" , observedBalance (E.receive F.initial (C.adopted F.payment)) (1 , 0) 7) ∷
  ("other asset remains separate" , observedBalance (E.receive F.initial (C.adopted F.payment)) (0 , 1) 7) ∷
  ("other account asset remains separate" , observedBalance (E.receive F.initial (C.adopted F.payment)) (1 , 1) 0) ∷
  ("replay rejection preserves queried balance" , observedBalance (E.receive paid (C.rejected F.payment)) (0 , 0) 5) ∷
  ("forged replay adoption refused" , refused (E.receive paid (C.adopted F.payment))) ∷
  ("false rejection of valid transfer refused" , refused (E.receive F.initial (C.rejected F.payment))) ∷
  ("unauthorized adoption refused" , refused (E.receive F.initial (C.adopted F.unauthorized))) ∷
  ("aggregate unfunded adoption refused" , refused (E.receive F.initial (C.adopted F.repeated-debit))) ∷
  ("honest unfunded rejection admitted" , received (E.receive F.initial (C.rejected F.repeated-debit))) ∷ []

smoke-checks-pass : map proj₂ smokeChecks ≡ replicate 10 true
smoke-checks-pass = refl

{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.Definitions using (DecidableEquality)

-- Abstract finalized outcomes only: this is not a claim about native Midnight
-- transaction atomicity or adoption of partial transactions. Authorization is a
-- supplied decidable policy over the complete prestate and transaction.
module Passport.FinalizedLedger
  (Account Asset TxId : Set)
  (_≟Account_ : DecidableEquality Account)
  (_≟Asset_ : DecidableEquality Asset)
  (_≟Id_ : DecidableEquality TxId) where

open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Membership.DecPropositional _≟Id_ using (_∈_; _∉_; _∈?_)
open import Data.List.Relation.Unary.All using (All; all?)
open import Data.Nat.Base using (ℕ; _+_; _∸_; _≤_)
open import Data.Nat.Properties using (_≤?_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

record Transfer : Set where
  constructor transfer
  field sender recipient : Account
        asset : Asset
        amount : ℕ
open Transfer public

record Fee : Set where
  constructor fee
  field payer : Account
        feeAsset : Asset
        feeAmount : ℕ
open Fee public

record Transaction : Set where
  constructor transaction
  field txId : TxId
        transfers : List Transfer
        feeCharge : Fee
open Transaction public

record State : Set where
  constructor state
  field balance : Account → Asset → ℕ
        fees : Asset → ℕ
        acceptedIds : List TxId
open State public

Key : Set
Key = Account × Asset

Posting : Set
Posting = Key × ℕ

_≟Key_ : DecidableEquality Key
(a , x) ≟Key (b , y) with a ≟Account b | x ≟Asset y
... | yes refl | yes refl = yes refl
... | no a≢b | _ = no (λ { refl → a≢b refl })
... | _ | no x≢y = no (λ { refl → x≢y refl })

total : List Posting → Key → ℕ
total [] q = 0
total ((k , n) ∷ ps) q with q ≟Key k
... | yes _ = n + total ps q
... | no _ = total ps q

charges : Transaction → List Posting
charges t = ((payer f , feeAsset f) , feeAmount f) ∷
  map (λ p → (sender p , asset p) , amount p) (transfers t)
  where f = feeCharge t

receipts : Transaction → List Posting
receipts t = map (λ p → (recipient p , asset p) , amount p) (transfers t)

debit credit : Transaction → Account → Asset → ℕ
debit t a x = total (charges t) (a , x)
credit t a x = total (receipts t) (a , x)

feeFor : Transaction → Asset → ℕ
feeFor t x with x ≟Asset feeAsset (feeCharge t)
... | yes _ = feeAmount (feeCharge t)
... | no _ = 0

-- Each occurrence is checked against the aggregate, not against its own amount.
-- Incoming credits never contribute to the prestate funding test.
Funded : State → Transaction → Set
Funded s t = All
  (λ p → total (charges t) (proj₁ p) ≤ balance s (proj₁ (proj₁ p)) (proj₂ (proj₁ p)))
  (charges t)

funded? : ∀ s t → Dec (Funded s t)
funded? s t = all?
  (λ p → total (charges t) (proj₁ p) ≤? balance s (proj₁ (proj₁ p)) (proj₂ (proj₁ p)))
  (charges t)

Fresh : State → Transaction → Set
Fresh s t = txId t ∉ acceptedIds s

-- Raw accounting update; only finalize guards this operation with validity.
apply : State → Transaction → State
apply s t = state
  (λ a x → (balance s a x ∸ debit t a x) + credit t a x)
  (λ x → fees s x + feeFor t x)
  (txId t ∷ acceptedIds s)

data Result : Set where
  accepted rejected : State → Result

resultState : Result → State
resultState (accepted s) = s
resultState (rejected s) = s

module Execution
  (Authorized : State → Transaction → Set)
  (authorized? : ∀ s t → Dec (Authorized s t)) where

  Valid : State → Transaction → Set
  Valid s t = Fresh s t × (Authorized s t × Funded s t)

  decideValid : ∀ s t → Dec (Valid s t)
  decideValid s t with txId t ∈? acceptedIds s
  ... | yes seen = no (λ v → proj₁ v seen)
  ... | no fresh with authorized? s t
  ...   | no denied = no (λ v → denied (proj₁ (proj₂ v)))
  ...   | yes authorized with funded? s t
  ...     | no unfunded = no (λ v → unfunded (proj₂ (proj₂ v)))
  ...     | yes funded = yes (fresh , authorized , funded)

  finalize : State → Transaction → Result
  finalize s t with decideValid s t
  ... | yes _ = accepted (apply s t)
  ... | no _ = rejected s

  -- Includes rejected attempts, whose IDs are not consumed.
  data Finalized : State → State → Set where
    done : ∀ {s} → Finalized s s
    step : ∀ {s s′} t → Finalized (resultState (finalize s t)) s′ → Finalized s s′

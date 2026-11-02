{-# OPTIONS --safe --without-K #-}

open import Midnight.ContractDSL.Ledger
open import Midnight.ContractDSL.Contract

module Midnight.ContractDSL.Protocol (L : Semantics) (Assertion : Set)
  (C : Contract L Assertion) where

open import Data.List
open import Data.Nat
open import Data.Product

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open Semantics L
open Contract C
open Transaction
open import Midnight.ContractDSL.Program L Assertion

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

toProtocol : State → Protocol unitᴵ ContractIf
toProtocol initial = record
  { St = State ; init = initial
  ; step = λ s q →
      let t , v = admit s q in ret (t , receiptFor (Submission.transaction q) v)
  }

{-# OPTIONS --safe --without-K #-}

-- Executing closed protocols on an injected coin stream: each `coin` node consumes the
-- next bit, ignoring its distribution. Exhausted bits and `dead` both yield nothing.
-- The deterministic special case is Midnight.ContractDSL.Helpers.Deterministic.
module Conformance.Coins where

open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Product.Base

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Strategy using (Strat; out; ask; coin)

private variable X : Set

readCoins : List Bool → Calls unitᴵ X → Maybe (X × List Bool)
readCoins bs (ret x) = just (x , bs)
readCoins bs (call q k) = ⊥-elim q
readCoins [] (coin μ k) = nothing
readCoins (b ∷ bs) (coin μ k) = readCoins bs (k b)
readCoins bs dead = nothing

-- One activation; returns the successor state, the answer and the unread bits.
stepCoins : {B : Iface} (P : Protocol unitᴵ B) → St P → List Bool → Neg B → Maybe ((St P × Pos B) × List Bool)
stepCoins P st bs q = readCoins bs (step P st q)

runCoins : {B : Iface} (P : Protocol unitᴵ B) → St P → List Bool → Strat (Neg B) (Pos B) → Maybe Bool
runCoins P st bs (out b) = just b
runCoins P st bs (ask q k) with stepCoins P st bs q
... | nothing = nothing
... | just ((next , answer) , rest) = runCoins P next rest (k answer)
runCoins P st [] (coin μ k) = nothing
runCoins P st (b ∷ bs) (coin μ k) = runCoins P st bs (k b)

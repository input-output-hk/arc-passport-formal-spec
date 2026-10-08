{-# OPTIONS --safe --without-K #-}

module Midnight.ContractDSL.Smoke where

open import Data.Bool.Base
open import Data.Empty
open import Data.Maybe.Base
open import Data.Product.Base
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Strategy using (Strat; out; ask; coin)
import Midnight.ContractDSL.Balance as Balance
open import Midnight.ContractDSL.Lock
import Midnight.ContractDSL.MerkleState as MerkleState

private variable X : Set

-- A deterministic reader of actual upstream call trees. Randomized trees and
-- divergence return nothing rather than inventing probabilities or coin values.
readDet : Calls unitᴵ X → Maybe X
readDet (ret x) = just x
readDet (call q k) = ⊥-elim q
readDet (coin μ k) = nothing
readDet dead = nothing

runDet : {B : Iface} (P : Protocol unitᴵ B) → St P → Strat (Neg B) (Pos B) → Maybe Bool
runDet P st (out b) = just b
runDet P st (ask q k) with readDet (step P st q)
... | nothing = nothing
... | just (next , answer) = runDet P next (k answer)
runDet P st (coin μ k) = nothing

validSmoke : Maybe Bool
validSmoke = runDet assembled (init assembled) validStrategy

wrongKeySmoke : Maybe Bool
wrongKeySmoke = runDet assembled (init assembled) wrongKeyStrategy

staleSmoke : Maybe Bool
staleSmoke = runDet assembled (init assembled) staleStrategy

valid-smoke : validSmoke ≡ just true
valid-smoke = refl

wrong-key-smoke : wrongKeySmoke ≡ just true
wrong-key-smoke = refl

stale-smoke : staleSmoke ≡ just true
stale-smoke = refl

balanceSmoke : Maybe Bool
balanceSmoke = runDet Balance.assembled (init Balance.assembled) Balance.successStrategy

balanceErrorSmoke : Maybe Bool
balanceErrorSmoke = runDet Balance.assembled (init Balance.assembled) Balance.errorStrategy

balanceFundsSmoke : Maybe Bool
balanceFundsSmoke = runDet Balance.assembled (init Balance.assembled) Balance.fundsStrategy

mutableRootSmoke : Maybe Bool
mutableRootSmoke = runDet MerkleState.assembled (init MerkleState.assembled) MerkleState.rootChangeStrategy

balance-smoke : balanceSmoke ≡ just true
balance-smoke = refl

balance-error-smoke : balanceErrorSmoke ≡ just true
balance-error-smoke = refl

balance-funds-smoke : balanceFundsSmoke ≡ just true
balance-funds-smoke = refl

mutable-root-smoke : mutableRootSmoke ≡ just true
mutable-root-smoke = refl

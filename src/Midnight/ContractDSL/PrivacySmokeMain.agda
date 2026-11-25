{-# OPTIONS --guardedness #-}

module Midnight.ContractDSL.PrivacySmokeMain where

open import Data.Bool.Base
open import Data.String.Base hiding (show)
open import Data.Rational.Show
open import IO
open import Midnight.ContractDSL.Merkle
open import Midnight.ContractDSL.PrivacySmoke

main : Main
main = run (putStrLn
  ("secure (a,b), two accepted calls: " ++ show (successfulProbability secure false) ++ "\n" ++
   "secure (a,c), two accepted calls: " ++ show (successfulProbability secure true) ++ "\n" ++
   "insecure (a,b), two accepted calls: " ++ show (successfulProbability insecure false) ++ "\n" ++
   "insecure (a,c), two accepted calls: " ++ show (successfulProbability insecure true) ++ "\n" ++
   "secure observer true mass (a,b) vs (a,c): " ++ show (attackProbability secure false) ++ " vs " ++ show (attackProbability secure true) ++ "\n" ++
   "insecure observer true mass (a,b) vs (a,c): " ++ show (attackProbability insecure false) ++ " vs " ++ show (attackProbability insecure true)))

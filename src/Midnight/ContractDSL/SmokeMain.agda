{-# OPTIONS --guardedness #-}

module Midnight.ContractDSL.SmokeMain where

open import Data.Bool.Base
open import Data.Maybe.Base
open import Data.String.Base
open import IO

open import Midnight.ContractDSL.Smoke

render : Maybe Bool → String
render nothing = "no deterministic completed run"
render (just true) = "true"
render (just false) = "false"

main : Main
main = run (putStrLn
  ("valid clear accepted (UNSET, round 1, value 99): " ++ render validSmoke ++ "\n" ++
   "wrong key fails and raw invalid submission rejects: " ++ render wrongKeySmoke ++ "\n" ++
   "clear/set interference then stale draft rejects (SET, round 1, value 100): " ++ render staleSmoke ++ "\n" ++
   "balance transfer and valid replay accepted (alice 4, bob 8; total 12): " ++ render balanceSmoke ++ "\n" ++
   "balance insufficientFunds operation error differs from emptyTransfer assertion: " ++ render balanceErrorSmoke ++ "\n" ++
   "balance repeated transfer rejects atomically when funds exhausted (alice 1, bob 11): " ++ render balanceFundsSmoke ++ "\n" ++
   "Merkle matching root accepts; root update rejects old draft; fresh path accepts: " ++ render mutableRootSmoke))

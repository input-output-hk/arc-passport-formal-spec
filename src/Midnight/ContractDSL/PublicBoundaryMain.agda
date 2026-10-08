{-# OPTIONS --guardedness #-}

module Midnight.ContractDSL.PublicBoundaryMain where

open import Data.Bool.Base
open import Data.String.Base
open import IO
open import Midnight.ContractDSL.PublicBoundary

render : Bool → String
render true = "true"
render false = "false"

main : Main
main = run (putStrLn
  ("private Boolean pure tt has equal public responses: " ++ render publicBooleanBoundary ++ "\n" ++
   "private recipient receives distinct Boolean results: " ++ render privateRecipientBoundary ++ "\n" ++
   "actual publication reveals supplied Boolean: " ++ render publicationBoundary ++ "\n" ++
   "actual ledger query argument reveals supplied Boolean: " ++ render queryBoundary ++ "\n" ++
   "publication/query trace survives assertion failure: " ++ render abortBoundary ++ "\n" ++
   "explicit public result policy preserves Boolean results: " ++ render publicResultBoundary ++ "\n" ++
   "generic admission accepts valid and rejects premature chain condition: " ++ render admissionBoundary ++ "\n" ++
   "public operation/assertion failures remain distinct: " ++ render operationFailureBoundary))

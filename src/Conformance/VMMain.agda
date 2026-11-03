{-# OPTIONS --guardedness #-}

-- Only native line transport lives outside safe Agda. VM parsing and execution
-- are Conformance.VMWire/VMConcrete, with no external opcode callback.
module Conformance.VMMain where

open import Codata.Musical.Notation using (♯_)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Unit.Polymorphic.Base using (⊤)
import IO
import IO.Primitive.Core as Primitive
import Conformance.VMWire as Wire

{-# FOREIGN GHC
import qualified System.IO as SIO
#-}

commandEOF : Primitive.IO Bool
commandEOF = Primitive.pure false
{-# COMPILE GHC commandEOF = SIO.isEOF #-}

commands : IO.IO ⊤
commands = IO.bind (♯ IO.lift commandEOF) λ where
  true → ♯ IO.pure _
  false → ♯ IO.bind (♯ IO.getLine) (λ line →
    ♯ IO.seq (♯ IO.putStrLn (Wire.respond line)) (♯ commands))

main : IO.Main
main = run (hSetBuffering stdout lineBuffering >> commands)
  where open IO

{-# OPTIONS --guardedness #-}

-- Native transport for FullAccountWire. All parsing and account evaluation stay
-- in safe modules; the primitive interpreter is the explicit external boundary.
module Conformance.FullAccountMain where

open import Codata.Musical.Notation using (♯_)
open import Data.Bool.Base using (Bool; true; false)
open import Data.String.Base using (String; _++_)
open import Data.Unit.Polymorphic.Base using (⊤)
import IO
import IO.Primitive.Core as Primitive
import Conformance.FullAccountWire as Wire

rpc : String → String
rpc query = query ++ ""
{-# NOINLINE rpc #-}

{-# FOREIGN GHC
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Control.Exception (evaluate)
import System.IO (stdout, hFlush)
import qualified System.IO as SIO
import System.IO.Unsafe (unsafePerformIO)

fullAccountRpc :: T.Text -> T.Text
fullAccountRpc query = unsafePerformIO $ do
  _ <- evaluate (T.length query)
  TIO.putStrLn (T.append (T.pack "? ") query)
  hFlush stdout
  TIO.getLine
{-# NOINLINE fullAccountRpc #-}
#-}
{-# COMPILE GHC rpc = fullAccountRpc #-}

commandEOF : Primitive.IO Bool
commandEOF = Primitive.pure false
{-# COMPILE GHC commandEOF = SIO.isEOF #-}

module Backend = Wire.Backend rpc

commands : IO.IO ⊤
commands = IO.bind (♯ IO.lift commandEOF) λ where
  true → ♯ IO.pure _
  false → ♯ IO.bind (♯ IO.getLine) (λ line →
    ♯ IO.seq (♯ IO.putStrLn (Backend.respond line)) (♯ commands))

main : IO.Main
main = run (hSetBuffering stdout lineBuffering >> commands)
  where open IO

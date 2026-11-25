{-# OPTIONS --guardedness #-}

-- Executable transport only. The pure library entry point is Wire.respond;
-- this adapter supplies the interactive shared-primitive backend.
module Conformance.Main where

open import Codata.Musical.Notation using (♯_)
open import Data.Bool.Base using (Bool; true; false)
open import Data.String.Base using (String; _++_)
open import Data.Unit.Polymorphic.Base using (⊤)
import IO
import IO.Primitive.Core as Primitive
import Conformance.Wire as Wire

-- Keep the argument live and resist identity inlining before COMPILE GHC replaces
-- this body; a constant or bare identity lets MAlonzo erase/bypass the RPC call.
rpc : String → String
rpc q = q ++ ""
{-# NOINLINE rpc #-}

{-# FOREIGN GHC
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Control.Exception (evaluate)
import System.IO (stdout, hFlush)
import qualified System.IO as SIO
import System.IO.Unsafe (unsafePerformIO)

conformanceRpc :: T.Text -> T.Text
conformanceRpc q = unsafePerformIO $ do
  _ <- evaluate (T.length q)
  TIO.putStrLn (T.append (T.pack "? ") q)
  hFlush stdout
  reply <- TIO.getLine
  let natural t = not (T.null t) && T.all (\c -> c >= '0' && c <= '9') t
      digest t = T.length t == 64 && T.all (\c -> (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f')) t
      valid = case T.words q of
        op : _ | op `elem` map T.pack ["mulg", "mul", "add"] ->
          case T.words reply of
            [x,y] -> natural x && natural y
            _ -> False
        op : _ | op == T.pack "entry" || T.isPrefixOf (T.pack "chal-") op -> digest reply
        _ -> False
  if valid then pure reply
    else ioError (userError "monitor backend returned malformed primitive response")
{-# NOINLINE conformanceRpc #-}
#-}
{-# COMPILE GHC rpc = conformanceRpc #-}

-- EOF is normal between commands, but not while answering a primitive request.
commandEOF : Primitive.IO Bool
commandEOF = Primitive.pure false
{-# COMPILE GHC commandEOF = SIO.isEOF #-}

commands : IO.IO ⊤
commands = IO.bind (♯ IO.lift commandEOF) λ where
  true → ♯ IO.pure _
  false → ♯ IO.bind (♯ IO.getLine) (λ line →
    ♯ IO.seq (♯ IO.putStrLn (Wire.respond rpc line)) (♯ commands))

main : IO.Main
main = run (hSetBuffering stdout lineBuffering >> commands)
  where open IO

{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Concurrent
import Control.Exception (throwIO)
import Control.Monad (forM_, unless)
import Data.IORef
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Passport.Monitor
import System.Environment (getArgs)
import System.IO
import System.Process

assert :: Bool -> String -> IO ()
assert yes message = unless yes (fail message)
right :: Show e => Either e a -> IO a
right = either (fail . show) pure
expect :: (Eq a, Show a) => IO (Either MonitorError a) -> a -> IO ()
expect action value = action >>= \actual -> assert (actual == Right value) ("expected " ++ show value ++ ", got " ++ show actual)
expectBackend :: IO (Either MonitorError a) -> IO ()
expectBackend action = action >>= \answer -> case answer of
  Left (BackendFailure _) -> pure ()
  _ -> fail "expected backend error (not false/internal error)"

main :: IO ()
main = do
  -- Minimal typed usage: an observed deposit needs no crypto callbacks.
  z <- right (bytes32 (T.replicate 64 "0"))
  one <- right (bytes32 (T.replicate 64 "1"))
  w <- right (bytes64 (T.replicate 128 "0"))
  let st = State
        { stateRound = 0, authNonce = 0, deviceEpoch = 0, deviceCount = 0
        , devices = [], balances = [(z,3)], encKey = z
        , recoveryPk = Point 0 1, phi = Nothing, phiLen = 0, session = z
        , wrap = w, pending = False, pendingEntry = z
        , pendingRecoveryPk = Point 0 1, pendingNotBefore = 0, vetoWindow = 0
        }
      post = st { stateRound = 1, balances = [(z,10)] }
      deposit = Deposit z 7
      ctx = Context 0 0
      obs = Observation Source z st (Invocation ctx deposit Accepted) post
      noCrypto = CryptoBackend (\request -> pure (Left ("unexpected crypto: " <> request)))
  result <- checkObservation noCrypto obs
  case result of
    Right True -> pure () -- Outcome and final state match; not merely acceptance.
    Right False -> fail "observed deposit disagrees with the model"
    Left err -> fail ("monitor could not check the observation: " ++ show err)

  -- Regression cases below: mismatches, codecs, backend errors, and admission.
  let signed = obs { transition = Invocation ctx (Authorised CancelRecovery (Authorisation (Point 1 2) 0 (Point 1 2) 1 0)) Accepted }
      backendFailure = CryptoBackend (\_ -> pure (Left "unavailable"))
  expect (checkObservation noCrypto obs { finalState = st }) False
  expect (checkObservation noCrypto obs { transition = Invocation ctx deposit Rejected }) False
  serialized <- right (encodeObservation obs)
  assert (decodeObservation serialized == Right obs) "typed observation roundtrip"
  expect (checkSerialized noCrypto serialized) True
  expect (normalizeSerialized ("  " <> serialized <> " \n")) serialized
  normalized <- normalizeObservation obs >>= right
  assert (normalized == obs) "Agda canonicalization matches typed codec"
  case decodeObservation (serialized <> " extra") of
    Left (Malformed _) -> pure ()
    _ -> fail "trailing tokens must be malformed"
  case bytes32 (T.replicate 64 "A") of
    Left (Malformed _) -> pure ()
    _ -> fail "uppercase hex must be malformed"
  case encodeState st { devices = [z,z] } of
    Left (Malformed _) -> pure ()
    _ -> fail "duplicate device keys must be malformed"
  case encodeState st { balances = [(z,1),(z,2)] } of
    Left (Malformed _) -> pure ()
    _ -> fail "duplicate balance keys must be malformed"
  let wide = st { stateRound = 2^(256 :: Int), deviceCount = 999 }
  wideText <- right (encodeState wide)
  assert (decodeState wideText == Right wide) "represented states have no artificial ABI-width restriction"
  expectBackend (checkObservation backendFailure signed)
  expectBackend (checkObservation (CryptoBackend (\_ -> pure (Right "malformed"))) signed)
  expectBackend (checkObservation (CryptoBackend (\_ -> throwIO (userError "IO failure"))) signed)
  expectBackend (checkObservation (CryptoBackend (\_ -> pure (Right (error "lazy backend failure")))) signed)
  -- Different operations can run concurrently without backend replacement or a
  -- process-global crypto channel. The failure does not contaminate the deposit.
  a <- newEmptyMVar; b <- newEmptyMVar
  _ <- forkIO (checkObservation backendFailure signed >>= putMVar a)
  _ <- forkIO (checkObservation noCrypto obs >>= putMVar b)
  expectBackend (takeMVar a)
  expect (takeMVar b) True
  candidate <- prepareCandidate noCrypto Source z 0 st deposit >>= right
  candidateText <- right (encodeCandidate candidate)
  assert (decodeCandidate candidateText == Right candidate) "candidate journal roundtrip"
  let admission before outcome after = Observation Source z before (Admission ctx candidate outcome) after
  expect (checkObservation noCrypto (admission st Accepted post)) True
  let unrelated = st { encKey = one }
  expect (checkObservation noCrypto (admission unrelated Accepted post { encKey = one })) True
  let staleRound = st { stateRound = 1 }
      staleBalance = st { balances = [(z,4)] }
  expect (checkObservation noCrypto (admission staleRound Rejected staleRound)) True
  expect (checkObservation noCrypto (admission staleRound Accepted post)) False
  expect (checkObservation noCrypto (admission staleBalance Rejected staleBalance)) True
  expect (checkObservation noCrypto (admission staleBalance Rejected st)) False
  let tampered = candidate { journal = [] }
      tamperedObs out after = Observation Source z st (Admission ctx tampered out) after
  expect (checkObservation noCrypto (tamperedObs Accepted post)) False
  expect (checkObservation noCrypto (tamperedObs Rejected st)) True
  noPending <- right (errorCode "noPending")
  expect (checkObservation noCrypto (admission st (Aborted noPending) st)) False
  expect (checkObservation noCrypto obs { transition = Invocation ctx FinaliseRecovery (Aborted noPending), finalState = st }) True
  built <- prepareCandidate noCrypto Source z 0 st FinaliseRecovery
  assert (built == Left (BuildAborted noPending)) "preparation preserves model build abort"
  -- Exercise the complete event and call codec, not merely forwarding strings.
  let counts = [ReadNonce,ReadRound,ReadEpoch,ReadDeviceCount,ReadVetoWindow,ReadNotBefore,ReadBalance z]
      flags = [ReadPending,DeviceMember z,BalanceMember z]
      points = [ReadRecoveryPk,ReadPendingRecoveryPk]
      byteOps = [ReadSession,ReadPendingEntry]
      writes = [WriteBalance z 4,InsertDevice z,RemoveDeviceEntry z,SetEncKey z,ResetDevices,
                WriteNonce 1,WriteRound 2,WriteEpoch 3,WriteDeviceCount 4,WriteNotBefore 5,WritePhiLen 4,
                WriteRecoveryPk (Point 1 2),WritePendingRecoveryPk (Point 3 4),WriteSession z,
                WritePendingEntry z,WritePending True,InsertPhi1 1,InsertPhi2 2,InsertPhi3 3,InsertPhi4 4,WriteWrap w]
      events = map (`CountEvent` 4) counts ++ map (`FlagEvent` True) flags ++
               map (`PointEvent` Point 1 2) points ++ map (`BytesEvent` z) byteOps ++
               map UnitEvent writes ++ [Published 5,Required (TimeAtLeast 3),Required (TimeAtMost 8)]
      withEvents = candidate { journal = events }
  encodedEvents <- right (encodeCandidate withEvents)
  assert (decodeCandidate encodedEvents == Right withEvents) "all journal forms roundtrip exactly"
  let gated = [Withdraw z 2 one,AddDevice z,RemoveDevice z,RotateEncKey z,
               PublishRecovery (Point 1 2) z (Phi 1 2 3 4) 4 w,CancelRecovery]
      calls = [deposit,FinaliseRecovery,SubmitRecovery (Point 1 2) (Point 3 4) 1 2 3 (Point 5 6) 7 (Point 8 9) 10 11] ++
              map (\g -> Authorised g (Authorisation (Point 1 2) 3 (Point 4 5) 6 7)) gated
  forM_ calls $ \call -> do
    text <- right (encodeCall call)
    assert (decodeCall text == Right call) "all raw calls roundtrip"
  args <- getArgs
  case args of
    [] -> pure ()
    "--real" : fixture : command : arguments -> realCrypto fixture command arguments
    _ -> fail "usage: haskell-smoke [--real OBSERVATION_FILE BACKEND_EXECUTABLE [ARG...]]"
  putStrLn "Haskell monitor smoke PASS (typed codecs, actual model, stale admission, errors, isolation)"

-- Optional integration mode owns its own crypto process and handles; the library
-- never imports executable Main or uses global stdin/stdout. The fixture must be
-- an accepted signed/recovery observation captured by the implementation harness.
realCrypto :: FilePath -> FilePath -> [String] -> IO ()
realCrypto fixture command arguments = do
  text <- TIO.readFile fixture
  observation <- right (decodeObservation text)
  case transition observation of
    Invocation _ (Authorised _ _) Accepted -> pure ()
    Invocation _ (SubmitRecovery _ _ _ _ _ _ _ _ _ _) Accepted -> pure ()
    _ -> fail "real fixture must be an accepted signed/recovery invocation"
  withCreateProcess (proc command arguments) { std_in = CreatePipe, std_out = CreatePipe, std_err = Inherit } $ \input output _ _ ->
    case (input,output) of
      (Just sink,Just source) -> do
        hSetBuffering sink LineBuffering
        lock <- newMVar ()
        calls <- newIORef (0 :: Int)
        let backend = CryptoBackend $ \request -> withMVar lock $ \_ -> do
              modifyIORef' calls (+1)
              TIO.hPutStrLn sink request
              reply <- TIO.hGetLine source
              pure $ maybe (Right reply) Left (T.stripPrefix "! " reply)
        expect (checkObservation backend observation) True
        let wrong = (finalState observation) { stateRound = stateRound (finalState observation) + 1 }
        expect (checkObservation backend observation { finalState = wrong }) False
        count <- readIORef calls
        assert (count > 0) "real signed fixture must exercise actual primitive callbacks"
      _ -> fail "failed to create explicit backend pipes"

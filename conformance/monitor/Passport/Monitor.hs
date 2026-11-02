{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-cse -fno-full-laziness #-}
-- | Handwritten, stable API; generated MAlonzo names remain private build glue.
module Passport.Monitor
  ( module Passport.Monitor.Types, module Passport.Monitor.Codec
  , CryptoBackend(..), checkObservation, checkSerialized, normalizeObservation
  , normalizeSerialized, prepareCandidate ) where

import Control.DeepSeq (force)
import Control.Exception
import Data.Data (Typeable)
import Data.Text (Text)
import qualified Data.Text as T
import Numeric.Natural (Natural)
import Passport.Monitor.Types
import Passport.Monitor.Codec
import System.IO.Unsafe (unsafePerformIO)
import qualified Passport.Monitor.Generated as Generated

-- | A deterministic trusted crypto implementation, captured per invocation.
-- Implement the actual entry/chal-*/mulg/mul/add primitives using the protocol in
-- @docs/conformance-recovery.md@, \"Runtime transition monitor\". Each request
-- must be referentially transparent: pure evaluation may share its result.
-- Failures are errors, never monitor false. No process-global backend is used.
-- All demanded callbacks and their replies are fully evaluated before the public
-- IO operation returns; backend resources need only remain live for that call.
newtype CryptoBackend = CryptoBackend
  { runCrypto :: Text -> IO (Either Text Text)
    -- ^ Answer one primitive request: @Right@ contains its protocol reply;
    -- @Left@ reports a backend failure, not a model discrepancy.
  }

data BackendException = BackendException MonitorError deriving (Show, Typeable)
instance Exception BackendException

-- The compiled Agda primitive record is pure. This is the sole deterministic IO
-- bridge: the backend is explicitly captured, never globally installed. NOINLINE
-- and the module optimizer safeguards prevent floating/merging callback actions.
-- Backends must be referentially transparent for each request: Agda/Haskell may
-- share a pure primitive result. Full forcing below keeps all callbacks inside
-- the public IO operation and, for C clients, inside the callback's lifetime.
primitiveReply :: CryptoBackend -> Text -> Text
primitiveReply backend request = unsafePerformIO $ do
  -- A request can depend on earlier crypto results. Resolve those before
  -- entering a backend that may hold a pipe lock or borrow callback buffers.
  _ <- evaluate (force request)
  attempted <- try (runCrypto backend request >>= evaluate . force)
  reply <- case attempted of
    Right value -> pure value
    Left (exception :: SomeException) -> case fromException exception :: Maybe SomeAsyncException of
      Just _ -> throwIO exception
      Nothing -> throwIO (BackendException (BackendFailure (T.pack (displayException exception))))
  case reply of
    Left message -> throwIO (BackendException (BackendFailure message))
    Right text -> either (throwIO . BackendException) (evaluate . force) (validateReply request text)
{-# NOINLINE primitiveReply #-}

respondIO :: CryptoBackend -> Text -> IO (Either MonitorError Text)
respondIO backend input = do
  evaluated <- try (evaluate (force (Generated.respond (primitiveReply backend) input)))
  case evaluated of
    Right text -> pure (Right text)
    Left (exception :: SomeException)
      | Just (BackendException err) <- fromException exception -> pure (Left err)
      | otherwise -> syncError InternalFailure exception

syncError :: (Text -> MonitorError) -> SomeException -> IO (Either MonitorError a)
syncError constructor exception = case fromException exception :: Maybe SomeAsyncException of
  Just _ -> throwIO exception
  Nothing -> pure (Left (constructor (T.pack (displayException exception))))

validateReply :: Text -> Text -> Either MonitorError Text
validateReply request reply = case T.words request of
  command : _
    | command `elem` ["mulg","mul","add"] -> case T.words reply of
        [x,y] | decimal x && decimal y -> Right (T.unwords [x,y])
        _ -> bad "expected exactly two nonnegative decimal point coordinates"
    | command `elem` ["entry","chal-w","chal-add","chal-rm","chal-rot","chal-pub","chal-cancel","chal-submit"] ->
        case bytes32 reply of
          Right _ -> Right reply
          Left _ -> bad "expected exactly one lowercase hex32 digest"
    | otherwise -> Left (InternalFailure ("unknown Agda primitive request: " <> request))
  [] -> Left (InternalFailure "empty Agda primitive request")
  where
    decimal t = not (T.null t) && T.all (\c -> c >= '0' && c <= '9') t
    bad message = Left (BackendFailure (message <> " for " <> request))

modelError :: Text -> MonitorError
modelError response = case T.stripPrefix "= error " response of
  Just message -> Malformed message
  Nothing -> InternalFailure ("unexpected Agda response: " <> response)

-- | Check the observed outcome and final state against the model. @Right True@
-- means they are consistent, including a correctly observed rejection or abort;
-- it does not mean the transaction was accepted. @Right False@ is a discrepancy.
-- @Left@ reports malformed input, backend failure, or an internal error.
checkObservation :: CryptoBackend -> Observation -> IO (Either MonitorError Bool)
checkObservation backend observation = case encodeObservation observation of
  Left err -> pure (Left err)
  Right text -> checkSerialized backend text

-- | Check a serialized @monitor-v1@ observation with the same verdict and error
-- meanings as 'checkObservation'. Agda validates the input directly; this path
-- never decodes and re-encodes observations in Haskell.
checkSerialized :: CryptoBackend -> Text -> IO (Either MonitorError Bool)
checkSerialized backend text = do
  reply <- respondIO backend ("check " <> text)
  pure $ reply >>= \response -> case response of
    "= true" -> Right True
    "= false" -> Right False
    _ -> Left (modelError response)

-- | Return the Agda-canonicalized observation in @Right@, without checking its
-- conformance or invoking crypto. @Left@ reports malformed input or an internal
-- error; successful normalization is not evidence that the observation matches.
normalizeObservation :: Observation -> IO (Either MonitorError Observation)
normalizeObservation observation = case encodeObservation observation of
  Left err -> pure (Left err)
  Right text -> do
    normalized <- normalizeSerialized text
    pure (normalized >>= decodeObservation)

-- | Return canonical @monitor-v1@ tokens in @Right@, or a malformed/internal
-- error in @Left@. Like 'normalizeObservation', this neither checks conformance
-- nor invokes crypto.
normalizeSerialized :: Text -> IO (Either MonitorError Text)
normalizeSerialized text = do
  reply <- respondIO (CryptoBackend (\_ -> pure (Left "normalization unexpectedly requested crypto"))) ("normalize " <> text)
  pure $ reply >>= \response -> case T.stripPrefix "= " response of
    Just canonical | "monitor-v1 " `T.isPrefixOf` canonical -> Right canonical
    _ -> Left (modelError response)

-- | Build model-side candidate evidence, not an implementation transcript.
-- Positional arguments after the backend are: source/corrected variant, crypto
-- domain ('self'), logical transaction account ('transactionAccount'), build
-- state, and raw call. @Right@ is the candidate; @Left (BuildAborted code)@
-- preserves a model build abort. Other @Left@ values report malformed input,
-- backend failure, or an internal error. Preparation does not check admission.
prepareCandidate :: CryptoBackend -> Variant -> Bytes32 -> Natural -> State -> Call -> IO (Either MonitorError Candidate)
prepareCandidate backend v s a st call = case preparationRequest v s a st call of
  Left err -> pure (Left err)
  Right request -> do
    reply <- respondIO backend request
    pure $ reply >>= \response -> case T.stripPrefix "= candidate " response of
      Just text -> decodeCandidate text
      Nothing -> case T.stripPrefix "= fail " response of
        Just code -> Left . BuildAborted =<< errorCode code
        Nothing -> Left (modelError response)

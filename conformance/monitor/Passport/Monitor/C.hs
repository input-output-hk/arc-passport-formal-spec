{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | C exports. The generated foreign-export stub is private; consumers include
-- passport_monitor.h and explicitly initialize the GHC RTS before calling.
module Passport.Monitor.C where

import Control.Exception
import qualified Data.ByteString as BS
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Word (Word8)
import Foreign
import Foreign.C
import Passport.Monitor

type Callback = Ptr () -> Ptr Word8 -> CSize -> Ptr (Ptr Word8) -> Ptr CSize -> IO CInt
foreign import ccall safe "dynamic" callBackend :: FunPtr Callback -> Callback

readText :: Ptr Word8 -> CSize -> IO (Either MonitorError Text)
readText pointer size
  | size > fromIntegral (maxBound :: Int) = pure (Left (Malformed "input length exceeds host address space"))
  | pointer == nullPtr && size /= 0 = pure (Left (Malformed "null input with nonzero length"))
  | size == 0 = pure (Right "")
  | otherwise = do
      bytes <- BS.packCStringLen (castPtr pointer, fromIntegral size)
      pure $ either (Left . Malformed . T.pack . show) Right (TE.decodeUtf8' bytes)

callbackBackend :: FunPtr Callback -> Ptr () -> CryptoBackend
callbackBackend callback userdata = CryptoBackend $ \request ->
  if callback == nullFunPtr then pure (Left "crypto backend is required for this operation")
  else BS.useAsCStringLen (TE.encodeUtf8 request) $ \(pointer,size) ->
    alloca $ \replyPointer -> alloca $ \replySize -> do
      poke replyPointer nullPtr
      poke replySize 0
      status <- callBackend callback userdata (castPtr pointer) (fromIntegral size) replyPointer replySize
      response <- peek replyPointer
      lengthBytes <- peek replySize
      copied <- readText response lengthBytes
      pure $ case copied of
        Left err -> Left ("invalid callback response: " <> T.pack (show err))
        Right text | status == 0 -> Right text
                   | otherwise -> Left (if T.null text then "crypto callback failed" else text)

statusOf :: MonitorError -> CInt
statusOf (Malformed _) = 2
statusOf (BackendFailure _) = 3
statusOf (InternalFailure _) = 4
statusOf (BuildAborted _) = 5
errorText :: MonitorError -> Text
errorText (Malformed t) = t
errorText (BackendFailure t) = t
errorText (InternalFailure t) = t
errorText (BuildAborted code) = errorCodeText code

-- Every output is allocated by this library and freed only by monitor_free.
-- No borrowed Haskell buffer escapes; this also covers error messages.
storeText :: Ptr (Ptr Word8) -> Ptr CSize -> Text -> IO ()
storeText output outputSize text = BS.useAsCStringLen (TE.encodeUtf8 text) $ \(source,size) -> do
  destination <- mallocBytes (size + 1)
  copyBytes destination (castPtr source) size
  pokeByteOff destination size (0 :: Word8)
  poke output destination
  poke outputSize (fromIntegral size)

boundary :: Ptr (Ptr Word8) -> Ptr CSize -> IO (Either MonitorError (CInt, Maybe Text)) -> IO CInt
boundary output outputSize action
  | output == nullPtr || outputSize == nullPtr = pure 2
  | otherwise = mask $ \restore -> do
      poke output nullPtr
      poke outputSize 0
      result <- try (restore action)
      let answer = case result of
            Left (exception :: SomeException) -> Left (InternalFailure (T.pack (displayException exception)))
            Right value -> value
      -- Catch allocation/encoding failures too: no Haskell exception crosses C.
      stored <- try $ case answer of
        Left err -> storeText output outputSize (errorText err) >> pure (statusOf err)
        Right (status, Nothing) -> pure status
        Right (status, Just text) -> storeText output outputSize text >> pure status
      case stored of
        Right status -> pure status
        Left (_ :: SomeException) -> pure 4

cCheck :: Ptr Word8 -> CSize -> FunPtr Callback -> Ptr () -> Ptr (Ptr Word8) -> Ptr CSize -> IO CInt
cCheck input size callback userdata output outputSize = boundary output outputSize $ do
  parsed <- readText input size
  case parsed of
    Left err -> pure (Left err)
    Right text -> do
      answer <- checkSerialized (callbackBackend callback userdata) text
      pure ((\ok -> (if ok then 0 else 1, Nothing)) <$> answer)

cNormalize :: Ptr Word8 -> CSize -> Ptr (Ptr Word8) -> Ptr CSize -> IO CInt
cNormalize input size output outputSize = boundary output outputSize $ do
  parsed <- readText input size
  case parsed of
    Left err -> pure (Left err)
    Right text -> fmap (fmap (\canonical -> (0,Just canonical))) (normalizeSerialized text)

cPrepare :: Ptr Word8 -> CSize -> FunPtr Callback -> Ptr () -> Ptr (Ptr Word8) -> Ptr CSize -> IO CInt
cPrepare input size callback userdata output outputSize = boundary output outputSize $ do
  parsed <- readText input size
  case parsed >>= decodePreparationRequest of
    Left err -> pure (Left err)
    Right (v,s,a,st,call) -> do
      candidate <- prepareCandidate (callbackBackend callback userdata) v s a st call
      pure $ candidate >>= encodeCandidate >>= \text -> Right (0,Just text)

cFree :: Ptr Word8 -> IO ()
cFree = free

foreign export ccall "passport_monitor_check" cCheck :: Ptr Word8 -> CSize -> FunPtr Callback -> Ptr () -> Ptr (Ptr Word8) -> Ptr CSize -> IO CInt
foreign export ccall "passport_monitor_normalize" cNormalize :: Ptr Word8 -> CSize -> Ptr (Ptr Word8) -> Ptr CSize -> IO CInt
foreign export ccall "passport_monitor_prepare" cPrepare :: Ptr Word8 -> CSize -> FunPtr Callback -> Ptr () -> Ptr (Ptr Word8) -> Ptr CSize -> IO CInt
foreign export ccall "passport_monitor_free" cFree :: Ptr Word8 -> IO ()

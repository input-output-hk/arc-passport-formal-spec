{-# LANGUAGE OverloadedStrings #-}
-- | Typed mirror of the monitor token grammar in
-- @docs/conformance-recovery.md@, \"Runtime transition monitor\".
-- Codecs check representation, not model conformance or cryptographic validity.
module Passport.Monitor.Codec
  ( encodeObservation, decodeObservation, encodeCandidate, decodeCandidate
  , encodeState, decodeState, encodeCall, decodeCall, preparationRequest, decodePreparationRequest ) where

import Control.Monad (replicateM, unless)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Numeric.Natural (Natural)
import Text.Parsec hiding (State, count)
import Passport.Monitor.Types

type Parser = Parsec [Text] ()
tokenP :: Parser Text
tokenP = tokenPrim T.unpack (\p _ _ -> incSourceColumn p 1) Just
literal :: Text -> Parser ()
literal t = do x <- tokenP; unless (x == t) (unexpected (T.unpack x))
checked :: (Text -> Either MonitorError a) -> Parser a
checked f = tokenP >>= either (fail . show) pure . f
natural :: Parser Natural
natural = do
  t <- tokenP
  if not (T.null t) && T.all (\c -> c >= '0' && c <= '9') t
    then pure (read (T.unpack t)) else fail "expected nonnegative decimal natural"
b32 :: Parser Bytes32
b32 = checked bytes32
b64 :: Parser Bytes64
b64 = checked bytes64
boolean :: Parser Bool
boolean = do t <- tokenP; case t of
               "0" -> pure False
               "1" -> pure True
               _ -> fail "expected 0 or 1"
pointP :: Parser Point
pointP = Point <$> natural <*> natural
phiP :: Parser Phi
phiP = Phi <$> natural <*> natural <*> natural <*> natural
listP :: Parser a -> Parser [a]
listP p = do
  n <- natural
  -- Counts are bounded by the actual token stream, not by model integer widths.
  remaining <- length <$> getInput
  if n > fromIntegral remaining then fail "count exceeds remaining input"
    else replicateM (fromIntegral n) p
uniqueKeys :: Ord a => [a] -> Bool
uniqueKeys xs = length xs == Set.size (Set.fromList xs)
unique :: Ord a => [a] -> Parser ()
unique xs = unless (uniqueKeys xs) (fail "duplicate state set/map key")
stateP :: Parser State
stateP = do
  r <- natural; n <- natural; e <- natural; c <- natural
  ds <- listP b32; unique ds
  bs <- listP ((,) <$> b32 <*> natural); unique (map fst bs)
  k <- b32; pk <- pointP
  marker <- tokenP
  ph <- case marker of "0" -> pure Nothing; "4" -> Just <$> phiP; _ -> fail "expected phi marker 0 or 4"
  State r n e c ds bs k pk ph <$> natural <*> b32 <*> b64 <*> boolean <*> b32 <*> pointP <*> natural <*> natural

gatedP :: Parser GatedCall
gatedP = do
  t <- tokenP
  case t of
    "W" -> Withdraw <$> b32 <*> natural <*> b32
    "A" -> AddDevice <$> b32
    "R" -> RemoveDevice <$> b32
    "K" -> RotateEncKey <$> b32
    "P" -> PublishRecovery <$> pointP <*> b32 <*> phiP <*> natural <*> b64
    "C" -> pure CancelRecovery
    _ -> fail "unknown gated call"
callP :: Parser Call
callP = do
  t <- tokenP
  case t of
    "D" -> Deposit <$> b32 <*> natural
    "F" -> pure FinaliseRecovery
    "U" -> SubmitRecovery <$> pointP <*> pointP <*> natural <*> natural <*> natural <*> pointP <*> natural <*> pointP <*> natural <*> natural
    "J" -> Authorised <$> gatedP <*> (Authorisation <$> pointP <*> natural <*> pointP <*> natural <*> natural)
    _ -> fail "unknown raw call"

result :: Text -> Parser a -> Parser a
result k p = literal k >> p
unitP :: WriteOp -> Parser Event
unitP op = literal "unit" >> literal "-" >> pure (UnitEvent op)
eventP :: Parser Event
eventP = do
  tag <- tokenP
  case tag of
    "publish" -> Published <$> natural
    "require" -> do
      bound <- tokenP
      Required <$> case bound of
        "min" -> TimeAtLeast <$> natural
        "max" -> TimeAtMost <$> natural
        _ -> fail "unknown time condition"
    "op" -> do
      name <- tokenP
      case name of
        "readNonce" -> CountEvent ReadNonce <$> result "count" natural
        "readRound" -> CountEvent ReadRound <$> result "count" natural
        "readEpoch" -> CountEvent ReadEpoch <$> result "count" natural
        "readDeviceCount" -> CountEvent ReadDeviceCount <$> result "count" natural
        "readVetoWindow" -> CountEvent ReadVetoWindow <$> result "count" natural
        "readNotBefore" -> CountEvent ReadNotBefore <$> result "count" natural
        "readBalance" -> CountEvent <$> (ReadBalance <$> b32) <*> result "count" natural
        "readPending" -> FlagEvent ReadPending <$> result "flag" boolean
        "deviceMember" -> FlagEvent <$> (DeviceMember <$> b32) <*> result "flag" boolean
        "balanceMember" -> FlagEvent <$> (BalanceMember <$> b32) <*> result "flag" boolean
        "readRecoveryPk" -> PointEvent ReadRecoveryPk <$> result "point" pointP
        "readPendingRecoveryPk" -> PointEvent ReadPendingRecoveryPk <$> result "point" pointP
        "readSession" -> BytesEvent ReadSession <$> result "bytes" b32
        "readPendingEntry" -> BytesEvent ReadPendingEntry <$> result "bytes" b32
        "writeBalance" -> (WriteBalance <$> b32 <*> natural) >>= unitP
        "insertDevice" -> (InsertDevice <$> b32) >>= unitP
        "removeDevice" -> (RemoveDeviceEntry <$> b32) >>= unitP
        "setEncKey" -> (SetEncKey <$> b32) >>= unitP
        "resetDevices" -> unitP ResetDevices
        "writeNonce" -> (WriteNonce <$> natural) >>= unitP
        "writeRound" -> (WriteRound <$> natural) >>= unitP
        "writeEpoch" -> (WriteEpoch <$> natural) >>= unitP
        "writeDeviceCount" -> (WriteDeviceCount <$> natural) >>= unitP
        "writeNotBefore" -> (WriteNotBefore <$> natural) >>= unitP
        "writePhiLen" -> (WritePhiLen <$> natural) >>= unitP
        "writeRecoveryPk" -> (WriteRecoveryPk <$> pointP) >>= unitP
        "writePendingRecoveryPk" -> (WritePendingRecoveryPk <$> pointP) >>= unitP
        "writeSession" -> (WriteSession <$> b32) >>= unitP
        "writePendingEntry" -> (WritePendingEntry <$> b32) >>= unitP
        "writePending" -> (WritePending <$> boolean) >>= unitP
        "insertPhi1" -> (InsertPhi1 <$> natural) >>= unitP
        "insertPhi2" -> (InsertPhi2 <$> natural) >>= unitP
        "insertPhi3" -> (InsertPhi3 <$> natural) >>= unitP
        "insertPhi4" -> (InsertPhi4 <$> natural) >>= unitP
        "writeWrap" -> (WriteWrap <$> b64) >>= unitP
        _ -> fail "unknown ledger operation"
    _ -> fail "unknown journal event"
candidateP :: Parser Candidate
candidateP = Candidate <$> natural <*> stateP <*> callP <*> (literal "J" >> listP eventP)
contextP :: Parser Context
contextP = Context <$> natural <*> natural
outcomeP :: Parser Outcome
outcomeP = do t <- tokenP; case t of
               "ok" -> pure Accepted
               "refused" -> pure Rejected
               "fail" -> Aborted <$> checked errorCode
               _ -> fail "unknown outcome"
variantP :: Parser Variant
variantP = do t <- tokenP; case t of
               "source" -> pure Source
               "corrected" -> pure Corrected
               _ -> fail "unknown finalisation variant"
observationP :: Parser Observation
observationP = do
  literal "monitor-v1"
  v <- variantP; s <- b32; before <- stateP
  kind <- tokenP
  tr <- case kind of
    "call" -> Invocation <$> contextP <*> callP <*> outcomeP
    "admit" -> Admission <$> contextP <*> candidateP <*> outcomeP
    _ -> fail "unknown transition kind"
  Observation v s before tr <$> stateP

parseAll :: Parser a -> Text -> Either MonitorError a
parseAll p t = either (Left . Malformed . T.pack . show) Right (parse (p <* eof) "monitor tokens" (T.words t))
-- | Parse a complete @monitor-v1@ observation; @Left Malformed@ on invalid tokens.
decodeObservation :: Text -> Either MonitorError Observation
decodeObservation = parseAll observationP
-- | Parse complete candidate evidence; @Left Malformed@ on invalid tokens.
decodeCandidate :: Text -> Either MonitorError Candidate
decodeCandidate = parseAll candidateP
-- | Parse a complete state, rejecting duplicate set/map keys with @Left Malformed@.
decodeState :: Text -> Either MonitorError State
decodeState = parseAll stateP
-- | Parse a complete raw call; @Left Malformed@ on invalid tokens.
decodeCall :: Text -> Either MonitorError Call
decodeCall = parseAll callP

number :: Natural -> Text
number = T.pack . show
boolT :: Bool -> Text
boolT False = "0"
boolT True = "1"
pointT :: Point -> [Text]
pointT (Point x y) = [number x, number y]
phiT :: Phi -> [Text]
phiT (Phi a b c d) = map number [a,b,c,d]
variantT :: Variant -> Text
variantT Source = "source"
variantT Corrected = "corrected"

-- | Parse a complete @prepare@ request into variant, crypto domain, logical
-- transaction account, build state, and raw call; @Left Malformed@ on invalid input.
decodePreparationRequest :: Text -> Either MonitorError (Variant, Bytes32, Natural, State, Call)
decodePreparationRequest = parseAll $ do
  literal "prepare"
  (,,,,) <$> variantP <*> b32 <*> natural <*> stateP <*> callP
stateT :: State -> [Text]
stateT (State r n e c ds bs k pk ph len sess w pend pe ppk time veto) =
  map number [r,n,e,c,fromIntegral (length ds)] ++ map bytes32Hex ds ++
  [number (fromIntegral (length bs))] ++ concatMap (\(key,value) -> [bytes32Hex key,number value]) bs ++
  [bytes32Hex k] ++ pointT pk ++ maybe ["0"] (("4":) . phiT) ph ++
  [number len,bytes32Hex sess,bytes64Hex w,boolT pend,bytes32Hex pe] ++ pointT ppk ++ map number [time,veto]
gatedT :: GatedCall -> [Text]
gatedT (Withdraw c n r) = ["W",bytes32Hex c,number n,bytes32Hex r]
gatedT (AddDevice e) = ["A",bytes32Hex e]
gatedT (RemoveDevice e) = ["R",bytes32Hex e]
gatedT (RotateEncKey e) = ["K",bytes32Hex e]
gatedT (PublishRecovery q sess ph len w) = ["P"] ++ pointT q ++ [bytes32Hex sess] ++ phiT ph ++ [number len,bytes64Hex w]
gatedT CancelRecovery = ["C"]
callT :: Call -> [Text]
callT (Deposit c n) = ["D",bytes32Hex c,number n]
callT FinaliseRecovery = ["F"]
callT (SubmitRecovery q q' e n u rr sr rs ss g) = ["U"] ++ pointT q ++ pointT q' ++ map number [e,n,u] ++ pointT rr ++ [number sr] ++ pointT rs ++ map number [ss,g]
callT (Authorised g (Authorisation pk uc r s gr)) = ["J"] ++ gatedT g ++ pointT pk ++ [number uc] ++ pointT r ++ map number [s,gr]
countT :: CountOp -> [Text]
countT ReadNonce = ["readNonce"]
countT ReadRound = ["readRound"]
countT ReadEpoch = ["readEpoch"]
countT ReadDeviceCount = ["readDeviceCount"]
countT ReadVetoWindow = ["readVetoWindow"]
countT ReadNotBefore = ["readNotBefore"]
countT (ReadBalance c) = ["readBalance",bytes32Hex c]
flagT :: FlagOp -> [Text]
flagT ReadPending = ["readPending"]
flagT (DeviceMember b) = ["deviceMember",bytes32Hex b]
flagT (BalanceMember b) = ["balanceMember",bytes32Hex b]
pointOpT :: PointOp -> Text
pointOpT ReadRecoveryPk = "readRecoveryPk"
pointOpT ReadPendingRecoveryPk = "readPendingRecoveryPk"
bytesOpT :: BytesOp -> Text
bytesOpT ReadSession = "readSession"
bytesOpT ReadPendingEntry = "readPendingEntry"
writeT :: WriteOp -> [Text]
writeT (WriteBalance b n) = ["writeBalance",bytes32Hex b,number n]
writeT (InsertDevice b) = ["insertDevice",bytes32Hex b]
writeT (RemoveDeviceEntry b) = ["removeDevice",bytes32Hex b]
writeT (SetEncKey b) = ["setEncKey",bytes32Hex b]
writeT ResetDevices = ["resetDevices"]
writeT (WriteNonce n) = ["writeNonce",number n]
writeT (WriteRound n) = ["writeRound",number n]
writeT (WriteEpoch n) = ["writeEpoch",number n]
writeT (WriteDeviceCount n) = ["writeDeviceCount",number n]
writeT (WriteNotBefore n) = ["writeNotBefore",number n]
writeT (WritePhiLen n) = ["writePhiLen",number n]
writeT (WriteRecoveryPk p) = "writeRecoveryPk" : pointT p
writeT (WritePendingRecoveryPk p) = "writePendingRecoveryPk" : pointT p
writeT (WriteSession b) = ["writeSession",bytes32Hex b]
writeT (WritePendingEntry b) = ["writePendingEntry",bytes32Hex b]
writeT (WritePending b) = ["writePending",boolT b]
writeT (InsertPhi1 n) = ["insertPhi1",number n]
writeT (InsertPhi2 n) = ["insertPhi2",number n]
writeT (InsertPhi3 n) = ["insertPhi3",number n]
writeT (InsertPhi4 n) = ["insertPhi4",number n]
writeT (WriteWrap b) = ["writeWrap",bytes64Hex b]
eventT :: Event -> [Text]
eventT (CountEvent op n) = ["op"] ++ countT op ++ ["count",number n]
eventT (FlagEvent op b) = ["op"] ++ flagT op ++ ["flag",boolT b]
eventT (PointEvent op p) = ["op",pointOpT op,"point"] ++ pointT p
eventT (BytesEvent op b) = ["op",bytesOpT op,"bytes",bytes32Hex b]
eventT (UnitEvent op) = ["op"] ++ writeT op ++ ["unit","-"]
eventT (Published n) = ["publish",number n]
eventT (Required (TimeAtLeast n)) = ["require","min",number n]
eventT (Required (TimeAtMost n)) = ["require","max",number n]
candidateT :: Candidate -> [Text]
candidateT (Candidate accountId st call events) = [number accountId] ++ stateT st ++ callT call ++ ["J",number (fromIntegral (length events))] ++ concatMap eventT events
contextT :: Context -> [Text]
contextT (Context a t) = map number [a,t]
outcomeT :: Outcome -> [Text]
outcomeT Accepted = ["ok"]
outcomeT Rejected = ["refused"]
outcomeT (Aborted e) = ["fail",errorCodeText e]
transitionT :: Transition -> [Text]
transitionT (Invocation ctx call out) = ["call"] ++ contextT ctx ++ callT call ++ outcomeT out
transitionT (Admission ctx candidate out) = ["admit"] ++ contextT ctx ++ candidateT candidate ++ outcomeT out
observationT :: Observation -> [Text]
observationT (Observation v s before tr after) = ["monitor-v1",variantT v,bytes32Hex s] ++ stateT before ++ transitionT tr ++ stateT after

-- Smart byte/error constructors and Natural fields guarantee scalar structure;
-- only duplicate set/map keys can be introduced through public record fields.
validateState :: State -> Either MonitorError ()
validateState st
  | uniqueKeys (devices st) && uniqueKeys (map fst (balances st)) = Right ()
  | otherwise = Left (Malformed "duplicate state set/map key")
-- | Encode an observation as @monitor-v1@ tokens; @Left Malformed@ on duplicate
-- set/map keys in any included state. Does not check the observed transition.
encodeObservation :: Observation -> Either MonitorError Text
encodeObservation observation = do
  validateState (initialState observation)
  validateState (finalState observation)
  case transition observation of
    Admission _ candidate _ -> validateState (buildState candidate)
    Invocation {} -> Right ()
  pure (T.unwords (observationT observation))
-- | Encode candidate evidence; @Left Malformed@ on duplicate build-state keys.
encodeCandidate :: Candidate -> Either MonitorError Text
encodeCandidate candidate = T.unwords (candidateT candidate) <$ validateState (buildState candidate)
-- | Encode a state; @Left Malformed@ on duplicate set/map keys.
encodeState :: State -> Either MonitorError Text
encodeState st = T.unwords (stateT st) <$ validateState st
-- | Encode a structurally typed raw call; always @Right@, without executing it.
encodeCall :: Call -> Either MonitorError Text
encodeCall = Right . T.unwords . callT
-- | Encode @prepare@ with positional variant, crypto domain, logical transaction
-- account, build state, and raw call; @Left Malformed@ on duplicate state keys.
preparationRequest :: Variant -> Bytes32 -> Natural -> State -> Call -> Either MonitorError Text
preparationRequest v s a st call = do
  stText <- encodeState st
  callText <- encodeCall call
  pure (T.unwords ["prepare",variantT v,bytes32Hex s,number a,stText,callText])

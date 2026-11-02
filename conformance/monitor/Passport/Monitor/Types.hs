{-# LANGUAGE OverloadedStrings #-}
-- | Stable domain types. Naturals have no artificial ABI-width restriction.
module Passport.Monitor.Types
  ( Bytes32, bytes32, bytes32Hex, Bytes64, bytes64, bytes64Hex
  , ErrorCode, errorCode, errorCodeText, MonitorError(..)
  , Variant(..), Point(..), Phi(..), State(..), Context(..)
  , Authorisation(..), GatedCall(..), Call(..), Candidate(..)
  , CountOp(..), FlagOp(..), PointOp(..), BytesOp(..), WriteOp(..)
  , Condition(..), Event(..), Outcome(..), Transition(..), Observation(..)
  ) where

import Data.Char (isSpace)
import Data.Text (Text)
import qualified Data.Text as T
import Numeric.Natural (Natural)

data MonitorError = Malformed Text | BackendFailure Text | InternalFailure Text
  | BuildAborted ErrorCode deriving (Eq, Show)

newtype Bytes32 = Bytes32 Text deriving (Eq, Ord, Show)
newtype Bytes64 = Bytes64 Text deriving (Eq, Ord, Show)
-- | Extract the validated lowercase, 64-digit hexadecimal representation.
bytes32Hex :: Bytes32 -> Text
bytes32Hex (Bytes32 t) = t
-- | Extract the validated lowercase, 128-digit hexadecimal representation.
bytes64Hex :: Bytes64 -> Text
bytes64Hex (Bytes64 t) = t

hex :: Int -> Text -> Either MonitorError Text
hex n t
  | T.length t == n && T.all (\c -> c >= '0' && c <= '9' || c >= 'a' && c <= 'f') t = Right t
  | otherwise = Left (Malformed ("expected lowercase hex with " <> T.pack (show n) <> " digits"))

-- | Validate exactly 64 lowercase hexadecimal digits; otherwise @Left Malformed@.
bytes32 :: Text -> Either MonitorError Bytes32
bytes32 t = Bytes32 <$> hex 64 t
-- | Validate exactly 128 lowercase hexadecimal digits; otherwise @Left Malformed@.
bytes64 :: Text -> Either MonitorError Bytes64
bytes64 t = Bytes64 <$> hex 128 t

newtype ErrorCode = ErrorCode Text deriving (Eq, Show)
-- | Extract the validated, nonempty single-token model error code.
errorCodeText :: ErrorCode -> Text
errorCodeText (ErrorCode t) = t
-- | Validate a nonempty token without whitespace; otherwise @Left Malformed@.
errorCode :: Text -> Either MonitorError ErrorCode
errorCode t
  | T.null t || T.any isSpace t = Left (Malformed "error code must be one nonempty token")
  | otherwise = Right (ErrorCode t)

data Variant = Source | Corrected deriving (Eq, Show)
data Point = Point Natural Natural deriving (Eq, Show)
data Phi = Phi Natural Natural Natural Natural deriving (Eq, Show)
data State = State
  { stateRound :: Natural, authNonce :: Natural, deviceEpoch :: Natural, deviceCount :: Natural
  , devices :: [Bytes32], balances :: [(Bytes32, Natural)], encKey :: Bytes32
  , recoveryPk :: Point, phi :: Maybe Phi, phiLen :: Natural, session :: Bytes32
  , wrap :: Bytes64, pending :: Bool, pendingEntry :: Bytes32
  , pendingRecoveryPk :: Point, pendingNotBefore :: Natural, vetoWindow :: Natural
  } deriving (Eq, Show)
data Context = Context
  { account :: Natural
    -- ^ Logical account invoking or admitting the transaction, not a crypto
    -- domain. Admission compares this with 'transactionAccount'.
  , blockTime :: Natural
  } deriving (Eq, Show)
data Authorisation = Authorisation
  { publicKey :: Point, useCounter :: Natural, commitment :: Point
  , response :: Natural, grind :: Natural } deriving (Eq, Show)
data GatedCall
  = Withdraw Bytes32 Natural Bytes32 | AddDevice Bytes32 | RemoveDevice Bytes32
  | RotateEncKey Bytes32 | PublishRecovery Point Bytes32 Phi Natural Bytes64 | CancelRecovery
  deriving (Eq, Show)
data Call
  = Deposit Bytes32 Natural | FinaliseRecovery
  | SubmitRecovery Point Point Natural Natural Natural Point Natural Point Natural Natural
  | Authorised GatedCall Authorisation deriving (Eq, Show)

data CountOp = ReadNonce | ReadRound | ReadEpoch | ReadDeviceCount | ReadVetoWindow
  | ReadNotBefore | ReadBalance Bytes32 deriving (Eq, Show)
data FlagOp = ReadPending | DeviceMember Bytes32 | BalanceMember Bytes32 deriving (Eq, Show)
data PointOp = ReadRecoveryPk | ReadPendingRecoveryPk deriving (Eq, Show)
data BytesOp = ReadSession | ReadPendingEntry deriving (Eq, Show)
data WriteOp
  = WriteBalance Bytes32 Natural | InsertDevice Bytes32 | RemoveDeviceEntry Bytes32
  | SetEncKey Bytes32 | ResetDevices | WriteNonce Natural | WriteRound Natural
  | WriteEpoch Natural | WriteDeviceCount Natural | WriteNotBefore Natural | WritePhiLen Natural
  | WriteRecoveryPk Point | WritePendingRecoveryPk Point | WriteSession Bytes32
  | WritePendingEntry Bytes32 | WritePending Bool | InsertPhi1 Natural | InsertPhi2 Natural
  | InsertPhi3 Natural | InsertPhi4 Natural | WriteWrap Bytes64 deriving (Eq, Show)
data Condition = TimeAtLeast Natural | TimeAtMost Natural deriving (Eq, Show)
-- | Results are paired only with operations of the correct result kind. Unit
-- results are represented by UnitEvent, and encoded explicitly as @unit -@.
data Event = CountEvent CountOp Natural | FlagEvent FlagOp Bool | PointEvent PointOp Point
  | BytesEvent BytesOp Bytes32 | UnitEvent WriteOp | Published Natural | Required Condition
  deriving (Eq, Show)
data Candidate = Candidate
  { transactionAccount :: Natural
    -- ^ Logical account used to build the candidate; admission requires it to
    -- equal the current context's 'account'. Unrelated to the crypto 'self'.
  , buildState :: State, rawCall :: Call, journal :: [Event] }
  deriving (Eq, Show)
-- | The observed transaction result, not the monitor's conformance verdict.
data Outcome = Accepted | Rejected | Aborted ErrorCode deriving (Eq, Show)
data Transition = Invocation Context Call Outcome | Admission Context Candidate Outcome
  deriving (Eq, Show)
data Observation = Observation
  { variant :: Variant
  , self :: Bytes32
    -- ^ Cryptographic domain supplied to the trusted primitives, not the
    -- natural-valued logical 'account' or 'transactionAccount'.
  , initialState :: State, transition :: Transition, finalState :: State } deriving (Eq, Show)

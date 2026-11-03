{-# OPTIONS --safe --without-K #-}

-- Positional ABI views of account.compact's GrantRecord and GrantScope at
-- fc19e471536febb2133f20e817847251622dcdf5. These are projections, not copies:
-- dispatch validates the tuple shapes before the source evaluator uses them.
module Conformance.FullAccountLayouts where

open import Conformance.FullAccountTypes using (Value; at; get)
open import Data.List.Base using (List)

-- GrantRecord declaration order; the names retain the Compact field meanings.
grantEpoch grantGeneration grantIssuedAt grantNonce grantSpentCommitment
  grantWindowStart grantWindowSpent grantActive grantScope : Value → Value
grantEpoch = at 0
grantGeneration = at 1
grantIssuedAt = at 2
grantNonce = at 3
grantSpentCommitment = at 4
grantWindowStart = at 5
grantWindowSpent = at 6
grantActive = at 7
grantScope = at 8

-- GrantScope declaration order.
scopeWithdrawUnshielded scopeWithdrawShielded scopeWithdrawShieldedToContract
  scopeRead scopeObjectCommitment scopePerCallCap scopeCap scopeExpiresAt
  scopeRPCommitment scopeReadKeyHash scopeWindowLength scopeWindowCap
  scopeCallerCommitment : Value → Value
scopeWithdrawUnshielded = at 0
scopeWithdrawShielded = at 1
scopeWithdrawShieldedToContract = at 2
scopeRead = at 3
scopeObjectCommitment = at 4
scopePerCallCap = at 5
scopeCap = at 6
scopeExpiresAt = at 7
scopeRPCommitment = at 8
scopeReadKeyHash = at 9
scopeWindowLength = at 10
scopeWindowCap = at 11
scopeCallerCommitment = at 12

-- Shared issue_grant argument prefix; authentication follows this prefix.
module IssueArguments (xs : List Value) where
  id withdrawUnshielded withdrawShielded withdrawToContract readFlag color
    recipientKind recipient maxCoinValue perCallCap cap expiresAt rpIdHash
    readKeyHash windowLength windowCap caller salt : Value
  id = get 0 xs
  withdrawUnshielded = get 1 xs
  withdrawShielded = get 2 xs
  withdrawToContract = get 3 xs
  readFlag = get 4 xs
  color = get 5 xs
  recipientKind = get 6 xs
  recipient = get 7 xs
  maxCoinValue = get 8 xs
  perCallCap = get 9 xs
  cap = get 10 xs
  expiresAt = get 11 xs
  rpIdHash = get 12 xs
  readKeyHash = get 13 xs
  windowLength = get 14 xs
  windowCap = get 15 xs
  caller = get 16 xs
  salt = get 17 xs

-- recover_submit's complete argument vector.
module SubmitArguments (xs : List Value) where
  successorKey nextRecoveryKey epoch authNonce nowBound recoveryR recoveryS
    successorR successorS grindNonce : Value
  successorKey = get 0 xs
  nextRecoveryKey = get 1 xs
  epoch = get 2 xs
  authNonce = get 3 xs
  nowBound = get 4 xs
  recoveryR = get 5 xs
  recoveryS = get 6 xs
  successorR = get 7 xs
  successorS = get 8 xs
  grindNonce = get 9 xs

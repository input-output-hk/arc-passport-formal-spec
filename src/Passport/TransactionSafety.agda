{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes
open import Midnight.ContractDSL.SymbolicSigning using (Ownership)
import Conformance.FullAccountSignatureBinding as SignatureBinding

-- Local withdrawal safety vocabulary; reader entry: TransactionSafetyProperties.
-- An occurrence contains the actual committed dispatcher transition. WithdrawalCall
-- tests that call's resolved operation, without choosing its authorisation branch.
module Passport.TransactionSafety (P : Primitives) (address : Value)
  (ownership : SignatureBinding.Key P → Ownership) where

open import Conformance.FullAccountBody P
open import Conformance.FullAccountCrypto P using (Auth)
import Conformance.FullAccountDeviceSecurity P as Device
open import Conformance.FullAccountGrant P
import Conformance.FullAccountGrantScope P as Scope
open import Conformance.FullAccountGrantSecurity P
open import Data.Bool.Base using (false)
open import Data.Empty using (⊥)
open import Data.List.Base using ([]; _∷_; take)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (_+_; _≤_)
open import Data.Product.Base using (Σ; _×_)
import Passport.AccountSecurity P address ownership as Security
open import Passport.AccountLifecycle P
open import Passport.GrantEffects P using (issuanceOf)
import Passport.GrantReplay P address as Replay
open import Passport.GrantSpending P
open Histories address
open import Passport.RevocationExclusion P address hiding (module Runs)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)

module Binding = SignatureBinding P

withdrawalEntry : Maybe Runtime.Entrypoint → Set
withdrawalEntry (just (Runtime.device _ op)) = Withdrawal op
withdrawalEntry (just (Runtime.grant _ op)) = Withdrawal op
withdrawalEntry _ = ⊥

WithdrawalCall : ∀ {s t} → CommittedOccurrence s t → Set
WithdrawalCall event = withdrawalEntry (resolve (RuntimeCall.request (CommittedOccurrence.call event)))

-- Every amount in this episode was observed in the deployment-rooted history.
-- The bound adds this accepted withdrawal, not merely the caller's spentPrev.
HistoricalCap : ∀ {s c op ctx ga xs} → Runs.History s → GrantCallEvidence c op ctx ga xs s → Set
HistoricalCap {op = op} {xs = xs} h evidence = Σ Episode λ ep →
  findEpisode (GrantCallEvidence.identifier evidence) (Book.current (historyBook h)) ≡ just ep ×
  issuanceOf (GrantCallEvidence.identifier evidence) (GrantCallEvidence.grantRecord evidence) ≡
    Episode.issuanceIdentity ep ×
  total ep + amountOf op xs ≤ Episode.capValue ep

ConsumedCredentials : ∀ {c op ctx xs s v t} → Device.DeviceCall c op ctx xs s v t → Set
ConsumedCredentials {c} {op} {ctx} {xs} {t = t} evidence =
  equal (Device.Authorisation.current (Device.DeviceCall.authorised evidence))
    (Device.DeviceCall.rolledEntry evidence) ≡ false →
  ∀ {ctx′ a digest next after} → self ctx′ ≡ self ctx → a ≡ Device.deviceAuth c op xs →
  ¬ Device.Authorisation c ctx′ a digest t next after

HistoricalTokenExclusion : ∀ {s t} → Replay.Spend s t → Set
HistoricalTokenExclusion {t = t} old = ∀ {later final} (trace : Runs.Trace t later)
  (next : Replay.Spend later final) → Replay.SameIssuance old trace next →
  Replay.RelevantRequestBinding (Replay.Spend.signingKey old) (Replay.Spend.request old)
    (Replay.Spend.signingKey next) (Replay.Spend.request next) →
  Binding.Symbolic.token ownership (Replay.Spend.signingKey old) (Replay.Spend.request old) ≢
    Binding.Symbolic.token ownership (Replay.Spend.signingKey next) (Replay.Spend.request next)

-- The replay vocabulary uses the same ABI split under a separate source name.
replaySpend : ∀ {s t} (event : CommittedOccurrence s t) c op → Withdrawal op →
  Resolved event (Runtime.grant c op) →
  GrantFinalState c op (occurrenceContext event)
    (Security.grantAuthorisation c op (occurrenceArguments event)) (take 3 (occurrenceArguments event)) s t →
  Replay.Spend s t
replaySpend event c .withdrawUnshielded unshieldedWithdrawal resolved final =
  record { curve = c ; operation = withdrawUnshielded ; event = event ; resolved = resolved ; finalState = final }
replaySpend event c .withdrawShielded shieldedWithdrawal resolved final =
  record { curve = c ; operation = withdrawShielded ; event = event ; resolved = resolved ; finalState = final }
replaySpend event c .withdrawToContract contractWithdrawal resolved final =
  record { curve = c ; operation = withdrawToContract ; event = event ; resolved = resolved ; finalState = final }

module _ {s t} (h : Runs.History s) (event : CommittedOccurrence s t)
  (policy : Scope.IntendedPolicy) where
  private
    ctx = occurrenceContext event
    xs = occurrenceArguments event
    env = CommittedOccurrence.environment event
    call = CommittedOccurrence.call event
    answer = CommittedOccurrence.answer event

  -- Scope and spent-opening assumptions apply only if this actual call resolves
  -- to a grant. They supply concrete openings, never a safety certificate.
  IntendedOpening : Set
  IntendedOpening = ∀ c op → Resolved event (Runtime.grant c op) →
    Scope.IntendedGrant c ctx (Security.grantAuthorisation c op xs) s policy

  ScopeAgreement : Set
  ScopeAgreement = ∀ c op → Resolved event (Runtime.grant c op) →
    Scope.RelevantOpeningsAgree op ctx (Security.grantAuthorisation c op xs) (take 3 xs) policy

  SpendAgreement : Set
  SpendAgreement = ∀ c op → Resolved event (Runtime.grant c op) →
    CallAgreement (Runtime.grant c op) ctx xs s (historyBook h)

  data SafeWithdrawal : Security.SignedRequest → Set where
    deviceWithdrawal : ∀ c op → Withdrawal op → Resolved event (Runtime.device c op) →
      (evidence : Device.DeviceCall c op ctx xs s answer t) →
      (checked : Binding.Verified c (Device.deviceAuth c op xs) (Device.DeviceCall.challengeValue evidence)) →
      Security.Encodes (Security.calledRequest evidence) (Binding.signedDigest checked) →
      ConsumedCredentials evidence → SafeWithdrawal (Security.calledRequest evidence)
    grantWithdrawal : ∀ c op → (withdrawal : Withdrawal op) → (resolved : Resolved event (Runtime.grant c op)) →
      (final : GrantFinalState c op ctx (Security.grantAuthorisation c op xs) (take 3 xs) s t) →
      (checked : Binding.Verified c (authorisation (Security.grantAuthorisation c op xs))
        (GrantCallEvidence.challengeValue (GrantFinalState.callEvidence final))) →
      Security.Encodes (Security.grantedRequest (GrantFinalState.callEvidence final)) (Binding.signedDigest checked) →
      Scope.SemanticScope op ctx (Security.grantAuthorisation c op xs) (take 3 xs) policy →
      HistoricalCap h (GrantFinalState.callEvidence final) →
      HistoricalTokenExclusion (replaySpend event c op withdrawal resolved final) →
      SafeWithdrawal (Security.grantedRequest (GrantFinalState.callEvidence final))

  record TransactionSafety : Set where
    field request : Security.SignedRequest
          classified : SafeWithdrawal request
          actualRequest : Security.signedRequests s env call ≡ request ∷ []

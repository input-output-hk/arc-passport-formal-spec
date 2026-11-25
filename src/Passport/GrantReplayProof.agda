{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

module Passport.GrantReplayProof (P : Primitives) (address : Value) where

open import Conformance.FullAccountBody P
open import Conformance.FullAccountCrypto P
open import Conformance.FullAccountExecution
open import Conformance.FullAccountGrant P
open import Conformance.FullAccountGrantSecurity P
import Conformance.FullAccountGrantSecurityProof P as G
open import Conformance.FullAccountLayouts
open import Conformance.FullAccountSignatureBinding P
import Conformance.FullAccountSignatureBindingProof P as Binding
open import Data.Bool.Base using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (take)
open import Data.Maybe.Base using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat.Base using (ℕ; suc; _≤_; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; <-irrefl)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (tt)
import Midnight.ContractDSL.SymbolicSigning as Signing
import Passport.Account as Account
open import Passport.AccountLifecycle P hiding (run)
open import Passport.GrantEffects P
import Passport.GrantEffectsProof P as EP
open import Passport.GrantReplay P address
open import Passport.GrantSpending P using (parseGrantAuth)
open import Passport.RevocationExclusion P address
import Passport.RevocationExclusionProof P address as H
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.PropositionalEquality

private
  module S = H.S
  module SP = H.SP
  open S using (AcceptedCall; activated; deviceAuthorised; grantAuthorised;
    depositedUnshielded; depositedShielded; recoverySubmitted; recoveryFinalised)

  accepted-spend : ∀ {c op s t requests} (event : CommittedOccurrence s t) →
    AcceptedCall (CommittedOccurrence.environment event) (CommittedOccurrence.call event)
      s (CommittedOccurrence.answer event) t (CommittedOccurrence.effects event) requests →
    Resolved event (Runtime.grant c op) → Spend s t
  accepted-spend event (activated _ d _) resolved with trans (sym (S.Dispatched.resolved d)) resolved
  ... | ()
  accepted-spend event (deviceAuthorised _ _ d _ _ _) resolved with trans (sym (S.Dispatched.resolved d)) resolved
  ... | ()
  accepted-spend event (grantAuthorised c op d w final _ _) resolved
    with trans (sym (S.Dispatched.resolved d)) resolved | w
  ... | refl | unshieldedWithdrawal = record
    { curve = c ; operation = withdrawUnshielded ; event = event ; resolved = resolved ; finalState = final }
  ... | refl | shieldedWithdrawal = record
    { curve = c ; operation = withdrawShielded ; event = event ; resolved = resolved ; finalState = final }
  ... | refl | contractWithdrawal = record
    { curve = c ; operation = withdrawToContract ; event = event ; resolved = resolved ; finalState = final }
  accepted-spend event (depositedUnshielded d) resolved with trans (sym (S.Dispatched.resolved d)) resolved
  ... | ()
  accepted-spend event (depositedShielded d) resolved with trans (sym (S.Dispatched.resolved d)) resolved
  ... | ()
  accepted-spend event (recoverySubmitted d _ _ _ _) resolved with trans (sym (S.Dispatched.resolved d)) resolved
  ... | ()
  accepted-spend event (recoveryFinalised d _) resolved with trans (sym (S.Dispatched.resolved d)) resolved
  ... | ()

certify-spend : ∀ {c op s t} (event : CommittedOccurrence s t) →
  Resolved event (Runtime.grant c op) → Spend s t
certify-spend event resolved with SP.accepted-call (CommittedOccurrence.environment event)
  (CommittedOccurrence.call event) (CommittedOccurrence.executed event)
... | _ , certificate , _ = accepted-spend event certificate resolved

private
  Retained : Value → Issuance → ℕ → State → Set
  Retained id identity lower s = ∀ g → lookupMap id (fields (cell "grants" s)) ≡ just g →
    grantActive g ≡ bool true → issuanceOf id g ≡ identity × lower ≤ number (grantNonce g)

  settled-identity : ∀ id {g n commitment updated} → SettledRecord g n commitment updated →
    issuanceOf id updated ≡ issuanceOf id g
  settled-identity id F rewrite SettledRecord.epochKept F | SettledRecord.generationKept F |
    SettledRecord.issuedKept F = refl

  retained-frame : ∀ {id identity lower s t} → cell "grants" t ≡ cell "grants" s →
    Retained id identity lower s → Retained id identity lower t
  retained-frame {id} frame retained g found = retained g
    (trans (sym (cong (λ v → lookupMap id (fields v)) frame)) found)

  retained-other : ∀ {id target updated identity lower s t} →
    cell "grants" t ≡ tuple (insertMap id updated (fields (cell "grants" s))) → target ≢ id →
    Retained target identity lower s → Retained target identity lower t
  retained-other {id} {target} {updated} {s = s} installed different retained g found = retained g
    (trans (sym (trans (cong (λ v → lookupMap target (fields v)) installed)
      (H.map-insert-other target id updated (fields (cell "grants" s)) different))) found)

  retained-effect : ∀ {s t id identity lower} (effect : GrantEffect s t) →
    H.NoMatchingIssue id effect → Retained id identity lower s → Retained id identity lower t
  retained-effect {s} {t} (kept frame) _ = retained-frame {s = s} {t = t} frame
  retained-effect {s} {t} {id} (grantIssued xs source frame issued) different retained =
    retained-other {s = source} {t = t} (IssueResult.installed issued) different
      (retained-frame {s = s} {t = source} frame retained)
  retained-effect {s} {t} {id} (grantRevoked target source frame revoked) _ retained
    with equal id target in same
  ... | true with G.equal-sound id target same
  ... | refl = λ g found active → ⊥-elim
    (H.disabled-inactive-insert {s = source} {t = t} (RevokeResult.installed revoked)
      (H.revoked-inactive (RevokeResult.old revoked) (RevokeResult.active revoked)) g found active)
  retained-effect {s} {t} {id} (grantRevoked target source frame revoked) _ retained | false =
    retained-other {s = source} {t = t} (RevokeResult.installed revoked) (H.false-equal-different same)
      (retained-frame {s = s} {t = source} frame retained)
  retained-effect {id = id} (cleared empty) _ retained g found active
    with trans (sym (cong (λ v → lookupMap id (fields v)) empty)) found
  ... | ()
  retained-effect {s} {t} {id} (grantSpent c op ctx ga xs w mutation) _ retained
    with equal id (identifier (SpendMutation.evidence mutation)) in same
  ... | false = retained-other {s = s} {t = t} (SpendMutation.installed mutation)
    (H.false-equal-different same) retained
  ... | true with G.equal-sound id (identifier (SpendMutation.evidence mutation)) same
  ... | refl = advance
    where
    E = SpendMutation.evidence mutation
    F = G.settled-record (grantRecord E) (suc (number (grantNonce (grantRecord E))))
      (Settlement.commitment (settlement E)) (LiveGrant.active (live E))
    previous = retained (grantRecord E) (EP.lookup-found "grants" (identifier E) (recorded E))
      (LiveGrant.active (live E))
    advance : Retained (identifier E) _ _ t
    advance g found active with just-injective (trans (sym found)
      (trans (cong (λ v → lookupMap (identifier E) (fields v)) (SpendMutation.installed mutation))
        (H.map-insert-same (identifier E) (SpendMutation.settledValue mutation) (fields (cell "grants" s)))))
    ... | refl = trans (settled-identity (identifier E) F) (proj₁ previous) ,
      subst (λ n → _ ≤ n) (sym (cong number (SettledRecord.nonceSet F)))
        (≤-trans (proj₂ previous) (n≤1+n _))

  accepted-no-issue : ∀ env call {s x t u es requests id}
    {executed : Account.Transition P (executionContext address env) (RuntimeCall.request call)
      s (Account.committed x es) t} {rest : Runs.Trace t u} →
    (E : AcceptedCall env call s x t es requests) →
    (ReissuedIn id (Runs.event env call (Account.committed x es) executed ◅ rest) → ⊥) →
    H.NoMatchingIssue id (H.accepted-grant-effect env call E)
  accepted-no-issue env call (activated _ _ _) absent = tt
  accepted-no-issue env call (deviceAuthorised c withdrawUnshielded d E v e) absent = tt
  accepted-no-issue env call (deviceAuthorised c withdrawShielded d E v e) absent = tt
  accepted-no-issue env call (deviceAuthorised c withdrawToContract d E v e) absent = tt
  accepted-no-issue env call (deviceAuthorised c appendInbox d E v e) absent = tt
  accepted-no-issue env call (deviceAuthorised c rotateEncKey d E v e) absent = tt
  accepted-no-issue env call (deviceAuthorised c addDevice d E v e) absent = tt
  accepted-no-issue env call (deviceAuthorised c removeDevice d E v e) absent = tt
  accepted-no-issue env call (deviceAuthorised c issueGrant d E v e) absent same =
    absent (issuedHere (S.Dispatched.resolved d) (sym same))
  accepted-no-issue env call (deviceAuthorised c revokeGrant d E v e) absent = tt
  accepted-no-issue env call (deviceAuthorised c revokeAllGrants d E v e) absent = tt
  accepted-no-issue env call (deviceAuthorised c publishRecovery d E v e) absent = tt
  accepted-no-issue env call (deviceAuthorised c cancelRecovery d E v e) absent = tt
  accepted-no-issue env call (grantAuthorised c withdrawUnshielded d unshieldedWithdrawal E v e) absent = tt
  accepted-no-issue env call (grantAuthorised c withdrawShielded d shieldedWithdrawal E v e) absent = tt
  accepted-no-issue env call (grantAuthorised c withdrawToContract d contractWithdrawal E v e) absent = tt
  accepted-no-issue env call (depositedUnshielded _) absent = tt
  accepted-no-issue env call (depositedShielded _) absent = tt
  accepted-no-issue env call (recoverySubmitted _ _ _ _ _) absent = tt
  accepted-no-issue env call (recoveryFinalised _ _) absent = tt

  retained-history : ∀ {s t id identity lower} (trace : Runs.Trace s t) →
    (ReissuedIn id trace → ⊥) → Retained id identity lower s → Retained id identity lower t
  retained-history ε absent retained = retained
  retained-history (Runs.event env call (Account.reverted error) executed ◅ rest) absent retained
    with H.reverted-state executed
  ... | refl = retained-history rest (λ issue → absent (issuedLater issue)) retained
  retained-history (Runs.event env call (Account.committed x es) executed ◅ rest) absent retained
    with SP.accepted-call env call executed
  ... | _ , E , _ = retained-history rest (λ issue → absent (issuedLater issue))
    (retained-effect (H.accepted-grant-effect env call E)
      (accepted-no-issue env call {executed = executed} {rest = rest} E absent) retained)

  spent-retained : ∀ {s t} (old : Spend s t) →
    Retained (Spend.identifier old) (Spend.issuance old) (suc (Spend.nonce old)) t
  spent-retained old g found active with just-injective
    (trans (sym found) (GrantFinalState.storedGrant (Spend.finalState old)))
  ... | refl = settled-identity (Spend.identifier old) (GrantFinalState.storedFields F) ,
    subst (λ n → suc (Spend.nonce old) ≤ n)
      (sym (cong number (SettledRecord.nonceSet (GrantFinalState.storedFields F)))) ≤-refl
    where F = Spend.finalState old

spend-message : ∀ {s t} (spend : Spend s t) →
  Σ Value λ d → encode (Spend.signingKey spend) (Spend.request spend) ≡ just d
spend-message {s} spend = signedDigest checked ,
  Binding.authorisation-message (Spend.curve spend) true (Spend.operation spend)
    (self (Spend.context spend)) (Spend.auth spend) _ (Spend.nonce spend)
    (Run.execution (challenged E)) checked
  where
  E = Spend.evidence spend
  checked = Binding.verification-evidence (Spend.curve spend) (Spend.auth spend)
    (challengeValue E) "invalid grant signature"
    (succeeded tt s (Run.journal (verified E)) (Run.execution (verified E)))

same-issuance-nonce : ∀ {s first later final} (old : Spend s first) (trace : Runs.Trace first later)
  (next : Spend later final) → SameIssuance old trace next →
  Spend.issuance next ≡ Spend.issuance old × Spend.nonce old < Spend.nonce next
same-issuance-nonce {later = later} old trace next (absent , same) =
  subst (λ id → issuanceOf id (Spend.recordValue next) ≡ Spend.issuance old ×
    Spend.nonce old < Spend.nonce next) (sym same)
    (retained-history trace absent (spent-retained old) (Spend.recordValue next)
      (subst (λ id → lookupMap id (fields (cell "grants" later)) ≡ just (Spend.recordValue next)) same
        (EP.lookup-found "grants" (Spend.identifier next) (recorded (Spend.evidence next))))
      (LiveGrant.active (live (Spend.evidence next))))

historical-request-separated : ∀ {s first later final} (old : Spend s first) (trace : Runs.Trace first later)
  (next : Spend later final) → SameIssuance old trace next → nonceView (Spend.request old) ≢ nonceView (Spend.request next)
historical-request-separated old trace next same equality =
  <-irrefl (just-injective equality) (proj₂ (same-issuance-nonce old trace next same))

historical-signature-replay-excluded : ∀ {s first later final} (old : Spend s first)
  (trace : Runs.Trace first later) (next : Spend later final) → SameIssuance old trace next →
  RelevantRequestBinding (Spend.signingKey old) (Spend.request old) (Spend.signingKey next) (Spend.request next) →
  SignatureTokenInterpretation old next → SameSignature old next → ⊥
historical-signature-replay-excluded old trace next same binding interpretation reused =
  historical-request-separated old trace next same (binding (proj₁ reused) (interpretation reused))

module SymbolicReplay (ownership : Key → Signing.Ownership) where
  open Symbolic ownership
  private module Provenance = Binding.Provenance ownership

  historical-token-replay-excluded : ∀ {s first later final} (old : Spend s first)
    (trace : Runs.Trace first later) (next : Spend later final) → SameIssuance old trace next →
    RelevantRequestBinding (Spend.signingKey old) (Spend.request old) (Spend.signingKey next) (Spend.request next) →
    token (Spend.signingKey old) (Spend.request old) ≢ token (Spend.signingKey next) (Spend.request next)
  historical-token-replay-excluded old trace next same binding equality =
    historical-request-separated old trace next same
      (binding (cong Signatures.Token.key equality) (cong Signatures.Token.message equality))

  -- Availability is deliberately not exclusion: a later independently authorized
  -- token can remain available alongside the retained old one.
  later-token-provenance : ∀ {s t knowledge} (next : Spend s t) →
    (trace : Signatures.Trace Signatures.initial knowledge) →
    (d : Value) → encode (Spend.signingKey next) (Spend.request next) ≡ just d →
    IssuedAgreement nonceView trace (Spend.signingKey next) d (Spend.request next) →
    Signatures.Available knowledge (token (Spend.signingKey next) (Spend.request next)) →
    Signatures.Controlled knowledge (Spend.signingKey next) ⊎
    Σ (Signatures.HonestlyIssued trace (token (Spend.signingKey next) (Spend.request next))) λ issued →
      nonceView (Signatures.HonestlyIssued.request issued) ≡ just (Spend.nonce next)
  later-token-provenance next trace d encoded agreement =
    Provenance.request-provenance nonceView encoded trace agreement

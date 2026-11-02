{-# OPTIONS --safe --without-K #-}

open import Conformance.Primitives
import Conformance.RecoveryAuthorityDefinitions

-- Implements RecoveryAuthority from the local Safe and policy predicates.
-- Program preservation below uses RecoveryExecutionProof's shared
-- successful-run facts for authorisation and recovery, then lifts to admission
-- traces without making their policy part of transaction validity.
module Conformance.RecoveryAuthorityProof (P : Primitives)
  (self : Primitives.Bytes32 P) (Compromised : Primitives.Point P → Set)
  (separation : Conformance.RecoveryAuthorityDefinitions.KeySeparation P self Compromised) where

open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe.Base using (nothing; just)
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Conformance.AccountLedger P
open import Conformance.Custody P self
open import Conformance.Recovery P self
open import Conformance.RecoveryAuthorityDefinitions P self Compromised
open import Conformance.RecoveryExecutionDefinitions P self
import Conformance.RecoveryExecutionProof P self as Execution
import Passport.AccountRecovery P self as Account
open Account using (module Chain)
open Chain using (Admissions; done; next)
open import Midnight.ContractDSL.Program accountLedger Assertion
open import Midnight.ContractDSL.Hoare accountLedger Assertion
import Midnight.ContractDSL.AdmissionProperties accountLedger Assertion Account.contract as Admission

open Primitives P

private variable
  A B : Set
  s t : State
  entry : Bytes32

------------------------------------------------------------------------
-- Authority facts and primitive preservation
------------------------------------------------------------------------

member-safe : ∀ {xs} → All EntrySafe xs → entry ∈ᵇ xs ≡ true → EntrySafe entry
member-safe [] ()
member-safe {entry = entry} {xs = x ∷ xs} (fresh ∷ rest) known with entry ≟ᴮ x
... | yes refl = fresh
... | no _ = member-safe rest known

point-safe : ∀ pk epoch counter → ¬ Compromised pk → EntrySafe (deviceEntry self pk epoch counter)
point-safe pk epoch counter honest q e c compromised collision =
  honest (subst Compromised (sym (separation pk q epoch e counter c collision)) compromised)

member-honest : ∀ pk epoch counter → Safe s →
  deviceEntry self pk epoch counter ∈ᵇ devices s ≡ true → ¬ Compromised pk
member-honest pk epoch counter pre known compromised =
  member-safe (devicesSafe pre) known pk epoch counter compromised refl

insert-safe : ∀ {xs} → EntrySafe entry → All EntrySafe xs → All EntrySafe (insertSet entry xs)
insert-safe {entry = entry} {xs = xs} fresh pre with entry ∈ᵇ xs
... | false = fresh ∷ pre
... | true = pre

remove-safe : ∀ {xs} → All EntrySafe xs → All EntrySafe (removeSet entry xs)
remove-safe [] = []
remove-safe {entry = entry} {xs = x ∷ xs} (fresh ∷ rest) with entry ≟ᴮ x
... | yes _ = remove-safe rest
... | no _ = fresh ∷ remove-safe rest

-- Submission writes its pending flag before its entry. The intermediate
-- state need not satisfy Safe; submission/cancellation use complete-run facts.
WriteSafe : ∀ {k} → Op k → Set
WriteSafe (insertDevice e) = EntrySafe e
WriteSafe (writePendingEntry e) = EntrySafe e
WriteSafe (writePending true) = ⊥
WriteSafe _ = ⊤

bounded-safe : ∀ bound n update {x t} → (∀ m → Safe (update m)) →
  bounded bound n update ≡ inj₂ (x , t) → Safe t
bounded-safe bound n update preserves eq with n <ᵇ bound
... | false with eq
...   | ()
bounded-safe bound n update preserves refl | true = preserves n

prepare-safe : ∀ {k} (o : Op k) {s x t} → WriteSafe o → Safe s →
  prepare o s ≡ inj₂ (x , t) → Safe t
prepare-safe readNonce _ pre refl = pre
prepare-safe readRound _ pre refl = pre
prepare-safe readEpoch _ pre refl = pre
prepare-safe readDeviceCount _ pre refl = pre
prepare-safe readVetoWindow _ pre refl = pre
prepare-safe readNotBefore _ pre refl = pre
prepare-safe readPending _ pre refl = pre
prepare-safe (deviceMember _) _ pre refl = pre
prepare-safe (balanceMember _) _ pre refl = pre
prepare-safe (readBalance c) {s} _ pre eq with lookup c (balances s)
... | nothing with eq
...   | ()
prepare-safe (readBalance c) _ pre refl | just _ = pre
prepare-safe readRecoveryPk _ pre refl = pre
prepare-safe readPendingRecoveryPk _ pre refl = pre
prepare-safe readSession _ pre refl = pre
prepare-safe readPendingEntry _ pre refl = pre
prepare-safe (writeBalance c n) {s} _ pre eq =
  bounded-safe uint128 n (λ m → record s { balances = insertMap c m (balances s) })
    (λ _ → safe (devicesSafe pre) (pendingSafe pre)) eq
prepare-safe (insertDevice e) fresh pre refl = safe (insert-safe fresh (devicesSafe pre)) (pendingSafe pre)
prepare-safe (removeDevice e) _ pre refl = safe (remove-safe (devicesSafe pre)) (pendingSafe pre)
prepare-safe resetDevices _ pre refl = safe [] (pendingSafe pre)
prepare-safe (setEncKey _) _ pre refl = safe (devicesSafe pre) (pendingSafe pre)
prepare-safe (writeNonce n) {s} _ pre eq =
  bounded-safe uint64 n (λ m → record s { authNonce = m })
    (λ _ → safe (devicesSafe pre) (pendingSafe pre)) eq
prepare-safe (writeRound n) {s} _ pre eq =
  bounded-safe uint64 n (λ m → record s { round = m })
    (λ _ → safe (devicesSafe pre) (pendingSafe pre)) eq
prepare-safe (writeEpoch n) {s} _ pre eq =
  bounded-safe uint32 n (λ m → record s { deviceEpoch = m })
    (λ _ → safe (devicesSafe pre) (pendingSafe pre)) eq
prepare-safe (writeDeviceCount n) {s} _ pre eq =
  bounded-safe uint8 n (λ m → record s { deviceCount = m })
    (λ _ → safe (devicesSafe pre) (pendingSafe pre)) eq
prepare-safe (writeNotBefore n) {s} _ pre eq =
  bounded-safe uint64 n (λ m → record s { pendingNotBefore = m })
    (λ _ → safe (devicesSafe pre) (pendingSafe pre)) eq
prepare-safe (writePhiLen n) {s} _ pre eq =
  bounded-safe uint8 n (λ m → record s { phiLen = m })
    (λ _ → safe (devicesSafe pre) (pendingSafe pre)) eq
prepare-safe (writeRecoveryPk _) _ pre refl = safe (devicesSafe pre) (pendingSafe pre)
prepare-safe (writePendingRecoveryPk _) _ pre refl = safe (devicesSafe pre) (pendingSafe pre)
prepare-safe (writeSession _) _ pre refl = safe (devicesSafe pre) (pendingSafe pre)
prepare-safe (writePendingEntry _) fresh pre refl = safe (devicesSafe pre) (λ _ → fresh)
prepare-safe (writePending false) _ pre refl = safe (devicesSafe pre) (λ ())
prepare-safe (writePending true) () pre eq
prepare-safe (insertPhi1 _) _ pre refl = safe (devicesSafe pre) (pendingSafe pre)
prepare-safe (insertPhi2 _) _ pre refl = safe (devicesSafe pre) (pendingSafe pre)
prepare-safe (insertPhi3 _) _ pre refl = safe (devicesSafe pre) (pendingSafe pre)
prepare-safe (insertPhi4 _) _ pre refl = safe (devicesSafe pre) (pendingSafe pre)
prepare-safe (writeWrap _) _ pre refl = safe (devicesSafe pre) (pendingSafe pre)

------------------------------------------------------------------------
-- Program preservation
------------------------------------------------------------------------

-- Retain the program index for inference: onSuccess is not injective.
record Keeps (p : Program A) : Set where
  constructor keeps
  field preservation : Hoare Safe p (onSuccess (λ r → Safe (working r)))
open Keeps

keeps-from-success : (p : Program A) →
  (∀ {s a t j} → Safe s → eval p s ≡ inj₂ (finished a t j) → Safe t) → Keeps p
preservation (keeps-from-success p preserved) s pre with eval p s in evaluated
... | inj₁ _ = tt
... | inj₂ (finished a t j) = preserved pre evaluated

keeps-result : ∀ {p : Program A} → Keeps p →
  ∀ {s a t j} → Safe s → eval p s ≡ inj₂ (finished a t j) → Safe t
keeps-result {p = p} preserves {s} pre evaluated =
  subst (onSuccess (λ r → Safe (working r))) evaluated (preservation preserves s pre)

ledger-keeps : ∀ {k} (o : Op k) → WriteSafe o → Keeps (perform (ledger o))
ledger-keeps o fresh = keeps (hoare-ledger {Q = onSuccess (λ r → Safe (working r))}
  o (λ _ _ _ _ → tt) (λ s x t pre prepared → prepare-safe o fresh pre prepared))

assert-keeps : ∀ b error → Keeps (assert b error)
assert-keeps b error = keeps (hoare-assert {Q = onSuccess (λ r → Safe (working r))}
  b error (λ _ _ _ → tt) (λ s pre _ → pre))

bind-keeps : (p : Program A) (f : A → Program B) → Keeps p →
  (∀ a → Keeps (f a)) → Keeps (p >>= f)
bind-keeps p f hp hf = keeps (hoare-bind
  {R = onSuccess (λ r → Safe (working r))} {Q = onSuccess (λ r → Safe (working r))}
  p f (preservation hp) (λ _ _ → tt) rest)
  where
  rest : ∀ a js → Hoare (λ u → Safe u) (f a)
    (λ outcome → onSuccess (λ r → Safe (working r)) (prefixJournal js outcome))
  rest a js u pre with eval (f a) u | preservation (hf a) u pre
  ... | inj₁ _ | _ = tt
  ... | inj₂ _ | preserved = preserved

then-keeps : (p : Program A) (q : Program B) → Keeps p → Keeps q → Keeps (p >> q)
then-keeps p q hp hq = bind-keeps p (λ _ → q) hp (λ _ → hq)

live-keeps : ∀ pk → Keeps (requireLive pk)
live-keeps pk = then-keeps _ _ (assert-keeps _ _) (assert-keeps _ _)

authorise-keeps : ∀ a challenge → Keeps (authorise a challenge)
authorise-keeps a challenge = keeps-from-success _ λ {s} pre eq →
  case-authorisation s pre eq (Execution.authorisation-details a challenge eq)
  where
  case-authorisation : ∀ s → Safe s → ∀ {result t j} →
    eval (authorise a challenge) s ≡ inj₂ (finished result t j) →
    deviceEntry self (pk a) (deviceEpoch s) (useCounter a) ∈ᵇ devices s ≡ true ×
    t ≡ authorisationState s a × j ≡ authorisationJournal s a → Safe t
  case-authorisation s pre eq (known , refl , journal) = safe
    (insert-safe (point-safe (pk a) (deviceEpoch s) (suc (useCounter a))
      (member-honest (pk a) (deviceEpoch s) (useCounter a) pre known))
      (remove-safe (devicesSafe pre))) (pendingSafe pre)

bump-round-keeps : Keeps bumpRound
bump-round-keeps = bind-keeps _ _ (ledger-keeps readRound tt) λ n →
  ledger-keeps (writeRound (suc n)) tt

credit-keeps : ∀ c amount → Keeps (credit c amount)
credit-keeps c amount = bind-keeps _ _ (ledger-keeps (balanceMember c) tt) λ
  { true → bind-keeps _ _ (ledger-keeps (readBalance c) tt) λ n →
      ledger-keeps (writeBalance c (n + amount)) tt
  ; false → ledger-keeps (writeBalance c amount) tt }

withdraw-keeps : ∀ c amount → Keeps (doWithdraw c amount)
withdraw-keeps c amount = bind-keeps _ _ (ledger-keeps (balanceMember c) tt) λ present →
  then-keeps _ _ (assert-keeps _ _)
    (bind-keeps _ _ (ledger-keeps (readBalance c) tt) λ n →
      then-keeps _ _ (assert-keeps _ _) (ledger-keeps (writeBalance c (n ∸ amount)) tt))

deposit-keeps : ∀ c amount → Keeps (deposit c amount)
deposit-keeps c amount = then-keeps _ _ (credit-keeps c amount) bump-round-keeps

add-keeps : ∀ e → EntrySafe e → Keeps (doAddDevice e)
add-keeps e fresh = bind-keeps _ _ (ledger-keeps (deviceMember e) tt) λ present →
  then-keeps _ _ (assert-keeps _ _)
    (then-keeps _ _ (ledger-keeps (insertDevice e) fresh)
      (bind-keeps _ _ (ledger-keeps readDeviceCount tt) λ n →
        ledger-keeps (writeDeviceCount (suc n)) tt))

remove-keeps : ∀ e pk uc → Keeps (doRemoveDevice e pk uc)
remove-keeps e pk uc = bind-keeps _ _ (ledger-keeps readEpoch tt) λ epoch →
  bind-keeps _ _ (ledger-keeps readDeviceCount tt) λ n →
  then-keeps _ _ (assert-keeps _ _) (then-keeps _ _ (assert-keeps _ _)
    (bind-keeps _ _ (ledger-keeps (deviceMember e) tt) λ present →
      then-keeps _ _ (assert-keeps _ _)
        (then-keeps _ _ (ledger-keeps (removeDevice e) tt) (ledger-keeps (writeDeviceCount (pred n)) tt))))

publish-keeps : ∀ args → Keeps (doPublish args)
publish-keeps (publishArgs pk nonce phi@(phi₁ , phi₂ , phi₃ , phi₄) len wrap) =
  bind-keeps _ _ (ledger-keeps readPending tt) λ pend →
  then-keeps _ _ (assert-keeps _ _) (then-keeps _ _ (assert-keeps _ _)
  (then-keeps _ _ (assert-keeps _ _) (then-keeps _ _ (assert-keeps _ _)
  (then-keeps _ _ (assert-keeps _ _) (then-keeps _ _ (assert-keeps _ _)
  (then-keeps _ _ (assert-keeps _ _)
    (bind-keeps _ _ (ledger-keeps readSession tt) λ stored →
      then-keeps _ _ (assert-keeps _ _)
        (bind-keeps _ _ (ledger-keeps readRecoveryPk tt) λ current →
          then-keeps _ _ (assert-keeps _ _)
            (then-keeps _ _ (live-keeps pk)
              (then-keeps _ _ (ledger-keeps (writeRecoveryPk pk) tt)
              (then-keeps _ _ (ledger-keeps (writeSession nonce) tt)
              (then-keeps _ _ (ledger-keeps (insertPhi1 phi₁) tt)
              (then-keeps _ _ (ledger-keeps (insertPhi2 phi₂) tt)
              (then-keeps _ _ (ledger-keeps (insertPhi3 phi₃) tt)
              (then-keeps _ _ (ledger-keeps (insertPhi4 phi₄) tt)
              (then-keeps _ _ (ledger-keeps (writePhiLen len) tt)
                (ledger-keeps (writeWrap wrap) tt)))))))))))))))))

cancel-keeps : Keeps doCancel
cancel-keeps = keeps-from-success _ preserved
  where
  preserved : ∀ {s result t j} → Safe s → eval doCancel s ≡ inj₂ (finished result t j) → Safe t
  preserved pre eq with Execution.cancellation-shape eq
  ... | refl = safe (devicesSafe pre) (λ ())

submit-keeps : ∀ a → ¬ Compromised (SubmitArgs.successorPk a) → Keeps (submitRecovery a)
submit-keeps a honest = keeps-from-success _ preserved
  where
  preserved : ∀ {s result t j} → Safe s →
    eval (submitRecovery a) s ≡ inj₂ (finished result t j) → Safe t
  preserved {s} pre eq with Execution.submission-shape {s = s} {a = a} eq
  ... | refl , journal = safe (devicesSafe pre)
    (λ _ → point-safe (SubmitArgs.successorPk a) (suc (deviceEpoch s)) 0 honest)

finalise-reset : ∀ {s a t j} → EntrySafe (pendingEntry s) →
  eval (finaliseRecovery corrected) s ≡ inj₂ (finished a t j) → Safe t
finalise-reset fresh eq with Execution.finalisation-shape eq
... | refl , journal = safe (fresh ∷ []) (λ ())

finalise-has-pending : ∀ {s result t j} →
  eval (finaliseRecovery corrected) s ≡ inj₂ (finished result t j) → pending s ≡ true
finalise-has-pending eq = FinalisationReady.hasPending (proj₁ (Execution.finalisation-details eq))

finalise-keeps : Keeps (finaliseRecovery corrected)
finalise-keeps = keeps-from-success _ λ {s} pre eq →
  finalise-reset {s = s} (pendingSafe pre (finalise-has-pending eq)) eq

------------------------------------------------------------------------
-- Contract admission and traces
------------------------------------------------------------------------

-- Keep the circuit case split explicit: it is the link to the executable
-- account, rather than an independently specified transition automaton.
circuit-keeps : ∀ n a → InputPolicy n a → Keeps (Account.circuit corrected n a)
circuit-keeps Account.depositUnshielded (c , amount) _ = deposit-keeps c amount
circuit-keeps Account.recoverSubmit a honest = submit-keeps a honest
circuit-keeps Account.recoverFinalise _ _ = finalise-keeps
circuit-keeps (Account.jubjub Account.withdrawUnshielded) ((c , amount , recipient) , a) _ =
  then-keeps _ _ (authorise-keeps a (Account.challengeOf Account.withdrawUnshielded (c , amount , recipient))) (withdraw-keeps c amount)
circuit-keeps (Account.jubjub Account.addDevice) (e , a) fresh =
  then-keeps _ _ (authorise-keeps a (Account.challengeOf Account.addDevice e)) (add-keeps e fresh)
circuit-keeps (Account.jubjub Account.removeDevice) (e , a) _ =
  then-keeps _ _ (authorise-keeps a (Account.challengeOf Account.removeDevice e)) (remove-keeps e (pk a) (useCounter a))
circuit-keeps (Account.jubjub Account.rotateEncKey) (k , a) _ =
  then-keeps _ _ (authorise-keeps a (Account.challengeOf Account.rotateEncKey k)) (ledger-keeps (setEncKey k) tt)
circuit-keeps (Account.jubjub Account.publishRecoverySession) (args , a) _ =
  then-keeps _ _ (authorise-keeps a (Account.challengeOf Account.publishRecoverySession args)) (publish-keeps args)
circuit-keeps (Account.jubjub Account.recoverCancel) (_ , a) _ =
  then-keeps _ _ (authorise-keeps a (Account.challengeOf Account.recoverCancel tt)) cancel-keeps

circuit-safe : ∀ n a → InputPolicy n a → ∀ {s result t j} → Safe s →
  eval (Account.circuit corrected n a) s ≡ inj₂ (finished result t j) → Safe t
circuit-safe n a policy = keeps-result (circuit-keeps n a policy)

admission-safe : ∀ q → TransactionPolicy (Chain.Submission.transaction q) → Safe s →
  ∀ {t v} → Chain.admit s q ≡ (t , v) → Safe t
admission-safe q policy pre {v = Chain.rejected} admitted =
  subst Safe (sym (Admission.rejection-atomic q _ _ admitted)) pre
admission-safe q policy pre {v = Chain.accepted} admitted =
  circuit-safe _ _ policy pre (proj₂ (Admission.accepted-execution q _ _ admitted))

trace-safe : ∀ {s t} (trace : Admissions s t) → TracePolicy trace → Safe s → SafeAdmissions trace
trace-safe done policy-done pre = all-done pre
trace-safe (next q v admitted rest) (policy-next policy policies) pre =
  all-next pre (trace-safe rest policies (admission-safe q policy pre admitted))

safe-endpoint : ∀ {s t} {trace : Admissions s t} → SafeAdmissions trace → Safe t
safe-endpoint (all-done pre) = pre
safe-endpoint (all-next pre rest) = safe-endpoint rest

trace-endpoint-safe : ∀ {s t} (trace : Admissions s t) → TracePolicy trace → Safe s → Safe t
trace-endpoint-safe trace policy pre = safe-endpoint (trace-safe trace policy pre)

authority-excluded : ∀ pk counter → Safe s → Compromised pk → ¬ DeviceAuthority s pk counter
authority-excluded pk counter pre compromised known =
  member-honest pk _ counter pre known compromised

trace-authority-excluded : ∀ {s t} (trace : Admissions s t) → TracePolicy trace → Safe s →
  ∀ pk counter → Compromised pk → ¬ DeviceAuthority t pk counter
trace-authority-excluded trace policy pre pk counter =
  authority-excluded pk counter (trace-endpoint-safe trace policy pre)


authorise-needs-membership : ∀ a challenge {s result t j} →
  eval (authorise a challenge) s ≡ inj₂ (finished result t j) →
  DeviceAuthority s (pk a) (useCounter a)
authorise-needs-membership a challenge ev = proj₁ (Execution.authorisation-details a challenge ev)

gated-needs-membership : ∀ g p a {s result t j} →
  eval (Account.gated g p a) s ≡ inj₂ (finished result t j) →
  DeviceAuthority s (pk a) (useCounter a)
gated-needs-membership g p a ev
  with bind-success (authorise a (Account.challengeOf g p)) _ _ ev
... | head , es , headEval , tailEval , joined = authorise-needs-membership a (Account.challengeOf g p) headEval

trace-compromised-call-impossible : ∀ {s t} (trace : Admissions s t) → TracePolicy trace → Safe s →
  ∀ g p a → Compromised (pk a) → ∀ {result u j} →
  eval (Account.gated g p a) t ≡ inj₂ (finished result u j) → ⊥
trace-compromised-call-impossible trace policy pre g p a compromised ev =
  trace-authority-excluded trace policy pre (pk a) (useCounter a) compromised
    (gated-needs-membership g p a ev)

recovery-trace-exclusion : ∀ {s recovered t result j} → EntrySafe (pendingEntry s) →
  eval (finaliseRecovery corrected) s ≡ inj₂ (finished result recovered j) →
  (trace : Admissions recovered t) → TracePolicy trace →
  ∀ pk counter → Compromised pk → ¬ DeviceAuthority t pk counter
recovery-trace-exclusion fresh recovered trace policy =
  trace-authority-excluded trace policy (finalise-reset fresh recovered)

finalisation-program : (n : Account.Name) (a : Account.Input n) →
  n ≡ Account.recoverFinalise → Account.circuit corrected n a ≡ finaliseRecovery corrected
finalisation-program Account.recoverFinalise _ refl = refl

accepted-finalisation-reset : ∀ now tx {s recovered} →
  Chain.Transaction.entry tx ≡ Account.recoverFinalise →
  EntrySafe (pendingEntry s) →
  Chain.admit s (Chain.submit now tx) ≡ (recovered , Chain.accepted) → Safe recovered
accepted-finalisation-reset now tx {s} isFinalisation fresh admitted =
  finalise-reset fresh (trans (cong (λ p → eval p s)
    (sym (finalisation-program (Chain.Transaction.entry tx)
      (Chain.Transaction.input tx) isFinalisation)))
    (proj₂ (Admission.accepted-execution (Chain.submit now tx) s _ admitted)))

accepted-recovery-trace-exclusion : ∀ now tx {s recovered t} →
  Chain.Transaction.entry tx ≡ Account.recoverFinalise →
  EntrySafe (pendingEntry s) →
  Chain.admit s (Chain.submit now tx) ≡ (recovered , Chain.accepted) →
  (trace : Admissions recovered t) → TracePolicy trace →
  ∀ pk counter → Compromised pk → ¬ DeviceAuthority t pk counter
accepted-recovery-trace-exclusion now tx isFinalisation fresh admitted trace policy =
  trace-authority-excluded trace policy (accepted-finalisation-reset now tx isFinalisation fresh admitted)

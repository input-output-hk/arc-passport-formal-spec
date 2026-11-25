{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes using (Primitives; Value)

module Passport.DeviceRemovalProof (P : Primitives) (address : Value) where

open import Conformance.FullAccountTypes
open import Conformance.FullAccountBody P
open import Conformance.FullAccountCrypto P
open import Conformance.FullAccountDeviceSecurity P
open import Conformance.FullAccountExecution
import Conformance.FullAccountDeviceSecurityProof as DeviceProof
open import Data.Bool.Base using (Bool; true; false; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe.Base using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat.Base using (ℕ; zero; suc; _<ᵇ_; _∸_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Passport.DeviceRemoval P address
open import Passport.RevocationExclusion P address
import Passport.RevocationExclusionProof as HistoryProof
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

module D = DeviceProof P
module H = HistoryProof P address

not-true-false : ∀ b → not b ≡ true → b ≡ false
not-true-false true ()
not-true-false false _ = refl

body-removal : ∀ ctx xs coin caller {s x t} →
  Run (body removeDevice ctx xs coin caller) s x t → RemovalEffect (get 0 xs) caller s t
body-removal ctx xs coin caller {s} r with then (readCount "device_count") r
... | count , s₁ , counted , rest with D.readCount-run "device_count" counted
... | old , found , refl , refl with then (assert (1 <ᵇ number old) "cannot remove last device") rest
... | _ , s₂ , guarded , rest₂ with D.assert-run (1 <ᵇ number old) "cannot remove last device" guarded
... | enough , refl with then (assert (not (equal (get 0 xs) caller)) "cannot remove the authorising device") rest₂
... | _ , s₃ , distinct , rest₃ with D.assert-run (not (equal (get 0 xs) caller)) "cannot remove the authorising device" distinct
... | different , refl with then (has "devices" (get 0 xs))
  {f = λ present → assert present "unknown device entry" >> (exclude "devices" (get 0 xs) >>
    (readCount "device_count" >>= λ current → writeCount "device_count" 8 (current ∸ 1) >> return unit))} rest₃
... | present , s₄ , tested , rest₄ with D.has-run "devices" (get 0 xs) tested
... | refl , refl with then (assert (member (get 0 xs) (fields (cell "devices" s))) "unknown device entry") rest₄
... | _ , s₅ , guardedLive , rest₅ with D.assert-run (member (get 0 xs) (fields (cell "devices" s))) "unknown device entry" guardedLive
... | live , refl with then (exclude "devices" (get 0 xs)) rest₅
... | _ , s₆ , excluded , rest₆ with D.exclude-run "devices" (get 0 xs) excluded
... | refl with then (readCount "device_count")
  {f = λ current → writeCount "device_count" 8 (current ∸ 1) >> return unit} rest₆
... | current , s₇ , recounted , rest₇ with D.readCount-run "device_count" recounted
... | old′ , found′ , refl , refl with just-injective (trans (sym found′)
  (trans (D.lookup-insert-other "device_count" "devices"
    (tuple (removeSet (get 0 xs) (fields (cell "devices" s)))) (ledger s) refl) found))
... | refl with then (writeCount "device_count" 8 (number old ∸ 1)) rest₇
... | _ , s₈ , written , returned with D.return-run unit returned
... | refl , refl with then (cast "device_count" 8 (number old ∸ 1)) written
... | n , s₉ , casted , stored with D.cast-run "device_count" 8 (number old ∸ 1) casted
... | refl , _ , refl with D.write-run "device_count" (nat (number old ∸ 1)) stored
... | refl = record
  { targetLive = live
  ; callerDistinct = not-true-false _ different
  ; moreThanOne = subst (λ n → (1 <ᵇ n) ≡ true) (sym (H.cell-number "device_count" s found)) enough
  ; devicesRemoved = D.cell-lookup "devices" (state (insertCell "device_count" decremented excludedLedger))
      (trans (D.lookup-insert-other "devices" "device_count" decremented excludedLedger refl)
        (D.lookup-insert-same "devices" remaining (ledger s)))
  ; countWritten = trans (D.cell-insert-same "device_count" decremented excludedLedger)
      (cong (λ n → nat (n ∸ 1)) (sym (H.cell-number "device_count" s found))) }
  where
  remaining = tuple (removeSet (get 0 xs) (fields (cell "devices" s)))
  excludedLedger = insertCell "devices" remaining (ledger s)
  decremented = nat (number old ∸ 1)

-- removeDevice recomputes its caller's successor rather than trusting a cached
-- argument. Purity and the unchanged epoch connect that computation to rolling.
caller-rolled : ∀ c ctx xs {s x t} →
  (E : DeviceCall c removeDevice ctx xs s x t) → DeviceCall.callerEntry E ≡ DeviceCall.rolledEntry E
caller-rolled c ctx xs E with then (readSelf ctx)
  {f = λ addr → readCount "device_epoch" >>= λ epoch →
    cast "use_counter" 64 (suc (counter (deviceAuth c removeDevice xs))) >>=
      entryAt c addr (deviceAuth c removeDevice xs) epoch} (DeviceCall.callerEntryRun E)
... | addr , s₁ , selfRun , rest with D.readSelf-run ctx selfRun
... | refl , refl with then (readCount "device_epoch")
  {f = λ epoch → cast "use_counter" 64 (suc (counter (deviceAuth c removeDevice xs))) >>=
    entryAt c (self ctx) (deviceAuth c removeDevice xs) epoch} rest
... | epoch , s₂ , epochRun , rest₂ with D.readCount-run "device_epoch" epochRun
... | value , found , refl , refl with then (cast "use_counter" 64 (suc (counter (deviceAuth c removeDevice xs))))
  {f = entryAt c (self ctx) (deviceAuth c removeDevice xs) (number value)} rest₂
... | count , s₃ , casted , opened with D.cast-run "use_counter" 64 (suc (counter (deviceAuth c removeDevice xs))) casted
... | refl , _ , refl with just-injective (trans (sym found)
  (trans (Authorisation.unchanged (DeviceCall.authorised E) "device_epoch" refl refl refl)
    (Authorisation.epochCell (DeviceCall.authorised E))))
... | refl = H.same-answer opened (proj₂ (D.pure-run
  (D.entryAt-pure c (self ctx) (deviceAuth c removeDevice xs)
    (number (Authorisation.epoch (DeviceCall.authorised E)))
    (suc (counter (deviceAuth c removeDevice xs))))
  (Authorisation.nextEntry (DeviceCall.authorised E))) (DeviceCall.authorisedState E))

successor-larger : ∀ n → (n <ᵇ suc n) ≡ true
successor-larger zero = refl
successor-larger (suc n) = successor-larger n

predecessor-smaller : ∀ n → (1 <ᵇ n) ≡ true → ((n ∸ 1) <ᵇ n) ≡ true
predecessor-smaller zero ()
predecessor-smaller (suc n) _ = successor-larger n

device-removal-evidence : ∀ {c s t} (event : CommittedOccurrence s t) →
  DeviceCall c removeDevice (occurrenceContext event) (occurrenceArguments event)
    s (CommittedOccurrence.answer event) t → Removal c event
device-removal-evidence {c} {s} {t} event E = record
  { call = E
  ; callerIsRolled = caller-rolled c (occurrenceContext event) (occurrenceArguments event) E
  ; effect = effect
  ; targetOriginallyLive = originally-live
  ; originalCountGuard = subst (λ n → (1 <ᵇ n) ≡ true) countSame (RemovalEffect.moreThanOne effect)
  ; countDecremented = written
  ; countStrictlyDecreased = subst (λ n → (n <ᵇ counterValue "device_count" s) ≡ true)
      (sym (cong number written))
      (predecessor-smaller (counterValue "device_count" s)
        (subst (λ n → (1 <ᵇ n) ≡ true) countSame (RemovalEffect.moreThanOne effect))) }
  where
  A = DeviceCall.authorised E
  effect = subst (λ caller → RemovalEffect (removedEntry event) caller (DeviceCall.authorisedState E) t)
    (caller-rolled c (occurrenceContext event) (occurrenceArguments event) E)
    (body-removal (occurrenceContext event) (deviceArguments removeDevice (occurrenceArguments event))
      (deviceCoin removeDevice (occurrenceContext event)) (DeviceCall.callerEntry E) (DeviceCall.bodyRun E))
  countSame = H.frame-number "device_count" {s = s} {t = DeviceCall.authorisedState E}
    (Authorisation.unchanged A "device_count" refl refl refl)
  written = trans (RemovalEffect.countWritten effect) (cong (λ n → nat (n ∸ 1)) countSame)
  originally-live : member (removedEntry event) (fields (cell "devices" s)) ≡ true
  originally-live with H.inserted-membership (removedEntry event) (DeviceCall.rolledEntry E)
    (removeSet (Authorisation.current A) (fields (cell "devices" s)))
    (cell "devices" (DeviceCall.authorisedState E)) (Authorisation.devicesRolled A)
    (RemovalEffect.targetLive effect)
  ... | inj₁ previous = H.removed-membership (removedEntry event) (Authorisation.current A)
    (fields (cell "devices" s)) _ refl previous
  ... | inj₂ same = ⊥-elim (H.false-equal-different (RemovalEffect.callerDistinct effect) same)

removal-evidence : ∀ {c s t} → Runs.History s →
  (event : CommittedOccurrence s t) → Resolved event (Runtime.device c removeDevice) → Removal c event
removal-evidence history event resolved = device-removal-evidence event
  (H.DeviceBoundary.evidence (H.device-boundary history event resolved))

removed-absent : ∀ {c s t} {event : CommittedOccurrence s t} → Removal c event →
  member (removedEntry event) (fields (cell "devices" t)) ≡ false
removed-absent {event = event} E = trans
  (cong (λ ds → member (removedEntry event) (fields ds)) (RemovalEffect.devicesRemoved (Removal.effect E)))
  (D.member-removeSet (removedEntry event) (fields (cell "devices" (DeviceCall.authorisedState (Removal.call E)))))

removed-device-origin : ∀ {c s removed later} → Runs.History s →
  (event : CommittedOccurrence s removed) → Resolved event (Runtime.device c removeDevice) →
  (trace : Runs.Trace removed later) → member (removedEntry event) (fields (cell "devices" later)) ≡ true →
  IntroducedIn (removedEntry event) trace
removed-device-origin history event resolved trace live with H.history-device-origin trace live
... | inj₁ previous = ⊥-elim (H.false-not-true
  (trans (sym (removed-absent (removal-evidence history event resolved))) previous))
... | inj₂ introduced = introduced

removed-device-absent : ∀ {c s removed later} → Runs.History s →
  (event : CommittedOccurrence s removed) → Resolved event (Runtime.device c removeDevice) →
  (trace : Runs.Trace removed later) → (IntroducedIn (removedEntry event) trace → ⊥) →
  member (removedEntry event) (fields (cell "devices" later)) ≡ false
removed-device-absent {later = later} history event resolved trace noIntroduction
  with member (removedEntry event) (fields (cell "devices" later)) in live
... | false = refl
... | true = ⊥-elim (noIntroduction (removed-device-origin history event resolved trace live))

removed-device-call-excluded : ∀ {ownerCurve s removed later c op after} → Runs.History s →
  (removal : CommittedOccurrence s removed) → Resolved removal (Runtime.device ownerCurve removeDevice) →
  (trace : Runs.Trace removed later) → (IntroducedIn (removedEntry removal) trace → ⊥) →
  (device : CommittedOccurrence later after) → Resolved device (Runtime.device c op) →
  Run (entryAt c address (occurrenceAuth c op device) (counterValue "device_epoch" later)
    (counter (occurrenceAuth c op device))) later (removedEntry removal) later → ⊥
removed-device-call-excluded {later = later} {c} {op} history removal resolved trace noIntroduction device deviceResolved opening =
  noIntroduction (removed-device-origin history removal resolved trace
    (subst (λ entry → member entry (fields (cell "devices" later)) ≡ true)
      (H.same-answer (H.authorisation-opened A) opening) (Authorisation.currentLive A)))
  where
  A = DeviceCall.authorised (H.DeviceBoundary.evidence
    (H.device-boundary (H.history-after history removal trace) device deviceResolved))

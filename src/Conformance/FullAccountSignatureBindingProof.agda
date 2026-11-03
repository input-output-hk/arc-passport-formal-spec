{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

-- Proofs for Conformance.FullAccountSignatureBindingProperties. Source
-- computations are decomposed along their actual evaluation
-- (FullAccountExecution.then). Continuations are spelled out because Agda
-- cannot infer them through the evaluator's binds.
module Conformance.FullAccountSignatureBindingProof (P : Primitives) where

open import Conformance.FullAccountBody P
open import Conformance.FullAccountCrypto P
open import Conformance.FullAccountExecution using (Succeeded; succeeded; Run; run)
  renaming (then to bind-run)
open import Conformance.FullAccountSignatureBinding P
open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; drop; take)
open import Data.Maybe.Base using (just; is-just)
open import Data.Nat.Base using (ℕ; _≡ᵇ_; _≤ᵇ_; _<ᵇ_; _%_)
open import Data.Product.Base using (Σ; _×_; _,_)
open import Data.String.Base using (String) renaming (_++_ to _++ˢ_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
import Midnight.ContractDSL.SymbolicSigning as Signing
import Midnight.ContractDSL.SymbolicSigningProof as SigningProof
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

private
  rejected≢accepted : ∀ {A : Set} {e x t es} → rejected {A} e ≡ accepted x t es → ⊥
  rejected≢accepted ()

  accepted≢rejected : ∀ {A : Set} {e x t es} → accepted {A} x t es ≡ rejected e → ⊥
  accepted≢rejected ()

------------------------------------------------------------------------
-- Steps of the actual evaluator

steps : ∀ {A B : Set} (m : M A) (f : A → M B) s {y u es} → (m >>= f) s ≡ accepted y u es →
  Σ A λ x → Σ State λ t → Run m s x t × Run (f x) t y u
steps m f s executed = bind-run m {f = f} {s = s} (run _ executed)

lift-step : ∀ {A : Set} (r : Result A) {s v t es} → lift r s ≡ accepted v t es → r ≡ success v
lift-step (failure e) ()
lift-step (success x) refl = refl

lift-preserves : ∀ {A : Set} (r : Result A) {s v t es} → lift r s ≡ accepted v t es → t ≡ s
lift-preserves (failure e) ()
lift-preserves (success x) refl = refl

guard-step : ∀ b e {s v t es} → (if b then return tt else abort e) s ≡ accepted v t es → b ≡ true
guard-step true e _ = refl
guard-step false e ()

assert-step : ∀ b message {s v t es} → assert b message s ≡ accepted v t es → b ≡ true
assert-step b message = guard-step b (assertion message)

return-step : ∀ {A : Set} {x : A} {s v t es} → return x s ≡ accepted v t es → x ≡ v
return-step refl = refl

assert-runs : ∀ {b} message → b ≡ true → ∀ u → assert b message u ≡ accepted tt u []
assert-runs message refl u = refl

hash-runs : ∀ {xs v} → persistentHash P xs ≡ success v → ∀ u → hash xs u ≡ accepted v u []
hash-runs hashed u = cong (λ r → lift r u) hashed

bind-rejected : ∀ {A B : Set} (m : M A) (f : A → M B) s {e} → m s ≡ rejected e →
  (m >>= f) s ≡ rejected e
bind-rejected m f s failed with m s
... | rejected _ with failed
...   | refl = refl
bind-rejected m f s failed | accepted _ _ _ = ⊥-elim (accepted≢rejected failed)

bind-step : ∀ {A B : Set} (m : M A) (f : A → M B) s {x} (r : Result B) →
  m s ≡ accepted x s [] → f x s ≡ lift r s → (m >>= f) s ≡ lift r s
bind-step m f s {x} r first second with m s
... | rejected _ = ⊥-elim (rejected≢accepted first)
... | accepted x′ t es with first
...   | refl with f x s
...     | rejected _ = second
...     | accepted _ _ _ = second

------------------------------------------------------------------------
-- State-free computations

-- `m` acts as one primitive result: it reads and writes no ledger cell and
-- records no effects.
record Pure {A : Set} (m : M A) : Set where
  constructor pure
  field result : Result A
        runs : ∀ s → m s ≡ lift result s

lift-pure : ∀ {A : Set} (r : Result A) → Pure (lift r)
lift-pure r = pure r λ _ → refl

return-pure : ∀ {A : Set} (x : A) → Pure (return x)
return-pure x = lift-pure (success x)

guard-pure : ∀ b e → Pure (if b then return tt else abort e)
guard-pure true e = return-pure tt
guard-pure false e = lift-pure (failure e)

assert-pure : ∀ b message → Pure (assert b message)
assert-pure b message = guard-pure b (assertion message)

hash-pure : ∀ xs → Pure (hash xs)
hash-pure xs = lift-pure (persistentHash P xs)

hashTag-pure : ∀ tag → Pure (hashTag tag)
hashTag-pure tag = hash-pure (("Bytes<64>" , pad 64 tag) ∷ [])

pure-bind : ∀ {A B : Set} (m : M A) (f : A → M B) → Pure m → (∀ x → Pure (f x)) → Pure (m >>= f)
pure-bind m f (pure (failure e) runs) pf = pure (failure e) λ s → bind-rejected m f s (runs s)
pure-bind m f (pure (success x) runs) pf =
  pure (Pure.result (pf x)) λ s → bind-step m f s (Pure.result (pf x)) (runs s) (Pure.runs (pf x) s)

lift-bind-pure : ∀ {A B : Set} (r : Result A) (f : A → M B) → (∀ x → Pure (f x)) → Pure (lift r >>= f)
lift-bind-pure r f = pure-bind (lift r) f (lift-pure r)

pure-result : ∀ {A : Set} {m : M A} (p : Pure m) {s v t es} → m s ≡ accepted v t es →
  Pure.result p ≡ success v
pure-result (pure r runs) {s} executed = lift-step r (trans (sym (runs s)) executed)

pure-preserves : ∀ {A : Set} {m : M A} (p : Pure m) {s v t es} → m s ≡ accepted v t es → t ≡ s
pure-preserves (pure r runs) {s} executed = lift-preserves r (trans (sym (runs s)) executed)

pure-runs : ∀ {A : Set} {m : M A} (p : Pure m) {s v t es} → m s ≡ accepted v t es →
  ∀ u → m u ≡ accepted v u []
pure-runs p executed u = trans (Pure.runs p u) (cong (λ r → lift r u) (pure-result p executed))

pure-evaluates : ∀ {A : Set} {m : M A} (p : Pure m) {s v t es} → m s ≡ accepted v t es →
  evaluate m ≡ just v
pure-evaluates p executed = cong outcome (pure-runs p executed (state []))

bind-evaluates : ∀ {A B : Set} (m : M A) (f : A → M B) → Pure m → ∀ {s x t es y} →
  m s ≡ accepted x t es → (∀ u → f x u ≡ accepted y u []) → evaluate (m >>= f) ≡ just y
bind-evaluates m f pm {y = y} first second =
  cong outcome (bind-step m f (state []) (success y) (pure-runs pm first (state [])) (second (state [])))

------------------------------------------------------------------------
-- Operation challenges

keyAtoms-pure : ∀ c pk → Pure (keyAtoms c pk)
keyAtoms-pure jubjub pk = return-pure (jub pk ∷ [])
keyAtoms-pure k256 pk with pointCoordinates P k256 pk
... | failure e = pure (failure e) λ _ → refl
... | success (x , y) = pure (success (b32 x ∷ b32 y ∷ [])) λ _ → refl
keyAtoms-pure p256 pk with pointCoordinates P p256 pk
... | failure e = pure (failure e) λ _ → refl
... | success (x , y) = pure (success (b32 x ∷ b32 y ∷ [])) λ _ → refl

authTag : Bool → Curve → String → String
authTag grant c operation =
  "midnight:account:" ++ˢ (if grant then "grant:auth:" else "auth:") ++ˢ armTag c ++ˢ ":" ++ˢ operation

-- challengeAt for the ECDSA curves, whose preimage has no Schnorr fields.
foreignChallenge-pure : ∀ c grant operation addr a args nonce →
  Pure (hashTag (authTag grant c operation) >>= λ dst → keyAtoms c (key a) >>= λ ks →
    hash (b32 dst ∷ contract addr ∷ ks ++ args ++ u64 (nat nonce) ∷ []))
foreignChallenge-pure c grant operation addr a args nonce =
  pure-bind (hashTag (authTag grant c operation)) keyed (hashTag-pure (authTag grant c operation)) λ dst →
  pure-bind (keyAtoms c (key a)) (λ ks → hash (preimage dst ks)) (keyAtoms-pure c (key a)) λ ks →
  hash-pure (preimage dst ks)
  where
  preimage : Value → List Atom → List Atom
  preimage dst ks = b32 dst ∷ contract addr ∷ ks ++ args ++ u64 (nat nonce) ∷ []
  keyed : Value → M Value
  keyed dst = keyAtoms c (key a) >>= λ ks → hash (preimage dst ks)

challengeAt-pure : ∀ c grant operation addr a args nonce →
  Pure (challengeAt c grant operation addr a args nonce)
challengeAt-pure jubjub grant operation addr a args nonce =
  pure-bind (hashTag (authTag grant jubjub operation)) keyed (hashTag-pure (authTag grant jubjub operation)) λ dst →
  pure-bind (keyAtoms jubjub (key a)) (λ ks → hash (preimage dst ks)) (keyAtoms-pure jubjub (key a)) λ ks →
  hash-pure (preimage dst ks)
  where
  preimage : Value → List Atom → List Atom
  preimage dst ks =
    b32 dst ∷ contract addr ∷ jub (sigR a) ∷ ks ++ args ++ u64 (nat nonce) ∷ u64 (nat (grind a)) ∷ []
  keyed : Value → M Value
  keyed dst = keyAtoms jubjub (key a) >>= λ ks → hash (preimage dst ks)
challengeAt-pure k256 grant operation addr a args nonce =
  foreignChallenge-pure k256 grant operation addr a args nonce
challengeAt-pure p256 grant operation addr a args nonce =
  foreignChallenge-pure p256 grant operation addr a args nonce

challengeAt-preserves : ∀ c grant operation addr a args nonce {s h t es} →
  challengeAt c grant operation addr a args nonce s ≡ accepted h t es → t ≡ s
challengeAt-preserves c grant operation addr a args nonce =
  pure-preserves (challengeAt-pure c grant operation addr a args nonce)

------------------------------------------------------------------------
-- Schnorr (device/grant jubjub, recovery and successor signatures)

module SchnorrRun (pk R S h : Value) (message : String) where
  inRange : Bool
  inRange = le (rawBytes h) <ᵇ fieldOrder

  bounded : M ⊤
  bounded = if inRange then return tt else abort (bounds "Bytes<32> as Field" 255)

  afterScaled : Value → Value → M ⊤
  afterScaled lhs cp = lift (ecAdd P jubjub R cp) >>= λ rhs → assert (equal lhs rhs) message

  afterGenerator : Value → M ⊤
  afterGenerator lhs = lift (ecMul P jubjub pk (le (rawBytes h) % jubjubOrder)) >>= afterScaled lhs

  afterBound : M ⊤
  afterBound = lift (ecMulGenerator P jubjub (number S % jubjubOrder)) >>= afterGenerator

  evidence : ∀ {s} → Succeeded (schnorr pk R S h message) s → SchnorrAccepts pk R S h
  evidence {s} (succeeded _ _ _ executed) with steps bounded (λ _ → afterBound) s executed
  ... | _ , t₁ , run _ inside , run _ executed₁
    with steps (lift (ecMulGenerator P jubjub (number S % jubjubOrder))) afterGenerator t₁ executed₁
  ... | lhs , t₂ , run _ generated , run _ executed₂
    with steps (lift (ecMul P jubjub pk (le (rawBytes h) % jubjubOrder))) (afterScaled lhs) t₂ executed₂
  ... | scaled , t₃ , run _ multiplied , run _ executed₃
    with steps (lift (ecAdd P jubjub R scaled)) (λ rhs → assert (equal lhs rhs) message) t₃ executed₃
  ... | rhs , _ , run _ summed , run _ executed₄ = schnorrAccepts
    (guard-step inRange (bounds "Bytes<32> as Field" 255) inside) lhs scaled rhs
    (lift-step (ecMulGenerator P jubjub (number S % jubjubOrder)) generated)
    (lift-step (ecMul P jubjub pk (le (rawBytes h) % jubjubOrder)) multiplied)
    (lift-step (ecAdd P jubjub R scaled) summed)
    (assert-step (equal lhs rhs) message executed₄)

  state-free : Pure (schnorr pk R S h message)
  state-free =
    pure-bind bounded (λ _ → afterBound) (guard-pure inRange (bounds "Bytes<32> as Field" 255)) λ _ →
    lift-bind-pure (ecMulGenerator P jubjub (number S % jubjubOrder)) afterGenerator λ lhs →
    lift-bind-pure (ecMul P jubjub pk (le (rawBytes h) % jubjubOrder)) (afterScaled lhs) λ cp →
    lift-bind-pure (ecAdd P jubjub R cp) (λ rhs → assert (equal lhs rhs) message) λ rhs →
    assert-pure (equal lhs rhs) message

schnorr-evidence : ∀ pk R S h message {s} → Succeeded (schnorr pk R S h message) s →
  SchnorrAccepts pk R S h
schnorr-evidence = SchnorrRun.evidence

schnorr-preserves : ∀ pk R S h message {s v t es} → schnorr pk R S h message s ≡ accepted v t es → t ≡ s
schnorr-preserves pk R S h message = pure-preserves (SchnorrRun.state-free pk R S h message)

schnorr-accepted : ∀ pk R S h message {s} → Succeeded (schnorr pk R S h message) s →
  schnorrAccepted pk R S h message ≡ true
schnorr-accepted pk R S h message (succeeded _ _ _ executed) =
  cong is-just (pure-evaluates (SchnorrRun.state-free pk R S h message) executed)

------------------------------------------------------------------------
-- secp256k1 envelopes

module EnvelopeRun (kind : ℕ) (h : Value) where
  select : Value → Value → M Value
  select plain connector = return (if kind ≡ᵇ 1 then connector else plain)

  afterPlain : Value → M Value
  afterPlain plain = hash (connectedEnvelope h) >>= select plain

  hashes : M Value
  hashes = hash (plainEnvelope h) >>= afterPlain

  evidence : ∀ {s d t es} → envelopeDigest kind h s ≡ accepted d t es → EnvelopeDigest kind h d
  evidence {s} executed with steps (assert (kind ≤ᵇ 1) "unknown envelope") (λ _ → hashes) s executed
  ... | _ , t₁ , run _ admitted , run _ executed₁
    with steps (hash (plainEnvelope h)) afterPlain t₁ executed₁
  ... | plain , t₂ , run _ plainHashed , run _ executed₂
    with steps (hash (connectedEnvelope h)) (select plain) t₂ executed₂
  ... | connector , _ , run _ connectorHashed , run _ chosen = enveloped
    (assert-step (kind ≤ᵇ 1) "unknown envelope" admitted) plain connector
    (lift-step (persistentHash P (plainEnvelope h)) plainHashed)
    (lift-step (persistentHash P (connectedEnvelope h)) connectorHashed)
    (sym (return-step chosen))

  runs : ∀ {d} → EnvelopeDigest kind h d → ∀ u → envelopeDigest kind h u ≡ accepted d u []
  runs {d} (enveloped admitted plain connector plainHash connectorHash selection) u =
    bind-step (assert (kind ≤ᵇ 1) "unknown envelope") (λ _ → hashes) u (success d)
      (assert-runs "unknown envelope" admitted u)
      (bind-step (hash (plainEnvelope h)) afterPlain u (success d) (hash-runs plainHash u)
        (bind-step (hash (connectedEnvelope h)) (select plain) u (success d) (hash-runs connectorHash u)
          (cong (λ v → accepted v u []) (sym selection))))

  state-free : Pure (envelopeDigest kind h)
  state-free =
    pure-bind (assert (kind ≤ᵇ 1) "unknown envelope") (λ _ → hashes) (assert-pure (kind ≤ᵇ 1) "unknown envelope") λ _ →
    lift-bind-pure (persistentHash P (plainEnvelope h)) afterPlain λ plain →
    lift-bind-pure (persistentHash P (connectedEnvelope h)) (select plain) λ connector →
    return-pure (if kind ≡ᵇ 1 then connector else plain)

module K256Run (a : Auth) (h : Value) (message : String) where
  ecdsaStep : Value → M ⊤
  ecdsaStep digest = lift (ecdsaVerify P k256 digest (signature a) (key a)) >>= λ valid → assert valid message

  evidence : ∀ {s v t es} → verify k256 a h message s ≡ accepted v t es → Verified k256 a h
  evidence {s} executed with steps (envelopeDigest (envelope a) h) ecdsaStep s executed
  ... | d , t₁ , run _ digested , run _ executed₁
    with steps (lift (ecdsaVerify P k256 d (signature a) (key a))) (λ valid → assert valid message) t₁ executed₁
  ... | valid , _ , run _ checked , run _ executed₂ with assert-step valid message executed₂
  ... | refl = k256Verified d (EnvelopeRun.evidence (envelope a) h digested)
    (lift-step (ecdsaVerify P k256 d (signature a) (key a)) checked)

  state-free : Pure (verify k256 a h message)
  state-free =
    pure-bind (envelopeDigest (envelope a) h) ecdsaStep (EnvelopeRun.state-free (envelope a) h) λ digest →
    lift-bind-pure (ecdsaVerify P k256 digest (signature a) (key a)) (λ valid → assert valid message) λ valid →
    assert-pure valid message

------------------------------------------------------------------------
-- secp256r1 WebAuthn assertions

checkOrigin-pure : ∀ bs → Pure (checkOrigin bs)
checkOrigin-pure [] = return-pure tt
checkOrigin-pure (b ∷ bs) =
  pure-bind (assert valid "invalid origin bytes") (λ _ → checkOrigin bs) (assert-pure valid "invalid origin bytes") λ _ →
  checkOrigin-pure bs
  where
  valid : Bool
  valid = (33 ≤ᵇ b) ∧ (b ≤ᵇ 126) ∧ not (b ≡ᵇ 34) ∧ not (b ≡ᵇ 92)

webAuthn-runs : ∀ {ad origin h d} → WebAuthnDigest ad origin h d → ∀ u → webAuthnDigest ad origin h u ≡ accepted d u []
webAuthn-runs {ad} {origin} {h} {d} (webAuthnHashed clientHash clientDataHash assertionHash) u =
  bind-step (hash (clientDataPreimage origin h)) (λ c → hash (assertionPreimage ad c)) u (success d)
    (hash-runs clientDataHash u) (hash-runs assertionHash u)

-- webAuthn's flags byte comes from a local helper on `drop 32`; the evaluator
-- below is webAuthn with that byte already read.
module WebAuthnRun (a : Auth) (h : Value) (message : String) where
  origin : Value
  origin = at 1 (policy a)

  relyingParty : Bool
  relyingParty = equal (bytes (take 32 (rawBytes (authenticator a)))) (at 0 (policy a))

  flagsAccepted : ℕ → Bool
  flagsAccepted flags = (flags ≡ᵇ 5) ∨ (flags ≡ᵇ 13) ∨ (flags ≡ᵇ 29)

  rNonzero sNonzero : Bool
  rNonzero = not (number (at 0 (signature a)) ≡ᵇ 0)
  sNonzero = not (number (at 1 (signature a)) ≡ᵇ 0)

  ecdsaStep : Value → M ⊤
  ecdsaStep digest = lift (ecdsaVerify P p256 digest (signature a) (key a)) >>= λ valid → assert valid message

  afterR : Value → M ⊤
  afterR digest = assert sNonzero "zero ECDSA s" >> ecdsaStep digest

  afterDigest : Value → M ⊤
  afterDigest digest = assert rNonzero "zero ECDSA r" >> afterR digest

  afterClient : Value → M ⊤
  afterClient clientHash = hash (assertionPreimage (authenticator a) clientHash) >>= afterDigest

  afterOrigin : M ⊤
  afterOrigin = hash (clientDataPreimage origin h) >>= afterClient

  afterFlags : M ⊤
  afterFlags = checkOrigin (rawBytes origin) >> afterOrigin

  flagsThen : ℕ → M ⊤
  flagsThen flags = assert (flagsAccepted flags) "WebAuthn flags require UP and UV" >> afterFlags

  withFlags : ℕ → M ⊤
  withFlags flags = assert relyingParty "WebAuthn RP mismatch" >> flagsThen flags

  absent : ∀ {s v t es} → withFlags 0 s ≡ accepted v t es → ⊥
  absent {s} executed with steps (assert relyingParty "WebAuthn RP mismatch") (λ _ → flagsThen 0) s executed
  ... | _ , t₁ , _ , run _ executed₁
    with steps (assert (flagsAccepted 0) "WebAuthn flags require UP and UV") (λ _ → afterFlags) t₁ executed₁
  ... | _ , _ , run _ flagsChecked , _
    with assert-step (flagsAccepted 0) "WebAuthn flags require UP and UV" {s = t₁} flagsChecked
  ... | ()

  present : ∀ flags remaining {s v t es} → drop 32 (rawBytes (authenticator a)) ≡ flags ∷ remaining →
    withFlags flags s ≡ accepted v t es → Verified p256 a h
  present flags remaining {s} flagsByte executed
    with steps (assert relyingParty "WebAuthn RP mismatch") (λ _ → flagsThen flags) s executed
  ... | _ , t₁ , run _ rpChecked , run _ executed₁
    with steps (assert (flagsAccepted flags) "WebAuthn flags require UP and UV") (λ _ → afterFlags) t₁ executed₁
  ... | _ , t₂ , run _ flagsChecked , run _ executed₂
    with steps (checkOrigin (rawBytes origin)) (λ _ → afterOrigin) t₂ executed₂
  ... | _ , t₃ , _ , run _ executed₃
    with steps (hash (clientDataPreimage origin h)) afterClient t₃ executed₃
  ... | clientHash , t₄ , run _ clientHashed , run _ executed₄
    with steps (hash (assertionPreimage (authenticator a) clientHash)) afterDigest t₄ executed₄
  ... | d , t₅ , run _ digestHashed , run _ executed₅
    with steps (assert rNonzero "zero ECDSA r") (λ _ → afterR d) t₅ executed₅
  ... | _ , t₆ , _ , run _ executed₆
    with steps (assert sNonzero "zero ECDSA s") (λ _ → ecdsaStep d) t₆ executed₆
  ... | _ , t₇ , _ , run _ executed₇
    with steps (lift (ecdsaVerify P p256 d (signature a) (key a))) (λ valid → assert valid message) t₇ executed₇
  ... | valid , _ , run _ checked , run _ executed₈ with assert-step valid message executed₈
  ... | refl = p256Verified d
    (assert-step relyingParty "WebAuthn RP mismatch" rpChecked)
    (flagged flags remaining flagsByte
      (assert-step (flagsAccepted flags) "WebAuthn flags require UP and UV" flagsChecked))
    (webAuthnHashed clientHash
      (lift-step (persistentHash P (clientDataPreimage origin h)) clientHashed)
      (lift-step (persistentHash P (assertionPreimage (authenticator a) clientHash)) digestHashed))
    (lift-step (ecdsaVerify P p256 d (signature a) (key a)) checked)

  flags-free : ∀ flags → Pure (withFlags flags)
  flags-free flags =
    pure-bind (assert relyingParty "WebAuthn RP mismatch") (λ _ → flagsThen flags)
      (assert-pure relyingParty "WebAuthn RP mismatch") λ _ →
    pure-bind (assert (flagsAccepted flags) "WebAuthn flags require UP and UV") (λ _ → afterFlags)
      (assert-pure (flagsAccepted flags) "WebAuthn flags require UP and UV") λ _ →
    pure-bind (checkOrigin (rawBytes origin)) (λ _ → afterOrigin) (checkOrigin-pure (rawBytes origin)) λ _ →
    lift-bind-pure (persistentHash P (clientDataPreimage origin h)) afterClient λ clientHash →
    lift-bind-pure (persistentHash P (assertionPreimage (authenticator a) clientHash)) afterDigest λ d →
    pure-bind (assert rNonzero "zero ECDSA r") (λ _ → afterR d) (assert-pure rNonzero "zero ECDSA r") λ _ →
    pure-bind (assert sNonzero "zero ECDSA s") (λ _ → ecdsaStep d) (assert-pure sNonzero "zero ECDSA s") λ _ →
    lift-bind-pure (ecdsaVerify P p256 d (signature a) (key a)) (λ valid → assert valid message) λ valid →
    assert-pure valid message

  -- Splitting on the flags byte exposes webAuthn as withFlags.
  evidence : ∀ {s v t es} → webAuthn a h message s ≡ accepted v t es → Verified p256 a h
  evidence executed with drop 32 (rawBytes (authenticator a)) in flagsByte
  ... | [] = ⊥-elim (absent executed)
  ... | flags ∷ remaining = present flags remaining flagsByte executed

  state-free : Pure (webAuthn a h message)
  state-free with drop 32 (rawBytes (authenticator a))
  ... | [] = flags-free 0
  ... | flags ∷ _ = flags-free flags

------------------------------------------------------------------------
-- verify

verify-pure : ∀ c a h message → Pure (verify c a h message)
verify-pure jubjub a h message = SchnorrRun.state-free (key a) (sigR a) (sigS a) h message
verify-pure k256 a h message = K256Run.state-free a h message
verify-pure p256 a h message = WebAuthnRun.state-free a h message

verify-preserves : ∀ c a h message {s v t es} → verify c a h message s ≡ accepted v t es → t ≡ s
verify-preserves c a h message = pure-preserves (verify-pure c a h message)

verification-evidence : ∀ c a h message {s} → Succeeded (verify c a h message) s → Verified c a h
verification-evidence jubjub a h message executed =
  jubjubVerified (SchnorrRun.evidence (key a) (sigR a) (sigS a) h message executed)
verification-evidence k256 a h message (succeeded _ _ _ executed) = K256Run.evidence a h message executed
verification-evidence p256 a h message (succeeded _ _ _ executed) = WebAuthnRun.evidence a h message executed

verified-digest : ∀ c a h message {s} → Succeeded (verify c a h message) s → (verified : Verified c a h) →
  verifiedDigest c a h message ≡ just (signedDigest verified)
verified-digest jubjub a h message (succeeded _ _ _ executed) (jubjubVerified _) =
  bind-evaluates (verify jubjub a h message) (λ _ → return h) (verify-pure jubjub a h message) executed
    (λ _ → refl)
verified-digest k256 a h message (succeeded _ _ _ executed) (k256Verified d digest _) =
  bind-evaluates (verify k256 a h message) (λ _ → envelopeDigest (envelope a) h) (verify-pure k256 a h message)
    executed (EnvelopeRun.runs (envelope a) h digest)
verified-digest p256 a h message (succeeded _ _ _ executed) (p256Verified d _ _ digest _) =
  bind-evaluates (verify p256 a h message) (λ _ → webAuthnDigest (authenticator a) (at 1 (policy a)) h)
    (verify-pure p256 a h message) executed (webAuthn-runs digest)

------------------------------------------------------------------------
-- Message binding

authorisation-message : ∀ c grant op addr a args nonce {s h t es} →
  challengeAt c grant (operationName op) addr a args nonce s ≡ accepted h t es →
  (verified : Verified c a h) →
  encode (authorisingKey c a) (authorisedRequest c grant op addr a args nonce) ≡ just (signedDigest verified)
authorisation-message jubjub grant op addr a args nonce challenged (jubjubVerified _) =
  pure-evaluates
    (challengeAt-pure jubjub grant (operationName op) addr (requestAuth (key a) (schemeInput jubjub a)) args nonce)
    challenged
authorisation-message k256 grant op addr a args nonce {h = h} challenged (k256Verified d digest _) =
  bind-evaluates (challengeAt k256 grant (operationName op) addr (requestAuth (key a) (schemeInput k256 a)) args nonce)
    (envelopeDigest (envelope a))
    (challengeAt-pure k256 grant (operationName op) addr (requestAuth (key a) (schemeInput k256 a)) args nonce)
    challenged (EnvelopeRun.runs (envelope a) h digest)
authorisation-message p256 grant op addr a args nonce challenged (p256Verified d _ _ digest _) =
  bind-evaluates (challengeAt p256 grant (operationName op) addr (requestAuth (key a) (schemeInput p256 a)) args nonce)
    (webAuthnDigest (authenticator a) (at 1 (policy a)))
    (challengeAt-pure p256 grant (operationName op) addr (requestAuth (key a) (schemeInput p256 a)) args nonce)
    challenged (webAuthn-runs digest)

recovery-message : ∀ r pk {s dst t es u h v fs} →
  hashTag recoverySubmitTag s ≡ accepted dst t es → hash (submitPreimage dst r) u ≡ accepted h v fs →
  encode (signingKey jubjub pk) (recoveryRequest r) ≡ just h
recovery-message r pk {dst = dst} tagged hashed =
  bind-evaluates (hashTag recoverySubmitTag) (λ dst → hash (submitPreimage dst r)) (hashTag-pure recoverySubmitTag)
    tagged (pure-runs (hash-pure (submitPreimage dst r)) hashed)

------------------------------------------------------------------------
-- Provenance

module Provenance (ownership : Key → Signing.Ownership) where
  open Symbolic ownership
  open Signing.Model interface
    using (Trace; Available; Controlled; HonestlyIssued; module HonestlyIssued; initial)
  module Core = SigningProof.Proofs interface

  message-provenance : ∀ {k r d t} → encode k r ≡ just d → (trace : Trace initial t) →
    Available t (token k r) →
    Controlled t k ⊎ Σ (HonestlyIssued trace (token k r)) λ issued →
      encode k (HonestlyIssued.request issued) ≡ just d
  message-provenance encoded trace available with Core.signature-provenance trace available
  ... | inj₁ controlled = inj₁ controlled
  ... | inj₂ issuance = inj₂ (issuance , trans (HonestlyIssued.encodes issuance) encoded)

  request-provenance : ∀ {X : Set} (view : Request → X) {k r d t} → encode k r ≡ just d →
    (trace : Trace initial t) → IssuedAgreement view trace k d r → Available t (token k r) →
    Controlled t k ⊎ Σ (HonestlyIssued trace (token k r)) λ issued →
      view (HonestlyIssued.request issued) ≡ view r
  request-provenance view encoded trace agreement available with message-provenance encoded trace available
  ... | inj₁ controlled = inj₁ controlled
  ... | inj₂ (issuance , issuedEncoding) = inj₂ (issuance , agreement (HonestlyIssued.request issuance)
    (HonestlyIssued.before issuance) (HonestlyIssued.occurs issuance) issuedEncoding)

  authorisation-provenance : ∀ c grant op addr a args nonce message {s h t es u final} →
    challengeAt c grant (operationName op) addr a args nonce s ≡ accepted h t es →
    Succeeded (verify c a h message) u →
    (trace : Trace initial final) →
    Available final (token (authorisingKey c a) (authorisedRequest c grant op addr a args nonce)) →
    Σ (Verified c a h) λ verified →
      Controlled final (authorisingKey c a) ⊎
      Σ (HonestlyIssued trace (token (authorisingKey c a) (authorisedRequest c grant op addr a args nonce)))
        λ issued → encode (authorisingKey c a) (HonestlyIssued.request issued) ≡ just (signedDigest verified)
  authorisation-provenance c grant op addr a args nonce message {h = h} challenged executed trace available =
    verified , message-provenance (authorisation-message c grant op addr a args nonce challenged verified)
      trace available
    where verified = verification-evidence c a h message executed

  recovery-provenance : ∀ r pk R S message {s dst t es u h v fs w final} →
    hashTag recoverySubmitTag s ≡ accepted dst t es →
    hash (submitPreimage dst r) u ≡ accepted h v fs →
    Succeeded (schnorr pk R S h message) w →
    (trace : Trace initial final) →
    Available final (token (signingKey jubjub pk) (recoveryRequest r)) →
    SchnorrAccepts pk R S h ×
      (Controlled final (signingKey jubjub pk) ⊎
       Σ (HonestlyIssued trace (token (signingKey jubjub pk) (recoveryRequest r))) λ issued →
         encode (signingKey jubjub pk) (HonestlyIssued.request issued) ≡ just h)
  recovery-provenance r pk R S message {h = h} tagged hashed executed trace available =
    SchnorrRun.evidence pk R S h message executed ,
    message-provenance {r = recoveryRequest r} (recovery-message r pk tagged hashed) trace available

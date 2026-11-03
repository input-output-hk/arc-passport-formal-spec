{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

-- What a successful device-authorised execution of the actual source evaluator
-- establishes: the device entry it used, the challenge and verification it ran,
-- how it rolled the entry and advanced the counters, and the activation
-- (bootstrap) step that installs a first entry without any signature.
-- Every field is read off FullAccountCrypto/FullAccountBody/FullAccount as they
-- execute; nothing here assumes a call was authorised. Cryptographic meaning
-- (signature binding, symbolic provenance) is FullAccountSignatureBinding's.
-- Statements: Conformance.FullAccountDeviceSecurityProperties.
module Conformance.FullAccountDeviceSecurity (P : Primitives) where

open import Conformance.FullAccount using (module AccountSemantics)
open import Conformance.FullAccountBody P
open import Conformance.FullAccountCrypto P
open import Conformance.FullAccountExecution using (Run)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_; take; drop; length)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (ℕ; suc; _<ᵇ_; _^_)
open import Data.String.Base using (String)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open AccountSemantics P using (operationSchema; parseAuth; callerEntryAfter)

------------------------------------------------------------------------
-- deviceCall's own decoding of its call

-- The operation arguments, the authentication suffix and the held-coin input
-- exactly as deviceCall's let-bindings and first step compute them.
deviceArguments : Operation → List Value → List Value
deviceArguments op xs = take (length (operationSchema op)) xs

deviceAuth : Curve → Operation → List Value → Auth
deviceAuth c op xs = parseAuth c (drop (length (operationSchema op)) xs)

deviceCoin : Operation → Context → Value
deviceCoin op ctx = if shielded op then heldCoin ctx else none

-- The failure message authorise passes to verify; only p256 differs.
verificationMessage : Curve → String
verificationMessage p256 = "invalid WebAuthn signature"
verificationMessage _ = "invalid signature"

------------------------------------------------------------------------
-- Counters and frames

-- A counter cell held `previous` and was bumped by one within its width,
-- as the source's bump label bits does.
record Advanced (label : String) (bits : ℕ) (previous : Value) (before after : State) : Set where
  field previousCell : lookupCell label (ledger before) ≡ just previous
        bounded : (suc (number previous) <ᵇ 2 ^ bits) ≡ true
        advanced : lookupCell label (ledger after) ≡ just (nat (suc (number previous)))

-- Every successful run of m leaves ledger cell k as it was.
Preserves : ∀ {A : Set} → String → M A → Set
Preserves k m = ∀ {s x t} → Run m s x t → lookupCell k (ledger t) ≡ lookupCell k (ledger s)

-- The ledger cells each device-operation body may write (body-frame proves it).
bodyWrites : Operation → List String
bodyWrites withdrawUnshielded = "unshielded_balances" ∷ []
bodyWrites withdrawShielded = []
bodyWrites withdrawToContract = []
bodyWrites appendInbox = "inbox" ∷ "inbox_count" ∷ []
bodyWrites rotateEncKey = "enc_key" ∷ []
bodyWrites addDevice = "devices" ∷ "device_count" ∷ []
bodyWrites removeDevice = "devices" ∷ "device_count" ∷ []
bodyWrites issueGrant = "grants" ∷ []
bodyWrites revokeGrant = "grants" ∷ []
bodyWrites revokeAllGrants = "grant_generation" ∷ "grants" ∷ []
bodyWrites publishRecovery = "recovery_pk" ∷ "recovery_session" ∷ "recovery_phi" ∷
  "recovery_phi_len" ∷ "recovery_wrap" ∷ "recovery_version" ∷ []
bodyWrites cancelRecovery = "pending_recovery" ∷ "pending_entry" ∷ "pending_recovery_pk" ∷
  "pending_not_before" ∷ []

------------------------------------------------------------------------
-- Device authorisation (FullAccountCrypto.authorise)

-- `Run m s x s`: m computes x from s and leaves the ledger unchanged.
-- The used entry is the hash entryAt computes for the context's own address,
-- the stored device epoch and the presented use counter; it must be a live
-- member of the device set. The verification is the actual curve-specific
-- verify on the challenge h (P256 before rolling, other curves after it).
record Authorisation (c : Curve) (ctx : Context) (a : Auth) (h : Value)
    (before : State) (next : Value) (after : State) : Set where
  field
    keyChecked : Run (keyGuard c (key a) "device key has small order") before tt before
    epoch : Value
    epochCell : lookupCell "device_epoch" (ledger before) ≡ just epoch
    current : Value
    currentEntry : Run (entryAt c (self ctx) a (number epoch) (counter a)) before current before
    currentLive : member current (fields (cell "devices" before)) ≡ true
    verified : Run (verify c a h (verificationMessage c)) before tt before
    counterBounded : (suc (counter a) <ᵇ 2 ^ 64) ≡ true
    nextEntry : Run (entryAt c (self ctx) a (number epoch) (suc (counter a))) before next before
    devicesRolled : cell "devices" after ≡
      tuple (insertSet next (removeSet current (fields (cell "devices" before))))
    nonce : Value
    nonceAdvanced : Advanced "auth_nonce" 64 nonce before after
    round : Value
    roundAdvanced : Advanced "round" 64 round before after
    unchanged : ∀ k → stringEqual k "devices" ≡ false → stringEqual k "auth_nonce" ≡ false →
      stringEqual k "round" ≡ false → lookupCell k (ledger after) ≡ lookupCell k (ledger before)

------------------------------------------------------------------------
-- Device-authorised calls (FullAccount.AccountSemantics.deviceCall)

-- The challenge signs the operation atoms computed from the decoded arguments
-- and held coin, the account address and the stored authorisation nonce.
-- authorise then runs from the before state; the body runs from its result.
-- The nonce and round advances are those of the committed final state.
record DeviceCall (c : Curve) (op : Operation) (ctx : Context) (xs : List Value)
    (before : State) (result : Value) (after : State) : Set where
  field
    atoms : List Atom
    encoded : Run (operationAtoms op (deviceArguments op xs) (deviceCoin op ctx)) before atoms before
    nonce : Value
    nonceAdvanced : Advanced "auth_nonce" 64 nonce before after
    challengeValue : Value
    challengeComputed : Run (challengeAt c false (operationName op) (self ctx) (deviceAuth c op xs)
      atoms (number nonce)) before challengeValue before
    rolledEntry : Value
    authorisedState : State
    authorised : Authorisation c ctx (deviceAuth c op xs) challengeValue before rolledEntry
      authorisedState
    callerEntry : Value
    callerEntryRun : Run (callerEntryAfter c op ctx (deviceAuth c op xs) rolledEntry)
      authorisedState callerEntry authorisedState
    bodyRun : Run (body op ctx (deviceArguments op xs) (deviceCoin op ctx) callerEntry)
      authorisedState result after
    round : Value
    roundAdvanced : Advanced "round" 64 round before after

------------------------------------------------------------------------
-- Activation (FullAccountBody.activate): the bootstrap boundary

-- Activation verifies no signature. Its authority is knowledge of a preimage
-- (key, salt and envelope or policy) of the constructor's boot commitment,
-- usable once: booted must be unset and is then set, and the commitment cleared.
record Activation (c : Curve) (ctx : Context) (a : Auth) (salt : Value)
    (before after : State) : Set where
  field
    booted : Value
    bootedCell : lookupCell "booted" (ledger before) ≡ just booted
    notBooted : flag booted ≡ false
    keyChecked : Run (keyGuard c (key a) "device key has small order") before tt before
    commitment : Value
    committed : Run (bootCommit c a salt) before commitment before
    boot : Value
    bootCell : lookupCell "boot" (ledger before) ≡ just boot
    bootMatched : equal commitment boot ≡ true
    epoch : Value
    epochCell : lookupCell "device_epoch" (ledger before) ≡ just epoch
    initial : Value
    initialEntry : Run (entryAt c (self ctx) a (number epoch) 0) before initial before
    installed : cell "devices" after ≡ tuple (insertSet initial (fields (cell "devices" before)))
    deviceCount : lookupCell "device_count" (ledger after) ≡ just (nat 1)
    nowBooted : lookupCell "booted" (ledger after) ≡ just (bool true)
    bootCleared : lookupCell "boot" (ledger after) ≡ just zero32
    round : Value
    roundAdvanced : Advanced "round" 64 round before after
    unchanged : ∀ k → stringEqual k "devices" ≡ false → stringEqual k "device_count" ≡ false →
      stringEqual k "booted" ≡ false → stringEqual k "boot" ≡ false →
      stringEqual k "round" ≡ false → lookupCell k (ledger after) ≡ lookupCell k (ledger before)

------------------------------------------------------------------------
-- Replay boundary

-- Two distinct typed preimages on which the persistent-hash primitive returns
-- the same digest. No theorem here assumes such collisions are impossible.
record Collision : Set where
  field left right : List Atom
        distinct : left ≢ right
        digest : Value
        leftHash : persistentHash P left ≡ success digest
        rightHash : persistentHash P right ≡ success digest

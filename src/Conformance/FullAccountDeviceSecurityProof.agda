{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

-- Proofs for Conformance.FullAccountDeviceSecurityProperties. Source
-- computations are decomposed along their actual evaluation with
-- FullAccountExecution.then. Continuations that Agda cannot infer through the
-- evaluator's binds are written out; Agda checks each against the source
-- definitionally. Purity of verification, challenges and key encodings is
-- FullAccountSignatureBindingProof's.
module Conformance.FullAccountDeviceSecurityProof (P : Primitives) where

open import Conformance.FullAccount using (module AccountSemantics)
open import Conformance.FullAccountBody P
open import Conformance.FullAccountCrypto P
open import Conformance.FullAccountDeviceSecurity P
open import Conformance.FullAccountExecution using (Run; run; then)
open import Conformance.FullAccountLayouts
import Conformance.FullAccountSignatureBindingProof as SignatureBindingProof
open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Bool.Properties using (∨-assoc)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; _++_; length; take)
open import Data.List.Properties using (∷-injectiveˡ; ∷-injectiveʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat.Base using (ℕ; zero; suc; _<ᵇ_; _≤ᵇ_; _≡ᵇ_; _^_; _∸_)
open import Data.Nat.Properties using (suc-injective; 1+n≢n)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String)
open import Data.String.Properties using () renaming (_≟_ to _≟ˢ_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (dec-true)
import Relation.Nullary.Decidable.Core as Decidable
open import Relation.Nullary.Reflects using (Reflects; invert)

open AccountSemantics P using (deviceCall; callerEntryAfter)

private
  module Binding = SignatureBindingProof P

------------------------------------------------------------------------
-- Ledger cells

stringEqual-refl : ∀ k → stringEqual k k ≡ true
stringEqual-refl k = dec-true (k ≟ˢ k) refl

stringEqual-sound : ∀ {k x : String} → stringEqual k x ≡ true → k ≡ x
stringEqual-sound {k} {x} same = invert (subst (Reflects (k ≡ x)) same (Decidable.Dec.proof (k ≟ˢ x)))

lookup-insert-same : ∀ k v l → lookupCell k (insertCell k v l) ≡ just v
lookup-insert-same k v [] = cong (λ b → if b then just v else nothing) (stringEqual-refl k)
lookup-insert-same k v ((x , w) ∷ xs) = same-step (stringEqual k x) refl (lookup-insert-same k v xs)
  where
  same-step : ∀ b → stringEqual k x ≡ b → lookupCell k (insertCell k v xs) ≡ just v →
    lookupCell k (if b then (k , v) ∷ xs else (x , w) ∷ insertCell k v xs) ≡ just v
  same-step true _ _ = cong (λ b → if b then just v else lookupCell k xs) (stringEqual-refl k)
  same-step false k≢x inserted =
    trans (cong (λ b → if b then just w else lookupCell k (insertCell k v xs)) k≢x) inserted

lookup-insert-other : ∀ k k′ v l → stringEqual k k′ ≡ false →
  lookupCell k (insertCell k′ v l) ≡ lookupCell k l
lookup-insert-other k k′ v [] k≢k′ = cong (λ b → if b then just v else nothing) k≢k′
lookup-insert-other k k′ v ((x , w) ∷ xs) k≢k′ =
  other-step (stringEqual k′ x) refl (lookup-insert-other k k′ v xs k≢k′)
  where
  other-step : ∀ b → stringEqual k′ x ≡ b → lookupCell k (insertCell k′ v xs) ≡ lookupCell k xs →
    lookupCell k (if b then (k′ , v) ∷ xs else (x , w) ∷ insertCell k′ v xs) ≡
    lookupCell k ((x , w) ∷ xs)
  other-step true k′≡x _ =
    trans (cong (λ b → if b then just v else lookupCell k xs) k≢k′)
      (sym (cong (λ b → if b then just w else lookupCell k xs)
        (subst (λ y → stringEqual k y ≡ false) (stringEqual-sound {k = k′} {x = x} k′≡x) k≢k′)))
  other-step false _ inserted = cong (λ r → if stringEqual k x then just w else r) inserted

cell-lookup : ∀ k s {v} → lookupCell k (ledger s) ≡ just v → cell k s ≡ v
cell-lookup k s found with lookupCell k (ledger s)
cell-lookup k s () | nothing
cell-lookup k s refl | just _ = refl

cell-insert-same : ∀ k v l → cell k (state (insertCell k v l)) ≡ v
cell-insert-same k v l = cell-lookup k (state (insertCell k v l)) (lookup-insert-same k v l)

------------------------------------------------------------------------
-- Successful runs of evaluator primitives

return-run : ∀ {A : Set} (v : A) {s x t} → Run (return v) s x t → x ≡ v × t ≡ s
return-run v (run _ refl) = refl , refl

emit-run : ∀ e {s x t} → Run (emit e) s x t → t ≡ s
emit-run e (run _ refl) = refl

lift-run : ∀ {A : Set} (r : Result A) {s x t} → Run (lift r) s x t → t ≡ s
lift-run (failure e) (run _ ())
lift-run (success v) (run _ refl) = refl

hash-run : ∀ xs {s x t} → Run (hash xs) s x t → persistentHash P xs ≡ success x × t ≡ s
hash-run xs (run _ execution) with persistentHash P xs
hash-run xs (run _ ()) | failure _
hash-run xs (run _ refl) | success _ = refl , refl

readSelf-run : ∀ ctx {s x t} → Run (readSelf ctx) s x t → x ≡ self ctx × t ≡ s
readSelf-run ctx (run _ refl) = refl , refl

read-run : ∀ k {s x t} → Run (read k) s x t → lookupCell k (ledger s) ≡ just x × t ≡ s
read-run k {s} (run _ execution) with lookupCell k (ledger s)
read-run k (run _ ()) | nothing
read-run k (run _ refl) | just _ = refl , refl

readCount-run : ∀ k {s n t} → Run (readCount k) s n t →
  Σ Value λ v → lookupCell k (ledger s) ≡ just v × n ≡ number v × t ≡ s
readCount-run k r with then (read k) {f = λ v → return (number v)} r
... | v , t₁ , r₁ , run _ refl with read-run k r₁
...   | found , refl = v , found , refl , refl

has-run : ∀ label key {s x t} → Run (has label key) s x t →
  x ≡ member key (fields (cell label s)) × t ≡ s
has-run label key (run _ refl) = refl , refl

memberMap-run : ∀ label key {s x t} → Run (memberMap label key) s x t → t ≡ s
memberMap-run label key (run _ refl) = refl

lookup-run : ∀ label key {s x t} → Run (lookup label key) s x t → t ≡ s
lookup-run label key {s} (run _ execution) with lookupCell label (ledger s)
lookup-run label key (run _ ()) | nothing
lookup-run label key (run _ execution) | just v with lookupMap key (fields v)
lookup-run label key (run _ ()) | just v | nothing
lookup-run label key (run _ refl) | just v | just _ = refl

assert-run : ∀ b message {s x t} → Run (assert b message) s x t → b ≡ true × t ≡ s
assert-run true message (run _ refl) = refl , refl
assert-run false message (run _ ())

cast-run : ∀ label bits n {s x t} → Run (cast label bits n) s x t →
  x ≡ n × (n <ᵇ 2 ^ bits) ≡ true × t ≡ s
cast-run label bits n (run _ execution) with n <ᵇ 2 ^ bits
cast-run label bits n (run _ refl) | true = refl , refl , refl
cast-run label bits n (run _ ()) | false

write-run : ∀ k v {s x t} → Run (write k v) s x t → t ≡ state (insertCell k v (ledger s))
write-run k v (run _ refl) = refl

insert-run : ∀ label key v {s x t} → Run (insert label key v) s x t →
  t ≡ state (insertCell label (tuple (insertMap key v (fields (cell label s)))) (ledger s))
insert-run label key v (run _ refl) = refl

include-run : ∀ label key {s x t} → Run (include label key) s x t →
  t ≡ state (insertCell label (tuple (insertSet key (fields (cell label s)))) (ledger s))
include-run label key (run _ refl) = refl

exclude-run : ∀ label key {s x t} → Run (exclude label key) s x t →
  t ≡ state (insertCell label (tuple (removeSet key (fields (cell label s)))) (ledger s))
exclude-run label key (run _ refl) = refl

clear-run : ∀ label {s x t} → Run (clear label) s x t →
  t ≡ state (insertCell label (tuple []) (ledger s))
clear-run label (run _ refl) = refl

bump-run : ∀ label bits {s x t} → Run (bump label bits) s x t →
  Σ Value λ v → lookupCell label (ledger s) ≡ just v × (suc (number v) <ᵇ 2 ^ bits) ≡ true ×
    t ≡ state (insertCell label (nat (suc (number v))) (ledger s))
bump-run label bits r with then (readCount label) {f = λ n → writeCount label bits (suc n)} r
... | n , t₁ , r₁ , r₂ with readCount-run label r₁
...   | v , found , refl , refl
  with then (cast label bits (suc (number v))) {f = λ w → write label (nat w)} r₂
...     | w , t₂ , r₃ , run _ refl with cast-run label bits (suc (number v)) r₃
...       | refl , bounded , refl = v , found , bounded , refl

pure-run : ∀ {A : Set} {m : M A} → Binding.Pure m → ∀ {s x t} → Run m s x t →
  t ≡ s × (∀ u → Run m u x u)
pure-run p (run _ execution) =
  Binding.pure-preserves p execution , λ u → run [] (Binding.pure-runs p execution u)

------------------------------------------------------------------------
-- State-free source computations (no ledger access, no effects)

if-pure : ∀ {A : Set} b {m n : M A} → Binding.Pure m → Binding.Pure n →
  Binding.Pure (if b then m else n)
if-pure true p q = p
if-pure false p q = q

keyGuard-pure : ∀ c pk message → Binding.Pure (keyGuard c pk message)
keyGuard-pure jubjub pk message =
  Binding.lift-bind-pure (ecMul P jubjub pk 8)
    (λ q → identityOf >>= λ o → assert (not (equal q o)) message) λ q →
  Binding.lift-bind-pure (ecMulGenerator P jubjub 0) (λ o → assert (not (equal q o)) message) λ o →
  Binding.assert-pure (not (equal q o)) message
keyGuard-pure k256 pk message =
  Binding.lift-bind-pure (pointCoordinates P k256 pk) _ λ where
    (x , y) → Binding.assert-pure (not (equal x zero32 ∧ equal y zero32))
      "device key is the point at infinity"
keyGuard-pure p256 pk message = Binding.return-pure tt

requireRecoveryKey-pure : ∀ pk → Binding.Pure (requireRecoveryKey pk)
requireRecoveryKey-pure pk =
  Binding.lift-bind-pure (ecMulGenerator P jubjub 0)
    (λ o → assert (not (equal pk o)) "recovery key is the identity" >>
      requireSmallOrderFree pk "recovery key has small order") λ o →
  Binding.pure-bind (assert (not (equal pk o)) "recovery key is the identity")
    (λ _ → requireSmallOrderFree pk "recovery key has small order")
    (Binding.assert-pure (not (equal pk o)) "recovery key is the identity") λ _ →
  keyGuard-pure jubjub pk "recovery key has small order"

entryAt-pure : ∀ c addr a epoch count → Binding.Pure (entryAt c addr a epoch count)
entryAt-pure jubjub addr a epoch count = Binding.hash-pure _
entryAt-pure k256 addr a epoch count =
  Binding.pure-bind (keyAtoms k256 (key a)) _ (Binding.keyAtoms-pure k256 (key a)) λ _ →
  Binding.hash-pure _
entryAt-pure p256 addr a epoch count =
  Binding.pure-bind (keyAtoms p256 (key a)) _ (Binding.keyAtoms-pure p256 (key a)) λ _ →
  Binding.hash-pure _

bootCommit-pure : ∀ c a salt → Binding.Pure (bootCommit c a salt)
bootCommit-pure jubjub a salt = Binding.hash-pure _
bootCommit-pure k256 a salt =
  Binding.pure-bind (keyAtoms k256 (key a)) _ (Binding.keyAtoms-pure k256 (key a)) λ _ →
  Binding.hash-pure _
bootCommit-pure p256 a salt =
  Binding.pure-bind (keyAtoms p256 (key a)) _ (Binding.keyAtoms-pure p256 (key a)) λ _ →
  Binding.hash-pure _

spentCommit-pure : ∀ salt spent → Binding.Pure (spentCommit salt spent)
spentCommit-pure salt spent = Binding.hash-pure _

objectCommit-pure : ∀ salt color kind recipient maxCoin →
  Binding.Pure (objectCommit salt color kind recipient maxCoin)
objectCommit-pure salt color kind recipient maxCoin = Binding.hash-pure _

rpCommit-pure : ∀ salt rp → Binding.Pure (rpCommit salt rp)
rpCommit-pure salt rp = Binding.hash-pure _

callerCommit-some-pure : ∀ salt addr → Binding.Pure (callerCommit salt (some addr))
callerCommit-some-pure salt addr =
  Binding.lift-bind-pure
    (persistentHash P (b32 (pad 32 "midnight:account:grant:caller:v1") ∷ b32 salt ∷ contract addr ∷ []))
    (λ c → assert (not (equal c zero32)) "reserved caller commitment" >> return c) λ c →
  Binding.pure-bind (assert (not (equal c zero32)) "reserved caller commitment") (λ _ → return c)
    (Binding.assert-pure (not (equal c zero32)) "reserved caller commitment") λ _ →
  Binding.return-pure c

private
  undecodedCaller : ∀ {A : Set} → Binding.Pure (abort {A} (decoding "Maybe<ContractAddress>"))
  undecodedCaller = Binding.lift-pure (failure (decoding "Maybe<ContractAddress>"))

callerCommit-pure : ∀ salt v → Binding.Pure (callerCommit salt v)
callerCommit-pure salt none = Binding.return-pure zero32
callerCommit-pure salt (some addr) = callerCommit-some-pure salt addr
callerCommit-pure salt (tuple (bool present ∷ addr ∷ [])) =
  Binding.pure-bind (assert (present ∨ equal addr zero32) "noncanonical absent caller")
    (λ _ → if present then callerCommit salt (some addr) else return zero32)
    (Binding.assert-pure (present ∨ equal addr zero32) "noncanonical absent caller") λ _ →
  if-pure present (callerCommit-some-pure salt addr) (Binding.return-pure zero32)
callerCommit-pure salt (nat _) = undecodedCaller
callerCommit-pure salt (bool _) = undecodedCaller
callerCommit-pure salt (bytes _) = undecodedCaller
callerCommit-pure salt (tuple []) = undecodedCaller
callerCommit-pure salt (tuple (nat _ ∷ _)) = undecodedCaller
callerCommit-pure salt (tuple (bool _ ∷ [])) = undecodedCaller
callerCommit-pure salt (tuple (bool _ ∷ _ ∷ _ ∷ _)) = undecodedCaller
callerCommit-pure salt (tuple (bytes _ ∷ _)) = undecodedCaller
callerCommit-pure salt (tuple (tuple _ ∷ _)) = undecodedCaller
callerCommit-pure salt (tuple (none ∷ _)) = undecodedCaller
callerCommit-pure salt (tuple (some _ ∷ _)) = undecodedCaller

scopeDigest-pure : ∀ xs → Binding.Pure (scopeDigest xs)
scopeDigest-pure xs =
  Binding.pure-bind (callerCommit (get 17 xs) (get 16 xs)) _ (callerCommit-pure (get 17 xs) (get 16 xs)) λ _ →
  Binding.hash-pure _

operationAtoms-pure : ∀ op xs coin → Binding.Pure (operationAtoms op xs coin)
operationAtoms-pure withdrawUnshielded xs coin = Binding.return-pure _
operationAtoms-pure withdrawShielded xs coin = Binding.return-pure _
operationAtoms-pure withdrawToContract xs coin = Binding.return-pure _
operationAtoms-pure appendInbox xs coin = Binding.return-pure _
operationAtoms-pure rotateEncKey xs coin = Binding.return-pure _
operationAtoms-pure addDevice xs coin = Binding.return-pure _
operationAtoms-pure removeDevice xs coin = Binding.return-pure _
operationAtoms-pure issueGrant xs coin =
  Binding.pure-bind (scopeDigest xs) (λ digest → return (b32 (get 0 xs) ∷ b32 digest ∷ []))
    (scopeDigest-pure xs) λ digest → Binding.return-pure (b32 (get 0 xs) ∷ b32 digest ∷ [])
operationAtoms-pure revokeGrant xs coin = Binding.return-pure _
operationAtoms-pure revokeAllGrants xs coin = Binding.return-pure []
operationAtoms-pure publishRecovery xs coin = Binding.return-pure _
operationAtoms-pure cancelRecovery xs coin = Binding.return-pure []

------------------------------------------------------------------------
-- Frames: cells a computation leaves unchanged

unchanged-preserves : ∀ {A : Set} {k} {m : M A} → (∀ {s x t} → Run m s x t → t ≡ s) → Preserves k m
unchanged-preserves {k = k} same r = cong (λ t → lookupCell k (ledger t)) (same r)

preserves-bind : ∀ {A B : Set} {k} {m : M A} {f : A → M B} → Preserves k m →
  (∀ x → Preserves k (f x)) → Preserves k (m >>= f)
preserves-bind {m = m} {f} first rest r =
  let (x , t , r₁ , r₂) = then m {f = f} r in trans (rest x r₂) (first r₁)

if-preserves : ∀ {A : Set} {k} b {m n : M A} → Preserves k m → Preserves k n →
  Preserves k (if b then m else n)
if-preserves true pm pn = pm
if-preserves false pm pn = pn

pure-preserves : ∀ {A : Set} {k} {m : M A} → Binding.Pure m → Preserves k m
pure-preserves p = unchanged-preserves λ r → proj₁ (pure-run p r)

return-preserves : ∀ {A : Set} {k} (v : A) → Preserves k (return v)
return-preserves v = unchanged-preserves λ r → proj₂ (return-run v r)

emit-preserves : ∀ {k} e → Preserves k (emit e)
emit-preserves e = unchanged-preserves (emit-run e)

lift-preserves : ∀ {A : Set} {k} (r : Result A) → Preserves k (lift r)
lift-preserves r = unchanged-preserves (lift-run r)

assert-preserves : ∀ {k} b message → Preserves k (assert b message)
assert-preserves b message = unchanged-preserves λ r → proj₂ (assert-run b message r)

cast-preserves : ∀ {k} label bits n → Preserves k (cast label bits n)
cast-preserves label bits n = unchanged-preserves λ r → proj₂ (proj₂ (cast-run label bits n r))

readSelf-preserves : ∀ {k} ctx → Preserves k (readSelf ctx)
readSelf-preserves ctx = unchanged-preserves λ r → proj₂ (readSelf-run ctx r)

read-preserves : ∀ {k} label → Preserves k (read label)
read-preserves label = unchanged-preserves λ r → proj₂ (read-run label r)

readCount-preserves : ∀ {k} label → Preserves k (readCount label)
readCount-preserves label = unchanged-preserves λ r → proj₂ (proj₂ (proj₂ (readCount-run label r)))

has-preserves : ∀ {k} label key → Preserves k (has label key)
has-preserves label key = unchanged-preserves λ r → proj₂ (has-run label key r)

memberMap-preserves : ∀ {k} label key → Preserves k (memberMap label key)
memberMap-preserves label key = unchanged-preserves (memberMap-run label key)

lookup-preserves : ∀ {k} label key → Preserves k (lookup label key)
lookup-preserves label key = unchanged-preserves (lookup-run label key)

write-preserves : ∀ {k} label v → stringEqual k label ≡ false → Preserves k (write label v)
write-preserves {k} label v distinct {s} r =
  trans (cong (λ t → lookupCell k (ledger t)) (write-run label v r))
    (lookup-insert-other k label v (ledger s) distinct)

insert-preserves : ∀ {k} label key v → stringEqual k label ≡ false → Preserves k (insert label key v)
insert-preserves {k} label key v distinct {s} r =
  trans (cong (λ t → lookupCell k (ledger t)) (insert-run label key v r))
    (lookup-insert-other k label (tuple (insertMap key v (fields (cell label s)))) (ledger s) distinct)

include-preserves : ∀ {k} label key → stringEqual k label ≡ false → Preserves k (include label key)
include-preserves {k} label key distinct {s} r =
  trans (cong (λ t → lookupCell k (ledger t)) (include-run label key r))
    (lookup-insert-other k label (tuple (insertSet key (fields (cell label s)))) (ledger s) distinct)

exclude-preserves : ∀ {k} label key → stringEqual k label ≡ false → Preserves k (exclude label key)
exclude-preserves {k} label key distinct {s} r =
  trans (cong (λ t → lookupCell k (ledger t)) (exclude-run label key r))
    (lookup-insert-other k label (tuple (removeSet key (fields (cell label s)))) (ledger s) distinct)

clear-preserves : ∀ {k} label → stringEqual k label ≡ false → Preserves k (clear label)
clear-preserves {k} label distinct {s} r =
  trans (cong (λ t → lookupCell k (ledger t)) (clear-run label r))
    (lookup-insert-other k label (tuple []) (ledger s) distinct)

bump-preserves : ∀ {k} label bits → stringEqual k label ≡ false → Preserves k (bump label bits)
bump-preserves {k} label bits distinct {s} r with bump-run label bits r
... | v , _ , _ , refl = lookup-insert-other k label (nat (suc (number v))) (ledger s) distinct

writeCount-preserves : ∀ {k} label bits n → stringEqual k label ≡ false →
  Preserves k (writeCount label bits n)
writeCount-preserves label bits n distinct =
  preserves-bind (cast-preserves label bits n) λ v → write-preserves label (nat v) distinct

------------------------------------------------------------------------
-- Frames of the device-operation bodies

debit-preserves : ∀ {k} color amount → stringEqual k "unshielded_balances" ≡ false →
  Preserves k (debit color amount)
debit-preserves color amount balances =
  preserves-bind (memberMap-preserves "unshielded_balances" color) λ present →
  preserves-bind (assert-preserves present "no balance for color") λ _ →
  preserves-bind (lookup-preserves "unshielded_balances" color) λ old →
  preserves-bind (assert-preserves (amount ≤ᵇ number old) "insufficient balance") λ _ →
  preserves-bind (cast-preserves "unshielded_balances" 128 (number old ∸ amount)) λ n →
  insert-preserves "unshielded_balances" color (nat n) balances

withdrawPublic-preserves : ∀ {k} color amount recipient → stringEqual k "unshielded_balances" ≡ false →
  Preserves k (withdrawPublic color amount recipient)
withdrawPublic-preserves color amount recipient balances =
  preserves-bind (debit-preserves color amount balances) λ _ →
  preserves-bind (emit-preserves (sendUnshielded color amount (tuple (bool false ∷ recipient ∷ [])))) λ _ →
  return-preserves unit

evolveNonce-preserves : ∀ {k} change nonce → Preserves k (evolveNonce change nonce)
evolveNonce-preserves change nonce =
  preserves-bind (lift-preserves (degradeToTransient P nonce)) λ degraded →
  preserves-bind (lift-preserves (transientHash P
    (le (ascii (if change then "midnight:kernel:nonce_evolve/2" else "midnight:kernel:nonce_evolve")) ∷
      degraded ∷ []))) λ evolved →
  lift-preserves (upgradeFromTransient P evolved)

createCoin-preserves : ∀ {k} coin recipient → Preserves k (createCoin coin recipient)
createCoin-preserves coin recipient =
  preserves-bind (lift-preserves (coinCommitment P coin recipient)) λ cm →
  emit-preserves (createShielded coin recipient cm)

sendCoin-preserves : ∀ {k} ctx isUser recipient amount coin →
  Preserves k (sendCoin ctx isUser recipient amount coin)
sendCoin-preserves ctx isUser recipient amount coin =
  preserves-bind (readSelf-preserves ctx) λ addr →
  preserves-bind (lift-preserves (coinNullifier P (coinInfo coin) addr)) λ nf →
  preserves-bind (emit-preserves (consumeShielded coin nf)) λ _ →
  preserves-bind (assert-preserves (amount ≤ᵇ number (at 2 coin)) "result of subtraction would be negative") λ _ →
  preserves-bind (evolveNonce-preserves false (at 0 coin)) λ nonce →
  preserves-bind (createCoin-preserves (tuple (nonce ∷ at 1 coin ∷ nat amount ∷ []))
    (tuple (bool isUser ∷ recipient ∷ []))) λ _ →
  preserves-bind (if-preserves (not isUser ∧ equal recipient addr)
    (emit-preserves (receiveShielded (tuple (nonce ∷ at 1 coin ∷ nat amount ∷ []))))
    (return-preserves tt)) λ _ →
  if-preserves (number (at 2 coin) ∸ amount ≡ᵇ 0) (return-preserves _)
    (preserves-bind (evolveNonce-preserves true (at 0 coin)) λ nonce′ →
     preserves-bind (createCoin-preserves (tuple (nonce′ ∷ at 1 coin ∷ nat (number (at 2 coin) ∸ amount) ∷ []))
       (tuple (bool false ∷ addr ∷ []))) λ _ →
     preserves-bind (emit-preserves
       (receiveShielded (tuple (nonce′ ∷ at 1 coin ∷ nat (number (at 2 coin) ∸ amount) ∷ [])))) λ _ →
     return-preserves _)

inboxAppend-preserves : ∀ {k} e → stringEqual k "inbox" ≡ false → stringEqual k "inbox_count" ≡ false →
  Preserves k (inboxAppend e)
inboxAppend-preserves e inbox count =
  preserves-bind (readCount-preserves "inbox_count") λ n →
  preserves-bind (insert-preserves "inbox" (nat n) e inbox) λ _ →
  bump-preserves "inbox_count" 64 count

-- issue's where-bound isSome, restated so that its check can be named below.
isSome′ : Value → Bool
isSome′ (some _) = true
isSome′ (tuple (bool b ∷ _ ∷ [])) = b
isSome′ _ = false

-- FullAccountBody.issue with its caller argument (get 16 xs) abstracted.
issueWith : List Value → Value → M ⊤
issueWith xs caller′ = do
  present ← memberMap "grants" A.id
  (if present then (do
    old ← lookup "grants" A.id
    if flag (grantActive old) then (do
      epoch ← read "device_epoch"
      if equal (grantEpoch old) epoch then (do
        generation ← read "grant_generation"
        assert (not (equal (grantGeneration old) generation)) "grant already active")
        else return tt)
      else return tt) else return tt)
  let spend = flag A.withdrawUnshielded ∨ flag A.withdrawShielded ∨ flag A.withdrawToContract
  let readFlag = flag A.readFlag
  assert (spend ∨ readFlag) "empty scope"
  assert (spend ∨ not (isSome′ caller′)) "read-only grant cannot restrict caller"
  assert (not (flag A.withdrawShielded ∨ flag A.withdrawToContract) ∨ readFlag)
    "shielded spend requires read"
  assert (number A.perCallCap ≤ᵇ number A.cap) "per-call cap above cap"
  assert (not spend ∨ (0 <ᵇ number A.cap)) "spend without cap"
  assert (not spend ∨ (number A.perCallCap ≤ᵇ number A.maxCoinValue)) "coin bound below per-call cap"
  assert (not readFlag ∨ not (equal A.readKeyHash zero32)) "read without delegate key"
  assert ((number A.windowLength ≡ᵇ 0) ∧ (number A.windowCap ≡ᵇ 0)) "window bounds reserved"
  assert (spend ∨ (equal A.color zero32 ∧ (number A.recipientKind ≡ᵇ 0) ∧ equal A.recipient zero32 ∧
    (number A.maxCoinValue ≡ᵇ 0) ∧ (number A.perCallCap ≡ᵇ 0) ∧ (number A.cap ≡ᵇ 0)))
    "read-only grant carries object fields"
  epoch ← read "device_epoch"
  generation ← read "grant_generation"
  issued ← read "auth_nonce"
  spent ← spentCommit A.salt 0
  object ← objectCommit A.salt A.color A.recipientKind A.recipient A.maxCoinValue
  rp ← rpCommit A.salt A.rpIdHash
  caller ← callerCommit A.salt caller′
  let scope = tuple (A.withdrawUnshielded ∷ A.withdrawShielded ∷ A.withdrawToContract ∷
        A.readFlag ∷ object ∷ A.perCallCap ∷ A.cap ∷ A.expiresAt ∷ rp ∷
        A.readKeyHash ∷ nat 0 ∷ nat 0 ∷ caller ∷ [])
  insert "grants" A.id (tuple (epoch ∷ generation ∷ issued ∷ nat 0 ∷ spent ∷
    nat 0 ∷ nat 0 ∷ bool true ∷ scope ∷ []))
  where module A = IssueArguments xs

issueWith-preserves : ∀ {k} xs caller′ → stringEqual k "grants" ≡ false → Preserves k (issueWith xs caller′)
issueWith-preserves xs caller′ grants =
  preserves-bind (memberMap-preserves "grants" A.id) λ present →
  preserves-bind (if-preserves present
    (preserves-bind (lookup-preserves "grants" A.id) λ old →
     if-preserves (flag (grantActive old))
       (preserves-bind (read-preserves "device_epoch") λ epoch →
        if-preserves (equal (grantEpoch old) epoch)
          (preserves-bind (read-preserves "grant_generation") λ generation →
           assert-preserves (not (equal (grantGeneration old) generation)) "grant already active")
          (return-preserves tt))
       (return-preserves tt))
    (return-preserves tt)) λ _ →
  preserves-bind (assert-preserves (spend ∨ readFlag) "empty scope") λ _ →
  preserves-bind (assert-preserves (spend ∨ not (isSome′ caller′)) "read-only grant cannot restrict caller") λ _ →
  preserves-bind (assert-preserves (not (flag A.withdrawShielded ∨ flag A.withdrawToContract) ∨ readFlag)
    "shielded spend requires read") λ _ →
  preserves-bind (assert-preserves (number A.perCallCap ≤ᵇ number A.cap) "per-call cap above cap") λ _ →
  preserves-bind (assert-preserves (not spend ∨ (0 <ᵇ number A.cap)) "spend without cap") λ _ →
  preserves-bind (assert-preserves (not spend ∨ (number A.perCallCap ≤ᵇ number A.maxCoinValue))
    "coin bound below per-call cap") λ _ →
  preserves-bind (assert-preserves (not readFlag ∨ not (equal A.readKeyHash zero32))
    "read without delegate key") λ _ →
  preserves-bind (assert-preserves ((number A.windowLength ≡ᵇ 0) ∧ (number A.windowCap ≡ᵇ 0))
    "window bounds reserved") λ _ →
  preserves-bind (assert-preserves (spend ∨ (equal A.color zero32 ∧ (number A.recipientKind ≡ᵇ 0) ∧
    equal A.recipient zero32 ∧ (number A.maxCoinValue ≡ᵇ 0) ∧ (number A.perCallCap ≡ᵇ 0) ∧
    (number A.cap ≡ᵇ 0))) "read-only grant carries object fields") λ _ →
  preserves-bind (read-preserves "device_epoch") λ epoch →
  preserves-bind (read-preserves "grant_generation") λ generation →
  preserves-bind (read-preserves "auth_nonce") λ issued →
  preserves-bind (pure-preserves (spentCommit-pure A.salt 0)) λ spent →
  preserves-bind (pure-preserves (objectCommit-pure A.salt A.color A.recipientKind A.recipient
    A.maxCoinValue)) λ object →
  preserves-bind (pure-preserves (rpCommit-pure A.salt A.rpIdHash)) λ rp →
  preserves-bind (pure-preserves (callerCommit-pure A.salt caller′)) λ caller →
  insert-preserves "grants" A.id _ grants
  where
  module A = IssueArguments xs
  spend readFlag : Bool
  spend = flag A.withdrawUnshielded ∨ flag A.withdrawShielded ∨ flag A.withdrawToContract
  readFlag = flag A.readFlag

-- Splitting the caller value makes issue's isSome and isSome′ compute alike.
issue-preserves : ∀ {k} xs → stringEqual k "grants" ≡ false → Preserves k (issue xs)
issue-preserves xs grants with get 16 xs
... | none = issueWith-preserves xs none grants
... | some v = issueWith-preserves xs (some v) grants
... | tuple (bool b ∷ v ∷ []) = issueWith-preserves xs (tuple (bool b ∷ v ∷ [])) grants
... | nat n = issueWith-preserves xs (nat n) grants
... | bool b = issueWith-preserves xs (bool b) grants
... | bytes bs = issueWith-preserves xs (bytes bs) grants
... | tuple [] = issueWith-preserves xs (tuple []) grants
... | tuple (nat n ∷ vs) = issueWith-preserves xs (tuple (nat n ∷ vs)) grants
... | tuple (bool b ∷ []) = issueWith-preserves xs (tuple (bool b ∷ [])) grants
... | tuple (bool b ∷ v ∷ w ∷ vs) = issueWith-preserves xs (tuple (bool b ∷ v ∷ w ∷ vs)) grants
... | tuple (bytes bs ∷ vs) = issueWith-preserves xs (tuple (bytes bs ∷ vs)) grants
... | tuple (tuple ws ∷ vs) = issueWith-preserves xs (tuple (tuple ws ∷ vs)) grants
... | tuple (none ∷ vs) = issueWith-preserves xs (tuple (none ∷ vs)) grants
... | tuple (some w ∷ vs) = issueWith-preserves xs (tuple (some w ∷ vs)) grants

revoke-preserves : ∀ {k} id → stringEqual k "grants" ≡ false → Preserves k (revoke id)
revoke-preserves id grants =
  preserves-bind (memberMap-preserves "grants" id) λ present →
  preserves-bind (assert-preserves present "unknown grant") λ _ →
  preserves-bind (lookup-preserves "grants" id) λ old →
  preserves-bind (assert-preserves (flag (grantActive old)) "grant not live") λ _ →
  insert-preserves "grants" id (tuple (take 7 (fields old) ++ (bool false ∷ grantScope old ∷ []))) grants

publish-preserves : ∀ {k} xs → stringEqual k "recovery_pk" ≡ false →
  stringEqual k "recovery_session" ≡ false → stringEqual k "recovery_phi" ≡ false →
  stringEqual k "recovery_phi_len" ≡ false → stringEqual k "recovery_wrap" ≡ false →
  stringEqual k "recovery_version" ≡ false → Preserves k (publish xs)
publish-preserves xs recoveryKey session phi phiLength wrap version =
  preserves-bind (read-preserves "pending_recovery") λ pending →
  preserves-bind (assert-preserves (not (flag pending)) "recovery pending; cancel first") λ _ →
  preserves-bind (assert-preserves (1 ≤ᵇ number (get 6 xs)) "phi must not be empty") λ _ →
  preserves-bind (assert-preserves (number (get 6 xs) ≤ᵇ 4) "phi length out of range") λ _ →
  preserves-bind (if-preserves (number (get 6 xs) <ᵇ 2)
    (assert-preserves (number (get 3 xs) ≡ᵇ 0) "unused phi slot 2 not zero") (return-preserves tt)) λ _ →
  preserves-bind (if-preserves (number (get 6 xs) <ᵇ 3)
    (assert-preserves (number (get 4 xs) ≡ᵇ 0) "unused phi slot 3 not zero") (return-preserves tt)) λ _ →
  preserves-bind (if-preserves (number (get 6 xs) <ᵇ 4)
    (assert-preserves (number (get 5 xs) ≡ᵇ 0) "unused phi slot 4 not zero") (return-preserves tt)) λ _ →
  preserves-bind (assert-preserves (not (equal (get 1 xs) zero32)) "session nonce is zero") λ _ →
  preserves-bind (read-preserves "recovery_session") λ storedSession →
  preserves-bind (assert-preserves (not (equal (get 1 xs) storedSession)) "session nonce reused") λ _ →
  preserves-bind (read-preserves "recovery_pk") λ storedKey →
  preserves-bind (assert-preserves (not (equal (get 0 xs) storedKey)) "recovery commitment reused") λ _ →
  preserves-bind (pure-preserves (requireRecoveryKey-pure (get 0 xs))) λ _ →
  preserves-bind (write-preserves "recovery_pk" (get 0 xs) recoveryKey) λ _ →
  preserves-bind (write-preserves "recovery_session" (get 1 xs) session) λ _ →
  preserves-bind (insert-preserves "recovery_phi" (nat 1) (get 2 xs) phi) λ _ →
  preserves-bind (insert-preserves "recovery_phi" (nat 2) (get 3 xs) phi) λ _ →
  preserves-bind (insert-preserves "recovery_phi" (nat 3) (get 4 xs) phi) λ _ →
  preserves-bind (insert-preserves "recovery_phi" (nat 4) (get 5 xs) phi) λ _ →
  preserves-bind (write-preserves "recovery_phi_len" (get 6 xs) phiLength) λ _ →
  preserves-bind (write-preserves "recovery_wrap" (get 7 xs) wrap) λ _ →
  write-preserves "recovery_version" (nat 1) version

cancel-preserves : ∀ {k} → stringEqual k "pending_recovery" ≡ false →
  stringEqual k "pending_entry" ≡ false → stringEqual k "pending_recovery_pk" ≡ false →
  stringEqual k "pending_not_before" ≡ false → Preserves k cancel
cancel-preserves pending pendingEntry pendingKey notBefore =
  preserves-bind (read-preserves "pending_recovery") λ stored →
  preserves-bind (assert-preserves (flag stored) "no recovery pending") λ _ →
  preserves-bind (write-preserves "pending_recovery" (bool false) pending) λ _ →
  preserves-bind (write-preserves "pending_entry" zero32 pendingEntry) λ _ →
  preserves-bind (read-preserves "pending_recovery_pk") λ pk →
  preserves-bind (lift-preserves (ecMul P jubjub pk 0)) λ o →
  preserves-bind (write-preserves "pending_recovery_pk" o pendingKey) λ _ →
  write-preserves "pending_not_before" (nat 0) notBefore

body-frame : ∀ k op ctx args coin callerEntry →
  All (λ label → stringEqual k label ≡ false) (bodyWrites op) →
  Preserves k (body op ctx args coin callerEntry)
body-frame k withdrawUnshielded ctx xs coin e (balances ∷ []) =
  withdrawPublic-preserves (get 0 xs) (number (get 1 xs)) (get 2 xs) balances
body-frame k withdrawShielded ctx xs coin e [] =
  preserves-bind (sendCoin-preserves ctx true (get 0 xs) (number (get 2 xs)) coin) λ where
    (sent , change) → return-preserves change
body-frame k withdrawToContract ctx xs coin e [] =
  preserves-bind (sendCoin-preserves ctx false (get 0 xs) (number (get 2 xs)) coin) λ where
    (sent , change) → return-preserves (tuple (sent ∷ change ∷ []))
body-frame k appendInbox ctx xs coin e (inbox ∷ count ∷ []) =
  preserves-bind (inboxAppend-preserves (get 0 xs) inbox count) λ _ → return-preserves unit
body-frame k rotateEncKey ctx xs coin e (encryption ∷ []) =
  preserves-bind (write-preserves "enc_key" (get 0 xs) encryption) λ _ → return-preserves unit
body-frame k addDevice ctx xs coin e (devices ∷ count ∷ []) =
  preserves-bind (has-preserves "devices" (get 0 xs)) λ present →
  preserves-bind (assert-preserves (not present) "device entry already present") λ _ →
  preserves-bind (include-preserves "devices" (get 0 xs) devices) λ _ →
  preserves-bind (bump-preserves "device_count" 8 count) λ _ →
  return-preserves unit
body-frame k removeDevice ctx xs coin e (devices ∷ count ∷ []) =
  preserves-bind (readCount-preserves "device_count") λ n →
  preserves-bind (assert-preserves (1 <ᵇ n) "cannot remove last device") λ _ →
  preserves-bind (assert-preserves (not (equal (get 0 xs) e)) "cannot remove the authorising device") λ _ →
  preserves-bind (has-preserves "devices" (get 0 xs)) λ present →
  preserves-bind (assert-preserves present "unknown device entry") λ _ →
  preserves-bind (exclude-preserves "devices" (get 0 xs) devices) λ _ →
  preserves-bind (readCount-preserves "device_count") λ current →
  preserves-bind (writeCount-preserves "device_count" 8 (current ∸ 1) count) λ _ →
  return-preserves unit
body-frame k issueGrant ctx xs coin e (grants ∷ []) =
  preserves-bind (issue-preserves xs grants) λ _ → return-preserves unit
body-frame k revokeGrant ctx xs coin e (grants ∷ []) =
  preserves-bind (revoke-preserves (get 0 xs) grants) λ _ → return-preserves unit
body-frame k revokeAllGrants ctx xs coin e (generation ∷ grants ∷ []) =
  preserves-bind (preserves-bind (bump-preserves "grant_generation" 32 generation) λ _ →
    clear-preserves "grants" grants) λ _ →
  return-preserves unit
body-frame k publishRecovery ctx xs coin e (recoveryKey ∷ session ∷ phi ∷ phiLength ∷ wrap ∷ version ∷ []) =
  preserves-bind (publish-preserves xs recoveryKey session phi phiLength wrap version) λ _ →
  return-preserves unit
body-frame k cancelRecovery ctx xs coin e (pending ∷ pendingEntry ∷ pendingKey ∷ notBefore ∷ []) =
  preserves-bind (cancel-preserves pending pendingEntry pendingKey notBefore) λ _ → return-preserves unit

nonce-outside-bodies : ∀ op → All (λ label → stringEqual "auth_nonce" label ≡ false) (bodyWrites op)
nonce-outside-bodies withdrawUnshielded = refl ∷ []
nonce-outside-bodies withdrawShielded = []
nonce-outside-bodies withdrawToContract = []
nonce-outside-bodies appendInbox = refl ∷ refl ∷ []
nonce-outside-bodies rotateEncKey = refl ∷ []
nonce-outside-bodies addDevice = refl ∷ refl ∷ []
nonce-outside-bodies removeDevice = refl ∷ refl ∷ []
nonce-outside-bodies issueGrant = refl ∷ []
nonce-outside-bodies revokeGrant = refl ∷ []
nonce-outside-bodies revokeAllGrants = refl ∷ refl ∷ []
nonce-outside-bodies publishRecovery = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []
nonce-outside-bodies cancelRecovery = refl ∷ refl ∷ refl ∷ refl ∷ []

round-outside-bodies : ∀ op → All (λ label → stringEqual "round" label ≡ false) (bodyWrites op)
round-outside-bodies withdrawUnshielded = refl ∷ []
round-outside-bodies withdrawShielded = []
round-outside-bodies withdrawToContract = []
round-outside-bodies appendInbox = refl ∷ refl ∷ []
round-outside-bodies rotateEncKey = refl ∷ []
round-outside-bodies addDevice = refl ∷ refl ∷ []
round-outside-bodies removeDevice = refl ∷ refl ∷ []
round-outside-bodies issueGrant = refl ∷ []
round-outside-bodies revokeGrant = refl ∷ []
round-outside-bodies revokeAllGrants = refl ∷ refl ∷ []
round-outside-bodies publishRecovery = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []
round-outside-bodies cancelRecovery = refl ∷ refl ∷ refl ∷ refl ∷ []

epoch-outside-bodies : ∀ op → All (λ label → stringEqual "device_epoch" label ≡ false) (bodyWrites op)
epoch-outside-bodies withdrawUnshielded = refl ∷ []
epoch-outside-bodies withdrawShielded = []
epoch-outside-bodies withdrawToContract = []
epoch-outside-bodies appendInbox = refl ∷ refl ∷ []
epoch-outside-bodies rotateEncKey = refl ∷ []
epoch-outside-bodies addDevice = refl ∷ refl ∷ []
epoch-outside-bodies removeDevice = refl ∷ refl ∷ []
epoch-outside-bodies issueGrant = refl ∷ []
epoch-outside-bodies revokeGrant = refl ∷ []
epoch-outside-bodies revokeAllGrants = refl ∷ refl ∷ []
epoch-outside-bodies publishRecovery = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []
epoch-outside-bodies cancelRecovery = refl ∷ refl ∷ refl ∷ refl ∷ []

------------------------------------------------------------------------
-- Ledger states produced by authorise

removedState : State → Value → State
removedState s old = state (insertCell "devices" (tuple (removeSet old (fields (cell "devices" s)))) (ledger s))

rolledState : State → Value → Value → State
rolledState s old next = state (insertCell "devices"
  (tuple (insertSet next (fields (cell "devices" (removedState s old))))) (ledger (removedState s old)))

advancedState : State → Value → Value → State
advancedState t nonce round = state (insertCell "round" (nat (suc (number round)))
  (insertCell "auth_nonce" (nat (suc (number nonce))) (ledger t)))

removed-other : ∀ k s old → stringEqual k "devices" ≡ false →
  lookupCell k (ledger (removedState s old)) ≡ lookupCell k (ledger s)
removed-other k s old distinct =
  lookup-insert-other k "devices" (tuple (removeSet old (fields (cell "devices" s)))) (ledger s) distinct

rolled-other : ∀ k s old next → stringEqual k "devices" ≡ false →
  lookupCell k (ledger (rolledState s old next)) ≡ lookupCell k (ledger s)
rolled-other k s old next distinct =
  trans (lookup-insert-other k "devices" (tuple (insertSet next (fields (cell "devices" (removedState s old)))))
      (ledger (removedState s old)) distinct)
    (removed-other k s old distinct)

rolled-devices : ∀ s old next → lookupCell "devices" (ledger (rolledState s old next)) ≡
  just (tuple (insertSet next (removeSet old (fields (cell "devices" s)))))
rolled-devices s old next =
  trans (lookup-insert-same "devices" (tuple (insertSet next (fields (cell "devices" (removedState s old)))))
      (ledger (removedState s old)))
    (cong (λ v → just (tuple (insertSet next (fields v))))
      (cell-insert-same "devices" (tuple (removeSet old (fields (cell "devices" s)))) (ledger s)))

advanced-other : ∀ k t nonce round → stringEqual k "auth_nonce" ≡ false → stringEqual k "round" ≡ false →
  lookupCell k (ledger (advancedState t nonce round)) ≡ lookupCell k (ledger t)
advanced-other k t nonce round distinctNonce distinctRound =
  trans (lookup-insert-other k "round" (nat (suc (number round)))
      (insertCell "auth_nonce" (nat (suc (number nonce))) (ledger t)) distinctRound)
    (lookup-insert-other k "auth_nonce" (nat (suc (number nonce))) (ledger t) distinctNonce)

advanced-nonce : ∀ t nonce round →
  lookupCell "auth_nonce" (ledger (advancedState t nonce round)) ≡ just (nat (suc (number nonce)))
advanced-nonce t nonce round =
  trans (lookup-insert-other "auth_nonce" "round" (nat (suc (number round)))
      (insertCell "auth_nonce" (nat (suc (number nonce))) (ledger t)) refl)
    (lookup-insert-same "auth_nonce" (nat (suc (number nonce))) (ledger t))

advanced-round : ∀ t nonce round →
  lookupCell "round" (ledger (advancedState t nonce round)) ≡ just (nat (suc (number round)))
advanced-round t nonce round =
  lookup-insert-same "round" (nat (suc (number round))) (insertCell "auth_nonce" (nat (suc (number nonce))) (ledger t))

------------------------------------------------------------------------
-- authorise up to its membership check, for any continuation k

record LiveEntry (c : Curve) (ctx : Context) (a : Auth) (s : State) (current : Value) : Set where
  field keyChecked : Run (keyGuard c (key a) "device key has small order") s tt s
        epoch : Value
        epochCell : lookupCell "device_epoch" (ledger s) ≡ just epoch
        currentEntry : Run (entryAt c (self ctx) a (number epoch) (counter a)) s current s
        currentLive : member current (fields (cell "devices" s)) ≡ true

module LiveEntrySteps (c : Curve) (ctx : Context) (a : Auth) (k : Value → M Value) where
  afterMember : Value → Bool → M Value
  afterMember old known = assert known "unknown device entry" >> k old

  afterEntry : Value → M Value
  afterEntry old = has "devices" old >>= afterMember old

  afterEpoch : Value → ℕ → M Value
  afterEpoch addr epoch = entryAt c addr a epoch (counter a) >>= afterEntry

  afterSelf : Value → M Value
  afterSelf addr = readCount "device_epoch" >>= afterEpoch addr

  afterGuard : M Value
  afterGuard = readSelf ctx >>= afterSelf

  program : M Value
  program = keyGuard c (key a) "device key has small order" >> afterGuard

  abstract
    steps : ∀ {s y u} → Run program s y u →
      Σ Value λ current → LiveEntry c ctx a s current × Run (k current) s y u
    steps r with then (keyGuard c (key a) "device key has small order") {f = λ _ → afterGuard} r
    ... | _ , t₁ , guard , r₁ with then (readSelf ctx) {f = afterSelf} r₁
    ... | addr , t₂ , selfRun , r₂ with then (readCount "device_epoch") {f = afterEpoch addr} r₂
    ... | epoch , t₃ , epochRun , r₃ with then (entryAt c addr a epoch (counter a)) {f = afterEntry} r₃
    ... | current , t₄ , entryRun , r₄ with then (has "devices" current) {f = afterMember current} r₄
    ... | known , t₅ , hasRun , r₅ with then (assert known "unknown device entry") {f = λ _ → k current} r₅
    ... | _ , t₆ , assertRun , r₆ with pure-run (keyGuard-pure c (key a) "device key has small order") guard
    ... | refl , _ with readSelf-run ctx selfRun
    ... | refl , refl with readCount-run "device_epoch" epochRun
    ... | v , epochCell , refl , refl with pure-run (entryAt-pure c (self ctx) a (number v) (counter a)) entryRun
    ... | refl , _ with assert-run known "unknown device entry" assertRun
    ... | live , refl with has-run "devices" current hasRun
    ... | refl , refl = current , record
      { keyChecked = guard
      ; epoch = v
      ; epochCell = epochCell
      ; currentEntry = entryRun
      ; currentLive = live
      } , r₆

------------------------------------------------------------------------
-- Rolling (FullAccountCrypto.roll) and the counter bumps

record Rolled (c : Curve) (ctx : Context) (a : Auth) (h : Value) (s : State) (next : Value) : Set where
  field rollEpoch : Value
        rollEpochCell : lookupCell "device_epoch" (ledger s) ≡ just rollEpoch
        bounded : (suc (counter a) <ᵇ 2 ^ 64) ≡ true
        nextEntry : Run (entryAt c (self ctx) a (number rollEpoch) (suc (counter a))) s next s
        verified : Run (verify c a h (verificationMessage c)) s tt s

module RollSteps (c : Curve) (ctx : Context) (a : Auth) (old : Value) where
  afterEntry : Value → M Value
  afterEntry next = include "devices" next >> return next

  afterCounter : Value → ℕ → ℕ → M Value
  afterCounter addr epoch n = entryAt c addr a epoch n >>= afterEntry

  afterEpoch : Value → ℕ → M Value
  afterEpoch addr epoch = cast "use_counter" 64 (suc (counter a)) >>= afterCounter addr epoch

  afterSelf : Value → M Value
  afterSelf addr = readCount "device_epoch" >>= afterEpoch addr

  afterExclude : M Value
  afterExclude = readSelf ctx >>= afterSelf

  abstract
    steps : ∀ {s next t} → Run (roll c ctx a old) s next t →
      Σ Value λ epoch → lookupCell "device_epoch" (ledger s) ≡ just epoch ×
        (suc (counter a) <ᵇ 2 ^ 64) ≡ true ×
        Run (entryAt c (self ctx) a (number epoch) (suc (counter a))) s next s ×
        t ≡ rolledState s old next
    steps {s} r with then (exclude "devices" old) {f = λ _ → afterExclude} r
    ... | _ , t₁ , excludeRun , r₁ with then (readSelf ctx) {f = afterSelf} r₁
    ... | addr , t₂ , selfRun , r₂ with then (readCount "device_epoch") {f = afterEpoch addr} r₂
    ... | epoch , t₃ , epochRun , r₃ with then (cast "use_counter" 64 (suc (counter a))) {f = afterCounter addr epoch} r₃
    ... | n , t₄ , castRun , r₄ with then (entryAt c addr a epoch n) {f = afterEntry} r₄
    ... | next′ , t₅ , entryRun , r₅ with then (include "devices" next′) {f = λ _ → return next′} r₅
    ... | _ , t₆ , includeRun , run _ refl with exclude-run "devices" old excludeRun
    ... | refl with readSelf-run ctx selfRun
    ... | refl , refl with readCount-run "device_epoch" epochRun
    ... | v , epochCell , refl , refl with cast-run "use_counter" 64 (suc (counter a)) castRun
    ... | refl , bounded , refl with pure-run (entryAt-pure c (self ctx) a (number v) (suc (counter a))) entryRun
    ... | refl , anywhere with include-run "devices" next′ includeRun
    ... | refl = v , trans (sym (removed-other "device_epoch" s old refl)) epochCell , bounded , anywhere s , refl

-- authorise's curve-specific segment: P256 verifies before rolling, others after.
rollThenVerify verifyThenRoll : Curve → Context → Auth → Value → Value → M Value
rollThenVerify c ctx a h old = roll c ctx a old >>= λ next → verify c a h (verificationMessage c) >> return next
verifyThenRoll c ctx a h old = verify c a h (verificationMessage c) >> roll c ctx a old

rollThenVerify-steps : ∀ c ctx a h old {s next t} → Run (rollThenVerify c ctx a h old) s next t →
  Rolled c ctx a h s next × t ≡ rolledState s old next
rollThenVerify-steps c ctx a h old {s} r
  with then (roll c ctx a old) {f = λ next → verify c a h (verificationMessage c) >> return next} r
... | next′ , t₁ , rollRun , r₁ with then (verify c a h (verificationMessage c)) {f = λ _ → return next′} r₁
... | _ , t₂ , verifyRun , run _ refl
  with pure-run (Binding.verify-pure c a h (verificationMessage c)) verifyRun
... | refl , anywhere with RollSteps.steps c ctx a old rollRun
... | epoch , epochCell , bounded , nextEntry , rolled = record
  { rollEpoch = epoch ; rollEpochCell = epochCell ; bounded = bounded ; nextEntry = nextEntry
  ; verified = anywhere s } , rolled

verifyThenRoll-steps : ∀ c ctx a h old {s next t} → Run (verifyThenRoll c ctx a h old) s next t →
  Rolled c ctx a h s next × t ≡ rolledState s old next
verifyThenRoll-steps c ctx a h old {s} r
  with then (verify c a h (verificationMessage c)) {f = λ _ → roll c ctx a old} r
... | _ , t₁ , verifyRun , r₁ with pure-run (Binding.verify-pure c a h (verificationMessage c)) verifyRun
... | refl , anywhere with RollSteps.steps c ctx a old r₁
... | epoch , epochCell , bounded , nextEntry , rolled = record
  { rollEpoch = epoch ; rollEpochCell = epochCell ; bounded = bounded ; nextEntry = nextEntry
  ; verified = anywhere s } , rolled

advance : Value → M Value
advance next = bump "auth_nonce" 64 >> (bump "round" 64 >> return next)

abstract
  advance-steps : ∀ next {t y u} → Run (advance next) t y u →
    Σ Value λ nonce → Σ Value λ round →
      lookupCell "auth_nonce" (ledger t) ≡ just nonce × (suc (number nonce) <ᵇ 2 ^ 64) ≡ true ×
      lookupCell "round" (ledger t) ≡ just round × (suc (number round) <ᵇ 2 ^ 64) ≡ true ×
      y ≡ next × u ≡ advancedState t nonce round
  advance-steps next {t} r with then (bump "auth_nonce" 64) {f = λ _ → bump "round" 64 >> return next} r
  ... | _ , t₁ , nonceRun , r₁ with then (bump "round" 64) {f = λ _ → return next} r₁
  ... | _ , t₂ , roundRun , run _ refl with bump-run "auth_nonce" 64 nonceRun
  ... | nonce , nonceCell , nonceBound , refl with bump-run "round" 64 roundRun
  ... | round , roundCell , roundBound , refl =
    nonce , round , nonceCell , nonceBound ,
    trans (sym (lookup-insert-other "round" "auth_nonce" (nat (suc (number nonce))) (ledger t) refl)) roundCell ,
    roundBound , refl , refl

------------------------------------------------------------------------
-- Device authorisation evidence

assemble : ∀ {c ctx a h s current next nonce round} → LiveEntry c ctx a s current → Rolled c ctx a h s next →
  lookupCell "auth_nonce" (ledger (rolledState s current next)) ≡ just nonce →
  (suc (number nonce) <ᵇ 2 ^ 64) ≡ true →
  lookupCell "round" (ledger (rolledState s current next)) ≡ just round →
  (suc (number round) <ᵇ 2 ^ 64) ≡ true →
  Authorisation c ctx a h s next (advancedState (rolledState s current next) nonce round)
assemble {c} {ctx} {a} {h} {s} {current} {next} {nonce} {round} live rolled nonceCell nonceBound roundCell roundBound =
  record
    { keyChecked = LiveEntry.keyChecked live
    ; epoch = LiveEntry.epoch live
    ; epochCell = LiveEntry.epochCell live
    ; current = current
    ; currentEntry = LiveEntry.currentEntry live
    ; currentLive = LiveEntry.currentLive live
    ; verified = Rolled.verified rolled
    ; counterBounded = Rolled.bounded rolled
    ; nextEntry = subst (λ e → Run (entryAt c (self ctx) a (number e) (suc (counter a))) s next s)
        (just-injective (trans (sym (Rolled.rollEpochCell rolled)) (LiveEntry.epochCell live)))
        (Rolled.nextEntry rolled)
    ; devicesRolled = cell-lookup "devices" final
        (trans (advanced-other "devices" rolled′ nonce round refl refl) (rolled-devices s current next))
    ; nonce = nonce
    ; nonceAdvanced = record
      { previousCell = trans (sym (rolled-other "auth_nonce" s current next refl)) nonceCell
      ; bounded = nonceBound
      ; advanced = advanced-nonce rolled′ nonce round }
    ; round = round
    ; roundAdvanced = record
      { previousCell = trans (sym (rolled-other "round" s current next refl)) roundCell
      ; bounded = roundBound
      ; advanced = advanced-round rolled′ nonce round }
    ; unchanged = λ k devices nonce′ round′ →
        trans (advanced-other k rolled′ nonce round nonce′ round′) (rolled-other k s current next devices)
    }
  where
  rolled′ final : State
  rolled′ = rolledState s current next
  final = advancedState rolled′ nonce round

authorise-with : ∀ c ctx a h (segment : Value → M Value) →
  (∀ old {s next t} → Run (segment old) s next t → Rolled c ctx a h s next × t ≡ rolledState s old next) →
  ∀ {s next after} → Run (LiveEntrySteps.program c ctx a (λ old → segment old >>= advance)) s next after →
  Authorisation c ctx a h s next after
authorise-with c ctx a h segment rolls r
  with LiveEntrySteps.steps c ctx a (λ old → segment old >>= advance) r
... | current , live , r₁ with then (segment current) {f = advance} r₁
... | next′ , t₁ , segmentRun , r₂ with rolls current segmentRun
... | rolled , refl with advance-steps next′ r₂
... | nonce , round , nonceCell , nonceBound , roundCell , roundBound , refl , refl =
  assemble live rolled nonceCell nonceBound roundCell roundBound

-- Each curve's authorise is LiveEntrySteps.program with its own segment.
authorise-evidence : ∀ c ctx a h {s next after} → Run (authorise c ctx a h) s next after →
  Authorisation c ctx a h s next after
authorise-evidence jubjub ctx a h r =
  authorise-with jubjub ctx a h (rollThenVerify jubjub ctx a h) (rollThenVerify-steps jubjub ctx a h) r
authorise-evidence k256 ctx a h r =
  authorise-with k256 ctx a h (rollThenVerify k256 ctx a h) (rollThenVerify-steps k256 ctx a h) r
authorise-evidence p256 ctx a h r =
  authorise-with p256 ctx a h (verifyThenRoll p256 ctx a h) (verifyThenRoll-steps p256 ctx a h) r

------------------------------------------------------------------------
-- Device-authorised calls

coin-run : ∀ op ctx color {s x t} → Run (if shielded op then held ctx color else return none) s x t →
  x ≡ deviceCoin op ctx × t ≡ s
coin-run op ctx color (run _ execution) with shielded op
coin-run op ctx color (run _ refl) | true = refl , refl
coin-run op ctx color (run _ refl) | false = refl , refl

removalEntry-run : ∀ c ctx a {cached s x t} → Run (callerEntryAfter c removeDevice ctx a cached) s x t → t ≡ s
removalEntry-run c ctx a r
  with then (readSelf ctx) {f = λ addr → readCount "device_epoch" >>= λ epoch →
    cast "use_counter" 64 (suc (counter a)) >>= λ count → entryAt c addr a epoch count} r
... | addr , t₁ , selfRun , r₁
  with then (readCount "device_epoch") {f = λ epoch →
    cast "use_counter" 64 (suc (counter a)) >>= λ count → entryAt c addr a epoch count} r₁
... | epoch , t₂ , epochRun , r₂
  with then (cast "use_counter" 64 (suc (counter a))) {f = entryAt c addr a epoch} r₂
... | count , t₃ , castRun , r₃ =
  trans (proj₁ (pure-run (entryAt-pure c addr a epoch count) r₃))
    (trans (proj₂ (proj₂ (cast-run "use_counter" 64 (suc (counter a)) castRun)))
      (trans (proj₂ (proj₂ (proj₂ (readCount-run "device_epoch" epochRun))))
        (proj₂ (readSelf-run ctx selfRun))))

callerEntryAfter-run : ∀ c op ctx a cached {s x t} → Run (callerEntryAfter c op ctx a cached) s x t → t ≡ s
callerEntryAfter-run c removeDevice ctx a cached r = removalEntry-run c ctx a {cached = cached} r
callerEntryAfter-run c withdrawUnshielded ctx a cached (run _ refl) = refl
callerEntryAfter-run c withdrawShielded ctx a cached (run _ refl) = refl
callerEntryAfter-run c withdrawToContract ctx a cached (run _ refl) = refl
callerEntryAfter-run c appendInbox ctx a cached (run _ refl) = refl
callerEntryAfter-run c rotateEncKey ctx a cached (run _ refl) = refl
callerEntryAfter-run c addDevice ctx a cached (run _ refl) = refl
callerEntryAfter-run c issueGrant ctx a cached (run _ refl) = refl
callerEntryAfter-run c revokeGrant ctx a cached (run _ refl) = refl
callerEntryAfter-run c revokeAllGrants ctx a cached (run _ refl) = refl
callerEntryAfter-run c publishRecovery ctx a cached (run _ refl) = refl
callerEntryAfter-run c cancelRecovery ctx a cached (run _ refl) = refl

advanced-same : ∀ {label bits p q before after} → lookupCell label (ledger before) ≡ just q →
  Advanced label bits p before after → Advanced label bits q before after
advanced-same found advanced with just-injective (trans (sym (Advanced.previousCell advanced)) found)
... | refl = advanced

advanced-frame : ∀ {label bits p before middle after} → Advanced label bits p before middle →
  lookupCell label (ledger after) ≡ lookupCell label (ledger middle) → Advanced label bits p before after
advanced-frame advanced frame = record
  { previousCell = Advanced.previousCell advanced
  ; bounded = Advanced.bounded advanced
  ; advanced = trans frame (Advanced.advanced advanced) }

module DeviceCallSteps (c : Curve) (op : Operation) (ctx : Context) (xs : List Value) where
  args : List Value
  args = deviceArguments op xs

  a : Auth
  a = deviceAuth c op xs

  afterAuthorise : Value → Value → M Value
  afterAuthorise coin postEntry = callerEntryAfter c op ctx a postEntry >>= body op ctx args coin

  afterChallenge : Value → Value → M Value
  afterChallenge coin h = authorise c ctx a h >>= afterAuthorise coin

  afterNonce : Value → List Atom → Value → ℕ → M Value
  afterNonce coin atoms addr nonce =
    challengeAt c false (operationName op) addr a atoms nonce >>= afterChallenge coin

  afterSelf : Value → List Atom → Value → M Value
  afterSelf coin atoms addr = readCount "auth_nonce" >>= afterNonce coin atoms addr

  afterAtoms : Value → List Atom → M Value
  afterAtoms coin atoms = readSelf ctx >>= afterSelf coin atoms

  afterCoin : Value → M Value
  afterCoin coin = operationAtoms op args coin >>= afterAtoms coin

  coinStep : M Value
  coinStep = if shielded op then held ctx (get 1 args) else return none

  -- deviceCall up to its challenge, all read from the before state.
  record Prefix (s : State) (y : Value) (u : State) : Set where
    field atoms : List Atom
          encoded : Run (operationAtoms op args (deviceCoin op ctx)) s atoms s
          nonce : Value
          nonceCell : lookupCell "auth_nonce" (ledger s) ≡ just nonce
          challengeValue : Value
          challengeComputed : Run (challengeAt c false (operationName op) (self ctx) a atoms (number nonce))
            s challengeValue s
          rest : Run (afterChallenge (deviceCoin op ctx) challengeValue) s y u

  -- authorise, the caller-entry recomputation and the body.
  record Suffix (coin h : Value) (s : State) (y : Value) (u : State) : Set where
    field rolledEntry : Value
          authorisedState : State
          authoriseRun : Run (authorise c ctx a h) s rolledEntry authorisedState
          callerEntry : Value
          callerEntryRun : Run (callerEntryAfter c op ctx a rolledEntry) authorisedState callerEntry authorisedState
          bodyRun : Run (body op ctx args coin callerEntry) authorisedState y u

  -- Kept abstract so that later goals do not unfold these long with-chains.
  abstract
    prefix : ∀ {s y u} → Run (deviceCall c op ctx xs) s y u → Prefix s y u
    prefix r with then coinStep {f = afterCoin} r
    ... | coin , t₁ , coinRun , r₁ with coin-run op ctx (get 1 args) coinRun
    ... | refl , refl with then (operationAtoms op args (deviceCoin op ctx)) {f = afterAtoms (deviceCoin op ctx)} r₁
    ... | atoms , t₂ , atomsRun , r₂
      with Binding.pure-preserves (operationAtoms-pure op args (deviceCoin op ctx)) (Run.execution atomsRun)
    ... | refl with then (readSelf ctx) {f = afterSelf (deviceCoin op ctx) atoms} r₂
    ... | addr , t₃ , selfRun , r₃ with readSelf-run ctx selfRun
    ... | refl , refl with then (readCount "auth_nonce") {f = afterNonce (deviceCoin op ctx) atoms (self ctx)} r₃
    ... | n , t₄ , nonceRun , r₄ with readCount-run "auth_nonce" nonceRun
    ... | v , nonceCell , refl , refl
      with then (challengeAt c false (operationName op) (self ctx) a atoms (number v))
        {f = afterChallenge (deviceCoin op ctx)} r₄
    ... | h , t₅ , challengeRun , r₅
      with Binding.challengeAt-preserves c false (operationName op) (self ctx) a atoms (number v)
        (Run.execution challengeRun)
    ... | refl = record
      { atoms = atoms ; encoded = atomsRun ; nonce = v ; nonceCell = nonceCell
      ; challengeValue = h ; challengeComputed = challengeRun ; rest = r₅ }

    suffix : ∀ coin h {s y u} → Run (afterChallenge coin h) s y u → Suffix coin h s y u
    suffix coin h r with then (authorise c ctx a h) {f = afterAuthorise coin} r
    ... | entry′ , t₆ , authoriseRun , r₆ with then (callerEntryAfter c op ctx a entry′) {f = body op ctx args coin} r₆
    ... | callerEntry′ , t₇ , callerRun , bodyRun′ with callerEntryAfter-run c op ctx a entry′ callerRun
    ... | refl = record
      { rolledEntry = entry′ ; authorisedState = t₆ ; authoriseRun = authoriseRun
      ; callerEntry = callerEntry′ ; callerEntryRun = callerRun ; bodyRun = bodyRun′ }

  steps : ∀ {s y u} → Run (deviceCall c op ctx xs) s y u → DeviceCall c op ctx xs s y u
  steps r = record
    { atoms = Prefix.atoms before
    ; encoded = Prefix.encoded before
    ; nonce = Prefix.nonce before
    ; nonceAdvanced = advanced-frame (advanced-same (Prefix.nonceCell before) (Authorisation.nonceAdvanced authorised′))
        (body-frame "auth_nonce" op ctx args (deviceCoin op ctx) (Suffix.callerEntry after)
          (nonce-outside-bodies op) (Suffix.bodyRun after))
    ; challengeValue = Prefix.challengeValue before
    ; challengeComputed = Prefix.challengeComputed before
    ; rolledEntry = Suffix.rolledEntry after
    ; authorisedState = Suffix.authorisedState after
    ; authorised = authorised′
    ; callerEntry = Suffix.callerEntry after
    ; callerEntryRun = Suffix.callerEntryRun after
    ; bodyRun = Suffix.bodyRun after
    ; round = Authorisation.round authorised′
    ; roundAdvanced = advanced-frame (Authorisation.roundAdvanced authorised′)
        (body-frame "round" op ctx args (deviceCoin op ctx) (Suffix.callerEntry after)
          (round-outside-bodies op) (Suffix.bodyRun after))
    }
    where
    before = prefix r
    after = suffix (deviceCoin op ctx) (Prefix.challengeValue before) (Prefix.rest before)
    authorised′ = authorise-evidence c ctx a (Prefix.challengeValue before) (Suffix.authoriseRun after)

device-call-evidence : ∀ c op ctx xs {s y u} → Run (deviceCall c op ctx xs) s y u → DeviceCall c op ctx xs s y u
device-call-evidence c op ctx xs = DeviceCallSteps.steps c op ctx xs

------------------------------------------------------------------------
-- Activation

installedState : State → Value → State
installedState s initial = state (insertCell "boot" zero32 (insertCell "booted" (bool true)
  (insertCell "device_count" (nat 1)
    (insertCell "devices" (tuple (insertSet initial (fields (cell "devices" s)))) (ledger s)))))

module Installed (s : State) (initial : Value) where
  devicesValue : Value
  devicesValue = tuple (insertSet initial (fields (cell "devices" s)))

  withDevices withCount withBooted : List (String × Value)
  withDevices = insertCell "devices" devicesValue (ledger s)
  withCount = insertCell "device_count" (nat 1) withDevices
  withBooted = insertCell "booted" (bool true) withCount

  other : ∀ k → stringEqual k "devices" ≡ false → stringEqual k "device_count" ≡ false →
    stringEqual k "booted" ≡ false → stringEqual k "boot" ≡ false →
    lookupCell k (ledger (installedState s initial)) ≡ lookupCell k (ledger s)
  other k notDevices notCount notBooted notBoot =
    trans (lookup-insert-other k "boot" zero32 withBooted notBoot)
      (trans (lookup-insert-other k "booted" (bool true) withCount notBooted)
        (trans (lookup-insert-other k "device_count" (nat 1) withDevices notCount)
          (lookup-insert-other k "devices" devicesValue (ledger s) notDevices)))

  devices : lookupCell "devices" (ledger (installedState s initial)) ≡ just devicesValue
  devices =
    trans (lookup-insert-other "devices" "boot" zero32 withBooted refl)
      (trans (lookup-insert-other "devices" "booted" (bool true) withCount refl)
        (trans (lookup-insert-other "devices" "device_count" (nat 1) withDevices refl)
          (lookup-insert-same "devices" devicesValue (ledger s))))

  count : lookupCell "device_count" (ledger (installedState s initial)) ≡ just (nat 1)
  count =
    trans (lookup-insert-other "device_count" "boot" zero32 withBooted refl)
      (trans (lookup-insert-other "device_count" "booted" (bool true) withCount refl)
        (lookup-insert-same "device_count" (nat 1) withDevices))

  booted : lookupCell "booted" (ledger (installedState s initial)) ≡ just (bool true)
  booted =
    trans (lookup-insert-other "booted" "boot" zero32 withBooted refl)
      (lookup-insert-same "booted" (bool true) withCount)

  boot : lookupCell "boot" (ledger (installedState s initial)) ≡ just zero32
  boot = lookup-insert-same "boot" zero32 withBooted

not-true : ∀ {b} → not b ≡ true → b ≡ false
not-true {false} _ = refl
not-true {true} ()

module ActivationSteps (c : Curve) (ctx : Context) (a : Auth) (salt : Value) where
  finish : M Value
  finish = bump "round" 64 >> return unit

  afterBootedWrite : M Value
  afterBootedWrite = write "boot" zero32 >> finish

  afterCount : M Value
  afterCount = write "booted" (bool true) >> afterBootedWrite

  afterInclude : M Value
  afterInclude = write "device_count" (nat 1) >> afterCount

  afterInitial : Value → M Value
  afterInitial initial = include "devices" initial >> afterInclude

  afterEpoch : Value → ℕ → M Value
  afterEpoch addr epoch = entryAt c addr a epoch 0 >>= afterInitial

  afterSelf : Value → M Value
  afterSelf addr = readCount "device_epoch" >>= afterEpoch addr

  afterMatch : M Value
  afterMatch = readSelf ctx >>= afterSelf

  afterBoot : Value → Value → M Value
  afterBoot commitment boot = assert (equal commitment boot) "boot commitment mismatch" >> afterMatch

  afterCommitment : Value → M Value
  afterCommitment commitment = read "boot" >>= afterBoot commitment

  afterGuard : M Value
  afterGuard = bootCommit c a salt >>= afterCommitment

  afterUnbooted : M Value
  afterUnbooted = keyGuard c (key a) "device key has small order" >> afterGuard

  afterBootedRead : Value → M Value
  afterBootedRead booted = assert (not (flag booted)) "already activated" >> afterUnbooted

  -- activate's checks up to its initial entry, all from the before state.
  record Checked (s : State) (y : Value) (u : State) : Set where
    field booted : Value
          bootedCell : lookupCell "booted" (ledger s) ≡ just booted
          notBooted : not (flag booted) ≡ true
          keyChecked : Run (keyGuard c (key a) "device key has small order") s tt s
          commitment : Value
          committed : Run (bootCommit c a salt) s commitment s
          boot : Value
          bootCell : lookupCell "boot" (ledger s) ≡ just boot
          bootMatched : equal commitment boot ≡ true
          epoch : Value
          epochCell : lookupCell "device_epoch" (ledger s) ≡ just epoch
          initial : Value
          initialEntry : Run (entryAt c (self ctx) a (number epoch) 0) s initial s
          rest : Run (afterInitial initial) s y u

  -- Kept abstract, in short stages, so that goals stay small and later goals
  -- do not unfold these with-chains.
  abstract
    unbooted : ∀ {s y u} → Run (activate c ctx a salt) s y u →
      Σ Value λ booted → lookupCell "booted" (ledger s) ≡ just booted × not (flag booted) ≡ true ×
        Run afterUnbooted s y u
    unbooted r with then (read "booted") {f = afterBootedRead} r
    ... | booted , t₁ , bootedRun , r₁ with read-run "booted" bootedRun
    ... | bootedCell , refl
      with then (assert (not (flag booted)) "already activated") {f = λ _ → afterUnbooted} r₁
    ... | _ , t₂ , notBootedRun , r₂ with assert-run (not (flag booted)) "already activated" notBootedRun
    ... | notBooted , refl = booted , bootedCell , notBooted , r₂

    opened : ∀ {s y u} → Run afterUnbooted s y u →
      Run (keyGuard c (key a) "device key has small order") s tt s ×
      Σ Value λ commitment → Run (bootCommit c a salt) s commitment s × Run (afterCommitment commitment) s y u
    opened r with then (keyGuard c (key a) "device key has small order") {f = λ _ → afterGuard} r
    ... | _ , t₃ , guardRun , r₃
      with Binding.pure-preserves (keyGuard-pure c (key a) "device key has small order") (Run.execution guardRun)
    ... | refl with then (bootCommit c a salt) {f = afterCommitment} r₃
    ... | commitment , t₄ , commitRun , r₄
      with Binding.pure-preserves (bootCommit-pure c a salt) (Run.execution commitRun)
    ... | refl = guardRun , commitment , commitRun , r₄

    matching : ∀ commitment {s y u} → Run (afterCommitment commitment) s y u →
      Σ Value λ boot → lookupCell "boot" (ledger s) ≡ just boot × equal commitment boot ≡ true × Run afterMatch s y u
    matching commitment r with then (read "boot") {f = afterBoot commitment} r
    ... | boot , t₅ , bootRun , r₅ with read-run "boot" bootRun
    ... | bootCell , refl
      with then (assert (equal commitment boot) "boot commitment mismatch") {f = λ _ → afterMatch} r₅
    ... | _ , t₆ , matchRun , r₆ with assert-run (equal commitment boot) "boot commitment mismatch" matchRun
    ... | matched , refl = boot , bootCell , matched , r₆

    entered : ∀ {s y u} → Run afterMatch s y u →
      Σ Value λ epoch → lookupCell "device_epoch" (ledger s) ≡ just epoch ×
      Σ Value λ initial → Run (entryAt c (self ctx) a (number epoch) 0) s initial s × Run (afterInitial initial) s y u
    entered r with then (readSelf ctx) {f = afterSelf} r
    ... | addr , t₇ , selfRun , r₇ with readSelf-run ctx selfRun
    ... | refl , refl with then (readCount "device_epoch") {f = afterEpoch (self ctx)} r₇
    ... | epoch , t₈ , epochRun , r₈ with readCount-run "device_epoch" epochRun
    ... | v , epochCell , refl , refl with then (entryAt c (self ctx) a (number v) 0) {f = afterInitial} r₈
    ... | initial , t₉ , entryRun , r₉
      with Binding.pure-preserves (entryAt-pure c (self ctx) a (number v) 0) (Run.execution entryRun)
    ... | refl = v , epochCell , initial , entryRun , r₉

  checks : ∀ {s y u} → Run (activate c ctx a salt) s y u → Checked s y u
  checks r =
    let (booted , bootedCell , notBooted , r₁) = unbooted r
        (guardRun , commitment , commitRun , r₂) = opened r₁
        (boot , bootCell , matched , r₃) = matching commitment r₂
        (epoch , epochCell , initial , entryRun , r₄) = entered r₃
    in record
      { booted = booted ; bootedCell = bootedCell ; notBooted = notBooted ; keyChecked = guardRun
      ; commitment = commitment ; committed = commitRun ; boot = boot ; bootCell = bootCell
      ; bootMatched = matched ; epoch = epoch ; epochCell = epochCell ; initial = initial
      ; initialEntry = entryRun ; rest = r₄ }

  abstract
    writes : ∀ initial {s y u} → Run (afterInitial initial) s y u →
      Σ Value λ round → lookupCell "round" (ledger (installedState s initial)) ≡ just round ×
        (suc (number round) <ᵇ 2 ^ 64) ≡ true ×
        u ≡ state (insertCell "round" (nat (suc (number round))) (ledger (installedState s initial)))
    writes initial r with then (include "devices" initial) {f = λ _ → afterInclude} r
    ... | _ , t₁₀ , includeRun , r₁₀ with include-run "devices" initial includeRun
    ... | refl with then (write "device_count" (nat 1)) {f = λ _ → afterCount} r₁₀
    ... | _ , t₁₁ , countRun , r₁₁ with write-run "device_count" (nat 1) countRun
    ... | refl with then (write "booted" (bool true)) {f = λ _ → afterBootedWrite} r₁₁
    ... | _ , t₁₂ , bootedWrite , r₁₂ with write-run "booted" (bool true) bootedWrite
    ... | refl with then (write "boot" zero32) {f = λ _ → finish} r₁₂
    ... | _ , t₁₃ , bootWrite , r₁₃ with write-run "boot" zero32 bootWrite
    ... | refl with then (bump "round" 64) {f = λ _ → return unit} r₁₃
    ... | _ , t₁₄ , roundRun , run _ refl with bump-run "round" 64 roundRun
    ... | round , roundCell , roundBound , refl = round , roundCell , roundBound , refl

  steps : ∀ {s y u} → Run (activate c ctx a salt) s y u → Activation c ctx a salt s u
  steps {s} {u = u} r = record
    { booted = Checked.booted checked
    ; bootedCell = Checked.bootedCell checked
    ; notBooted = not-true (Checked.notBooted checked)
    ; keyChecked = Checked.keyChecked checked
    ; commitment = Checked.commitment checked
    ; committed = Checked.committed checked
    ; boot = Checked.boot checked
    ; bootCell = Checked.bootCell checked
    ; bootMatched = Checked.bootMatched checked
    ; epoch = Checked.epoch checked
    ; epochCell = Checked.epochCell checked
    ; initial = initial
    ; initialEntry = Checked.initialEntry checked
    ; installed = cell-lookup "devices" u
        (final (trans (lookup-insert-other "devices" "round" roundValue installedCells refl)
          (Installed.devices s initial)))
    ; deviceCount = final (trans (lookup-insert-other "device_count" "round" roundValue installedCells refl)
        (Installed.count s initial))
    ; nowBooted = final (trans (lookup-insert-other "booted" "round" roundValue installedCells refl)
        (Installed.booted s initial))
    ; bootCleared = final (trans (lookup-insert-other "boot" "round" roundValue installedCells refl)
        (Installed.boot s initial))
    ; round = round
    ; roundAdvanced = record
      { previousCell = trans (sym (Installed.other s initial "round" refl refl refl refl)) roundCell
      ; bounded = roundBound
      ; advanced = final (lookup-insert-same "round" roundValue installedCells) }
    ; unchanged = λ k devices count booted′ boot′ round′ →
        final (trans (lookup-insert-other k "round" roundValue installedCells round′)
          (Installed.other s initial k devices count booted′ boot′))
    }
    where
    checked = checks r
    initial = Checked.initial checked
    written = writes initial (Checked.rest checked)
    round = proj₁ written
    roundCell = proj₁ (proj₂ written)
    roundBound = proj₁ (proj₂ (proj₂ written))
    roundValue : Value
    roundValue = nat (suc (number round))
    installedCells : List (String × Value)
    installedCells = ledger (installedState s initial)
    -- Transport a fact about the written ledger to the final state u.
    final : ∀ {k v} → lookupCell k (insertCell "round" roundValue installedCells) ≡ v → lookupCell k (ledger u) ≡ v
    final {k} {v} = subst (λ t → lookupCell k (ledger t) ≡ v) (sym (proj₂ (proj₂ (proj₂ written))))

activation-evidence : ∀ c ctx a salt {s y u} → Run (activate c ctx a salt) s y u → Activation c ctx a salt s u
activation-evidence c ctx a salt = ActivationSteps.steps c ctx a salt

------------------------------------------------------------------------
-- Consequences

private
  true≢false : true ≢ false
  true≢false ()

  false≢true : false ≢ true
  false≢true ()

activation-once : ∀ c ctx a salt {before y after} → lookupCell "booted" (ledger before) ≡ just (bool true) →
  ¬ Run (activate c ctx a salt) before y after
activation-once c ctx a salt booted r =
  true≢false (subst (λ v → flag v ≡ false)
    (just-injective (trans (sym (Activation.bootedCell activated)) booted)) (Activation.notBooted activated))
  where activated = activation-evidence c ctx a salt r

device-call-needs-device : ∀ c op ctx xs {before y after} → cell "devices" before ≡ tuple [] →
  ¬ Run (deviceCall c op ctx xs) before y after
device-call-needs-device c op ctx xs empty r =
  false≢true (subst (λ v → member (Authorisation.current authorised) (fields v) ≡ true) empty
    (Authorisation.currentLive authorised))
  where authorised = DeviceCall.authorised (device-call-evidence c op ctx xs r)

no-device-call-at-deployment : ∀ c op ctx xs boot encryption recovery wrap window {y after} →
  ¬ Run (deviceCall c op ctx xs) (initialState boot encryption recovery wrap window) y after
no-device-call-at-deployment c op ctx xs boot encryption recovery wrap window =
  device-call-needs-device c op ctx xs refl

member-++ : ∀ x xs ys → member x (xs ++ ys) ≡ member x xs ∨ member x ys
member-++ x [] ys = refl
member-++ x (z ∷ zs) ys =
  trans (cong (equal x z ∨_) (member-++ x zs ys)) (sym (∨-assoc (equal x z) (member x zs) (member x ys)))

member-removeSet : ∀ x xs → member x (removeSet x xs) ≡ false
member-removeSet x [] = refl
member-removeSet x (y ∷ ys) with equal x y in eq
... | true = member-removeSet x ys
... | false = trans (cong (_∨ member x (removeSet x ys)) eq) (member-removeSet x ys)

member-insertSet : ∀ x y ys → equal x y ≡ false → member x ys ≡ false → member x (insertSet y ys) ≡ false
member-insertSet x y ys distinct absent with member y ys
... | true = absent
... | false = trans (member-++ x ys (y ∷ [])) (cong₂ (λ p q → p ∨ (q ∨ false)) absent distinct)

entry-consumed : ∀ {c ctx a h before next after} (authorised : Authorisation c ctx a h before next after) →
  equal (Authorisation.current authorised) next ≡ false →
  member (Authorisation.current authorised) (fields (cell "devices" after)) ≡ false
entry-consumed {before = before} {next} authorised distinct =
  trans (cong (λ v → member current (fields v)) (Authorisation.devicesRolled authorised))
    (member-insertSet current next (removeSet current (fields (cell "devices" before))) distinct
      (member-removeSet current (fields (cell "devices" before))))
  where current = Authorisation.current authorised

private
  cell-frame : ∀ k {s t} → lookupCell k (ledger t) ≡ lookupCell k (ledger s) → cell k t ≡ cell k s
  cell-frame k {s} {t} same with lookupCell k (ledger t) | lookupCell k (ledger s)
  ... | nothing | nothing = refl
  ... | just v | just w = just-injective same
  ... | nothing | just w with same
  ... | ()
  cell-frame k {s} {t} same | just v | nothing with same
  ... | ()

  run-answer-unique : ∀ {A : Set} {m : M A} {s x y t u} →
    Run m s x t → Run m s y u → x ≡ y
  run-answer-unique (run _ first) (run _ second) = answer (trans (sym first) second)
    where
    answer : ∀ {A x y t u es fs} → accepted {A} x t es ≡ accepted y u fs → x ≡ y
    answer refl = refl

consumed-credentials-refused : ∀ c op {ctx xs s y t}
  (first : DeviceCall c op ctx xs s y t) →
  All (λ label → stringEqual "devices" label ≡ false) (bodyWrites op) →
  equal (Authorisation.current (DeviceCall.authorised first)) (DeviceCall.rolledEntry first) ≡ false →
  ∀ {ctx′ a h next u} → self ctx′ ≡ self ctx → a ≡ deviceAuth c op xs →
  ¬ Authorisation c ctx′ a h t next u
consumed-credentials-refused c op {ctx} {xs} {s} {y} {t} first framed distinct
  {ctx′} {a} sameSelf sameAuth second = true≢false
    (trans (sym (Authorisation.currentLive second))
      (trans (cong (λ entry → member entry (fields (cell "devices" t))) sameCurrent) absent))
  where
  module First = DeviceCall first
  module Initial = Authorisation First.authorised
  module Second = Authorisation second

  bodyDevices = body-frame "devices" op ctx (deviceArguments op xs) (deviceCoin op ctx)
    First.callerEntry framed First.bodyRun

  absent : member Initial.current (fields (cell "devices" t)) ≡ false
  absent = trans (cong (λ devices → member Initial.current (fields devices))
    (cell-frame "devices" {s = First.authorisedState} {t = t} bodyDevices))
    (entry-consumed First.authorised distinct)

  sameEpoch : Second.epoch ≡ Initial.epoch
  sameEpoch = just-injective (trans (sym Second.epochCell)
    (trans (body-frame "device_epoch" op ctx (deviceArguments op xs) (deviceCoin op ctx)
      First.callerEntry (epoch-outside-bodies op) First.bodyRun)
      (trans (Initial.unchanged "device_epoch" refl refl refl) Initial.epochCell)))

  sameCurrent : Second.current ≡ Initial.current
  sameCurrent = run-answer-unique
    (subst (λ m → Run m t Second.current t)
      (cong₂ (λ addr credentials → entryAt c addr credentials (number Initial.epoch)
        (counter credentials)) sameSelf sameAuth)
      (subst (λ epoch → Run (entryAt c (self ctx′) a (number epoch) (counter a))
        t Second.current t) sameEpoch Second.currentEntry))
    (proj₂ (pure-run (entryAt-pure c (self ctx) (deviceAuth c op xs)
      (number Initial.epoch) (counter (deviceAuth c op xs))) Initial.currentEntry) t)

exact-device-replay-refused : ∀ c op ctx xs {s y t}
  (first : Run (deviceCall c op ctx xs) s y t) →
  All (λ label → stringEqual "devices" label ≡ false) (bodyWrites op) →
  equal (Authorisation.current (DeviceCall.authorised (device-call-evidence c op ctx xs first)))
    (DeviceCall.rolledEntry (device-call-evidence c op ctx xs first)) ≡ false →
  ∀ {result after} → ¬ Run (deviceCall c op ctx xs) t result after
exact-device-replay-refused c op ctx xs first framed distinct second =
  consumed-credentials-refused c op (device-call-evidence c op ctx xs first) framed distinct
    refl refl (DeviceCall.authorised (device-call-evidence c op ctx xs second))

------------------------------------------------------------------------
-- Challenge separation

challengePreimage : Curve → Value → Value → Auth → List Atom → List Atom → ℕ → List Atom
challengePreimage jubjub dst addr a ks atoms n =
  b32 dst ∷ contract addr ∷ jub (sigR a) ∷ ks ++ atoms ++ u64 (nat n) ∷ u64 (nat (grind a)) ∷ []
challengePreimage k256 dst addr a ks atoms n = b32 dst ∷ contract addr ∷ ks ++ atoms ++ u64 (nat n) ∷ []
challengePreimage p256 dst addr a ks atoms n = b32 dst ∷ contract addr ∷ ks ++ atoms ++ u64 (nat n) ∷ []

ChallengeParts : Curve → String → Value → Auth → List Atom → ℕ → State → Value → Set
ChallengeParts c opn addr a atoms n s h = Σ Value λ dst → Σ (List Atom) λ ks →
  persistentHash P (("Bytes<64>" , pad 64 (Binding.authTag false c opn)) ∷ []) ≡ success dst ×
  Run (keyAtoms c (key a)) s ks s × persistentHash P (challengePreimage c dst addr a ks atoms n) ≡ success h

challenge-parts : ∀ c opn addr a atoms n {s h t} → Run (challengeAt c false opn addr a atoms n) s h t →
  ChallengeParts c opn addr a atoms n s h
challenge-parts jubjub opn addr a atoms n r
  with then (hashTag (Binding.authTag false jubjub opn))
    {f = λ dst → keyAtoms jubjub (key a) >>= λ ks → hash (challengePreimage jubjub dst addr a ks atoms n)} r
... | dst , t₁ , tagRun , r₁
  with then (keyAtoms jubjub (key a)) {f = λ ks → hash (challengePreimage jubjub dst addr a ks atoms n)} r₁
... | ks , t₂ , keyRun , r₂
  with hash-run (("Bytes<64>" , pad 64 (Binding.authTag false jubjub opn)) ∷ []) tagRun
... | tagged , refl with pure-run (Binding.keyAtoms-pure jubjub (key a)) keyRun
... | refl , _ with hash-run (challengePreimage jubjub dst addr a ks atoms n) r₂
... | hashed , refl = dst , ks , tagged , keyRun , hashed
challenge-parts k256 opn addr a atoms n r
  with then (hashTag (Binding.authTag false k256 opn))
    {f = λ dst → keyAtoms k256 (key a) >>= λ ks → hash (challengePreimage k256 dst addr a ks atoms n)} r
... | dst , t₁ , tagRun , r₁
  with then (keyAtoms k256 (key a)) {f = λ ks → hash (challengePreimage k256 dst addr a ks atoms n)} r₁
... | ks , t₂ , keyRun , r₂
  with hash-run (("Bytes<64>" , pad 64 (Binding.authTag false k256 opn)) ∷ []) tagRun
... | tagged , refl with pure-run (Binding.keyAtoms-pure k256 (key a)) keyRun
... | refl , _ with hash-run (challengePreimage k256 dst addr a ks atoms n) r₂
... | hashed , refl = dst , ks , tagged , keyRun , hashed
challenge-parts p256 opn addr a atoms n r
  with then (hashTag (Binding.authTag false p256 opn))
    {f = λ dst → keyAtoms p256 (key a) >>= λ ks → hash (challengePreimage p256 dst addr a ks atoms n)} r
... | dst , t₁ , tagRun , r₁
  with then (keyAtoms p256 (key a)) {f = λ ks → hash (challengePreimage p256 dst addr a ks atoms n)} r₁
... | ks , t₂ , keyRun , r₂
  with hash-run (("Bytes<64>" , pad 64 (Binding.authTag false p256 opn)) ∷ []) tagRun
... | tagged , refl with pure-run (Binding.keyAtoms-pure p256 (key a)) keyRun
... | refl , _ with hash-run (challengePreimage p256 dst addr a ks atoms n) r₂
... | hashed , refl = dst , ks , tagged , keyRun , hashed

keyWidth : Curve → ℕ
keyWidth jubjub = 1
keyWidth k256 = 2
keyWidth p256 = 2

keyAtoms-width : ∀ c pk {s ks t} → Run (keyAtoms c pk) s ks t → length ks ≡ keyWidth c
keyAtoms-width jubjub pk (run _ refl) = refl
keyAtoms-width k256 pk (run _ execution) with pointCoordinates P k256 pk
keyAtoms-width k256 pk (run _ ()) | failure _
keyAtoms-width k256 pk (run _ refl) | success (_ , _) = refl
keyAtoms-width p256 pk (run _ execution) with pointCoordinates P p256 pk
keyAtoms-width p256 pk (run _ ()) | failure _
keyAtoms-width p256 pk (run _ refl) | success (_ , _) = refl

atomCount : Operation → ℕ
atomCount withdrawUnshielded = 3
atomCount withdrawShielded = 4
atomCount withdrawToContract = 4
atomCount appendInbox = 1
atomCount rotateEncKey = 1
atomCount addDevice = 1
atomCount removeDevice = 1
atomCount issueGrant = 2
atomCount revokeGrant = 1
atomCount revokeAllGrants = 0
atomCount publishRecovery = 8
atomCount cancelRecovery = 0

operationAtoms-width : ∀ op xs coin {s atoms t} → Run (operationAtoms op xs coin) s atoms t →
  length atoms ≡ atomCount op
operationAtoms-width withdrawUnshielded xs coin (run _ refl) = refl
operationAtoms-width withdrawShielded xs coin (run _ refl) = refl
operationAtoms-width withdrawToContract xs coin (run _ refl) = refl
operationAtoms-width appendInbox xs coin (run _ refl) = refl
operationAtoms-width rotateEncKey xs coin (run _ refl) = refl
operationAtoms-width addDevice xs coin (run _ refl) = refl
operationAtoms-width removeDevice xs coin (run _ refl) = refl
operationAtoms-width issueGrant xs coin r
  with then (scopeDigest xs) {f = λ digest → return (b32 (get 0 xs) ∷ b32 digest ∷ [])} r
... | _ , _ , _ , run _ refl = refl
operationAtoms-width revokeGrant xs coin (run _ refl) = refl
operationAtoms-width revokeAllGrants xs coin (run _ refl) = refl
operationAtoms-width publishRecovery xs coin (run _ refl) = refl
operationAtoms-width cancelRecovery xs coin (run _ refl) = refl

++-cancel : ∀ {A : Set} (xs ys : List A) {us vs} → length xs ≡ length ys → xs ++ us ≡ ys ++ vs → us ≡ vs
++-cancel [] [] _ same = same
++-cancel (x ∷ xs) (y ∷ ys) lengths same = ++-cancel xs ys (suc-injective lengths) (∷-injectiveʳ same)
++-cancel [] (_ ∷ _) () _
++-cancel (_ ∷ _) [] () _

u64-injective : ∀ {m n} → u64 (nat m) ≡ u64 (nat n) → m ≡ n
u64-injective = cong (λ atom → number (proj₂ atom))

preimage-fields : ∀ c {d₁ d₂ addr₁ addr₂ a₁ a₂ ks₁ ks₂ atoms₁ atoms₂ n₁ n₂} →
  length ks₁ ≡ length ks₂ → length atoms₁ ≡ length atoms₂ →
  challengePreimage c d₁ addr₁ a₁ ks₁ atoms₁ n₁ ≡ challengePreimage c d₂ addr₂ a₂ ks₂ atoms₂ n₂ →
  addr₁ ≡ addr₂ × n₁ ≡ n₂
preimage-fields jubjub {ks₁ = ks₁} {ks₂} {atoms₁} {atoms₂} keys operation same =
  cong proj₂ (∷-injectiveˡ (∷-injectiveʳ same)) ,
  u64-injective (∷-injectiveˡ (++-cancel atoms₁ atoms₂ operation
    (++-cancel ks₁ ks₂ keys (∷-injectiveʳ (∷-injectiveʳ (∷-injectiveʳ same))))))
preimage-fields k256 {ks₁ = ks₁} {ks₂} {atoms₁} {atoms₂} keys operation same =
  cong proj₂ (∷-injectiveˡ (∷-injectiveʳ same)) ,
  u64-injective (∷-injectiveˡ (++-cancel atoms₁ atoms₂ operation
    (++-cancel ks₁ ks₂ keys (∷-injectiveʳ (∷-injectiveʳ same)))))
preimage-fields p256 {ks₁ = ks₁} {ks₂} {atoms₁} {atoms₂} keys operation same =
  cong proj₂ (∷-injectiveˡ (∷-injectiveʳ same)) ,
  u64-injective (∷-injectiveˡ (++-cancel atoms₁ atoms₂ operation
    (++-cancel ks₁ ks₂ keys (∷-injectiveʳ (∷-injectiveʳ same)))))

private
  separated : ∀ {A B : Set} {x₁ x₂ : A} {y₁ y₂ : B} → x₁ ≢ x₂ ⊎ y₁ ≢ y₂ → x₁ ≡ x₂ × y₁ ≡ y₂ → ⊥
  separated (inj₁ different) (same , _) = different same
  separated (inj₂ different) (_ , same) = different same

challenge-collision : ∀ c op {ctx₁ ctx₂ xs₁ xs₂ s₁ s₂ y₁ y₂ u₁ u₂}
  (first : DeviceCall c op ctx₁ xs₁ s₁ y₁ u₁) (second : DeviceCall c op ctx₂ xs₂ s₂ y₂ u₂) →
  self ctx₁ ≢ self ctx₂ ⊎ number (DeviceCall.nonce first) ≢ number (DeviceCall.nonce second) →
  DeviceCall.challengeValue first ≡ DeviceCall.challengeValue second → Collision
challenge-collision c op {ctx₁} {ctx₂} {xs₁} {xs₂} first second different same
  with challenge-parts c (operationName op) (self ctx₁) (deviceAuth c op xs₁) (DeviceCall.atoms first)
         (number (DeviceCall.nonce first)) (DeviceCall.challengeComputed first)
     | challenge-parts c (operationName op) (self ctx₂) (deviceAuth c op xs₂) (DeviceCall.atoms second)
         (number (DeviceCall.nonce second)) (DeviceCall.challengeComputed second)
... | d₁ , ks₁ , _ , keys₁ , hashed₁ | d₂ , ks₂ , _ , keys₂ , hashed₂ = record
  { left = challengePreimage c d₁ (self ctx₁) (deviceAuth c op xs₁) ks₁ (DeviceCall.atoms first)
      (number (DeviceCall.nonce first))
  ; right = challengePreimage c d₂ (self ctx₂) (deviceAuth c op xs₂) ks₂ (DeviceCall.atoms second)
      (number (DeviceCall.nonce second))
  ; distinct = λ preimages → separated different (preimage-fields c keys operation preimages)
  ; digest = DeviceCall.challengeValue second
  ; leftHash = subst (λ h → persistentHash P (challengePreimage c d₁ (self ctx₁) (deviceAuth c op xs₁) ks₁
      (DeviceCall.atoms first) (number (DeviceCall.nonce first))) ≡ success h) same hashed₁
  ; rightHash = hashed₂
  }
  where
  keys : length ks₁ ≡ length ks₂
  keys = trans (keyAtoms-width c (key (deviceAuth c op xs₁)) keys₁)
    (sym (keyAtoms-width c (key (deviceAuth c op xs₂)) keys₂))
  operation : length (DeviceCall.atoms first) ≡ length (DeviceCall.atoms second)
  operation = trans (operationAtoms-width op (deviceArguments op xs₁) (deviceCoin op ctx₁) (DeviceCall.encoded first))
    (sym (operationAtoms-width op (deviceArguments op xs₂) (deviceCoin op ctx₂) (DeviceCall.encoded second)))

immediate-replay-collision : ∀ c op {ctx₁ ctx₂ xs₁ xs₂ s y₁ t y₂ u}
  (first : DeviceCall c op ctx₁ xs₁ s y₁ t) (second : DeviceCall c op ctx₂ xs₂ t y₂ u) →
  DeviceCall.challengeValue first ≡ DeviceCall.challengeValue second → Collision
immediate-replay-collision c op first second = challenge-collision c op first second (inj₂ moved)
  where
  moved : number (DeviceCall.nonce first) ≢ number (DeviceCall.nonce second)
  moved same = 1+n≢n (sym (trans same (cong number (just-injective
    (trans (sym (Advanced.previousCell (DeviceCall.nonceAdvanced second)))
      (Advanced.advanced (DeviceCall.nonceAdvanced first)))))))

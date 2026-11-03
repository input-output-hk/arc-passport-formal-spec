{-# OPTIONS --safe --without-K #-}

-- Proofs for Conformance.FullAccountGrantSecurityProperties. grantCall is
-- decomposed along its actual binds with FullAccountExecution.then; each step
-- names the source computation explicitly. Where a step's answer is not a
-- fresh variable (memberMap, readSelf, readTimeLess, insert), the continuation
-- is pinned. Steps whose source code sits in a where-block are reached by
-- splitting the curve, or by with-abstraction on the execution equation.

open import Conformance.FullAccountTypes

module Conformance.FullAccountGrantSecurityProof (P : Primitives) where

open import Conformance.FullAccountBody P
open import Conformance.FullAccountCrypto P
open import Conformance.FullAccountDeviceSecurity P using (Preserves; bodyWrites)
open import Conformance.FullAccountExecution using (Run; run) renaming (then to bind-run)
open import Conformance.FullAccountGrant P
open import Conformance.FullAccountGrantSecurity P
open import Conformance.FullAccountLayouts
open import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; take; drop)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base hiding (equal)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≤ᵇ⇒≤; <ᵇ⇒<)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String)
open import Data.String.Properties using () renaming (_≟_ to _≟ˢ_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
import Conformance.FullAccountSignatureBindingProof P as Binding
import Conformance.FullAccountDeviceSecurityProof P as Device
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec; does; yes; no)
open import Relation.Nullary.Decidable using (dec-true)

------------------------------------------------------------------------
-- Boolean guards and value equality

private
  rejected≠accepted : ∀ {A : Set} {e : Error} {x : A} {t es} → rejected e ≡ accepted x t es → ⊥
  rejected≠accepted ()

  accepted-injective : ∀ {A : Set} {x y : A} {t u es fs} → accepted x t es ≡ accepted y u fs →
    y ≡ x × u ≡ t
  accepted-injective refl = refl , refl

  T-true : ∀ {b} → b ≡ true → T b
  T-true refl = tt

  ∧-true : ∀ a b → a ∧ b ≡ true → a ≡ true × b ≡ true
  ∧-true true b same = refl , same
  ∧-true false b ()

  ∨-true : ∀ a b → a ∨ b ≡ true → a ≡ true ⊎ b ≡ true
  ∨-true true b _ = inj₁ refl
  ∨-true false b same = inj₂ same

  flag-true : ∀ v → flag v ≡ true → v ≡ bool true
  flag-true (bool true) _ = refl
  flag-true (bool false) ()
  flag-true (nat _) ()
  flag-true (bytes _) ()
  flag-true (tuple _) ()
  flag-true none ()
  flag-true (some _) ()

  just-transport : ∀ {A : Set} {m : Maybe A} {x y} → m ≡ just x → x ≡ y → m ≡ just y
  just-transport found refl = found

  answer-subst : ∀ {A : Set} {m : M A} {s x y t} → x ≡ y → Run m s x t → Run m s y t
  answer-subst refl r = r

  ≡ᵇ-refl : ∀ n → (n ≡ᵇ n) ≡ true
  ≡ᵇ-refl zero = refl
  ≡ᵇ-refl (suc n) = ≡ᵇ-refl n

  equalNats-sound : ∀ xs ys → equalNats xs ys ≡ true → xs ≡ ys
  equalNats-sound [] [] _ = refl
  equalNats-sound [] (_ ∷ _) ()
  equalNats-sound (_ ∷ _) [] ()
  equalNats-sound (x ∷ xs) (y ∷ ys) same =
    cong₂ _∷_ (≡ᵇ⇒≡ x y (T-true (proj₁ halves))) (equalNats-sound xs ys (proj₂ halves))
    where halves = ∧-true (x ≡ᵇ y) (equalNats xs ys) same

  equalNats-refl : ∀ xs → equalNats xs xs ≡ true
  equalNats-refl [] = refl
  equalNats-refl (x ∷ xs) rewrite ≡ᵇ-refl x = equalNats-refl xs

mutual
  equal-sound : ∀ x y → equal x y ≡ true → x ≡ y
  equal-sound (nat m) (nat n) same = cong nat (≡ᵇ⇒≡ m n (T-true same))
  equal-sound (bool false) (bool false) _ = refl
  equal-sound (bool true) (bool true) _ = refl
  equal-sound (bytes xs) (bytes ys) same = cong bytes (equalNats-sound xs ys same)
  equal-sound (tuple xs) (tuple ys) same = cong tuple (equalValues-sound xs ys same)
  equal-sound none none _ = refl
  equal-sound (some x) (some y) same = cong some (equal-sound x y same)
  equal-sound (nat _) (bool _) ()
  equal-sound (nat _) (bytes _) ()
  equal-sound (nat _) (tuple _) ()
  equal-sound (nat _) none ()
  equal-sound (nat _) (some _) ()
  equal-sound (bool false) (bool true) ()
  equal-sound (bool true) (bool false) ()
  equal-sound (bool false) (nat _) ()
  equal-sound (bool false) (bytes _) ()
  equal-sound (bool false) (tuple _) ()
  equal-sound (bool false) none ()
  equal-sound (bool false) (some _) ()
  equal-sound (bool true) (nat _) ()
  equal-sound (bool true) (bytes _) ()
  equal-sound (bool true) (tuple _) ()
  equal-sound (bool true) none ()
  equal-sound (bool true) (some _) ()
  equal-sound (bytes _) (nat _) ()
  equal-sound (bytes _) (bool _) ()
  equal-sound (bytes _) (tuple _) ()
  equal-sound (bytes _) none ()
  equal-sound (bytes _) (some _) ()
  equal-sound (tuple _) (nat _) ()
  equal-sound (tuple _) (bool _) ()
  equal-sound (tuple _) (bytes _) ()
  equal-sound (tuple _) none ()
  equal-sound (tuple _) (some _) ()
  equal-sound none (nat _) ()
  equal-sound none (bool _) ()
  equal-sound none (bytes _) ()
  equal-sound none (tuple _) ()
  equal-sound none (some _) ()
  equal-sound (some _) (nat _) ()
  equal-sound (some _) (bool _) ()
  equal-sound (some _) (bytes _) ()
  equal-sound (some _) (tuple _) ()
  equal-sound (some _) none ()

  equalValues-sound : ∀ xs ys → equalValues xs ys ≡ true → xs ≡ ys
  equalValues-sound [] [] _ = refl
  equalValues-sound [] (_ ∷ _) ()
  equalValues-sound (_ ∷ _) [] ()
  equalValues-sound (x ∷ xs) (y ∷ ys) same =
    cong₂ _∷_ (equal-sound x y (proj₁ (∧-true (equal x y) (equalValues xs ys) same)))
      (equalValues-sound xs ys (proj₂ (∧-true (equal x y) (equalValues xs ys) same)))

mutual
  equal-refl : ∀ x → equal x x ≡ true
  equal-refl (nat n) = ≡ᵇ-refl n
  equal-refl (bool false) = refl
  equal-refl (bool true) = refl
  equal-refl (bytes xs) = equalNats-refl xs
  equal-refl (tuple xs) = equalValues-refl xs
  equal-refl none = refl
  equal-refl (some x) = equal-refl x

  equalValues-refl : ∀ xs → equalValues xs xs ≡ true
  equalValues-refl [] = refl
  equalValues-refl (x ∷ xs) rewrite equal-refl x = equalValues-refl xs

------------------------------------------------------------------------
-- Ledger cells and maps

private
  does-sound : ∀ {A : Set} (d : Dec A) → does d ≡ true → A
  does-sound (yes a) _ = a
  does-sound (no _) ()

  stringEqual-sound : ∀ a b → stringEqual a b ≡ true → a ≡ b
  stringEqual-sound a b = does-sound (a ≟ˢ b)

  stringEqual-refl : ∀ k → stringEqual k k ≡ true
  stringEqual-refl k = dec-true (k ≟ˢ k) refl

  lookupCell-insertCell-same : ∀ k v l → lookupCell k (insertCell k v l) ≡ just v
  lookupCell-insertCell-same k v [] rewrite stringEqual-refl k = refl
  lookupCell-insertCell-same k v ((x , w) ∷ l) with stringEqual k x in same
  ... | true rewrite stringEqual-refl k = refl
  ... | false rewrite same = lookupCell-insertCell-same k v l

  lookupCell-insertCell-other : ∀ k k′ v l → stringEqual k k′ ≡ false →
    lookupCell k (insertCell k′ v l) ≡ lookupCell k l
  lookupCell-insertCell-other k k′ v [] different rewrite different = refl
  lookupCell-insertCell-other k k′ v ((x , w) ∷ l) different with stringEqual k′ x in same
  ... | true rewrite different | subst (λ y → stringEqual k y ≡ false) (stringEqual-sound k′ x same) different = refl
  ... | false with stringEqual k x
  ...   | true = refl
  ...   | false = lookupCell-insertCell-other k k′ v l different

  cell-at : ∀ k st {v} → lookupCell k (ledger st) ≡ just v → cell k st ≡ v
  cell-at k st found rewrite found = refl

  lookupMap-insertMap-same : ∀ k v m → lookupMap k (insertMap k v m) ≡ just v
  lookupMap-insertMap-same k v [] rewrite equal-refl k = refl
  lookupMap-insertMap-same k v (tuple (x ∷ y ∷ []) ∷ m) with equal k x in same
  ... | true rewrite equal-refl k = refl
  ... | false rewrite same = lookupMap-insertMap-same k v m
  lookupMap-insertMap-same k v (nat _ ∷ m) = lookupMap-insertMap-same k v m
  lookupMap-insertMap-same k v (bool _ ∷ m) = lookupMap-insertMap-same k v m
  lookupMap-insertMap-same k v (bytes _ ∷ m) = lookupMap-insertMap-same k v m
  lookupMap-insertMap-same k v (none ∷ m) = lookupMap-insertMap-same k v m
  lookupMap-insertMap-same k v (some _ ∷ m) = lookupMap-insertMap-same k v m
  lookupMap-insertMap-same k v (tuple [] ∷ m) = lookupMap-insertMap-same k v m
  lookupMap-insertMap-same k v (tuple (_ ∷ []) ∷ m) = lookupMap-insertMap-same k v m
  lookupMap-insertMap-same k v (tuple (_ ∷ _ ∷ _ ∷ _) ∷ m) = lookupMap-insertMap-same k v m

------------------------------------------------------------------------
-- Successful evaluator primitives

private
  return-run : ∀ {A : Set} (x : A) {s y t} → Run (return x) s y t → y ≡ x × t ≡ s
  return-run x (run _ refl) = refl , refl

  assert-run : ∀ b {message s x t} → Run (assert b message) s x t → b ≡ true × t ≡ s
  assert-run true (run _ refl) = refl , refl
  assert-run false (run _ ())

  lift-run : ∀ {A : Set} (r : Result A) {s x t} → Run (lift r) s x t → r ≡ success x × t ≡ s
  lift-run (failure _) (run _ ())
  lift-run (success _) (run _ refl) = refl , refl

  hash-run : ∀ xs {s v t} → Run (hash xs) s v t → persistentHash P xs ≡ success v × t ≡ s
  hash-run xs = lift-run (persistentHash P xs)

  read-run : ∀ k {s v t} → Run (read k) s v t → lookupCell k (ledger s) ≡ just v × t ≡ s
  read-run k {s} (run _ execution) with lookupCell k (ledger s)
  ... | nothing = ⊥-elim (rejected≠accepted execution)
  ... | just w = cong just (sym (proj₁ (accepted-injective execution))) , proj₂ (accepted-injective execution)

  lookup-run : ∀ label k {s v t} → Run (lookup label k) s v t →
    lookupMap k (fields (cell label s)) ≡ just v × t ≡ s
  lookup-run label k {s} (run _ execution) with lookupMap k (fields (cell label s))
  ... | nothing = ⊥-elim (rejected≠accepted execution)
  ... | just w = cong just (sym (proj₁ (accepted-injective execution))) , proj₂ (accepted-injective execution)

  cast-run : ∀ label bits n {s m t} → Run (cast label bits n) s m t → m ≡ n × n < 2 ^ bits × t ≡ s
  cast-run label bits n (run _ execution) with n <ᵇ 2 ^ bits in bounded
  ... | false = ⊥-elim (rejected≠accepted execution)
  ... | true = proj₁ (accepted-injective execution) , <ᵇ⇒< n (2 ^ bits) (T-true bounded) ,
    proj₂ (accepted-injective execution)

  if-run : ∀ {A : Set} b {m n : M A} {s x t} → Run (if b then m else n) s x t →
    (b ≡ true × Run m s x t) ⊎ (b ≡ false × Run n s x t)
  if-run true r = inj₁ (refl , r)
  if-run false r = inj₂ (refl , r)

  memberMap-run : ∀ label k {s b t} → Run (memberMap label k) s b t → t ≡ s
  memberMap-run label k (run _ refl) = refl

  insert-run : ∀ label k v {s x t} → Run (insert label k v) s x t →
    t ≡ state (insertCell label (tuple (insertMap k v (fields (cell label s)))) (ledger s))
  insert-run label k v (run _ refl) = refl

  write-run : ∀ k v {s x t} → Run (write k v) s x t → t ≡ state (insertCell k v (ledger s))
  write-run k v (run _ refl) = refl

  readSelf-run : ∀ ctx {s v t} → Run (readSelf ctx) s v t → v ≡ self ctx × t ≡ s
  readSelf-run ctx (run _ refl) = refl , refl

  readTimeLess-run : ∀ ctx n {s b t} → Run (readTimeLess ctx n) s b t → b ≡ (blockTime ctx <ᵇ n) × t ≡ s
  readTimeLess-run ctx n (run _ refl) = refl , refl

  held-run : ∀ ctx color {s v t} → Run (held ctx color) s v t → v ≡ heldCoin ctx × t ≡ s
  held-run ctx color (run _ refl) = refl , refl

  bump-run : ∀ label bits {s x t} → Run (bump label bits) s x t →
    Σ Value λ n → lookupCell label (ledger s) ≡ just n × suc (number n) < 2 ^ bits ×
      t ≡ state (insertCell label (nat (suc (number n))) (ledger s))
  bump-run label bits r with bind-run (readCount label) r
  ... | n , t₁ , counted , rest with bind-run (read label) counted
  ...   | v , t₂ , readV , returned with read-run label readV
  ...     | found , refl with return-run (number v) returned
  ...       | refl , refl with bind-run (cast label bits (suc (number v))) rest
  ...         | w , t₃ , casted , written with cast-run label bits (suc (number v)) casted
  ...           | refl , bounded , refl with write-run label (nat (suc (number v))) written
  ...             | refl = v , found , bounded , refl

------------------------------------------------------------------------
-- Pure source helpers used by authentication and scope checks

private
  smallOrder-run : ∀ pk message {s x t} → Run (requireSmallOrderFree pk message) s x t → t ≡ s
  smallOrder-run pk message r with bind-run (lift (ecMul P jubjub pk 8)) r
  ... | q , t₁ , multiplied , rest with lift-run (ecMul P jubjub pk 8) multiplied
  ...   | _ , refl with bind-run identityOf rest
  ...     | o , t₂ , generated , checked with lift-run (ecMulGenerator P jubjub 0) generated
  ...       | _ , refl = proj₂ (assert-run (not (equal q o)) checked)

  k256Key-run : ∀ pk {s x t} → Run (requireK256Key pk) s x t → t ≡ s
  k256Key-run pk r with bind-run (lift (pointCoordinates P k256 pk)) r
  ... | (px , py) , t₁ , coordinates , checked with lift-run (pointCoordinates P k256 pk) coordinates
  ...   | _ , refl = proj₂ (assert-run (not (equal px zero32 ∧ equal py zero32)) checked)

  callerCommit-run : ∀ salt′ address {s v t} → Run (callerCommit salt′ (some address)) s v t → t ≡ s
  callerCommit-run salt′ address r
    with bind-run (hash (b32 (pad 32 "midnight:account:grant:caller:v1") ∷ b32 salt′ ∷ contract address ∷ [])) r
  ... | commitment , t₁ , hashed , rest with hash-run _ hashed
  ...   | _ , refl with bind-run (assert (not (equal commitment zero32)) "reserved caller commitment") rest
  ...     | _ , t₂ , nonzero , returned with assert-run (not (equal commitment zero32)) nonzero
  ...       | _ , refl = proj₂ (return-run commitment returned)

  -- grantId's preimage with its where-local tag and envelope atom unfolded.
  grantIdPreimage : Curve → GrantAuth → Value → List Atom → List Atom
  grantIdPreimage jubjub ga addr ks = b32 (pad 32 "midnight:account:grant:id:v1") ∷ contract addr ∷
    (ks ++ [] ++ (b32 (origin ga) ∷ u8 (nat (slot ga)) ∷ []))
  grantIdPreimage k256 ga addr ks = b32 (pad 32 "midnight:account:grant:id:k1:v1") ∷ contract addr ∷
    (ks ++ (u8 (nat (envelope (authorisation ga))) ∷ []) ++ (b32 (origin ga) ∷ u8 (nat (slot ga)) ∷ []))
  grantIdPreimage p256 ga addr ks = b32 (pad 32 "midnight:account:grant:id:r1:v1") ∷ contract addr ∷
    (ks ++ [] ++ (b32 (origin ga) ∷ u8 (nat (slot ga)) ∷ []))

  grantIdTail : Curve → GrantAuth → Value → M Value
  grantIdTail c ga addr = keyAtoms c (key (authorisation ga)) >>= λ ks → hash (grantIdPreimage c ga addr ks)

  grantIdTail-pure : ∀ c ga addr → Binding.Pure (grantIdTail c ga addr)
  grantIdTail-pure c ga addr =
    Binding.pure-bind (keyAtoms c (key (authorisation ga))) (λ ks → hash (grantIdPreimage c ga addr ks))
      (Binding.keyAtoms-pure c (key (authorisation ga))) λ ks → Binding.hash-pure (grantIdPreimage c ga addr ks)

  self-then-pure : ∀ ctx {A : Set} (k : Value → M A) → (∀ addr → Binding.Pure (k addr)) →
    ∀ {s v t} → Run (readSelf ctx >>= k) s v t → t ≡ s
  self-then-pure ctx k isPure r with bind-run (readSelf ctx) {f = k} r
  ... | _ , t₁ , selfRead , rest with readSelf-run ctx selfRead
  ...   | refl , refl = Binding.pure-preserves (isPure (self ctx)) (Run.execution rest)

  grantId-run : ∀ c ctx ga {s v t} → Run (grantId c ctx ga) s v t → t ≡ s
  grantId-run jubjub ctx ga = self-then-pure ctx (grantIdTail jubjub ga) (grantIdTail-pure jubjub ga)
  grantId-run k256 ctx ga = self-then-pure ctx (grantIdTail k256 ga) (grantIdTail-pure k256 ga)
  grantId-run p256 ctx ga = self-then-pure ctx (grantIdTail p256 ga) (grantIdTail-pure p256 ga)

------------------------------------------------------------------------
-- authenticateGrant

private
  validate-run : ∀ g {s x t} → Run (validateGrantRecord g) s x t →
    t ≡ s × grantActive g ≡ bool true × lookupCell "device_epoch" (ledger s) ≡ just (grantEpoch g) ×
    lookupCell "grant_generation" (ledger s) ≡ just (grantGeneration g)
  validate-run g r with bind-run (assert (flag (grantActive g)) "grant revoked") r
  ... | _ , t₁ , activeRun , rest₁ with assert-run (flag (grantActive g)) activeRun
  ...   | live , refl with bind-run (read "device_epoch") rest₁
  ...     | epoch , t₂ , epochRead , rest₂ with read-run "device_epoch" epochRead
  ...       | currentEpoch , refl with bind-run (assert (equal (grantEpoch g) epoch) "grant epoch stale") rest₂
  ...         | _ , t₃ , epochChecked , rest₃ with assert-run (equal (grantEpoch g) epoch) epochChecked
  ...           | sameEpoch , refl with bind-run (read "grant_generation") rest₃
  ...             | generation , t₄ , generationRead , checked with read-run "grant_generation" generationRead
  ...               | currentGeneration , refl with assert-run (equal (grantGeneration g) generation) checked
  ...                 | sameGeneration , refl =
    refl , flag-true (grantActive g) live ,
    just-transport currentEpoch (sym (equal-sound (grantEpoch g) epoch sameEpoch)) ,
    just-transport currentGeneration (sym (equal-sound (grantGeneration g) generation sameGeneration))

  -- authenticateGrant's inline expiry guard.
  expiryCheck : Context → Value → M ⊤
  expiryCheck ctx scope = if number (scopeExpiresAt scope) ≡ᵇ 0 then return tt else
    (readTimeLess ctx (number (scopeExpiresAt scope)) >>= λ beforeExpiry → assert beforeExpiry "grant expired")

  expiry-run : ∀ ctx scope {s x t} → Run (expiryCheck ctx scope) s x t → t ≡ s × Unexpired ctx scope
  expiry-run ctx scope r with if-run (number (scopeExpiresAt scope) ≡ᵇ 0) r
  ... | inj₁ (never , returned) =
    proj₂ (return-run tt returned) , inj₁ (≡ᵇ⇒≡ (number (scopeExpiresAt scope)) 0 (T-true never))
  ... | inj₂ (_ , timed)
    with bind-run (readTimeLess ctx (number (scopeExpiresAt scope)))
      {f = λ beforeExpiry → assert beforeExpiry "grant expired"} timed
  ...   | before , t₁ , timeRead , checked with readTimeLess-run ctx (number (scopeExpiresAt scope)) timeRead
  ...     | refl , refl with assert-run (blockTime ctx <ᵇ number (scopeExpiresAt scope)) checked
  ...       | beforeExpiry , refl =
    refl , inj₂ (<ᵇ⇒< (blockTime ctx) (number (scopeExpiresAt scope)) (T-true beforeExpiry))

  -- authenticateGrant after its membership test, with the curve's final
  -- scope check (checkRP, a where-local) supplied as `check`.
  located : Value → Context → (Value → M ⊤) → Bool → M (Value × Value)
  located identifier ctx check present =
    assert present "unknown grant" >> (lookup "grants" identifier >>= λ g →
    validateGrantRecord g >> (expiryCheck ctx (grantScope g) >> (check (grantScope g) >> return (identifier , g))))

  located-run : ∀ identifier ctx check {s present y t} → Run (located identifier ctx check present) s y t →
    Σ Value λ g → Run (lookup "grants" identifier) s g s × grantActive g ≡ bool true ×
      lookupCell "device_epoch" (ledger s) ≡ just (grantEpoch g) ×
      lookupCell "grant_generation" (ledger s) ≡ just (grantGeneration g) × Unexpired ctx (grantScope g) ×
      Σ State λ u → Run (check (grantScope g)) s tt u × Run (return (identifier , g)) u y t
  located-run identifier ctx check {present = present} r with bind-run (assert present "unknown grant") r
  ... | _ , t₁ , known , rest₁ with assert-run present known
  ...   | _ , refl with bind-run (lookup "grants" identifier) rest₁
  ...     | g , t₂ , found , rest₂ with lookup-run "grants" identifier found
  ...       | _ , refl with bind-run (validateGrantRecord g) rest₂
  ...         | _ , t₃ , valid , rest₃ with validate-run g valid
  ...           | refl , active , epoch , generation with bind-run (expiryCheck ctx (grantScope g)) rest₃
  ...             | _ , t₄ , expiry , rest₄ with expiry-run ctx (grantScope g) expiry
  ...               | refl , unexpired with bind-run (check (grantScope g)) rest₄
  ...                 | _ , u , checked , returned =
    g , found , active , epoch , generation , unexpired , u , checked , returned

  rpCheck : GrantAuth → Value → M ⊤
  rpCheck ga scope = rpCommit (salt ga) (at 0 (policy (authorisation ga))) >>= λ commitment →
    assert (equal commitment (scopeRPCommitment scope)) "grant RP mismatch"

  live-grant : ∀ {c ctx ga s g} → grantActive g ≡ bool true →
    lookupCell "device_epoch" (ledger s) ≡ just (grantEpoch g) →
    lookupCell "grant_generation" (ledger s) ≡ just (grantGeneration g) →
    Unexpired ctx (grantScope g) → CurvePolicy c ga s (grantScope g) → LiveGrant c ctx ga s g
  live-grant active epoch generation unexpired policy = record
    { active = active ; currentEpoch = epoch ; currentGeneration = generation
    ; unexpired = unexpired ; curvePolicy = policy }

-- Exported step lemmas below may be reused to relate other decompositions of
-- grantCall to this one; each also shows its step leaves the state unchanged.
authenticate-run : ∀ c ctx ga {s identifier g t} → Run (authenticateGrant c ctx ga) s (identifier , g) t →
  t ≡ s × Run (grantId c ctx ga) s identifier s × Run (lookup "grants" identifier) s g s ×
  LiveGrant c ctx ga s g
authenticate-run jubjub ctx ga r
  with bind-run (requireSmallOrderFree (key (authorisation ga)) "grantee key has small order") r
... | _ , t₁ , guarded , rest₀ with smallOrder-run (key (authorisation ga)) "grantee key has small order" guarded
...   | refl with bind-run (grantId jubjub ctx ga) rest₀
...     | identifier′ , t₂ , identified , rest₁ with grantId-run jubjub ctx ga identified
...       | refl with bind-run (memberMap "grants" identifier′) {f = located identifier′ ctx (λ _ → return tt)} rest₁
...         | present , t₃ , member , rest₂ with memberMap-run "grants" identifier′ member
...           | refl with located-run identifier′ ctx (λ _ → return tt) {present = present} rest₂
...             | g′ , found , active , epoch , generation , unexpired , u , checked , returned
                  with return-run tt checked
...               | _ , refl with return-run (identifier′ , g′) returned
...                 | refl , refl =
  refl , identified , found , live-grant active epoch generation unexpired guarded
authenticate-run k256 ctx ga r
  with bind-run (assert (envelope (authorisation ga) ≡ᵇ 0) "envelope not admitted for a spend grant" >>
    requireK256Key (key (authorisation ga))) r
... | _ , t₁ , guarded , rest₀
      with bind-run (assert (envelope (authorisation ga) ≡ᵇ 0) "envelope not admitted for a spend grant") guarded
...   | _ , t₀ , unenveloped , keyChecked with assert-run (envelope (authorisation ga) ≡ᵇ 0) unenveloped
...     | noEnvelope , refl with k256Key-run (key (authorisation ga)) keyChecked
...       | refl with bind-run (grantId k256 ctx ga) rest₀
...         | identifier′ , t₂ , identified , rest₁ with grantId-run k256 ctx ga identified
...           | refl with bind-run (memberMap "grants" identifier′) {f = located identifier′ ctx (λ _ → return tt)} rest₁
...             | present , t₃ , member , rest₂ with memberMap-run "grants" identifier′ member
...               | refl with located-run identifier′ ctx (λ _ → return tt) {present = present} rest₂
...                 | g′ , found , active , epoch , generation , unexpired , u , checked , returned
                      with return-run tt checked
...                   | _ , refl with return-run (identifier′ , g′) returned
...                     | refl , refl =
  refl , identified , found , live-grant active epoch generation unexpired
    (≡ᵇ⇒≡ (envelope (authorisation ga)) 0 (T-true noEnvelope) , keyChecked)
authenticate-run p256 ctx ga r
  with bind-run (hash (grantOriginPreimage ga) >>= λ originHash →
    assert (equal originHash (origin ga)) "grant origin mismatch") r
... | _ , t₁ , guarded , rest₀ with bind-run (hash (grantOriginPreimage ga)) guarded
...   | originHash , t₀ , hashed , originChecked with hash-run (grantOriginPreimage ga) hashed
...     | originDigest , refl with assert-run (equal originHash (origin ga)) originChecked
...       | sameOrigin , refl with bind-run (grantId p256 ctx ga) rest₀
...         | identifier′ , t₂ , identified , rest₁ with grantId-run p256 ctx ga identified
...           | refl with bind-run (memberMap "grants" identifier′) {f = located identifier′ ctx (rpCheck ga)} rest₁
...             | present , t₃ , member , rest₂ with memberMap-run "grants" identifier′ member
...               | refl with located-run identifier′ ctx (rpCheck ga) {present = present} rest₂
...                 | g′ , found , active , epoch , generation , unexpired , u , checked , returned
                      with bind-run (rpCommit (salt ga) (at 0 (policy (authorisation ga)))) checked
...                   | rp , t₄ , committed , rpChecked with hash-run _ committed
...                     | _ , refl with assert-run (equal rp (scopeRPCommitment (grantScope g′))) rpChecked
...                       | sameRP , refl with return-run (identifier′ , g′) returned
...                         | refl , refl =
  refl , identified , found , live-grant active epoch generation unexpired
    (trans originDigest (cong success (equal-sound originHash (origin ga) sameOrigin)) ,
     answer-subst (equal-sound rp (scopeRPCommitment (grantScope g′)) sameRP) committed)

------------------------------------------------------------------------
-- scopeCheck

private
  -- checkCaller's contract-caller branch is a where-local, so it is followed
  -- on the execution equation after fixing the caller value.
  caller-run : ∀ ctx ga scope {s x t} → Run (checkCaller ctx ga scope) s x t →
    t ≡ s × CallerAdmitted ctx ga s scope
  caller-run ctx ga scope {s} (run journal execution)
    with equal (scopeCallerCommitment scope) zero32 in unrestricted
  ... | true = proj₂ (accepted-injective execution) ,
    inj₁ (equal-sound (scopeCallerCommitment scope) zero32 unrestricted)
  ... | false with caller ctx
  ...   | none = ⊥-elim (rejected≠accepted execution)
  ...   | nat _ = ⊥-elim (rejected≠accepted execution)
  ...   | bool _ = ⊥-elim (rejected≠accepted execution)
  ...   | bytes _ = ⊥-elim (rejected≠accepted execution)
  ...   | tuple _ = ⊥-elim (rejected≠accepted execution)
  ...   | some (nat _) = ⊥-elim (rejected≠accepted execution)
  ...   | some (bool _) = ⊥-elim (rejected≠accepted execution)
  ...   | some (bytes _) = ⊥-elim (rejected≠accepted execution)
  ...   | some none = ⊥-elim (rejected≠accepted execution)
  ...   | some (some _) = ⊥-elim (rejected≠accepted execution)
  ...   | some (tuple []) = ⊥-elim (rejected≠accepted execution)
  ...   | some (tuple (nat _ ∷ _)) = ⊥-elim (rejected≠accepted execution)
  ...   | some (tuple (bytes _ ∷ _)) = ⊥-elim (rejected≠accepted execution)
  ...   | some (tuple (tuple _ ∷ _)) = ⊥-elim (rejected≠accepted execution)
  ...   | some (tuple (none ∷ _)) = ⊥-elim (rejected≠accepted execution)
  ...   | some (tuple (some _ ∷ _)) = ⊥-elim (rejected≠accepted execution)
  ...   | some (tuple (bool _ ∷ [])) = ⊥-elim (rejected≠accepted execution)
  ...   | some (tuple (bool _ ∷ _ ∷ _ ∷ _)) = ⊥-elim (rejected≠accepted execution)
  ...   | some (tuple (bool false ∷ _ ∷ [])) = ⊥-elim (rejected≠accepted execution)
  ...   | some (tuple (bool true ∷ address ∷ [])) with callerCommit (salt ga) (some address) s in committed
  ...     | rejected _ = ⊥-elim (rejected≠accepted execution)
  ...     | accepted commitment t₁ es₁ with callerCommit-run (salt ga) address (run es₁ committed)
  ...       | refl with equal commitment (scopeCallerCommitment scope) in sameCaller
  ...         | false = ⊥-elim (rejected≠accepted execution)
  ...         | true = proj₂ (accepted-injective execution) ,
    inj₂ (address , refl ,
      answer-subst (equal-sound commitment (scopeCallerCommitment scope) sameCaller) (run es₁ committed))

  recipientCondition : Operation → GrantAuth → List Value → Bool
  recipientCondition op ga xs = (number (recipientKind ga) ≡ᵇ 0) ∨
    ((number (recipientKind ga) ≡ᵇ thisKind op) ∧ equal (pinnedRecipient ga) (recipientOf op xs))

  recipient-sound : ∀ op ga xs → recipientCondition op ga xs ≡ true → RecipientAdmitted op ga xs
  recipient-sound op ga xs admitted
    with ∨-true (number (recipientKind ga) ≡ᵇ 0)
      ((number (recipientKind ga) ≡ᵇ thisKind op) ∧ equal (pinnedRecipient ga) (recipientOf op xs)) admitted
  ... | inj₁ unpinned = inj₁ (≡ᵇ⇒≡ (number (recipientKind ga)) 0 (T-true unpinned))
  ... | inj₂ pinned = inj₂
    (≡ᵇ⇒≡ (number (recipientKind ga)) (thisKind op) (T-true (proj₁ halves)) ,
     equal-sound (pinnedRecipient ga) (recipientOf op xs) (proj₂ halves))
    where
    halves = ∧-true (number (recipientKind ga) ≡ᵇ thisKind op)
      (equal (pinnedRecipient ga) (recipientOf op xs)) pinned

scope-run : ∀ op ctx ga xs coin g {s spent t} → Run (scopeCheck op ctx ga xs coin g) s spent t →
  t ≡ s × ScopeAdmitted op ctx ga xs coin s g spent
scope-run op ctx ga xs coin g r
  with bind-run (assert (flag (scopeAllows op (grantScope g))) "operation not in scope") r
... | _ , t₁ , allowed , rest₁ with assert-run (flag (scopeAllows op (grantScope g))) allowed
...   | inScope , refl with bind-run (checkCaller ctx ga (grantScope g)) rest₁
...     | _ , t₂ , callerRun , rest₂ with caller-run ctx ga (grantScope g) callerRun
...       | refl , callerAdmitted
            with bind-run (objectCommit (salt ga) (if shielded op then at 1 coin else get 0 xs)
              (recipientKind ga) (pinnedRecipient ga) (nat (maxCoinValue ga))) rest₂
...         | object , t₃ , objectRun , rest₃ with hash-run _ objectRun
...           | _ , refl
                with bind-run (assert (equal object (scopeObjectCommitment (grantScope g))) "scope object mismatch") rest₃
...             | _ , t₄ , objectChecked , rest₄
                  with assert-run (equal object (scopeObjectCommitment (grantScope g))) objectChecked
...               | sameObject , refl
                    with bind-run (assert (amountOf op xs ≤ᵇ number (scopePerCallCap (grantScope g)))
                      "amount above per-call cap") rest₄
...                 | _ , t₅ , perCallRun , rest₅
                      with assert-run (amountOf op xs ≤ᵇ number (scopePerCallCap (grantScope g))) perCallRun
...                   | withinPerCall , refl with bind-run (spentCommit (salt ga) (spentPrev ga)) rest₅
...                     | opening , t₆ , openingRun , rest₆ with hash-run _ openingRun
...                       | _ , refl
                            with bind-run (assert (equal opening (grantSpentCommitment g)) "spent opening mismatch") rest₆
...                         | _ , t₇ , openingChecked , rest₇
                              with assert-run (equal opening (grantSpentCommitment g)) openingChecked
...                           | sameOpening , refl
                                with bind-run (assert (spentPrev ga + amountOf op xs ≤ᵇ number (scopeCap (grantScope g)))
                                  "cumulative cap exceeded") rest₇
...                             | _ , t₈ , capRun , rest₈
                                  with assert-run (spentPrev ga + amountOf op xs ≤ᵇ number (scopeCap (grantScope g))) capRun
...                               | withinCap , refl
                                    with bind-run (cast "new_spent" 128 (spentPrev ga + amountOf op xs)) rest₈
...                                 | total , t₉ , castRun , rest₉
                                      with cast-run "new_spent" 128 (spentPrev ga + amountOf op xs) castRun
...                                   | refl , bounded , refl
                                        with bind-run (assert (recipientCondition op ga xs) "recipient not admitted by pin") rest₉
...                                     | _ , t₁₀ , pinRun , returned with assert-run (recipientCondition op ga xs) pinRun
...                                       | pinned , refl with return-run (spentPrev ga + amountOf op xs) returned
...                                         | refl , refl = refl , record
  { operationAllowed = flag-true (scopeAllows op (grantScope g)) inScope
  ; callerAdmitted = callerAdmitted
  ; objectCommitted = answer-subst (equal-sound object (scopeObjectCommitment (grantScope g)) sameObject) objectRun
  ; perCallCap = ≤ᵇ⇒≤ (amountOf op xs) (number (scopePerCallCap (grantScope g))) (T-true withinPerCall)
  ; spentOpened = answer-subst (equal-sound opening (grantSpentCommitment g) sameOpening) openingRun
  ; cumulativeCap = ≤ᵇ⇒≤ (spentPrev ga + amountOf op xs) (number (scopeCap (grantScope g))) (T-true withinCap)
  ; spentTotal = refl
  ; spentBound = bounded
  ; recipientAdmitted = recipient-sound op ga xs pinned }

------------------------------------------------------------------------
-- grantCall

coin-run : ∀ op ctx xs {s coin t} → Run (if shielded op then held ctx (get 1 xs) else return none) s coin t →
  coin ≡ grantCoin op ctx × t ≡ s
coin-run op ctx xs r with shielded op
... | true = held-run ctx (get 1 xs) r
... | false = return-run none r

-- grantCall's inline shielded-coin guard.
coinCheck : Operation → GrantAuth → Value → M ⊤
coinCheck op ga coin = if shielded op then
  (assert (number (at 2 coin) ≤ᵇ maxCoinValue ga) "coin above max_coin_value" >>
   (read "enc_key" >>= λ encryption → assert (equal (encryptionKey ga) encryption) "stale encryption key"))
  else return tt

coinCheck-run : ∀ op ga coin {s x t} → Run (coinCheck op ga coin) s x t → t ≡ s × CoinAdmitted op ga coin s
coinCheck-run op ga coin r with if-run (shielded op) r
... | inj₂ (unshielded , returned) = proj₂ (return-run tt returned) , inj₁ unshielded
... | inj₁ (isShielded , checked)
  with bind-run (assert (number (at 2 coin) ≤ᵇ maxCoinValue ga) "coin above max_coin_value") checked
...   | _ , t₁ , bounded , rest with assert-run (number (at 2 coin) ≤ᵇ maxCoinValue ga) bounded
...     | withinBound , refl with bind-run (read "enc_key") rest
...       | encryption , t₂ , keyRead , keyChecked with read-run "enc_key" keyRead
...         | current , refl with assert-run (equal (encryptionKey ga) encryption) keyChecked
...           | sameKey , refl = refl , inj₂ (isShielded ,
  ≤ᵇ⇒≤ (number (at 2 coin)) (maxCoinValue ga) (T-true withinBound) ,
  just-transport current (sym (equal-sound (encryptionKey ga) encryption sameKey)))

challenge-run : ∀ c grant operation ctx a args nonce {s h t} →
  Run (challenge c grant operation ctx a args nonce) s h t →
  Run (challengeAt c grant operation (self ctx) a args nonce) s h s × t ≡ s
challenge-run c grant operation ctx a args nonce r
  with bind-run (readSelf ctx) {f = λ addr → challengeAt c grant operation addr a args nonce} r
... | _ , t₁ , selfRead , rest with readSelf-run ctx selfRead
...   | refl , refl with Binding.challengeAt-preserves c grant operation (self ctx) a args nonce (Run.execution rest)
...     | refl = rest , refl

settle-run : ∀ c ga identifier g h spent {s x t} → Run (settle c ga identifier g h spent) s x t →
  Run (verify c (authorisation ga) h "invalid grant signature") s tt s × Settlement ga s identifier g spent t
settle-run c ga identifier g h spent r
  with bind-run (verify c (authorisation ga) h "invalid grant signature") r
... | _ , t₁ , verified , rest₁
      with Binding.verify-preserves c (authorisation ga) h "invalid grant signature" (Run.execution verified)
...   | refl with bind-run (cast "grant nonce" 64 (suc (number (grantNonce g)))) rest₁
...     | nonce , t₂ , nonceRun , rest₂ with cast-run "grant nonce" 64 (suc (number (grantNonce g))) nonceRun
...       | refl , nonceBound , refl with bind-run (spentCommit (salt ga) spent) rest₂
...         | commitment , t₃ , committed , rest₃ with hash-run _ committed
...           | _ , refl
                with bind-run (insert "grants" identifier (settledGrant g (suc (number (grantNonce g))) commitment))
                  {f = λ _ → bump "round" 64} rest₃
...             | _ , t₄ , inserted , bumped
                  with insert-run "grants" identifier (settledGrant g (suc (number (grantNonce g))) commitment) inserted
...               | refl = verified , record
  { nextNonce = nonceBound ; commitment = commitment ; spentCommitted = committed ; roundAdvanced = bumped }

evidence : ∀ c op ctx ga xs {s v t} → Run (grantCall c op ctx ga xs) s v t → GrantCallEvidence c op ctx ga xs s
evidence c op ctx ga xs r with bind-run (if shielded op then held ctx (get 1 xs) else return none) r
... | coin , t₁ , coinRun , rest₁ with coin-run op ctx xs coinRun
...   | refl , refl with bind-run (authenticateGrant c ctx ga) rest₁
...     | (identifier , g) , t₂ , authenticated , rest₂ with authenticate-run c ctx ga authenticated
...       | refl , identified , recorded , live with bind-run (scopeCheck op ctx ga xs (grantCoin op ctx) g) rest₂
...         | spent , t₃ , scopeRun , rest₃ with scope-run op ctx ga xs (grantCoin op ctx) g scopeRun
...           | refl , scoped with bind-run (coinCheck op ga (grantCoin op ctx)) rest₃
...             | _ , t₄ , coinGuarded , rest₄ with coinCheck-run op ga (grantCoin op ctx) coinGuarded
...               | refl , coinAdmitted
                    with bind-run (challenge c true (operationName op) ctx (authorisation ga)
                      (grantChallengeAtoms op xs (grantCoin op ctx) ga identifier g) (number (grantNonce g))) rest₄
...                 | h , t₅ , challengeRun , rest₅
                      with challenge-run c true (operationName op) ctx (authorisation ga)
                        (grantChallengeAtoms op xs (grantCoin op ctx) ga identifier g) (number (grantNonce g)) challengeRun
...                   | challenged , refl with bind-run (settle c ga identifier g h spent) rest₅
...                     | _ , settled , settleRun , rest₆ with settle-run c ga identifier g h spent settleRun
...                       | verified , settlement with bind-run (body op ctx xs (grantCoin op ctx) none) rest₆
...                         | result , after , withdrawn , _ = record
  { identifier = identifier ; grantRecord = g ; challengeValue = h ; spent = spent ; settled = settled
  ; identified = identified ; recorded = recorded ; live = live ; scoped = scoped
  ; coinAdmitted = coinAdmitted ; challenged = challenged ; verified = verified
  ; settlement = settlement ; withdrawn = result , after , withdrawn }

------------------------------------------------------------------------
-- Advertised consequences

grant-call-evidence : ∀ c op ctx ga xs {s v t es} →
  grantCall c op ctx ga xs s ≡ accepted v t es → GrantCallEvidence c op ctx ga xs s
grant-call-evidence c op ctx ga xs {es = es} execution = evidence c op ctx ga xs (run es execution)

settled-grant : ∀ {ga s identifier g spent settled} (S : Settlement ga s identifier g spent settled) →
  lookupMap identifier (fields (cell "grants" settled)) ≡
    just (settledGrant g (suc (number (grantNonce g))) (Settlement.commitment S))
settled-grant {s = s} {identifier = identifier} {g = g} S with bump-run "round" 64 (Settlement.roundAdvanced S)
... | round , _ , _ , sameState =
  trans (cong (λ st → lookupMap identifier (fields (cell "grants" st))) sameState)
    (trans (cong (λ v → lookupMap identifier (fields v))
      (cell-at "grants" (state (insertCell "round" (nat (suc (number round))) grants)) stored))
      (lookupMap-insertMap-same identifier updated (fields (cell "grants" s))))
  where
  updated : Value
  updated = settledGrant g (suc (number (grantNonce g))) (Settlement.commitment S)
  grants : List (String × Value)
  grants = insertCell "grants" (tuple (insertMap identifier updated (fields (cell "grants" s)))) (ledger s)
  stored : lookupCell "grants" (insertCell "round" (nat (suc (number round))) grants) ≡
    just (tuple (insertMap identifier updated (fields (cell "grants" s))))
  stored = trans (lookupCell-insertCell-other "grants" "round" (nat (suc (number round))) grants refl)
    (lookupCell-insertCell-same "grants" (tuple (insertMap identifier updated (fields (cell "grants" s)))) (ledger s))

settled-record : ∀ g nonce commitment → grantActive g ≡ bool true →
  SettledRecord g nonce commitment (settledGrant g nonce commitment)
settled-record (tuple (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _)) nonce commitment _ = record
  { nonceSet = refl ; commitmentSet = refl ; epochKept = refl ; generationKept = refl
  ; issuedKept = refl ; windowStartKept = refl ; windowSpentKept = refl ; activeKept = refl
  ; scopeKept = refl }
settled-record (nat _) _ _ ()
settled-record (bool _) _ _ ()
settled-record (bytes _) _ _ ()
settled-record none _ _ ()
settled-record (some _) _ _ ()
settled-record (tuple []) _ _ ()
settled-record (tuple (_ ∷ [])) _ _ ()
settled-record (tuple (_ ∷ _ ∷ [])) _ _ ()
settled-record (tuple (_ ∷ _ ∷ _ ∷ [])) _ _ ()
settled-record (tuple (_ ∷ _ ∷ _ ∷ _ ∷ [])) _ _ ()
settled-record (tuple (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [])) _ _ ()
settled-record (tuple (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [])) _ _ ()
settled-record (tuple (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [])) _ _ ()

cumulative-spend : ∀ {c op ctx ga xs s} (E : GrantCallEvidence c op ctx ga xs s) {salt′ total} →
  SpentOpeningsAgree (salt ga) (spentPrev ga) salt′ total →
  Run (spentCommit salt′ total) s (grantSpentCommitment (grantRecord E)) s →
  salt ga ≡ salt′ × spentPrev ga ≡ total × spent E ≡ total + amountOf op xs ×
  total + amountOf op xs ≤ number (scopeCap (grantScope (grantRecord E)))
cumulative-spend E agreement opened with agreement (ScopeAdmitted.spentOpened (scoped E)) opened
... | sameSalt , refl =
  sameSalt , refl , ScopeAdmitted.spentTotal (scoped E) , ScopeAdmitted.cumulativeCap (scoped E)

------------------------------------------------------------------------
-- Final state of an accepted withdrawal

private
  cellValue : Maybe Value → Value
  cellValue nothing = none
  cellValue (just v) = v

  cell-view : ∀ k st → cell k st ≡ cellValue (lookupCell k (ledger st))
  cell-view k st with lookupCell k (ledger st)
  ... | nothing = refl
  ... | just v = refl

  cell-cong : ∀ k t u → lookupCell k (ledger t) ≡ lookupCell k (ledger u) → cell k t ≡ cell k u
  cell-cong k t u same = trans (cell-view k t) (trans (cong cellValue same) (sym (cell-view k u)))

  -- The final record is the settled one when the body and the change append
  -- leave the grants cell alone.
  final-state : ∀ {c op ctx ga xs s t} (E : GrantCallEvidence c op ctx ga xs s) →
    lookupCell "grants" (ledger t) ≡ lookupCell "grants" (ledger (settled E)) → GrantFinalState c op ctx ga xs s t
  final-state {t = t} E frame = record
    { callEvidence = E
    ; storedGrant = trans (cong (λ v → lookupMap (identifier E) (fields v)) (cell-cong "grants" t (settled E) frame))
        (settled-grant (settlement E))
    ; storedFields = settled-record (grantRecord E) (suc (number (grantNonce (grantRecord E))))
        (Settlement.commitment (settlement E)) (LiveGrant.active (live E)) }

  grants-outside : ∀ {op} → Withdrawal op → All (λ label → stringEqual "grants" label ≡ false) (bodyWrites op)
  grants-outside unshieldedWithdrawal = refl ∷ []
  grants-outside shieldedWithdrawal = []
  grants-outside contractWithdrawal = []

-- grantCall's appendChange tail, as it reduces for each withdrawal. Exported
-- for frames of other cells.
unshielded-tail : ∀ {k} (result : Value) → Preserves k (return tt >> return result)
unshielded-tail result = Device.preserves-bind {m = return tt} {f = λ _ → return result}
  (Device.return-preserves tt) λ _ → Device.return-preserves result

change-tail : ∀ {k} b e (result : Value) → stringEqual k "inbox" ≡ false → stringEqual k "inbox_count" ≡ false →
  Preserves k ((if b then inboxAppend e else return tt) >> return result)
change-tail b e result inbox count = Device.preserves-bind {m = if b then inboxAppend e else return tt}
  {f = λ _ → return result}
  (Device.if-preserves b (Device.inboxAppend-preserves e inbox count) (Device.return-preserves tt))
  λ _ → Device.return-preserves result

private
  -- evidence's decomposition, continued through the body and appendChange.
  -- Matching the Withdrawal last fixes op, so appendChange reduces.
  final-run : ∀ c op ctx ga xs → Withdrawal op → ∀ {s v t} → Run (grantCall c op ctx ga xs) s v t →
    GrantFinalState c op ctx ga xs s t
  final-run c op ctx ga xs w r with bind-run (if shielded op then held ctx (get 1 xs) else return none) r
  ... | coin , t₁ , coinRun , rest₁ with coin-run op ctx xs coinRun
  ...   | refl , refl with bind-run (authenticateGrant c ctx ga) rest₁
  ...     | (identifier , g) , t₂ , authenticated , rest₂ with authenticate-run c ctx ga authenticated
  ...       | refl , identified , recorded , live with bind-run (scopeCheck op ctx ga xs (grantCoin op ctx) g) rest₂
  ...         | spent , t₃ , scopeRun , rest₃ with scope-run op ctx ga xs (grantCoin op ctx) g scopeRun
  ...           | refl , scoped with bind-run (coinCheck op ga (grantCoin op ctx)) rest₃
  ...             | _ , t₄ , coinGuarded , rest₄ with coinCheck-run op ga (grantCoin op ctx) coinGuarded
  ...               | refl , coinAdmitted
                      with bind-run (challenge c true (operationName op) ctx (authorisation ga)
                        (grantChallengeAtoms op xs (grantCoin op ctx) ga identifier g) (number (grantNonce g))) rest₄
  ...                 | h , t₅ , challengeRun , rest₅
                        with challenge-run c true (operationName op) ctx (authorisation ga)
                          (grantChallengeAtoms op xs (grantCoin op ctx) ga identifier g) (number (grantNonce g)) challengeRun
  ...                   | challenged , refl with bind-run (settle c ga identifier g h spent) rest₅
  ...                     | _ , settled , settleRun , rest₆ with settle-run c ga identifier g h spent settleRun
  ...                       | verified , settlement with bind-run (body op ctx xs (grantCoin op ctx) none) rest₆
  ...                         | result , after , withdrawn , tailRun with w
  ...                           | unshieldedWithdrawal = final-state
    (grantCallEvidence identifier g h spent settled identified recorded live scoped coinAdmitted challenged verified
      settlement (result , after , withdrawn))
    (trans (unshielded-tail {k = "grants"} result tailRun)
      (Device.body-frame "grants" withdrawUnshielded ctx xs (grantCoin withdrawUnshielded ctx) none
        (grants-outside unshieldedWithdrawal) withdrawn))
  ...                           | shieldedWithdrawal = final-state
    (grantCallEvidence identifier g h spent settled identified recorded live scoped coinAdmitted challenged verified
      settlement (result , after , withdrawn))
    (trans (change-tail {k = "grants"} (flag (at 0 result)) (changeEntry ga) result refl refl tailRun)
      (Device.body-frame "grants" withdrawShielded ctx xs (grantCoin withdrawShielded ctx) none
        (grants-outside shieldedWithdrawal) withdrawn))
  ...                           | contractWithdrawal = final-state
    (grantCallEvidence identifier g h spent settled identified recorded live scoped coinAdmitted challenged verified
      settlement (result , after , withdrawn))
    (trans (change-tail {k = "grants"} (flag (at 0 (at 1 result))) (changeEntry ga) result refl refl tailRun)
      (Device.body-frame "grants" withdrawToContract ctx xs (grantCoin withdrawToContract ctx) none
        (grants-outside contractWithdrawal) withdrawn))

grant-final-state : ∀ c op ctx ga xs → Withdrawal op → ∀ {s v t es} →
  grantCall c op ctx ga xs s ≡ accepted v t es → GrantFinalState c op ctx ga xs s t
grant-final-state c op ctx ga xs w {es = es} execution = final-run c op ctx ga xs w (run es execution)

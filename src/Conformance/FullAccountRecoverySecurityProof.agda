{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

-- Proofs for Conformance.FullAccountRecoverySecurityProperties. Runs of the
-- actual evaluator are split statement by statement with
-- FullAccountExecution.then, in continuation-passing style: each step names
-- the source statement it consumes and passes its facts and the remaining run
-- on. The remaining program is inferred from the run being split; after a
-- statement that always accepts, the next step's statement determines it.
module Conformance.FullAccountRecoverySecurityProof (P : Primitives) where

import Conformance.FullAccount as Model
open import Conformance.FullAccountBody P
open import Conformance.FullAccountCrypto P
import Conformance.FullAccountDeviceSecurity P as Device
import Conformance.FullAccountDeviceSecurityProperties P as DeviceProperties
import Conformance.FullAccountDeviceSecurityProof P as DeviceProof
open import Conformance.FullAccountExecution using (Run; run) renaming (then to split)
open import Conformance.FullAccountGrant P
import Conformance.FullAccountGrantSecurity P as GrantSecurity
import Conformance.FullAccountGrantSecurityProof P as GrantProof
open import Conformance.FullAccountLayouts
open import Conformance.FullAccountRecoverySecurity P
open import Conformance.FullAccountSignatureBinding P using (recoverySubmitTag; submitChallenge; submitPreimage)
import Conformance.FullAccountSignatureBindingProof P as SignatureProof
open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_; if_then_else_; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; take; drop)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.All using (All; tabulate)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat.Base hiding (equal)
open import Data.Nat.Properties using (≡ᵇ⇒≡; <⇒<ᵇ; ≮⇒≥; <⇒≱)
open import Data.Product.Base using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String)
open import Data.String.Properties using () renaming (_≟_ to _≟ˢ_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Decidable using (dec-true; dec-false)

open Model.AccountSemantics P using (Entrypoint; construct; activation; device; grant;
  depositPublic; depositPrivate; submitRecovery; finaliseRecovery; execute; deviceCall; parseActivation; parseGrant)

private
  ----------------------------------------------------------------------
  -- Booleans, numbers and cell names

  rejected≢accepted : ∀ {A : Set} {e x t es} → rejected {A} e ≡ accepted x t es → ⊥
  rejected≢accepted ()

  accepted-injective : ∀ {A : Set} {x y t u es fs} → accepted {A} x t es ≡ accepted y u fs →
    x ≡ y × t ≡ u × es ≡ fs
  accepted-injective refl = refl , refl , refl

  true≢false : true ≡ false → ⊥
  true≢false ()

  not-true : ∀ b → not b ≡ true → b ≡ false
  not-true false _ = refl
  not-true true ()

  ≡ᵇ-true : ∀ m n → (m ≡ᵇ n) ≡ true → m ≡ n
  ≡ᵇ-true m n eq = ≡ᵇ⇒≡ m n (subst T (sym eq) tt)

  <ᵇ-false : ∀ m n → (m <ᵇ n) ≡ false → n ≤ m
  <ᵇ-false m n eq = ≮⇒≥ λ lt → subst T eq (<⇒<ᵇ lt)

  ∧-left : ∀ a {b} → T (a ∧ b) → T a
  ∧-left true _ = tt
  ∧-left false ()

  ∧-right : ∀ a {b} → T (a ∧ b) → T b
  ∧-right true holds = holds
  ∧-right false ()

  same-key : ∀ k → stringEqual k k ≡ true
  same-key k = dec-true (k ≟ˢ k) refl

  equal-key : ∀ k k′ → stringEqual k k′ ≡ true → k ≡ k′
  equal-key k k′ = DeviceProof.stringEqual-sound

  -- Decided by evaluating literal cell names.
  fresh : String → List String → Bool
  fresh k [] = true
  fresh k (w ∷ ws) = not (stringEqual k w) ∧ fresh k ws

  absent : ∀ {k ws} → T (fresh k ws) → k ∉ ws
  absent {k} {[]} _ ()
  absent {k} {w ∷ ws} ok (here refl) = subst (λ b → T (not b ∧ fresh k ws)) (same-key k) ok
  absent {k} {w ∷ ws} ok (there i) = absent (∧-right (not (stringEqual k w)) ok) i

  occurs : String → List String → Bool
  occurs k [] = false
  occurs k (w ∷ ws) = stringEqual k w ∨ occurs k ws

  occurs-∈ : ∀ k ws → T (occurs k ws) → k ∈ ws
  occurs-∈ k [] ()
  occurs-∈ k (w ∷ ws) ok with stringEqual k w in hit
  ... | true = here (equal-key k w hit)
  ... | false = there (occurs-∈ k ws ok)

  included : List String → List String → Bool
  included [] ws′ = true
  included (w ∷ ws) ws′ = occurs w ws′ ∧ included ws ws′

  subset : ∀ {ws ws′} → T (included ws ws′) → ∀ {k} → k ∈ ws → k ∈ ws′
  subset {[]} _ ()
  subset {w ∷ ws} {ws′} ok (here refl) = occurs-∈ w ws′ (∧-left (occurs w ws′) ok)
  subset {w ∷ ws} {ws′} ok (there i) = subset (∧-right (occurs w ws′) ok) i

  separate : List String → List String → Bool
  separate [] ws = true
  separate (p ∷ ps) ws = fresh p ws ∧ separate ps ws

  separated : ∀ {ps ws} → T (separate ps ws) → ∀ {k} → k ∈ ps → k ∉ ws
  separated {[]} _ ()
  separated {p ∷ ps} {ws} ok (here refl) = absent (∧-left (fresh p ws) ok)
  separated {p ∷ ps} {ws} ok (there i) = separated (∧-right (fresh p ws) ok) i

  pending-away : ∀ {k} → k ∈ pendingCells → ∀ w → T (fresh w pendingCells) → stringEqual k w ≡ false
  pending-away {k} pend w ok = dec-false (k ≟ˢ w) λ k≡w → absent {w} {pendingCells} ok (subst (_∈ pendingCells) k≡w pend)

  away-all : ∀ {k ws} → k ∈ pendingCells → T (separate pendingCells ws) → All (λ w → stringEqual k w ≡ false) ws
  away-all {k} {ws} pend ok = tabulate λ {w} w∈ →
    dec-false (k ≟ˢ w) λ k≡w → separated {pendingCells} {ws} ok pend (subst (_∈ ws) (sym k≡w) w∈)

  ----------------------------------------------------------------------
  -- Cells, frames and the pending record

  after : String → Value → State → State
  after k v s = state (insertCell k v (ledger s))

  lookup-insert-same : ∀ k v l → lookupCell k (insertCell k v l) ≡ just v
  lookup-insert-same k v [] rewrite same-key k = refl
  lookup-insert-same k v ((x , w) ∷ l) with stringEqual k x in hit
  ... | true rewrite same-key k = refl
  ... | false rewrite hit = lookup-insert-same k v l

  lookup-insert-other : ∀ k k′ v l → stringEqual k k′ ≡ false →
    lookupCell k (insertCell k′ v l) ≡ lookupCell k l
  lookup-insert-other k k′ v [] ne rewrite ne = refl
  lookup-insert-other k k′ v ((x , w) ∷ l) ne with stringEqual k′ x in hit
  ... | true rewrite ne | subst (λ y → stringEqual k y ≡ false) (equal-key k′ x hit) ne = refl
  ... | false with stringEqual k x
  ...   | true = refl
  ...   | false = lookup-insert-other k k′ v l ne

  written : ∀ k v s → Stores (after k v s) k v
  written k v s = stored (lookup-insert-same k v (ledger s))

  stores-unique : ∀ {s k v w} → Stores s k v → Stores s k w → v ≡ w
  stores-unique (stored a) (stored b) = just-injective (trans (sym a) b)

  cell-stored : ∀ {s k v} → Stores s k v → cell k s ≡ v
  cell-stored {s} {k} (stored eq) with lookupCell k (ledger s) | eq
  ... | nothing | ()
  ... | just w | refl = refl

  -- include of e into a cleared set leaves exactly e.
  include-empty : ∀ {s s′ k e} → Stores s k (tuple []) →
    Stores s′ k (tuple (insertSet e (fields (cell k s)))) → Stores s′ k (tuple (e ∷ []))
  include-empty {s} {s′} {k} {e} empty included′ =
    subst (λ d → Stores s′ k (tuple (insertSet e (fields d)))) (cell-stored empty) included′

  frames-insert : ∀ k v s → Frames (k ∷ []) s (after k v s)
  frames-insert k v s = framed λ j j∉ →
    lookup-insert-other j k v (ledger s) (dec-false (j ≟ˢ k) λ eq → j∉ (here eq))

  frames-then : ∀ {ws ws′ s t u} → Frames ws s t → Frames ws′ t u → Frames (ws ++ ws′) s u
  frames-then {ws} (framed first) (framed second) =
    framed λ k k∉ → trans (second k λ i → k∉ (∈-++⁺ʳ ws i)) (first k λ i → k∉ (∈-++⁺ˡ i))

  frames-weaken : ∀ {ws ws′ s t} → T (included ws ws′) → Frames ws s t → Frames ws′ s t
  frames-weaken ok (framed kept) = framed λ k k∉ → kept k λ i → k∉ (subset ok i)

  stores-frames : ∀ {ws s t k v} → Frames ws s t → Stores s k v → k ∉ ws → Stores t k v
  stores-frames {k = k} (framed kept) (stored eq) k∉ = stored (trans (kept k k∉) eq)

  stores-frames-back : ∀ {ws s t k v} → Frames ws s t → Stores t k v → k ∉ ws → Stores s k v
  stores-frames-back {k = k} (framed kept) (stored eq) k∉ = stored (trans (sym (kept k k∉)) eq)

  same-refl : ∀ {s} → SamePending s s
  same-refl = samePending λ _ _ → refl

  same-trans : ∀ {s t u} → SamePending s t → SamePending t u → SamePending s u
  same-trans (samePending first) (samePending second) = samePending λ k p → trans (second k p) (first k p)

  same-stores : ∀ {s t k v} → SamePending s t → k ∈ pendingCells → Stores s k v → Stores t k v
  same-stores {k = k} (samePending kept) p (stored eq) = stored (trans (kept k p) eq)

  same-stores-back : ∀ {s t k v} → SamePending s t → k ∈ pendingCells → Stores t k v → Stores s k v
  same-stores-back {k = k} (samePending kept) p (stored eq) = stored (trans (sym (kept k p)) eq)

  frames-pending : ∀ {ws s t} → T (separate pendingCells ws) → Frames ws s t → SamePending s t
  frames-pending ok (framed kept) = samePending λ k p → kept k (separated ok p)

  ----------------------------------------------------------------------
  -- Runs of single source statements

  return-run : ∀ {A : Set} (x : A) {s y t} → Run (return x) s y t → y ≡ x × t ≡ s
  return-run x (run _ refl) = refl , refl

  read-run : ∀ k {s v t} → Run (read k) s v t → Stores s k v × t ≡ s
  read-run k {s} (run _ execution) with lookupCell k (ledger s) in found
  ... | nothing = ⊥-elim (rejected≢accepted execution)
  ... | just w with accepted-injective execution
  ...   | refl , refl , _ = stored found , refl

  assert-run : ∀ b msg {s x t} → Run (assert b msg) s x t → b ≡ true × t ≡ s
  assert-run true msg (run _ refl) = refl , refl
  assert-run false msg (run _ ())

  lift-run : ∀ {A : Set} (r : Result A) {s x t} → Run (lift r) s x t → r ≡ success x × t ≡ s
  lift-run (failure e) (run _ ())
  lift-run (success v) (run _ refl) = refl , refl

  cast-run : ∀ label bits n {s x t} → Run (cast label bits n) s x t →
    (n <ᵇ 2 ^ bits) ≡ true × x ≡ n × t ≡ s
  cast-run label bits n (run _ execution) with n <ᵇ 2 ^ bits
  ... | false = ⊥-elim (rejected≢accepted execution)
  ... | true with accepted-injective execution
  ...   | refl , refl , _ = refl , refl , refl

  write-run : ∀ k v {s x t} → Run (write k v) s x t → t ≡ after k v s
  write-run k v (run _ refl) = refl

  emit-run : ∀ e {s x t} → Run (emit e) s x t → t ≡ s
  emit-run e (run _ refl) = refl

  clear-run : ∀ k {s x t} → Run (clear k) s x t → t ≡ after k (tuple []) s
  clear-run k (run _ refl) = refl

  include-run : ∀ k e {s x t} → Run (include k e) s x t →
    t ≡ after k (tuple (insertSet e (fields (cell k s)))) s
  include-run k e (run _ refl) = refl

  insert-run : ∀ label key v {s x t} → Run (insert label key v) s x t →
    t ≡ after label (tuple (insertMap key v (fields (cell label s)))) s
  insert-run label key v (run _ refl) = refl

  memberMap-run : ∀ label key {s x t} → Run (memberMap label key) s x t → t ≡ s
  memberMap-run label key (run _ refl) = refl

  lookup-run : ∀ label key {s x t} → Run (lookup label key) s x t → t ≡ s
  lookup-run label key {s} (run _ execution) with lookupMap key (fields (cell label s))
  ... | nothing = ⊥-elim (rejected≢accepted execution)
  ... | just w with accepted-injective execution
  ...   | _ , refl , _ = refl

  readCount-run : ∀ k {s n t} → Run (readCount k) s n t → Σ Value λ v → Stores s k v × n ≡ number v × t ≡ s
  readCount-run k r with split (read k) {λ v → return (number v)} r
  ... | v , t , first , rest with read-run k first
  ...   | found , refl with return-run (number v) rest
  ...     | refl , refl = v , found , refl , refl

  writeCount-run : ∀ k bits n {s x t} → Run (writeCount k bits n) s x t →
    (n <ᵇ 2 ^ bits) ≡ true × t ≡ after k (nat n) s
  writeCount-run k bits n r with split (cast k bits n) {λ v → write k (nat v)} r
  ... | x , t , first , rest with cast-run k bits n first
  ...   | bound , refl , refl = bound , write-run k (nat n) rest

  bump-frames : ∀ k bits {s x t} → Run (bump k bits) s x t → Frames (k ∷ []) s t
  bump-frames k bits {s} r with split (readCount k) {λ n → writeCount k bits (suc n)} r
  ... | n , t , counted , wrote with readCount-run k counted
  ...   | v , _ , refl , refl with writeCount-run k bits (suc (number v)) wrote
  ...     | _ , refl = frames-insert k (nat (suc (number v))) s

  insert-frames : ∀ label key v {s x t} → Run (insert label key v) s x t → Frames (label ∷ []) s t
  insert-frames label key v {s} r with insert-run label key v r
  ... | refl = frames-insert label (tuple (insertMap key v (fields (cell label s)))) s

  readSelf-run : ∀ ctx {s a t} → Run (readSelf ctx) s a t → a ≡ self ctx × t ≡ s
  readSelf-run ctx r with split (emit (contextRead "self" (self ctx))) {λ _ → return (self ctx)} r
  ... | _ , t , first , rest with emit-run (contextRead "self" (self ctx)) first
  ...   | refl with return-run (self ctx) rest
  ...     | refl , refl = refl , refl

  past-run : ∀ ctx n {s b t} → Run (readTimeGreater ctx n) s b t → b ≡ (n <ᵇ blockTime ctx) × t ≡ s
  past-run ctx n r
    with split (emit (contextRead "blockTimeGreaterThan" (nat n))) {λ _ → return (n <ᵇ blockTime ctx)} r
  ... | _ , t , first , rest with emit-run (contextRead "blockTimeGreaterThan" (nat n)) first
  ...   | refl with return-run (n <ᵇ blockTime ctx) rest
  ...     | refl , refl = refl , refl

  early-run : ∀ ctx n {s b t} → Run (readTimeLess ctx n) s b t → b ≡ (blockTime ctx <ᵇ n) × t ≡ s
  early-run ctx n r
    with split (emit (contextRead "blockTimeLessThan" (nat n))) {λ _ → return (blockTime ctx <ᵇ n)} r
  ... | _ , t , first , rest with emit-run (contextRead "blockTimeLessThan" (nat n)) first
  ...   | refl with return-run (blockTime ctx <ᵇ n) rest
  ...     | refl , refl = refl , refl

  -- The final return fixes the call's final state.
  finish : ∀ {A : Set} {x : A} {s y t} → Run (return x) s y t → (Q : State → Set) → Q s → Q t
  finish (run _ refl) Q q = q

  ----------------------------------------------------------------------
  -- State-free source computations

  Pure : {A : Set} → M A → Set
  Pure m = ∀ {s x t} → Run m s x t → t ≡ s

  pure-return : ∀ {A : Set} (x : A) → Pure (return x)
  pure-return x ran = proj₂ (return-run x ran)

  pure-abort : ∀ {A : Set} e → Pure {A} (abort e)
  pure-abort e (run _ ())

  pure-assert : ∀ b msg → Pure (assert b msg)
  pure-assert b msg ran = proj₂ (assert-run b msg ran)

  pure-lift : ∀ {A : Set} (r : Result A) → Pure (lift r)
  pure-lift r ran = proj₂ (lift-run r ran)

  pure-hash : ∀ {xs} → Pure (hash xs)
  pure-hash {xs} = pure-lift (persistentHash P xs)

  pure-lookup : ∀ label key → Pure (lookup label key)
  pure-lookup label key = lookup-run label key

  pure-if : ∀ {A : Set} b {m₁ m₂ : M A} → Pure m₁ → Pure m₂ → Pure (if b then m₁ else m₂)
  pure-if true p q = p
  pure-if false p q = q

  pure-schnorr : ∀ pk r sig h msg → Pure (schnorr pk r sig h msg)
  pure-schnorr pk r sig h msg (run _ executed) = SignatureProof.schnorr-preserves pk r sig h msg executed

  ----------------------------------------------------------------------
  -- Continuation-passing steps: the next statement of the run being split

  step-read : ∀ {B R : Set} k {f : Value → M B} {s y u} → Run (read k >>= f) s y u →
    (∀ v → Stores s k v → Run (f v) s y u → R) → R
  step-read k {f} r κ with split (read k) {f} r
  ... | v , t , first , rest with read-run k first
  ...   | found , refl = κ v found rest

  -- A read of a cell whose value is already known continues with that value.
  read-known : ∀ {B : Set} k {f : Value → M B} {s y u w} → Stores s k w →
    Run (read k >>= f) s y u → Run (f w) s y u
  read-known k {f} known r with split (read k) {f} r
  ... | v , t , first , rest with read-run k first
  ...   | found , refl with stores-unique known found
  ...     | refl = rest

  step-readCount : ∀ {B R : Set} k {f : ℕ → M B} {s y u} → Run (readCount k >>= f) s y u →
    (∀ v → Stores s k v → Run (f (number v)) s y u → R) → R
  step-readCount k {f} r κ with split (readCount k) {f} r
  ... | n , t , first , rest with readCount-run k first
  ...   | v , found , refl , refl = κ v found rest

  readCount-known : ∀ {B : Set} k {f : ℕ → M B} {s y u w} → Stores s k w →
    Run (readCount k >>= f) s y u → Run (f (number w)) s y u
  readCount-known k {f} known r with split (readCount k) {f} r
  ... | n , t , first , rest with readCount-run k first
  ...   | v , found , refl , refl with stores-unique known found
  ...     | refl = rest

  step-assert : ∀ {B R : Set} b msg {f : ⊤ → M B} {s y u} → Run (assert b msg >>= f) s y u →
    (b ≡ true → Run (f tt) s y u → R) → R
  step-assert b msg {f} r κ with split (assert b msg) {f} r
  ... | _ , t , first , rest with assert-run b msg first
  ...   | holds , refl = κ holds rest

  step-lift : ∀ {A B R : Set} (r : Result A) {f : A → M B} {s y u} → Run (lift r >>= f) s y u →
    (∀ x → r ≡ success x → Run (f x) s y u → R) → R
  step-lift r {f} ran κ with split (lift r) {f} ran
  ... | x , t , first , rest with lift-run r first
  ...   | lifted , refl = κ x lifted rest

  step-cast : ∀ {B R : Set} label bits n {f : ℕ → M B} {s y u} → Run (cast label bits n >>= f) s y u →
    ((n <ᵇ 2 ^ bits) ≡ true → Run (f n) s y u → R) → R
  step-cast label bits n {f} r κ with split (cast label bits n) {f} r
  ... | x , t , first , rest with cast-run label bits n first
  ...   | bound , refl , refl = κ bound rest

  step-pure : ∀ {A B R : Set} (m : M A) → Pure m → ∀ {f : A → M B} {s y u} → Run (m >>= f) s y u →
    (∀ x → Run m s x s → Run (f x) s y u → R) → R
  step-pure m stays {f} r κ with split m {f} r
  ... | x , t , first , rest with stays first
  ...   | refl = κ x first rest

  step-hash : ∀ {B R : Set} {xs} {f : Value → M B} {s y u} → Run (hash xs >>= f) s y u →
    (∀ h → Run (hash xs) s h s → Run (f h) s y u → R) → R
  step-hash {xs = xs} r κ = step-pure (hash xs) pure-hash r κ

  step-if : ∀ {B R : Set} b {m₁ m₂ : M ⊤} → Pure m₁ → Pure m₂ → ∀ {f : ⊤ → M B} {s y u} →
    Run ((if b then m₁ else m₂) >>= f) s y u → (Run (f tt) s y u → R) → R
  step-if b {m₁} {m₂} p₁ p₂ {f} r κ with split (if b then m₁ else m₂) {f} r
  ... | _ , t , first , rest with pure-if b p₁ p₂ first
  ...   | refl = κ rest

  step-emit : ∀ {B R : Set} e {f : ⊤ → M B} {s y u} → Run (emit e >>= f) s y u → (Run (f tt) s y u → R) → R
  step-emit e {f} r κ with split (emit e) {f} r
  ... | _ , t , first , rest with emit-run e first
  ...   | refl = κ rest

  step-write : ∀ {B R : Set} k v {f : ⊤ → M B} {s y u} → Run (write k v >>= f) s y u →
    (Stores (after k v s) k v → Frames (k ∷ []) s (after k v s) → Run (f tt) (after k v s) y u → R) → R
  step-write k v {f} {s} r κ with split (write k v) {f} r
  ... | _ , t , first , rest with write-run k v first
  ...   | refl = κ (written k v s) (frames-insert k v s) rest

  -- A final write, with no statement after it.
  write-last : ∀ {R : Set} k v {s x t} → Run (write k v) s x t → (Stores t k v → Frames (k ∷ []) s t → R) → R
  write-last k v {s} (run _ refl) κ = κ (written k v s) (frames-insert k v s)

  step-writeCount : ∀ {B R : Set} k bits n {f : ⊤ → M B} {s y u} → Run (writeCount k bits n >>= f) s y u →
    ((n <ᵇ 2 ^ bits) ≡ true → Stores (after k (nat n) s) k (nat n) → Frames (k ∷ []) s (after k (nat n) s) →
      Run (f tt) (after k (nat n) s) y u → R) → R
  step-writeCount k bits n {f} {s} r κ with split (writeCount k bits n) {f} r
  ... | _ , t , first , rest with writeCount-run k bits n first
  ...   | bound , refl = κ bound (written k (nat n) s) (frames-insert k (nat n) s) rest

  step-bump : ∀ {B R : Set} k bits {f : ⊤ → M B} {s y u} → Run (bump k bits >>= f) s y u →
    (∀ v → Stores s k v → (suc (number v) <ᵇ 2 ^ bits) ≡ true →
      Stores (after k (nat (suc (number v))) s) k (nat (suc (number v))) →
      Frames (k ∷ []) s (after k (nat (suc (number v))) s) →
      Run (f tt) (after k (nat (suc (number v))) s) y u → R) → R
  step-bump k bits {f} {s} r κ with split (bump k bits) {f} r
  ... | _ , t , first , rest with split (readCount k) {λ n → writeCount k bits (suc n)} first
  ...   | n , t₁ , counted , wrote with readCount-run k counted
  ...     | v , found , refl , refl with writeCount-run k bits (suc (number v)) wrote
  ...       | bound , refl =
    κ v found bound (written k (nat (suc (number v))) s) (frames-insert k (nat (suc (number v))) s) rest

  step-clear : ∀ {B R : Set} k {f : ⊤ → M B} {s y u} → Run (clear k >>= f) s y u →
    (Stores (after k (tuple []) s) k (tuple []) → Frames (k ∷ []) s (after k (tuple []) s) →
      Run (f tt) (after k (tuple []) s) y u → R) → R
  step-clear k {f} {s} r κ with split (clear k) {f} r
  ... | _ , t , first , rest with clear-run k first
  ...   | refl = κ (written k (tuple []) s) (frames-insert k (tuple []) s) rest

  step-include : ∀ {B R : Set} k e {f : ⊤ → M B} {s y u} → Run (include k e >>= f) s y u →
    (Stores (after k (tuple (insertSet e (fields (cell k s)))) s) k (tuple (insertSet e (fields (cell k s)))) →
      Frames (k ∷ []) s (after k (tuple (insertSet e (fields (cell k s)))) s) →
      Run (f tt) (after k (tuple (insertSet e (fields (cell k s)))) s) y u → R) → R
  step-include k e {f} {s} r κ with split (include k e) {f} r
  ... | _ , t , first , rest with include-run k e first
  ...   | refl = κ (written k (tuple (insertSet e (fields (cell k s)))) s)
    (frames-insert k (tuple (insertSet e (fields (cell k s)))) s) rest

  step-insert : ∀ {B R : Set} label key v {f : ⊤ → M B} {s y u} → Run (insert label key v >>= f) s y u →
    (Frames (label ∷ []) s (after label (tuple (insertMap key v (fields (cell label s)))) s) →
      Run (f tt) (after label (tuple (insertMap key v (fields (cell label s)))) s) y u → R) → R
  step-insert label key v {f} {s} r κ with split (insert label key v) {f} r
  ... | _ , t , first , rest with insert-run label key v first
  ...   | refl = κ (frames-insert label (tuple (insertMap key v (fields (cell label s)))) s) rest

  -- Statements that always accept with a non-unit answer are consumed together
  -- with the next statement, which then fixes the remaining program.
  step-readSelf : ∀ {B C : Set} ctx (next : Value → M C) {g : Value → C → M B} {s y u} →
    Run (readSelf ctx >>= λ a → next a >>= g a) s y u → Run (next (self ctx) >>= g (self ctx)) s y u
  step-readSelf ctx next {g} r with split (readSelf ctx) {λ a → next a >>= g a} r
  ... | a , t , first , rest with readSelf-run ctx first
  ...   | refl , refl = rest

  step-past : ∀ {B C : Set} ctx n (next : Bool → M C) {g : Bool → C → M B} {s y u} →
    Run (readTimeGreater ctx n >>= λ b → next b >>= g b) s y u →
    Run (next (n <ᵇ blockTime ctx) >>= g (n <ᵇ blockTime ctx)) s y u
  step-past ctx n next {g} r with split (readTimeGreater ctx n) {λ b → next b >>= g b} r
  ... | b , t , first , rest with past-run ctx n first
  ...   | refl , refl = rest

  step-early : ∀ {B C : Set} ctx n (next : Bool → M C) {g : Bool → C → M B} {s y u} →
    Run (readTimeLess ctx n >>= λ b → next b >>= g b) s y u →
    Run (next (blockTime ctx <ᵇ n) >>= g (blockTime ctx <ᵇ n)) s y u
  step-early ctx n next {g} r with split (readTimeLess ctx n) {λ b → next b >>= g b} r
  ... | b , t , first , rest with early-run ctx n first
  ...   | refl , refl = rest

  -- A statement known only through a frame of the cells it may write.
  step-frames : ∀ {B R : Set} {m : M ⊤} {ws} → (∀ {s x t} → Run m s x t → Frames ws s t) →
    ∀ {f : ⊤ → M B} {s y u} → Run (m >>= f) s y u → (∀ {t} → Frames ws s t → Run (f tt) t y u → R) → R
  step-frames {m = m} framing {f} r κ with split m {f} r
  ... | _ , t , first , rest = κ (framing first) rest

  ----------------------------------------------------------------------
  -- Key validation and the successor entry

  pure-requireSmallOrderFree : ∀ pk msg → Pure (requireSmallOrderFree pk msg)
  pure-requireSmallOrderFree pk msg r =
    step-lift (ecMul P jubjub pk 8) r λ q _ r₁ →
    step-lift (ecMulGenerator P jubjub 0) r₁ λ o _ r₂ →
    pure-assert (not (equal q o)) msg r₂

  pure-requireRecoveryKey : ∀ pk → Pure (requireRecoveryKey pk)
  pure-requireRecoveryKey pk r =
    step-lift (ecMulGenerator P jubjub 0) r λ o _ r₁ →
    step-assert (not (equal pk o)) "recovery key is the identity" r₁ λ _ r₂ →
    pure-requireSmallOrderFree pk "recovery key has small order" r₂

  hash-everywhere : ∀ {xs h} → persistentHash P xs ≡ success h → ∀ s → Run (hash xs) s h s
  hash-everywhere hashed s = run [] (cong (λ r → lift r s) hashed)

  hash-run : ∀ {xs s h t} → Run (hash xs) s h t → persistentHash P xs ≡ success h × t ≡ s
  hash-run {xs} = lift-run (persistentHash P xs)

  -- entry hashes the successor's device entry at the call's own address.
  step-entry : ∀ {B R : Set} ctx a e c {f : Value → M B} {s y u} → Run (entry jubjub ctx a e c >>= f) s y u →
    (∀ x → (∀ s′ → Run (entryAt jubjub (self ctx) a e c) s′ x s′) → Run (f x) s y u → R) → R
  step-entry ctx a e c {f} r κ with split (entry jubjub ctx a e c) {f} r
  ... | x , t , first , rest with split (readSelf ctx) {λ addr → entryAt jubjub addr a e c} first
  ...   | _ , t₁ , selfRead , hashed with readSelf-run ctx selfRead
  ...     | refl , refl with hash-run hashed
  ...       | hashedEq , refl = κ x (hash-everywhere hashedEq) rest

  ----------------------------------------------------------------------
  -- Deposits, the only runtime entrypoints outside device, grant, activation
  -- and recovery calls

  pure-createCoin : ∀ coin recipient → Pure (createCoin coin recipient)
  pure-createCoin coin recipient r =
    step-lift (coinCommitment P coin recipient) r λ cm _ r₁ → emit-run (createShielded coin recipient cm) r₁

  pure-receiveCoin : ∀ ctx coin → Pure (receiveCoin ctx coin)
  pure-receiveCoin ctx coin r =
    step-pure (createCoin coin (tuple (bool false ∷ self ctx ∷ []))) (pure-createCoin coin (tuple (bool false ∷ self ctx ∷ [])))
      (step-readSelf ctx (λ addr → createCoin coin (tuple (bool false ∷ addr ∷ []))) r) λ _ _ r₁ →
    emit-run (receiveShielded coin) r₁

  credit-branch : ∀ b color amount {s x t} →
    Run (if b
      then (lookup "unshielded_balances" color >>= λ old →
            cast "unshielded_balances" 128 (number old + amount) >>= λ n →
            insert "unshielded_balances" color (nat n))
      else insert "unshielded_balances" color (nat amount)) s x t →
    Frames ("unshielded_balances" ∷ []) s t
  credit-branch true color amount r =
    step-pure (lookup "unshielded_balances" color) (pure-lookup "unshielded_balances" color) r λ old _ r₁ →
    step-cast "unshielded_balances" 128 (number old + amount) r₁ λ _ r₂ →
    insert-frames "unshielded_balances" color (nat (number old + amount)) r₂
  credit-branch false color amount r = insert-frames "unshielded_balances" color (nat amount) r

  credit-frames : ∀ color amount {s x t} → Run (credit color amount) s x t → Frames ("unshielded_balances" ∷ []) s t
  credit-frames color amount r
    with split (memberMap "unshielded_balances" color)
      {λ present → if present
        then (lookup "unshielded_balances" color >>= λ old →
              cast "unshielded_balances" 128 (number old + amount) >>= λ n →
              insert "unshielded_balances" color (nat n))
        else insert "unshielded_balances" color (nat amount)} r
  ... | present , t , first , rest with memberMap-run "unshielded_balances" color first
  ...   | refl = credit-branch present color amount rest

  inbox-frames : ∀ entry {s x t} → Run (inboxAppend entry) s x t → Frames ("inbox" ∷ "inbox_count" ∷ []) s t
  inbox-frames entry r =
    step-readCount "inbox_count" r λ count _ r₁ →
    step-insert "inbox" (nat (number count)) entry r₁ λ f₁ r₂ →
    frames-then f₁ (bump-frames "inbox_count" 64 r₂)

  deposit-public : ∀ ctx xs {s v t} → Run (execute depositPublic ctx xs) s v t → SamePending s t
  deposit-public ctx xs {s} r =
    step-emit (receiveUnshielded (get 0 xs) (number (get 1 xs))) r λ r₁ →
    step-frames (credit-frames (get 0 xs) (number (get 1 xs))) r₁ λ f₁ r₂ →
    step-bump "round" 64 r₂ λ _ _ _ _ f₂ r₃ →
    finish r₃ (SamePending s) (frames-pending _ (frames-then f₁ f₂))

  deposit-private : ∀ ctx xs {s v t} → Run (execute depositPrivate ctx xs) s v t → SamePending s t
  deposit-private ctx xs {s} r =
    step-pure (receiveCoin ctx (get 0 xs)) (pure-receiveCoin ctx (get 0 xs)) r λ _ _ r₁ →
    step-frames (inbox-frames (get 1 xs)) r₁ λ f₁ r₂ →
    step-bump "round" 64 r₂ λ _ _ _ _ f₂ r₃ →
    finish r₃ (SamePending s) (frames-pending _ (frames-then f₁ f₂))

------------------------------------------------------------------------
-- recover_submit

module SubmitRun (ctx : Context) (xs : List Value) where
  open SubmitArguments xs

  private
    installation : ℕ → M Value
    installation postEpoch = do
      write "pending_recovery" (bool true)
      successor ← entry jubjub ctx (successorAuthority xs) postEpoch 0
      write "pending_entry" successor
      write "pending_recovery_pk" nextRecoveryKey
      window ← readCount "veto_window"
      writeCount "pending_not_before" 64 (number nowBound + window)
      bump "round" 64
      return unit

    signatures : ℕ → Value → Value → M Value
    signatures postEpoch digest pk = do
      schnorr pk recoveryR recoveryS digest "invalid recovery signature"
      schnorr successorKey successorR successorS digest "invalid successor co-signature"
      past ← readTimeGreater ctx (number nowBound)
      assert (not past) "now bound is in the past"
      installation postEpoch

    signing : ℕ → Value → Value → ℕ → M Value
    signing postEpoch addr pk nonce = do
      domain ← hashTag recoverySubmitTag
      digest ← hash (submitPreimage domain (submitChallenge addr pk xs postEpoch nonce))
      verifyingPk ← read "recovery_pk"
      signatures postEpoch digest verifyingPk

    record InstalledCells (postEpoch : ℕ) (s t : State) : Set where
      field
        successor window : Value
        successorEntry : Run (entryAt jubjub (self ctx) (successorAuthority xs) postEpoch 0) s successor s
        windowCell : Stores s "veto_window" window
        flagStored : Stores t "pending_recovery" (bool true)
        entryStored : Stores t "pending_entry" successor
        keyStored : Stores t "pending_recovery_pk" nextRecoveryKey
        deadlineStored : Stores t "pending_not_before" (nat (number nowBound + number window))
        frame : Frames (pendingCells ++ "round" ∷ []) s t

    record Ready (s : State) (v : Value) (t : State) : Set where
      field
        storedEpoch : Value
        complete : InstalledCells (suc (number storedEpoch)) s t → Submission.Evidence ctx xs s t
        remaining : Run (installation (suc (number storedEpoch))) s v t

    abstract
      install : ∀ postEpoch {s v t} → Run (installation postEpoch) s v t → InstalledCells postEpoch s t
      install postEpoch {s} r₀ =
        step-write "pending_recovery" (bool true) r₀ λ flagStored f₁ r₁ →
        step-entry ctx (successorAuthority xs) postEpoch 0 r₁ λ successor successorEntry r₂ →
        step-write "pending_entry" successor r₂ λ entryStored f₂ r₃ →
        step-write "pending_recovery_pk" nextRecoveryKey r₃ λ keyStored f₃ r₄ →
        step-readCount "veto_window"
          {f = λ window → writeCount "pending_not_before" 64 (number nowBound + window) >> (bump "round" 64 >> return unit)}
          r₄ λ window windowCell r₅ →
        step-writeCount "pending_not_before" 64 (number nowBound + number window) r₅ λ _ deadlineStored f₄ r₆ →
        step-bump "round" 64 r₆ λ _ _ _ _ f₅ r₇ →
        finish r₇ (InstalledCells postEpoch s) record
          { successor = successor
          ; window = window
          ; successorEntry = successorEntry s
          ; windowCell = stores-frames-back (frames-then f₁ (frames-then f₂ f₃)) windowCell (absent _)
          ; flagStored = stores-frames (frames-then f₂ (frames-then f₃ (frames-then f₄ f₅))) flagStored (absent _)
          ; entryStored = stores-frames (frames-then f₃ (frames-then f₄ f₅)) entryStored (absent _)
          ; keyStored = stores-frames (frames-then f₄ f₅) keyStored (absent _)
          ; deadlineStored = stores-frames f₅ deadlineStored (absent _)
          ; frame = frames-then f₁ (frames-then f₂ (frames-then f₃ (frames-then f₄ f₅)))
          }

      prefix : ∀ {s v t} → Run (submit ctx xs) s v t → Ready s v t
      prefix {s} r₀ =
        step-read "pending_recovery" r₀ λ pending idle r₁ →
        step-assert (not (flag pending)) "recovery already pending" r₁ λ free r₂ →
        step-readCount "device_epoch" r₂ λ storedEpoch epochCell r₃ →
        step-assert (number epoch ≡ᵇ number storedEpoch) "stale epoch" r₃ λ signedEpoch r₄ →
        step-readCount "auth_nonce" r₄ λ storedNonce nonceCell r₅ →
        step-assert (number authNonce ≡ᵇ number storedNonce) "stale authorisation nonce" r₅ λ signedNonce r₆ →
        step-read "recovery_pk" r₆ λ pk pkCell r₇ →
        step-pure (requireRecoveryKey pk) (pure-requireRecoveryKey pk) r₇ λ _ pkValid r₈ →
        step-pure (requireRecoveryKey successorKey) (pure-requireRecoveryKey successorKey) r₈ λ _ successorValid r₉ →
        step-pure (requireRecoveryKey nextRecoveryKey) (pure-requireRecoveryKey nextRecoveryKey) r₉ λ _ nextValid r₁₀ →
        step-assert (not (equal nextRecoveryKey pk)) "recovery commitment reused"
          (read-known "recovery_pk" pkCell r₁₀) λ reused r₁₁ →
        step-cast "device_epoch" 32 (suc (number storedEpoch))
          (readCount-known "device_epoch" epochCell r₁₁) λ epochBound r₁₂ →
        step-pure (hashTag recoverySubmitTag) pure-hash
          (readCount-known "auth_nonce" {f = signing (suc (number storedEpoch)) (self ctx) pk} nonceCell
            (read-known "recovery_pk"
              {f = λ signingPk → readCount "auth_nonce" >>= signing (suc (number storedEpoch)) (self ctx) signingPk}
              pkCell (step-readSelf ctx (λ _ → read "recovery_pk")
                {g = λ addr signingPk → readCount "auth_nonce" >>= signing (suc (number storedEpoch)) addr signingPk} r₁₂)))
          λ domain domainHash r₁₃ →
        step-hash r₁₃ λ digest challengeHash r₁₄ →
        step-pure (schnorr pk recoveryR recoveryS digest "invalid recovery signature")
          (pure-schnorr pk recoveryR recoveryS digest "invalid recovery signature")
          (read-known "recovery_pk" {f = signatures (suc (number storedEpoch)) digest} pkCell r₁₄)
          λ _ recoverySignature r₁₅ →
        step-pure (schnorr successorKey successorR successorS digest "invalid successor co-signature")
          (pure-schnorr successorKey successorR successorS digest "invalid successor co-signature") r₁₅
          λ _ successorSignature r₁₆ →
        step-assert (not (number nowBound <ᵇ blockTime ctx)) "now bound is in the past"
          (step-past ctx (number nowBound) (λ past → assert (not past) "now bound is in the past")
            {g = λ _ _ → installation (suc (number storedEpoch))} r₁₆)
          λ notPast r₁₇ → record
          { storedEpoch = storedEpoch
          ; remaining = r₁₇
          ; complete = λ cells → record
            { pendingFlag = pending
            ; storedEpoch = storedEpoch
            ; storedNonce = storedNonce
            ; recoveryKey = pk
            ; idle = idle
            ; notPending = not-true (flag pending) free
            ; epochCell = epochCell
            ; signedEpoch = ≡ᵇ-true (number epoch) (number storedEpoch) signedEpoch
            ; nonceCell = nonceCell
            ; signedNonce = ≡ᵇ-true (number authNonce) (number storedNonce) signedNonce
            ; recoveryKeyCell = pkCell
            ; recoveryKeyValid = pkValid
            ; successorKeyValid = successorValid
            ; nextKeyValid = nextValid
            ; freshRecoveryKey = not-true (equal nextRecoveryKey pk) reused
            ; epochBound = epochBound
            ; domain = domain
            ; digest = digest
            ; domainHash = domainHash
            ; challengeHash = challengeHash
            ; recoverySignature = recoverySignature
            ; successorSignature = successorSignature
            ; notPast = <ᵇ-false (number nowBound) (blockTime ctx) (not-true (number nowBound <ᵇ blockTime ctx) notPast)
            ; successor = InstalledCells.successor cells
            ; vetoWindow = InstalledCells.window cells
            ; successorEntry = InstalledCells.successorEntry cells
            ; windowCell = InstalledCells.windowCell cells
            ; installsFlag = InstalledCells.flagStored cells
            ; installsEntry = InstalledCells.entryStored cells
            ; installsRecoveryKey = InstalledCells.keyStored cells
            ; installsDeadline = InstalledCells.deadlineStored cells
            ; frame = InstalledCells.frame cells
            }
          }

  evidence : ∀ {s v t} → Run (submit ctx xs) s v t → Submission.Evidence ctx xs s t
  evidence r = Ready.complete ready (install (suc (number (Ready.storedEpoch ready))) (Ready.remaining ready))
    where ready = prefix r

abstract
  submit-evidence : ∀ ctx xs {s v t es} → submit ctx xs s ≡ accepted v t es → Submission.Evidence ctx xs s t
  submit-evidence ctx xs ok = SubmitRun.evidence ctx xs (run _ ok)

submit-refused-while-pending : ∀ ctx xs {s p} → Stores s "pending_recovery" p → flag p ≡ true →
  ∃ λ error → submit ctx xs s ≡ rejected error
submit-refused-while-pending ctx xs {s} {p} cell flagged with submit ctx xs s in ran
... | rejected error = error , refl
... | accepted v t es = ⊥-elim (true≢false
  (trans (sym flagged) (trans (cong flag (stores-unique cell (Submission.Evidence.idle evidence)))
    (Submission.Evidence.notPending evidence))))
  where evidence = submit-evidence ctx xs ran

------------------------------------------------------------------------
-- recover_finalise

module FinaliseRun (ctx : Context) where
  private
    clearing : Value → M Value
    clearing pk = do
      o ← lift (ecMul P jubjub pk 0)
      write "pending_recovery_pk" o
      write "pending_not_before" (nat 0)
      bump "auth_nonce" 64
      bump "round" 64
      return unit

    installing : Value → M Value
    installing pk = do
      write "recovery_pk" pk
      write "recovery_phi_len" (nat 0)
      write "pending_recovery" (bool false)
      write "pending_entry" zero32
      clearingPk ← read "pending_recovery_pk"
      clearing clearingPk

    enacting : M Value
    enacting = do
      pk ← read "pending_recovery_pk"
      requireRecoveryKey pk
      bump "device_epoch" 32
      clear "devices"
      successor ← read "pending_entry"
      include "devices" successor
      write "device_count" (nat 1)
      installingPk ← read "pending_recovery_pk"
      installing installingPk

  evidence : ∀ {s v t} → Run (finalise ctx) s v t → Finalisation.Evidence ctx s t
  evidence {s} r₀ =
    step-read "pending_recovery" r₀ λ pending pendingCell r₁ →
    step-assert (flag pending) "no recovery pending" r₁ λ isPending r₂ →
    step-readCount "pending_not_before" r₂ λ deadline deadlineCell r₃ →
    step-assert (not (blockTime ctx <ᵇ number deadline)) "veto window still open"
      (step-early ctx (number deadline) (λ early → assert (not early) "veto window still open")
        {g = λ _ _ → enacting} r₃)
      λ notEarly r₄ →
    step-read "pending_recovery_pk" r₄ λ pk pkCell r₅ →
    step-pure (requireRecoveryKey pk) (pure-requireRecoveryKey pk) r₅ λ _ pkValid r₆ →
    step-bump "device_epoch" 32 r₆ λ storedEpoch epochCell _ epochStored f₁ r₇ →
    step-clear "devices" r₇ λ emptied f₂ r₈ →
    step-read "pending_entry" r₈ λ successor successorRead r₉ →
    step-include "devices" successor r₉ λ includedSuccessor f₃ r₁₀ →
    step-write "device_count" (nat 1) r₁₀ λ countStored f₄ r₁₁ →
    step-write "recovery_pk" pk
      (read-known "pending_recovery_pk" {f = installing}
        (stores-frames (frames-then f₁ (frames-then f₂ (frames-then f₃ f₄))) pkCell (absent _)) r₁₁)
      λ keyStored f₅ r₁₂ →
    step-write "recovery_phi_len" (nat 0) r₁₂ λ phiStored f₆ r₁₃ →
    step-write "pending_recovery" (bool false) r₁₃ λ flagStored f₇ r₁₄ →
    step-write "pending_entry" zero32 r₁₄ λ entryStored f₈ r₁₅ →
    step-lift (ecMul P jubjub pk 0)
      (read-known "pending_recovery_pk" {f = clearing}
        (stores-frames (frames-then f₁ (frames-then f₂ (frames-then f₃ (frames-then f₄
          (frames-then f₅ (frames-then f₆ (frames-then f₇ f₈))))))) pkCell (absent _)) r₁₅)
      λ clearedKey clearedKeyValue r₁₆ →
    step-write "pending_recovery_pk" clearedKey r₁₆ λ clearedStored f₉ r₁₇ →
    step-write "pending_not_before" (nat 0) r₁₇ λ deadlineStored f₁₀ r₁₈ →
    step-bump "auth_nonce" 64 r₁₈ λ storedNonce nonceRead _ nonceStored f₁₁ r₁₉ →
    step-bump "round" 64 r₁₉ λ _ _ _ _ f₁₂ r₂₀ →
    let F₁₂ = f₁₂
        F₁₁ = frames-then f₁₁ F₁₂
        F₁₀ = frames-then f₁₀ F₁₁
        F₉ = frames-then f₉ F₁₀
        F₈ = frames-then f₈ F₉
        F₇ = frames-then f₇ F₈
        F₆ = frames-then f₆ F₇
        F₅ = frames-then f₅ F₆
        F₄ = frames-then f₄ F₅
        F₃ = frames-then f₃ F₄
        F₂ = frames-then f₂ F₃
        F₁ = frames-then f₁ F₂
    in finish r₂₀ (Finalisation.Evidence ctx s) record
      { pendingFlag = pending
      ; deadline = deadline
      ; successor = successor
      ; recoveryKey = pk
      ; storedEpoch = storedEpoch
      ; storedNonce = storedNonce
      ; clearedKey = clearedKey
      ; pending = pendingCell
      ; isPending = isPending
      ; deadlineCell = deadlineCell
      ; windowElapsed = <ᵇ-false (blockTime ctx) (number deadline) (not-true (blockTime ctx <ᵇ number deadline) notEarly)
      ; successorCell = stores-frames-back (frames-then f₁ f₂) successorRead (absent _)
      ; recoveryKeyCell = pkCell
      ; recoveryKeyValid = pkValid
      ; epochCell = epochCell
      ; nonceCell = stores-frames-back (frames-then f₁ (frames-then f₂ (frames-then f₃ (frames-then f₄
          (frames-then f₅ (frames-then f₆ (frames-then f₇ (frames-then f₈ (frames-then f₉ f₁₀)))))))))
          nonceRead (absent _)
      ; advancesEpoch = stores-frames F₂ epochStored (absent _)
      ; replacesDevices = stores-frames F₄ (include-empty emptied includedSuccessor) (absent _)
      ; resetsDeviceCount = stores-frames F₅ countStored (absent _)
      ; installsRecoveryKey = stores-frames F₆ keyStored (absent _)
      ; clearsPhi = stores-frames F₇ phiStored (absent _)
      ; advancesNonce = stores-frames F₁₂ nonceStored (absent _)
      ; clearsFlag = stores-frames F₈ flagStored (absent _)
      ; clearsEntry = stores-frames F₉ entryStored (absent _)
      ; clearedKeyValue = clearedKeyValue
      ; clearsKey = stores-frames F₁₀ clearedStored (absent _)
      ; clearsDeadline = stores-frames F₁₁ deadlineStored (absent _)
      ; frame = frames-weaken _ F₁
      }

abstract
  finalise-evidence : ∀ ctx {s v t es} → finalise ctx s ≡ accepted v t es → Finalisation.Evidence ctx s t
  finalise-evidence ctx ok = FinaliseRun.evidence ctx (run _ ok)

finalise-refused-without-pending : ∀ ctx {s p} → Stores s "pending_recovery" p → flag p ≡ false →
  ∃ λ error → finalise ctx s ≡ rejected error
finalise-refused-without-pending ctx {s} {p} cell idle with finalise ctx s in ran
... | rejected error = error , refl
... | accepted v t es = ⊥-elim (true≢false
  (trans (sym (Finalisation.Evidence.isPending evidence))
    (trans (cong flag (stores-unique (Finalisation.Evidence.pending evidence) cell)) idle)))
  where evidence = finalise-evidence ctx ran

finalise-refused-before-deadline : ∀ ctx {s d} → Stores s "pending_not_before" d → blockTime ctx < number d →
  ∃ λ error → finalise ctx s ≡ rejected error
finalise-refused-before-deadline ctx {s} {d} cell early with finalise ctx s in ran
... | rejected error = error , refl
... | accepted v t es = ⊥-elim (<⇒≱ early
  (subst (λ w → number w ≤ blockTime ctx) (stores-unique (Finalisation.Evidence.deadlineCell evidence) cell)
    (Finalisation.Evidence.windowElapsed evidence)))
  where evidence = finalise-evidence ctx ran

------------------------------------------------------------------------
-- recover_cancel and publish_recovery_session bodies

private
  cancel-run : ∀ {s x t} → Run cancel s x t → Cancellation s t
  cancel-run {s} r₀ =
    step-read "pending_recovery" r₀ λ pending pendingCell r₁ →
    step-assert (flag pending) "no recovery pending" r₁ λ isPending r₂ →
    step-write "pending_recovery" (bool false) r₂ λ flagStored f₁ r₃ →
    step-write "pending_entry" zero32 r₃ λ entryStored f₂ r₄ →
    step-read "pending_recovery_pk" r₄ λ pk pkRead r₅ →
    step-lift (ecMul P jubjub pk 0) r₅ λ clearedKey clearedKeyValue r₆ →
    step-write "pending_recovery_pk" clearedKey r₆ λ keyStored f₃ r₇ →
    write-last "pending_not_before" (nat 0) r₇ λ deadlineStored f₄ → record
      { pendingFlag = pending
      ; recoveryKey = pk
      ; clearedKey = clearedKey
      ; pending = pendingCell
      ; isPending = isPending
      ; recoveryKeyCell = stores-frames-back (frames-then f₁ f₂) pkRead (absent _)
      ; clearedKeyValue = clearedKeyValue
      ; clearsFlag = stores-frames (frames-then f₂ (frames-then f₃ f₄)) flagStored (absent _)
      ; clearsEntry = stores-frames (frames-then f₃ f₄) entryStored (absent _)
      ; clearsKey = stores-frames f₄ keyStored (absent _)
      ; clearsDeadline = deadlineStored
      ; frame = frames-then f₁ (frames-then f₂ (frames-then f₃ f₄))
      }

  -- body cancelRecovery is `cancel >> return unit`, whatever its other arguments.
  cancel-body : ∀ {s v t} → Run (cancel >> return unit) s v t → Cancellation s t
  cancel-body r with split cancel {λ _ → return unit} r
  ... | _ , t₁ , cancelled , returned = finish returned (Cancellation _) (cancel-run cancelled)

  publish-run : ∀ xs {s x t} → Run (publish xs) s x t → Publication.Evidence xs s t
  publish-run xs {s} r₀ =
    step-read "pending_recovery" r₀ λ pending idle r₁ →
    step-assert (not (flag pending)) "recovery pending; cancel first" r₁ λ free r₂ →
    step-assert (1 ≤ᵇ number (get 6 xs)) "phi must not be empty" r₂ λ _ r₃ →
    step-assert (number (get 6 xs) ≤ᵇ 4) "phi length out of range" r₃ λ _ r₄ →
    step-if (number (get 6 xs) <ᵇ 2) (pure-assert (number (get 3 xs) ≡ᵇ 0) "unused phi slot 2 not zero")
      (pure-return tt) r₄ λ r₅ →
    step-if (number (get 6 xs) <ᵇ 3) (pure-assert (number (get 4 xs) ≡ᵇ 0) "unused phi slot 3 not zero")
      (pure-return tt) r₅ λ r₆ →
    step-if (number (get 6 xs) <ᵇ 4) (pure-assert (number (get 5 xs) ≡ᵇ 0) "unused phi slot 4 not zero")
      (pure-return tt) r₆ λ r₇ →
    step-assert (not (equal (get 1 xs) zero32)) "session nonce is zero" r₇ λ _ r₈ →
    step-read "recovery_session" r₈ λ session sessionCell r₉ →
    step-assert (not (equal (get 1 xs) session)) "session nonce reused" r₉ λ sessionFresh r₁₀ →
    step-read "recovery_pk" r₁₀ λ oldKey keyCell r₁₁ →
    step-assert (not (equal (get 0 xs) oldKey)) "recovery commitment reused" r₁₁ λ keyFresh r₁₂ →
    step-pure (requireRecoveryKey (get 0 xs)) (pure-requireRecoveryKey (get 0 xs)) r₁₂ λ _ newValid r₁₃ →
    step-write "recovery_pk" (get 0 xs) r₁₃ λ keyStored f₁ r₁₄ →
    step-write "recovery_session" (get 1 xs) r₁₄ λ sessionStored f₂ r₁₅ →
    step-insert "recovery_phi" (nat 1) (get 2 xs) r₁₅ λ f₃ r₁₆ →
    step-insert "recovery_phi" (nat 2) (get 3 xs) r₁₆ λ f₄ r₁₇ →
    step-insert "recovery_phi" (nat 3) (get 4 xs) r₁₇ λ f₅ r₁₈ →
    step-insert "recovery_phi" (nat 4) (get 5 xs) r₁₈ λ f₆ r₁₉ →
    step-write "recovery_phi_len" (get 6 xs) r₁₉ λ _ f₇ r₂₀ →
    step-write "recovery_wrap" (get 7 xs) r₂₀ λ _ f₈ r₂₁ →
    write-last "recovery_version" (nat 1) r₂₁ λ _ f₉ →
    let F₃ = frames-then f₃ (frames-then f₄ (frames-then f₅ (frames-then f₆ (frames-then f₇
          (frames-then f₈ f₉)))))
    in record
      { pendingFlag = pending
      ; session = session
      ; oldRecoveryKey = oldKey
      ; idle = idle
      ; notPending = not-true (flag pending) free
      ; sessionCell = sessionCell
      ; freshSession = not-true (equal (get 1 xs) session) sessionFresh
      ; recoveryKeyCell = keyCell
      ; freshRecoveryKey = not-true (equal (get 0 xs) oldKey) keyFresh
      ; newKeyValid = newValid
      ; installsRecoveryKey = stores-frames (frames-then f₂ F₃) keyStored (absent _)
      ; installsSession = stores-frames F₃ sessionStored (absent _)
      ; frame = frames-weaken _ (frames-then f₁ (frames-then f₂ F₃))
      }

  publish-body : ∀ ctx xs coin e {s v t} → Run (body publishRecovery ctx xs coin e) s v t →
    Publication.Evidence xs s t
  publish-body ctx xs coin e r with split (publish xs) {λ _ → return unit} r
  ... | _ , t₁ , published , returned = finish returned (Publication.Evidence xs _) (publish-run xs published)

cancel-evidence : ∀ ctx xs coin e {s v t es} → body cancelRecovery ctx xs coin e s ≡ accepted v t es →
  Cancellation s t
cancel-evidence ctx xs coin e ok = cancel-body (run _ ok)

publish-evidence : ∀ ctx xs coin e {s v t es} → body publishRecovery ctx xs coin e s ≡ accepted v t es →
  Publication.Evidence xs s t
publish-evidence ctx xs coin e ok = publish-body ctx xs coin e (run _ ok)

publish-refused-while-pending : ∀ ctx xs coin e {s p} → Stores s "pending_recovery" p → flag p ≡ true →
  ∃ λ error → body publishRecovery ctx xs coin e s ≡ rejected error
publish-refused-while-pending ctx xs coin e {s} {p} cell flagged with body publishRecovery ctx xs coin e s in ran
... | rejected error = error , refl
... | accepted v t es = ⊥-elim (true≢false
  (trans (sym flagged) (trans (cong flag (stores-unique cell (Publication.Evidence.idle evidence)))
    (Publication.Evidence.notPending evidence))))
  where evidence = publish-evidence ctx xs coin e ran

------------------------------------------------------------------------
-- Pending-record effect of every entrypoint

private
  authorised-same : ∀ {c ctx a h before e after′} → Device.Authorisation c ctx a h before e after′ →
    SamePending before after′
  authorised-same authority = samePending λ k pend →
    Device.Authorisation.unchanged authority k
      (pending-away pend "devices" _) (pending-away pend "auth_nonce" _) (pending-away pend "round" _)

  device-same : ∀ c op ctx xs {s v t} → T (separate pendingCells (Device.bodyWrites op)) →
    Run (deviceCall c op ctx xs) s v t → SamePending s t
  device-same c op ctx xs ok r =
    same-trans (authorised-same (Device.DeviceCall.authorised call)) (samePending λ k pend →
      DeviceProperties.body-frame k op ctx _ _ _ (away-all pend ok) (Device.DeviceCall.bodyRun call))
    where call = DeviceProperties.device-call-evidence c op ctx xs r

  cleared-after : ∀ {s s′ s″ t} → SamePending s s′ → Cancellation s′ s″ → SamePending s″ t → Cleared s t
  cleared-after before cancelled tail = record
    { pendingFlag = Cancellation.pendingFlag cancelled
    ; wasPending = same-stores-back before (here refl) (Cancellation.pending cancelled)
    ; isPending = Cancellation.isPending cancelled
    ; clearsFlag = same-stores tail (here refl) (Cancellation.clearsFlag cancelled)
    }

  device-cleared : ∀ c ctx xs {s v t} → Run (deviceCall c cancelRecovery ctx xs) s v t → Cleared s t
  device-cleared c ctx xs r =
    cleared-after (authorised-same (Device.DeviceCall.authorised call))
      (cancel-body (Device.DeviceCall.bodyRun call)) same-refl
    where call = DeviceProperties.device-call-evidence c cancelRecovery ctx xs r

  activation-same : ∀ c ctx a salt {s v t} → Run (activate c ctx a salt) s v t → SamePending s t
  activation-same c ctx a salt r = samePending λ k pend →
    Device.Activation.unchanged (DeviceProperties.activation-evidence c ctx a salt r) k
      (pending-away pend "devices" _) (pending-away pend "device_count" _) (pending-away pend "booted" _)
      (pending-away pend "boot" _) (pending-away pend "round" _)

  -- The tail after a grant-authorised body: grantCall's appendChange, then
  -- return (frames from FullAccountGrantSecurityProof).
  plain-tail : ∀ {x s v t} → Run (return tt >> return x) s v t → SamePending s t
  plain-tail {x} r = samePending λ k _ → GrantProof.unshielded-tail x r

  change-tail : ∀ b e {x s v t} → Run ((if b then inboxAppend e else return tt) >> return x) s v t →
    SamePending s t
  change-tail b e {x} r = samePending λ k pend →
    GrantProof.change-tail b e x (pending-away pend "inbox" _) (pending-away pend "inbox_count" _) r

  -- settle writes the grant record, then bumps round.
  settled-same : ∀ c ga identifier g h spent {s x t} → Run (settle c ga identifier g h spent) s x t →
    SamePending s t
  settled-same c ga identifier g h spent {s} r =
    frames-pending _ (frames-then (frames-insert "grants" _ s)
      (bump-frames "round" 64 (GrantSecurity.Settlement.roundAdvanced
        (proj₂ (GrantProof.settle-run c ga identifier g h spent r)))))

  body-same : ∀ op ctx xs coin e {s v t} → T (separate pendingCells (Device.bodyWrites op)) →
    Run (body op ctx xs coin e) s v t → SamePending s t
  body-same op ctx xs coin e ok r = samePending λ k pend →
    DeviceProperties.body-frame k op ctx xs coin e (away-all pend ok) r

  grant-change : Operation → GrantAuth → Value → M ⊤
  grant-change withdrawShielded ga result =
    if flag (at 0 result) then inboxAppend (changeEntry ga) else return tt
  grant-change withdrawToContract ga result =
    if flag (at 0 (at 1 result)) then inboxAppend (changeEntry ga) else return tt
  grant-change _ ga result = return tt

  grant-program : Curve → Operation → Context → GrantAuth → List Value → M Value
  grant-program c op ctx ga xs = do
    coin ← (if shielded op then held ctx (get 1 xs) else return none)
    (identifier , g) ← authenticateGrant c ctx ga
    spent ← scopeCheck op ctx ga xs coin g
    GrantProof.coinCheck op ga coin
    h ← challenge c true (operationName op) ctx (authorisation ga)
      (b32 identifier ∷ u64 (grantIssuedAt g) ∷ grantChallengeArgs op xs coin ga) (number (grantNonce g))
    settle c ga identifier g h spent
    result ← body op ctx xs coin none
    grant-change op ga result
    return result

  grant-program-equal : ∀ c op ctx ga xs → grantCall c op ctx ga xs ≡ grant-program c op ctx ga xs
  grant-program-equal c withdrawUnshielded ctx ga xs = refl
  grant-program-equal c withdrawShielded ctx ga xs = refl
  grant-program-equal c withdrawToContract ctx ga xs = refl
  grant-program-equal c appendInbox ctx ga xs = refl
  grant-program-equal c rotateEncKey ctx ga xs = refl
  grant-program-equal c addDevice ctx ga xs = refl
  grant-program-equal c removeDevice ctx ga xs = refl
  grant-program-equal c issueGrant ctx ga xs = refl
  grant-program-equal c revokeGrant ctx ga xs = refl
  grant-program-equal c revokeAllGrants ctx ga xs = refl
  grant-program-equal c publishRecovery ctx ga xs = refl
  grant-program-equal c cancelRecovery ctx ga xs = refl

  record GrantReady (c : Curve) (op : Operation) (ctx : Context) (ga : GrantAuth)
    (xs : List Value) (s : State) (v : Value) (t : State) : Set where
    field
      coin : Value
      settled : State
      unchanged : SamePending s settled
      remaining : Run (body op ctx xs coin none >>= λ result → grant-change op ga result >> return result) settled v t

  abstract
    grant-prefix : ∀ c op ctx ga xs {s v t} → Run (grant-program c op ctx ga xs) s v t → GrantReady c op ctx ga xs s v t
    grant-prefix c op ctx ga xs {s} r
      with split (if shielded op then held ctx (get 1 xs) else return none) r
    ... | coin , t₁ , coinRun , r₁ with GrantProof.coin-run op ctx xs coinRun
    ... | _ , refl with split (authenticateGrant c ctx ga) r₁
    ... | (identifier , g) , t₂ , authenticated , r₂ with GrantProof.authenticate-run c ctx ga authenticated
    ... | refl , _ with split (scopeCheck op ctx ga xs coin g) r₂
    ... | spent , t₃ , scoped , r₃ with GrantProof.scope-run op ctx ga xs coin g scoped
    ... | refl , _ with split (GrantProof.coinCheck op ga coin) r₃
    ... | _ , t₄ , checked , r₄ with GrantProof.coinCheck-run op ga coin checked
    ... | refl , _ with split (challenge c true (operationName op) ctx (authorisation ga)
      (b32 identifier ∷ u64 (grantIssuedAt g) ∷ grantChallengeArgs op xs coin ga) (number (grantNonce g))) r₄
    ... | h , t₅ , challenged , r₅ with GrantProof.challenge-run c true (operationName op) ctx (authorisation ga)
      (b32 identifier ∷ u64 (grantIssuedAt g) ∷ grantChallengeArgs op xs coin ga) (number (grantNonce g)) challenged
    ... | _ , refl with split (settle c ga identifier g h spent) r₅
    ... | _ , t₆ , settled , r₆ = record
      { coin = coin
      ; settled = t₆
      ; unchanged = settled-same c ga identifier g h spent settled
      ; remaining = r₆
      }

    grant-body : ∀ op ctx ga xs coin {s v t} →
      Run (body op ctx xs coin none >>= λ result → grant-change op ga result >> return result) s v t →
      OperationEffect op s t
    grant-body op ctx ga xs coin r
      with split (body op ctx xs coin none)
        {f = λ result → grant-change op ga result >> return result} r
    ... | result , after , bodyRun , rest with op
    ... | withdrawUnshielded = same-trans (body-same withdrawUnshielded ctx xs coin none _ bodyRun) (plain-tail rest)
    ... | withdrawShielded = same-trans (body-same withdrawShielded ctx xs coin none _ bodyRun)
      (change-tail (flag (at 0 result)) (changeEntry ga) rest)
    ... | withdrawToContract = same-trans (body-same withdrawToContract ctx xs coin none _ bodyRun)
      (change-tail (flag (at 0 (at 1 result))) (changeEntry ga) rest)
    ... | appendInbox = same-trans (body-same appendInbox ctx xs coin none _ bodyRun) (plain-tail rest)
    ... | rotateEncKey = same-trans (body-same rotateEncKey ctx xs coin none _ bodyRun) (plain-tail rest)
    ... | addDevice = same-trans (body-same addDevice ctx xs coin none _ bodyRun) (plain-tail rest)
    ... | removeDevice = same-trans (body-same removeDevice ctx xs coin none _ bodyRun) (plain-tail rest)
    ... | issueGrant = same-trans (body-same issueGrant ctx xs coin none _ bodyRun) (plain-tail rest)
    ... | revokeGrant = same-trans (body-same revokeGrant ctx xs coin none _ bodyRun) (plain-tail rest)
    ... | revokeAllGrants = same-trans (body-same revokeAllGrants ctx xs coin none _ bodyRun) (plain-tail rest)
    ... | publishRecovery = same-trans (body-same publishRecovery ctx xs coin none _ bodyRun) (plain-tail rest)
    ... | cancelRecovery = cleared-after same-refl (cancel-body bodyRun) (plain-tail rest)

  operation-before : ∀ op {s s′ t} → SamePending s s′ → OperationEffect op s′ t → OperationEffect op s t
  operation-before withdrawUnshielded = same-trans
  operation-before withdrawShielded = same-trans
  operation-before withdrawToContract = same-trans
  operation-before appendInbox = same-trans
  operation-before rotateEncKey = same-trans
  operation-before addDevice = same-trans
  operation-before removeDevice = same-trans
  operation-before issueGrant = same-trans
  operation-before revokeGrant = same-trans
  operation-before revokeAllGrants = same-trans
  operation-before publishRecovery = same-trans
  operation-before cancelRecovery before cleared = record
    { pendingFlag = Cleared.pendingFlag cleared
    ; wasPending = same-stores-back before (here refl) (Cleared.wasPending cleared)
    ; isPending = Cleared.isPending cleared
    ; clearsFlag = Cleared.clearsFlag cleared
    }

  grant-call : ∀ c op ctx ga xs {s v t} → Run (grantCall c op ctx ga xs) s v t → OperationEffect op s t
  grant-call c op ctx ga xs r = operation-before op (GrantReady.unchanged ready)
    (grant-body op ctx ga xs (GrantReady.coin ready) (GrantReady.remaining ready))
    where ready = grant-prefix c op ctx ga xs (subst (λ m → Run m _ _ _) (grant-program-equal c op ctx ga xs) r)

pending-effect : ∀ e ctx xs {s v t es} → execute e ctx xs s ≡ accepted v t es → PendingEffect e ctx xs s t
pending-effect construct ctx xs refl = stored refl
pending-effect submitRecovery ctx xs ok = submit-evidence ctx xs ok
pending-effect finaliseRecovery ctx xs ok = finalise-evidence ctx ok
pending-effect (activation c) ctx xs ok = activation-same c ctx (parseActivation c xs) (get 1 xs) (run _ ok)
pending-effect (device c withdrawUnshielded) ctx xs ok = device-same c withdrawUnshielded ctx xs _ (run _ ok)
pending-effect (device c withdrawShielded) ctx xs ok = device-same c withdrawShielded ctx xs _ (run _ ok)
pending-effect (device c withdrawToContract) ctx xs ok = device-same c withdrawToContract ctx xs _ (run _ ok)
pending-effect (device c appendInbox) ctx xs ok = device-same c appendInbox ctx xs _ (run _ ok)
pending-effect (device c rotateEncKey) ctx xs ok = device-same c rotateEncKey ctx xs _ (run _ ok)
pending-effect (device c addDevice) ctx xs ok = device-same c addDevice ctx xs _ (run _ ok)
pending-effect (device c removeDevice) ctx xs ok = device-same c removeDevice ctx xs _ (run _ ok)
pending-effect (device c issueGrant) ctx xs ok = device-same c issueGrant ctx xs _ (run _ ok)
pending-effect (device c revokeGrant) ctx xs ok = device-same c revokeGrant ctx xs _ (run _ ok)
pending-effect (device c revokeAllGrants) ctx xs ok = device-same c revokeAllGrants ctx xs _ (run _ ok)
pending-effect (device c publishRecovery) ctx xs ok = device-same c publishRecovery ctx xs _ (run _ ok)
pending-effect (device c cancelRecovery) ctx xs ok = device-cleared c ctx xs (run _ ok)
pending-effect (grant c withdrawUnshielded) ctx xs ok =
  grant-call c withdrawUnshielded ctx (parseGrant c (drop 3 xs) none none) (take 3 xs) (run _ ok)
pending-effect (grant c withdrawShielded) ctx xs ok =
  grant-call c withdrawShielded ctx (parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) (run _ ok)
pending-effect (grant c withdrawToContract) ctx xs ok =
  grant-call c withdrawToContract ctx (parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) (run _ ok)
pending-effect (grant c appendInbox) ctx xs ok =
  grant-call c appendInbox ctx (parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) (run _ ok)
pending-effect (grant c rotateEncKey) ctx xs ok =
  grant-call c rotateEncKey ctx (parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) (run _ ok)
pending-effect (grant c addDevice) ctx xs ok =
  grant-call c addDevice ctx (parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) (run _ ok)
pending-effect (grant c removeDevice) ctx xs ok =
  grant-call c removeDevice ctx (parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) (run _ ok)
pending-effect (grant c issueGrant) ctx xs ok =
  grant-call c issueGrant ctx (parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) (run _ ok)
pending-effect (grant c revokeGrant) ctx xs ok =
  grant-call c revokeGrant ctx (parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) (run _ ok)
pending-effect (grant c revokeAllGrants) ctx xs ok =
  grant-call c revokeAllGrants ctx (parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) (run _ ok)
pending-effect (grant c publishRecovery) ctx xs ok =
  grant-call c publishRecovery ctx (parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) (run _ ok)
pending-effect (grant c cancelRecovery) ctx xs ok =
  grant-call c cancelRecovery ctx (parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs) (run _ ok)
pending-effect depositPublic ctx xs ok = deposit-public ctx xs (run _ ok)
pending-effect depositPrivate ctx xs ok = deposit-private ctx xs (run _ ok)

------------------------------------------------------------------------
-- Provenance of the pending record

private
  cleared-provenance : ∀ {t} → Stores t "pending_recovery" (bool false) → PendingProvenance t
  cleared-provenance cleared cell flagged =
    ⊥-elim (true≢false (sym (trans (cong flag (stores-unique cleared cell)) flagged)))

  kept-provenance : ∀ {s t} → SamePending s t → PendingProvenance s → PendingProvenance t
  kept-provenance same prov cell flagged =
    let installed = prov (same-stores-back same (here refl) cell) flagged
    in record
      { submitContext = Installed.submitContext installed
      ; submitArguments = Installed.submitArguments installed
      ; submittedFrom = Installed.submittedFrom installed
      ; installedAt = Installed.installedAt installed
      ; submission = Installed.submission installed
      ; unchanged = same-trans (Installed.unchanged installed) same
      }

  operation-provenance : ∀ op {s t} → OperationEffect op s t → PendingProvenance s → PendingProvenance t
  operation-provenance withdrawUnshielded = kept-provenance
  operation-provenance withdrawShielded = kept-provenance
  operation-provenance withdrawToContract = kept-provenance
  operation-provenance appendInbox = kept-provenance
  operation-provenance rotateEncKey = kept-provenance
  operation-provenance addDevice = kept-provenance
  operation-provenance removeDevice = kept-provenance
  operation-provenance issueGrant = kept-provenance
  operation-provenance revokeGrant = kept-provenance
  operation-provenance revokeAllGrants = kept-provenance
  operation-provenance publishRecovery = kept-provenance
  operation-provenance cancelRecovery cleared _ = cleared-provenance (Cleared.clearsFlag cleared)

empty-provenance : PendingProvenance (state [])
empty-provenance (stored ()) _

provenance-step : ∀ e ctx xs {s v t es} → execute e ctx xs s ≡ accepted v t es →
  PendingProvenance s → PendingProvenance t
provenance-step construct ctx xs {s} ok _ = cleared-provenance (pending-effect construct ctx xs {s = s} ok)
provenance-step submitRecovery ctx xs {s} {t = t} ok _ _ _ = record
  { submitContext = ctx
  ; submitArguments = xs
  ; submittedFrom = s
  ; installedAt = t
  ; submission = submit-evidence ctx xs ok
  ; unchanged = same-refl
  }
provenance-step finaliseRecovery ctx xs {s} ok _ =
  cleared-provenance (Finalisation.Evidence.clearsFlag (finalise-evidence ctx {s = s} ok))
provenance-step (activation c) ctx xs ok = kept-provenance (pending-effect (activation c) ctx xs ok)
provenance-step (device c op) ctx xs ok = operation-provenance op (pending-effect (device c op) ctx xs ok)
provenance-step (grant c op) ctx xs ok = operation-provenance op (pending-effect (grant c op) ctx xs ok)
provenance-step depositPublic ctx xs ok = kept-provenance (pending-effect depositPublic ctx xs ok)
provenance-step depositPrivate ctx xs ok = kept-provenance (pending-effect depositPrivate ctx xs ok)

finalise-enacts-submission : ∀ ctx {s v t es} → PendingProvenance s → finalise ctx s ≡ accepted v t es →
  EnactsSubmission ctx s t
finalise-enacts-submission ctx prov ok = record
  { installation = installed
  ; finalisation = evidence
  ; sameSuccessor = stores-unique (Finalisation.Evidence.successorCell evidence)
      (same-stores (Installed.unchanged installed) (there (here refl))
        (Submission.Evidence.installsEntry (Installed.submission installed)))
  ; sameRecoveryKey = stores-unique (Finalisation.Evidence.recoveryKeyCell evidence)
      (same-stores (Installed.unchanged installed) (there (there (here refl)))
        (Submission.Evidence.installsRecoveryKey (Installed.submission installed)))
  ; sameDeadline = stores-unique (Finalisation.Evidence.deadlineCell evidence)
      (same-stores (Installed.unchanged installed) (there (there (there (here refl))))
        (Submission.Evidence.installsDeadline (Installed.submission installed)))
  }
  where
  evidence = finalise-evidence ctx ok
  installed = prov (Finalisation.Evidence.pending evidence) (Finalisation.Evidence.isPending evidence)

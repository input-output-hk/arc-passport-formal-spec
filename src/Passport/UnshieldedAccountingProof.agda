{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

module Passport.UnshieldedAccountingProof (P : Primitives) where

open import Passport.UnshieldedAccounting
open Passport.UnshieldedAccounting.Semantics P
open import Passport.UnshieldedAccountingNeutral P using (Quiet; transfers-++)
import Passport.UnshieldedAccountingNeutral P as Q
open import Conformance.FullAccountBody P hiding (credit; debit)
import Conformance.FullAccountBody P as Body
open import Conformance.FullAccountCrypto P
open import Conformance.FullAccountExecution using (Run; run; then)
open import Conformance.FullAccountGrant P
open import Conformance.FullAccountLayouts
import Conformance.FullAccount as Model
import Conformance.FullAccountDeviceSecurityProof P as Device
import Conformance.FullAccountGrantSecurityProof P as Grant
import Conformance.FullAccountSignatureBindingProof P as Binding
open import Data.Bool.Base using (Bool; true; false; if_then_else_; not; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; take; drop; length)
open import Data.Bool.ListAction using (all)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
import Data.List.Membership.DecPropositional as Membership
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.Maybe.Base using (nothing; just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat.Base hiding (equal)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-comm; +-cancelˡ-≡; m∸n+n≡m; ≤ᵇ⇒≤)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
import Data.String as String
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec; does; yes; no)
open import Relation.Nullary.Decidable using (toWitnessFalse)
import Midnight.ContractDSL.Lifecycle as Generic
import Passport.Account as Account
open import Passport.AccountLifecycle P hiding (run)

open Model.AccountSemantics P using (Entrypoint; construct; activation; device; grant; depositPublic;
  depositPrivate; submitRecovery; finaliseRecovery; execute; checked; schema; deviceCall; callerEntryAfter)

record Tracks {A : Set} (a : Action) (m : M A) : Set where
  field accounted : ∀ {s x t es} → m s ≡ accepted x t es → Accounting a s es t
open Tracks public

updated-same : ∀ a {s t} → balanceMap t ≡ balanceMap s → updatedMap a t ≡ updatedMap a s
updated-same idle same = same
updated-same (credit c n) same = cong₂ (λ amount values → tuple (insertMap c (nat (amount + n)) (fields values)))
  (cong (balanceOf c) same) same
updated-same (debit c n) same = cong₂ (λ amount values → tuple (insertMap c (nat (amount ∸ n)) (fields values)))
  (cong (balanceOf c) same) same

funded-same : ∀ a {s t} → balanceMap t ≡ balanceMap s → Funded a t → Funded a s
funded-same idle same funded = refl
funded-same (credit _ _) same funded = refl
funded-same (debit c n) same funded = trans (cong (n ≤ᵇ_) (sym (cong (balanceOf c) same))) funded

quiet-tracks : ∀ {A : Set} {m : M A} → Quiet m → Tracks idle m
accounted (quiet-tracks q) execution = accounting (proj₂ (Q.inspect q execution)) (proj₁ (Q.inspect q execution)) refl

before : ∀ {A B : Set} {a m} {f : A → M B} → Quiet m → (∀ x → Tracks a (f x)) → Tracks a (m >>= f)
accounted (before {m = m} {f} q rest) {s} execution with m s in prefix
... | rejected _ = ⊥-elim (Q.rejected≢accepted execution)
accounted (before {a = a} {m = m} {f} q rest) {s} execution | accepted x t es with f x t in suffix
... | rejected _ = ⊥-elim (Q.rejected≢accepted execution)
... | accepted y u fs with execution
...   | refl = accounting
  (trans (transfers-++ es fs) (cong₂ _++_ (proj₂ (Q.inspect q prefix)) (Accounting.declared (accounted (rest x) suffix))))
  (trans (Accounting.updated (accounted (rest x) suffix)) (updated-same a (proj₁ (Q.inspect q prefix))))
  (funded-same a (proj₁ (Q.inspect q prefix)) (Accounting.funded (accounted (rest x) suffix)))

after : ∀ {A B : Set} {a} {m : M A} {f : A → M B} → Tracks a m → (∀ x → Quiet (f x)) → Tracks a (m >>= f)
accounted (after {m = m} {f} first q) {s} execution with m s in prefix
... | rejected _ = ⊥-elim (Q.rejected≢accepted execution)
accounted (after {m = m} {f} first q) {s} execution | accepted x t es with f x t in suffix
... | rejected _ = ⊥-elim (Q.rejected≢accepted execution)
... | accepted y u fs with execution
...   | refl = accounting
  (trans (transfers-++ es fs)
    (trans (cong₂ _++_ (Accounting.declared (accounted first prefix)) (proj₂ (Q.inspect (q x) suffix))) (++-identityʳ _)))
  (trans (proj₁ (Q.inspect (q x) suffix)) (Accounting.updated (accounted first prefix)))
  (Accounting.funded (accounted first prefix))

bind-associative : ∀ {A B C : Set} (m : M A) (f : A → M B) (g : B → M C) s →
  ((m >>= f) >>= g) s ≡ (m >>= λ x → f x >>= g) s
bind-associative m f g s with m s
... | rejected _ = refl
... | accepted x t es with f x t
...   | rejected _ = refl
...   | accepted y u fs with g y u
...     | rejected _ = refl
...     | accepted z v gs = cong (accepted z v) (++-assoc es fs gs)

reassociate : ∀ {A B C : Set} {a} {m : M A} {f : A → M B} {g : B → M C} →
  Tracks a ((m >>= f) >>= g) → Tracks a (m >>= λ x → f x >>= g)
accounted (reassociate {m = m} {f} {g} proof) {s} execution =
  accounted proof (trans (bind-associative m f g s) execution)

credit-run : ∀ color amount {s x t es} → Body.credit color amount s ≡ accepted x t es →
  balanceMap t ≡ updatedMap (credit color amount) s × transfers es ≡ []
credit-run color amount {s} execution with lookupMap color (fields (balanceMap s)) in found
credit-run color amount {s} refl | nothing = Device.cell-insert-same "unshielded_balances" _ (ledger s) , refl
credit-run color amount {s} execution | just old with (number old + amount) <ᵇ 2 ^ 128 in limit
credit-run color amount {s} execution | just old | true rewrite found | limit with execution
... | refl = Device.cell-insert-same "unshielded_balances" _ (ledger s) , refl
credit-run color amount {s} execution | just old | false rewrite found | limit = ⊥-elim (Q.rejected≢accepted execution)

debit-run : ∀ color amount {s x t es} → Body.debit color amount s ≡ accepted x t es →
  balanceMap t ≡ updatedMap (debit color amount) s × transfers es ≡ [] × Funded (debit color amount) s
debit-run color amount {s} execution with lookupMap color (fields (balanceMap s)) in found
debit-run color amount () | nothing
debit-run color amount {s} execution | just old with amount ≤ᵇ number old in enough
debit-run color amount {s} execution | just old | false rewrite found | enough = ⊥-elim (Q.rejected≢accepted execution)
debit-run color amount {s} execution | just old | true with (number old ∸ amount) <ᵇ 2 ^ 128 in limit
debit-run color amount {s} execution | just old | true | true rewrite found | enough | limit with execution
... | refl = Device.cell-insert-same "unshielded_balances" _ (ledger s) , refl , refl
debit-run color amount {s} execution | just old | true | false rewrite found | enough | limit =
  ⊥-elim (Q.rejected≢accepted execution)

credit-stage : ∀ color amount → Tracks (credit color amount)
  (emit (receiveUnshielded color amount) >> Body.credit color amount)
accounted (credit-stage color amount) {s} execution with Body.credit color amount s in credited
... | rejected _ = ⊥-elim (Q.rejected≢accepted execution)
... | accepted x t es with execution
...   | refl = accounting (cong (received color amount ∷_) (proj₂ (credit-run color amount {s = s} credited)))
  (proj₁ (credit-run color amount {s = s} credited)) refl

withdraw-stage : ∀ color amount recipient → Tracks (debit color amount) (withdrawPublic color amount recipient)
accounted (withdraw-stage color amount recipient) {s} execution with Body.debit color amount s in debited
... | rejected _ = ⊥-elim (Q.rejected≢accepted execution)
... | accepted x t es with execution
...   | refl = accounting
  (trans (transfers-++ es (sendUnshielded color amount (tuple (bool false ∷ recipient ∷ [])) ∷ []))
    (cong (_++ (sent color amount ∷ [])) (proj₁ (proj₂ (debit-run color amount {s = s} debited)))))
  (proj₁ (debit-run color amount {s = s} debited)) (proj₂ (proj₂ (debit-run color amount {s = s} debited)))

operation-action : Operation → List Value → Action
operation-action withdrawUnshielded xs = debit (get 0 xs) (number (get 1 xs))
operation-action _ xs = idle

body-tracks : ∀ op ctx xs coin callerEntry → Tracks (operation-action op xs) (body op ctx xs coin callerEntry)
body-tracks withdrawUnshielded ctx xs coin e = withdraw-stage (get 0 xs) (number (get 1 xs)) (get 2 xs)
body-tracks withdrawShielded ctx xs coin e = quiet-tracks (Q.body-quiet withdrawShielded ctx xs coin e refl)
body-tracks withdrawToContract ctx xs coin e = quiet-tracks (Q.body-quiet withdrawToContract ctx xs coin e refl)
body-tracks appendInbox ctx xs coin e = quiet-tracks (Q.body-quiet appendInbox ctx xs coin e refl)
body-tracks rotateEncKey ctx xs coin e = quiet-tracks (Q.body-quiet rotateEncKey ctx xs coin e refl)
body-tracks addDevice ctx xs coin e = quiet-tracks (Q.body-quiet addDevice ctx xs coin e refl)
body-tracks removeDevice ctx xs coin e = quiet-tracks (Q.body-quiet removeDevice ctx xs coin e refl)
body-tracks issueGrant ctx xs coin e = quiet-tracks (Q.body-quiet issueGrant ctx xs coin e refl)
body-tracks revokeGrant ctx xs coin e = quiet-tracks (Q.body-quiet revokeGrant ctx xs coin e refl)
body-tracks revokeAllGrants ctx xs coin e = quiet-tracks (Q.body-quiet revokeAllGrants ctx xs coin e refl)
body-tracks publishRecovery ctx xs coin e = quiet-tracks (Q.body-quiet publishRecovery ctx xs coin e refl)
body-tracks cancelRecovery ctx xs coin e = quiet-tracks (Q.body-quiet cancelRecovery ctx xs coin e refl)

caller-after-quiet : ∀ c op ctx a cached → Quiet (callerEntryAfter c op ctx a cached)
caller-after-quiet c removeDevice ctx a cached = Q.bind (Q.self-read ctx) λ addr →
  Q.bind (Q.counted "device_epoch") λ epoch →
  Q.bind (Q.bounded "use_counter" 64 (suc (counter a))) λ count → Q.pure (Device.entryAt-pure c addr a epoch count)
caller-after-quiet c withdrawUnshielded ctx a cached = Q.ret cached
caller-after-quiet c withdrawShielded ctx a cached = Q.ret cached
caller-after-quiet c withdrawToContract ctx a cached = Q.ret cached
caller-after-quiet c appendInbox ctx a cached = Q.ret cached
caller-after-quiet c rotateEncKey ctx a cached = Q.ret cached
caller-after-quiet c addDevice ctx a cached = Q.ret cached
caller-after-quiet c issueGrant ctx a cached = Q.ret cached
caller-after-quiet c revokeGrant ctx a cached = Q.ret cached
caller-after-quiet c revokeAllGrants ctx a cached = Q.ret cached
caller-after-quiet c publishRecovery ctx a cached = Q.ret cached
caller-after-quiet c cancelRecovery ctx a cached = Q.ret cached

device-action : ∀ c op xs → operation-action op (take (length (Model.AccountSemantics.operationSchema P op)) xs) ≡ action (device c op) xs
device-action c withdrawUnshielded [] = refl
device-action c withdrawUnshielded (x ∷ []) = refl
device-action c withdrawUnshielded (x ∷ y ∷ xs) = refl
device-action c withdrawShielded xs = refl
device-action c withdrawToContract xs = refl
device-action c appendInbox xs = refl
device-action c rotateEncKey xs = refl
device-action c addDevice xs = refl
device-action c removeDevice xs = refl
device-action c issueGrant xs = refl
device-action c revokeGrant xs = refl
device-action c revokeAllGrants xs = refl
device-action c publishRecovery xs = refl
device-action c cancelRecovery xs = refl

device-tracks : ∀ c op ctx xs → Tracks (action (device c op) xs) (deviceCall c op ctx xs)
device-tracks c op ctx xs = subst (λ a → Tracks a (deviceCall c op ctx xs)) (device-action c op xs)
  (before (Q.branch (shielded op) (Q.held-read ctx (get 1 args)) (Q.ret none)) λ coin →
    before (Q.pure (Device.operationAtoms-pure op args coin)) λ atoms →
    before (Q.self-read ctx) λ addr →
    before (Q.counted "auth_nonce") λ nonce →
    before (Q.pure (Binding.challengeAt-pure c false (operationName op) addr a atoms nonce)) λ h →
    before (Q.authorise-quiet c ctx a h) λ postEntry →
    before (caller-after-quiet c op ctx a postEntry) λ callerEntry → body-tracks op ctx args coin callerEntry)
  where
  n = length (Model.AccountSemantics.operationSchema P op)
  args = take n xs
  a = Model.AccountSemantics.parseAuth P c (drop n xs)

append-change : Operation → GrantAuth → Value → M _
append-change withdrawShielded ga result = if flag (at 0 result) then inboxAppend (changeEntry ga) else return tt
append-change withdrawToContract ga result = if flag (at 0 (at 1 result)) then inboxAppend (changeEntry ga) else return tt
append-change _ ga result = return tt

append-change-quiet : ∀ op ga result → Quiet (append-change op ga result)
append-change-quiet withdrawShielded ga result = Q.branch (flag (at 0 result)) (Q.inbox (changeEntry ga)) (Q.ret tt)
append-change-quiet withdrawToContract ga result = Q.branch (flag (at 0 (at 1 result))) (Q.inbox (changeEntry ga)) (Q.ret tt)
append-change-quiet withdrawUnshielded ga result = Q.ret tt
append-change-quiet appendInbox ga result = Q.ret tt
append-change-quiet rotateEncKey ga result = Q.ret tt
append-change-quiet addDevice ga result = Q.ret tt
append-change-quiet removeDevice ga result = Q.ret tt
append-change-quiet issueGrant ga result = Q.ret tt
append-change-quiet revokeGrant ga result = Q.ret tt
append-change-quiet revokeAllGrants ga result = Q.ret tt
append-change-quiet publishRecovery ga result = Q.ret tt
append-change-quiet cancelRecovery ga result = Q.ret tt

grant-program : Curve → Operation → Context → GrantAuth → List Value → M Value
grant-program c op ctx ga xs = do
  coin ← (if shielded op then held ctx (get 1 xs) else return none)
  (id , g) ← authenticateGrant c ctx ga
  spent ← scopeCheck op ctx ga xs coin g
  (if shielded op then (do
    assert (number (at 2 coin) ≤ᵇ maxCoinValue ga) "coin above max_coin_value"
    encryption ← read "enc_key"
    assert (equal (encryptionKey ga) encryption) "stale encryption key") else return tt)
  h ← challenge c true (operationName op) ctx (authorisation ga)
    (b32 id ∷ u64 (grantIssuedAt g) ∷ grantChallengeArgs op xs coin ga) (number (grantNonce g))
  settle c ga id g h spent
  result ← body op ctx xs coin none
  append-change op ga result
  return result

grant-program-equal : ∀ c op ctx ga xs → grant-program c op ctx ga xs ≡ grantCall c op ctx ga xs
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

grant-program-tracks : ∀ c op ctx ga xs → Tracks (operation-action op xs) (grant-program c op ctx ga xs)
grant-program-tracks c op ctx ga xs = before (Q.branch (shielded op) (Q.held-read ctx (get 1 xs)) (Q.ret none)) λ coin →
  before (Q.authenticate-quiet c ctx ga) λ where
    (id , g) → before (Q.scope-quiet op ctx ga xs coin g) λ spent →
      before (Q.branch (shielded op)
        (Q.bind (Q.guard (number (at 2 coin) ≤ᵇ maxCoinValue ga) "coin above max_coin_value") λ _ →
          Q.bind (Q.observed "enc_key") λ encryption → Q.guard (equal (encryptionKey ga) encryption) "stale encryption key")
        (Q.ret tt)) λ _ →
      before (Q.challenge-quiet c true (operationName op) ctx (authorisation ga)
        (b32 id ∷ u64 (grantIssuedAt g) ∷ grantChallengeArgs op xs coin ga) (number (grantNonce g))) λ h →
      before (Q.settle-quiet c ga id g h spent) λ _ →
      after (body-tracks op ctx xs coin none) λ result → Q.bind (append-change-quiet op ga result) λ _ → Q.ret result

grant-tracks : ∀ c op ctx ga xs → Tracks (operation-action op xs) (grantCall c op ctx ga xs)
grant-tracks c op ctx ga xs = subst (Tracks (operation-action op xs)) (grant-program-equal c op ctx ga xs)
  (grant-program-tracks c op ctx ga xs)

grant-action : ∀ c op xs → operation-action op (take 3 xs) ≡ action (grant c op) xs
grant-action c withdrawUnshielded [] = refl
grant-action c withdrawUnshielded (x ∷ []) = refl
grant-action c withdrawUnshielded (x ∷ y ∷ xs) = refl
grant-action c withdrawShielded xs = refl
grant-action c withdrawToContract xs = refl
grant-action c appendInbox xs = refl
grant-action c rotateEncKey xs = refl
grant-action c addDevice xs = refl
grant-action c removeDevice xs = refl
grant-action c issueGrant xs = refl
grant-action c revokeGrant xs = refl
grant-action c revokeAllGrants xs = refl
grant-action c publishRecovery xs = refl
grant-action c cancelRecovery xs = refl

execute-grant : ∀ c op ctx xs → Tracks (action (grant c op) xs) (execute (grant c op) ctx xs)
execute-grant c withdrawUnshielded ctx xs = subst (λ a → Tracks a (execute (grant c withdrawUnshielded) ctx xs))
  (grant-action c withdrawUnshielded xs)
  (grant-tracks c withdrawUnshielded ctx (Model.AccountSemantics.parseGrant P c (drop 3 xs) none none) (take 3 xs))
execute-grant c withdrawShielded ctx xs = grant-tracks c withdrawShielded ctx _ (take 3 xs)
execute-grant c withdrawToContract ctx xs = grant-tracks c withdrawToContract ctx _ (take 3 xs)
execute-grant c appendInbox ctx xs = grant-tracks c appendInbox ctx _ (take 3 xs)
execute-grant c rotateEncKey ctx xs = grant-tracks c rotateEncKey ctx _ (take 3 xs)
execute-grant c addDevice ctx xs = grant-tracks c addDevice ctx _ (take 3 xs)
execute-grant c removeDevice ctx xs = grant-tracks c removeDevice ctx _ (take 3 xs)
execute-grant c issueGrant ctx xs = grant-tracks c issueGrant ctx _ (take 3 xs)
execute-grant c revokeGrant ctx xs = grant-tracks c revokeGrant ctx _ (take 3 xs)
execute-grant c revokeAllGrants ctx xs = grant-tracks c revokeAllGrants ctx _ (take 3 xs)
execute-grant c publishRecovery ctx xs = grant-tracks c publishRecovery ctx _ (take 3 xs)
execute-grant c cancelRecovery ctx xs = grant-tracks c cancelRecovery ctx _ (take 3 xs)

execute-tracks : ∀ e ctx xs → e ≢ construct → Tracks (action e xs) (execute e ctx xs)
execute-tracks construct ctx xs notConstructor = ⊥-elim (notConstructor refl)
execute-tracks (activation c) ctx xs _ = quiet-tracks (Q.activate-quiet c ctx _ (get 1 xs))
execute-tracks (device c op) ctx xs _ = device-tracks c op ctx xs
execute-tracks (grant c op) ctx xs _ = execute-grant c op ctx xs
execute-tracks depositPublic ctx xs _ = reassociate
  {m = emit (receiveUnshielded (get 0 xs) (number (get 1 xs)))}
  {f = λ _ → Body.credit (get 0 xs) (number (get 1 xs))}
  {g = λ _ → bump "round" 64 >> return unit}
  (after (credit-stage (get 0 xs) (number (get 1 xs))) λ _ →
    Q.bind (Q.bumped "round" 64 refl) λ _ → Q.ret unit)
execute-tracks depositPrivate ctx xs _ = quiet-tracks
  (Q.bind (Q.receive-quiet ctx (get 0 xs)) λ _ →
    Q.bind (Q.inbox (get 1 xs)) λ _ → Q.bind (Q.bumped "round" 64 refl) λ _ → Q.ret unit)
execute-tracks submitRecovery ctx xs _ = quiet-tracks (Q.submit-quiet ctx xs)
execute-tracks finaliseRecovery ctx xs _ = quiet-tracks (Q.finalise-quiet ctx)

lookup-insert-same : ∀ k v values → lookupMap k (insertMap k v values) ≡ just v
lookup-insert-same k v [] rewrite Grant.equal-refl k = refl
lookup-insert-same k v (tuple (x ∷ y ∷ []) ∷ values) with equal k x in hit
... | true rewrite Grant.equal-refl k = refl
... | false rewrite hit = lookup-insert-same k v values
lookup-insert-same k v (nat _ ∷ values) = lookup-insert-same k v values
lookup-insert-same k v (bool _ ∷ values) = lookup-insert-same k v values
lookup-insert-same k v (bytes _ ∷ values) = lookup-insert-same k v values
lookup-insert-same k v (none ∷ values) = lookup-insert-same k v values
lookup-insert-same k v (some _ ∷ values) = lookup-insert-same k v values
lookup-insert-same k v (tuple [] ∷ values) = lookup-insert-same k v values
lookup-insert-same k v (tuple (_ ∷ []) ∷ values) = lookup-insert-same k v values
lookup-insert-same k v (tuple (_ ∷ _ ∷ _ ∷ _) ∷ values) = lookup-insert-same k v values

lookup-insert-other : ∀ query k v values → equal query k ≡ false →
  lookupMap query (insertMap k v values) ≡ lookupMap query values
lookup-insert-other query k v [] different rewrite different = refl
lookup-insert-other query k v (tuple (x ∷ y ∷ []) ∷ values) different with equal k x in hit
... | true rewrite different | subst (λ key → equal query key ≡ false) (Grant.equal-sound k x hit) different = refl
... | false with equal query x
...   | true = refl
...   | false = lookup-insert-other query k v values different
lookup-insert-other query k v (nat _ ∷ values) different = lookup-insert-other query k v values different
lookup-insert-other query k v (bool _ ∷ values) different = lookup-insert-other query k v values different
lookup-insert-other query k v (bytes _ ∷ values) different = lookup-insert-other query k v values different
lookup-insert-other query k v (none ∷ values) different = lookup-insert-other query k v values different
lookup-insert-other query k v (some _ ∷ values) different = lookup-insert-other query k v values different
lookup-insert-other query k v (tuple [] ∷ values) different = lookup-insert-other query k v values different
lookup-insert-other query k v (tuple (_ ∷ []) ∷ values) different = lookup-insert-other query k v values different
lookup-insert-other query k v (tuple (_ ∷ _ ∷ _ ∷ _) ∷ values) different = lookup-insert-other query k v values different

insert-balance : ∀ k n values → balanceOf k (tuple (insertMap k (nat n) values)) ≡ n
insert-balance k n values rewrite lookup-insert-same k (nat n) values = refl

insert-balance-other : ∀ query k n values → equal query k ≡ false →
  balanceOf query (tuple (insertMap k (nat n) values)) ≡ balanceOf query (tuple values)
insert-balance-other query k n values different rewrite lookup-insert-other query k (nat n) values different = refl

balance-fields : ∀ color balances → balanceOf color (tuple (fields balances)) ≡ balanceOf color balances
balance-fields color (nat _) = refl
balance-fields color (bool _) = refl
balance-fields color (bytes _) = refl
balance-fields color (tuple _) = refl
balance-fields color none = refl
balance-fields color (some _) = refl

credited-balance : ∀ {c n s es t} → Accounting (credit c n) s es t → balance c t ≡ balance c s + n
credited-balance {c} {n} {s} accounted = trans (cong (balanceOf c) (Accounting.updated accounted))
  (insert-balance c (balance c s + n) (fields (balanceMap s)))

debited-balance : ∀ {c n s es t} → Accounting (debit c n) s es t → balance c t + n ≡ balance c s
debited-balance {c} {n} {s} accounted = trans
  (cong (_+ n) (trans (cong (balanceOf c) (Accounting.updated accounted))
    (insert-balance c (balance c s ∸ n) (fields (balanceMap s)))))
  (m∸n+n≡m (≤ᵇ⇒≤ n (balance c s) (subst Data.Bool.Base.T (sym (Accounting.funded accounted)) tt)))

unrelated-credit : ∀ {c n s es t} → Accounting (credit c n) s es t → ∀ query → equal query c ≡ false →
  lookupMap query (fields (balanceMap t)) ≡ lookupMap query (fields (balanceMap s))
unrelated-credit {c} {n} {s} accounted query different = trans
  (cong (λ values → lookupMap query (fields values)) (Accounting.updated accounted))
  (lookup-insert-other query c (nat (balance c s + n)) (fields (balanceMap s)) different)

unrelated-debit : ∀ {c n s es t} → Accounting (debit c n) s es t → ∀ query → equal query c ≡ false →
  lookupMap query (fields (balanceMap t)) ≡ lookupMap query (fields (balanceMap s))
unrelated-debit {c} {n} {s} accounted query different = trans
  (cong (λ values → lookupMap query (fields values)) (Accounting.updated accounted))
  (lookup-insert-other query c (nat (balance c s ∸ n)) (fields (balanceMap s)) different)

conserved-accounting : ∀ {a s es t} → Accounting a s es t → Conserved s (transfers es) t
conserved-accounting {a} {s} {es} {t} accounted =
  subst (λ flow → Conserved s flow t) (sym (Accounting.declared accounted)) (by-action a accounted)
  where
  by-action : ∀ a → Accounting a s es t → Conserved s (actionTransfers a) t
  by-action idle p color = cong (_+ 0) (cong (balanceOf color) (Accounting.updated p))
  by-action (credit c n) p color with equal color c in same
  ... | true with Grant.equal-sound color c same
  ...   | refl = trans (+-identityʳ (balance c t)) (trans (credited-balance p)
      (cong (balance c s +_) (sym (+-identityʳ n))))
  by-action (credit c n) p color | false = cong (_+ 0) (trans (cong (balanceOf color) (Accounting.updated p))
      (trans (insert-balance-other color c (balance c s + n) (fields (balanceMap s)) same)
        (balance-fields color (balanceMap s))))
  by-action (debit c n) p color with equal color c in same
  ... | true with Grant.equal-sound color c same
  ...   | refl = trans (cong (balance c t +_) (+-identityʳ n))
      (trans (debited-balance p) (sym (+-identityʳ (balance c s))))
  by-action (debit c n) p color | false = cong (_+ 0) (trans (cong (balanceOf color) (Accounting.updated p))
      (trans (insert-balance-other color c (balance c s ∸ n) (fields (balanceMap s)) same)
        (balance-fields color (balanceMap s))))

then-branch : ∀ b {A : Set} {err x y t es} →
  (if b then x else rejected err) ≡ accepted {A} y t es → x ≡ accepted y t es
then-branch true execution = execution
then-branch false ()

else-branch : ∀ b {A : Set} {err x y t es} →
  (if b then rejected err else x) ≡ accepted {A} y t es → x ≡ accepted y t es
else-branch false execution = execution
else-branch true ()

checked-execute : ∀ e ctx xs s {x t es} → e ≢ construct →
  checked e ctx xs s ≡ accepted x t es → execute e ctx xs s ≡ accepted x t es
checked-execute construct ctx xs s impossible _ = ⊥-elim (impossible refl)
checked-execute (activation c) ctx xs s _ execution = then-branch (Model.validState s)
  (then-branch (Model.validContext ctx) (then-branch (Model.validArguments (schema (activation c)) xs) execution))
checked-execute (device c op) ctx xs s _ execution = then-branch (Model.validState s)
  (else-branch (Model.AccountSemantics.needsCoin P (device c op) ∧ not (Model.valid Model.qualifiedCoinT (heldCoin ctx)))
    (then-branch (Model.validContext ctx) (then-branch (Model.validArguments (schema (device c op)) xs) execution)))
checked-execute (grant c op) ctx xs s _ execution = then-branch (Model.validState s)
  (else-branch (Model.AccountSemantics.needsCoin P (grant c op) ∧ not (Model.valid Model.qualifiedCoinT (heldCoin ctx)))
    (then-branch (Model.validContext ctx) (then-branch (Model.validArguments (schema (grant c op)) xs) execution)))
checked-execute depositPublic ctx xs s _ execution = then-branch (Model.validState s)
  (then-branch (Model.validContext ctx) (then-branch (Model.validArguments (schema depositPublic) xs) execution))
checked-execute depositPrivate ctx xs s _ execution = then-branch (Model.validState s)
  (then-branch (Model.validContext ctx) (then-branch (Model.validArguments (schema depositPrivate) xs) execution))
checked-execute submitRecovery ctx xs s _ execution = then-branch (Model.validState s)
  (then-branch (Model.validContext ctx) (then-branch (Model.validArguments (schema submitRecovery) xs) execution))
checked-execute finaliseRecovery ctx xs s _ execution = then-branch (Model.validState s)
  (then-branch (Model.validContext ctx) (then-branch (Model.validArguments (schema finaliseRecovery) xs) execution))

checked-accounting : ∀ e ctx xs s {x t es} → e ≢ construct →
  checked e ctx xs s ≡ accepted x t es → Accounting (action e xs) s es t
checked-accounting e ctx xs s notConstructor execution =
  accounted (execute-tracks e ctx xs notConstructor) (checked-execute e ctx xs s notConstructor execution)

isConstructor : Entrypoint → Bool
isConstructor construct = true
isConstructor _ = false

∧-true : ∀ a {b} → a ∧ b ≡ true → a ≡ true × b ≡ true
∧-true true same = refl , same
∧-true false ()

lookup-all : ∀ (p : Entrypoint → Bool) n entries {e} → all (λ entry → p (proj₂ entry)) entries ≡ true →
  Model.AccountSemantics.lookupEntrypoint P n entries ≡ just e → p e ≡ true
lookup-all p n [] _ ()
lookup-all p n ((k , e′) ∷ entries) {e} holds found = choose (stringEqual n k) found
  where
  choose : ∀ b → (if b then just e′ else Model.AccountSemantics.lookupEntrypoint P n entries) ≡ just e → p e ≡ true
  choose true same = subst (λ x → p x ≡ true) (just-injective same) (proj₁ (∧-true (p e′) holds))
  choose false rest = lookup-all p n entries (proj₂ (∧-true (p e′) holds)) rest

resolved-constructor : ∀ n → Model.AccountSemantics.lookupEntrypoint P n (Model.AccountSemantics.entrypoints P) ≡ just construct →
  n ≡ "constructor"
resolved-constructor n found = choose (n String.≟ "constructor") found
  where
  runtime-entries : all (λ entry → not (isConstructor (proj₂ entry))) (Model.AccountSemantics.runtimeEntrypoints P) ≡ true
  runtime-entries = refl
  false≢true : false ≢ true
  false≢true ()
  choose : (d : Dec (n ≡ "constructor")) →
    (if does d then just construct else Model.AccountSemantics.lookupEntrypoint P n (Model.AccountSemantics.runtimeEntrypoints P))
      ≡ just construct → n ≡ "constructor"
  choose (yes same) _ = same
  choose (no _) rest = ⊥-elim (false≢true
    (lookup-all (λ e → not (isConstructor e)) n (Model.AccountSemantics.runtimeEntrypoints P) runtime-entries rest))

constructor-not-runtime : "constructor" ∉ Model.runtimeNames P
constructor-not-runtime = toWitnessFalse {a? = Membership._∈?_ String._≟_ "constructor" (Model.runtimeNames P)} _

runtime-not-constructor : ∀ (call : RuntimeCall) {e} →
  Model.AccountSemantics.lookupEntrypoint P (name (RuntimeCall.request call)) (Model.AccountSemantics.entrypoints P) ≡ just e →
  e ≢ construct
runtime-not-constructor call found refl = constructor-not-runtime
  (subst (_∈ Model.runtimeNames P) (resolved-constructor (name (RuntimeCall.request call)) found) (RuntimeCall.runtime call))

dispatch-accounting : ∀ ctx (call : RuntimeCall) {s x t es} →
  Model.dispatch P ctx (RuntimeCall.request call) s ≡ accepted x t es →
  Accounting (dispatchedAction (RuntimeCall.request call)) s es t
dispatch-accounting ctx call {s} execution
  with Model.AccountSemantics.lookupEntrypoint P (name (RuntimeCall.request call)) (Model.AccountSemantics.entrypoints P) in resolved
dispatch-accounting ctx call () | nothing
dispatch-accounting ctx call {s} execution | just e =
  checked-accounting e ctx (arguments (RuntimeCall.request call)) s (runtime-not-constructor call resolved) execution

transaction-committed : ∀ s result {x es t} →
  Account.transaction s result ≡ (Account.committed x es , t) → result ≡ accepted x t es
transaction-committed s (rejected _) ()
transaction-committed s (accepted _ _ _) refl = refl

refused-preserves : ∀ ctx call s {error t} →
  Account.Transition P ctx call s (Account.reverted error) t → t ≡ s
refused-preserves ctx call s (Account.transition execution) with Model.dispatch P ctx call s
refused-preserves ctx call s (Account.transition refl) | rejected _ = refl
refused-preserves ctx call s (Account.transition ()) | accepted _ _ _

transition-conserved : ∀ ctx (call : RuntimeCall) {s observation t} →
  Account.Transition P ctx (RuntimeCall.request call) s observation t →
  Conserved s (Histories.observationTransfers zero32 observation) t
transition-conserved ctx call {s} {Account.committed x es} (Account.transition execution) =
  conserved-accounting (dispatch-accounting ctx call (transaction-committed s _ execution))
transition-conserved ctx call {s} {Account.reverted error} tr color =
  cong (λ t → balance color t + 0) (refused-preserves ctx (RuntimeCall.request call) s tr)

total-received-++ : ∀ c xs ys → receivedTotal c (xs ++ ys) ≡ receivedTotal c xs + receivedTotal c ys
total-received-++ c [] ys = refl
total-received-++ c (received color amount ∷ xs) ys =
  trans (cong (amountFor c color amount +_) (total-received-++ c xs ys))
    (sym (+-assoc (amountFor c color amount) (receivedTotal c xs) (receivedTotal c ys)))
total-received-++ c (sent color amount ∷ xs) ys = total-received-++ c xs ys

total-sent-++ : ∀ c xs ys → sentTotal c (xs ++ ys) ≡ sentTotal c xs + sentTotal c ys
total-sent-++ c [] ys = refl
total-sent-++ c (received color amount ∷ xs) ys = total-sent-++ c xs ys
total-sent-++ c (sent color amount ∷ xs) ys =
  trans (cong (amountFor c color amount +_) (total-sent-++ c xs ys))
    (sym (+-assoc (amountFor c color amount) (sentTotal c xs) (sentTotal c ys)))

swap : ∀ a b c → a + (b + c) ≡ (a + c) + b
swap a b c = trans (cong (a +_) (+-comm b c)) (sym (+-assoc a c b))

compose-conserved : ∀ {s t u} xs ys → Conserved s xs t → Conserved t ys u → Conserved s (xs ++ ys) u
compose-conserved {s} {t} {u} xs ys first second c =
  trans (cong (balance c u +_) (total-sent-++ c xs ys))
  (trans (swap (balance c u) (sentTotal c xs) (sentTotal c ys))
  (trans (cong (_+ sentTotal c xs) (second c))
  (trans (trans (+-assoc (balance c t) (receivedTotal c ys) (sentTotal c xs))
    (swap (balance c t) (receivedTotal c ys) (sentTotal c xs)))
  (trans (cong (λ n → n + receivedTotal c ys) (first c))
  (trans (+-assoc (balance c s) (receivedTotal c xs) (receivedTotal c ys))
    (cong (balance c s +_) (sym (total-received-++ c xs ys))))))))

deployment-accounting : ∀ ctx d {x s es} → Account.deploy P ctx d ≡ accepted x s es →
  balanceMap s ≡ tuple [] × transfers es ≡ []
deployment-accounting ctx d execution
  with Model.validArguments (schema construct)
    (Account.initialDeviceBoot d ∷ Account.encryptionKey d ∷ Account.initialRecoveryKey d ∷
      Account.initialRecoveryWrap d ∷ nat (Account.vetoWindowSeconds d) ∷ [])
deployment-accounting ctx d () | false
deployment-accounting ctx d execution | true with Model.validContext ctx
deployment-accounting ctx d () | true | false
deployment-accounting ctx d refl | true | true = refl , refl

deployment-empty : ∀ ctx d {x s es} → Account.deploy P ctx d ≡ accepted x s es → balanceMap s ≡ tuple []
deployment-empty ctx d execution = proj₁ (deployment-accounting ctx d execution)

module History (address : Value) where
  open Histories address

  trace-conserved : ∀ {s t} (trace : Runs.Trace s t) → Conserved s (traceTransfers trace) t
  trace-conserved ε c = refl
  trace-conserved {s} {t} (_◅_ {j = middle} step rest) =
    compose-conserved {s = s} {t = middle} {u = t}
      (observationTransfers (Runs.Step.outcome step)) (traceTransfers rest)
      (transition-conserved (executionContext address (Runs.Step.environment step)) (Runs.Step.call step)
        {s = s} {observation = Runs.Step.outcome step} {t = middle} (Runs.Step.executed step))
      (trace-conserved {s = middle} {t = t} rest)

  history-accounted : ∀ {s} (h : Runs.History s) → HistoryAccounted h
  history-accounted h c with Runs.History.deploymentOutcome h | Runs.History.initialized h
  ... | Account.reverted _ | ()
  ... | Account.committed x es | deployed rewrite proj₂ (deployment-accounting
      (executionContext address (Runs.History.deploymentEnvironment h)) (Runs.History.deployment h) deployed) =
    trans (trace-conserved (Runs.History.execution h) c)
      (cong (_+ receivedTotal c (traceTransfers (Runs.History.execution h)))
        (cong (balanceOf c) (deployment-empty
          (executionContext address (Runs.History.deploymentEnvironment h)) (Runs.History.deployment h) deployed)))

valid-natural-bound : ∀ bits value → Model.valid (Model.natural (2 ^ bits)) value ≡ true →
  (number value <ᵇ 2 ^ bits) ≡ true
valid-natural-bound bits (nat n) bound = bound
valid-natural-bound bits (bool _) ()
valid-natural-bound bits (bytes _) ()
valid-natural-bound bits (tuple _) ()
valid-natural-bound bits none ()
valid-natural-bound bits (some _) ()

deposit-amount-bound : ∀ xs → Model.validArguments (schema depositPublic) xs ≡ true →
  (number (get 1 xs) <ᵇ 2 ^ 128) ≡ true
deposit-amount-bound [] ()
deposit-amount-bound (c ∷ []) valid = impossible (proj₂ (∧-true (Model.valid Model.b32T c) valid))
  where
  impossible : false ≡ true → (number (get 1 (c ∷ [])) <ᵇ 2 ^ 128) ≡ true
  impossible ()
deposit-amount-bound (c ∷ a ∷ xs) valid = valid-natural-bound 128 a
  (proj₁ (∧-true (Model.valid Model.u128T a) (proj₂ (∧-true (Model.valid Model.b32T c) valid))))

checked-arguments : ∀ e ctx xs s {x t es} → checked e ctx xs s ≡ accepted x t es →
  Model.validArguments (schema e) xs ≡ true
checked-arguments e ctx xs s execution with Model.validArguments (schema e) xs
checked-arguments e ctx xs s () | false
checked-arguments e ctx xs s execution | true = refl

credit-sum-bound : ∀ color amount → (amount <ᵇ 2 ^ 128) ≡ true → ∀ {s x t es} →
  Body.credit color amount s ≡ accepted x t es → (balance color s + amount <ᵇ 2 ^ 128) ≡ true
credit-sum-bound color amount bound {s} execution with lookupMap color (fields (balanceMap s)) in found
credit-sum-bound color amount bound execution | nothing = bound
credit-sum-bound color amount bound execution | just old with (number old + amount) <ᵇ 2 ^ 128 in bounded
credit-sum-bound color amount bound execution | just old | true = refl
credit-sum-bound color amount bound {s} execution | just old | false rewrite found | bounded =
  ⊥-elim (Q.rejected≢accepted execution)

deposit-sum-bound : ∀ ctx xs {s x t es} → (number (get 1 xs) <ᵇ 2 ^ 128) ≡ true →
  execute depositPublic ctx xs s ≡ accepted x t es →
  (balance (get 0 xs) s + number (get 1 xs) <ᵇ 2 ^ 128) ≡ true
deposit-sum-bound ctx xs {s} {x} {t} {es} bound execution
  with then (emit (receiveUnshielded (get 0 xs) (number (get 1 xs))))
    {f = λ _ → Body.credit (get 0 xs) (number (get 1 xs)) >> (bump "round" 64 >> return unit)}
    {s = s} {y = x} {u = t} (run es execution)
... | _ , middle , emitted , rest with Device.emit-run _ emitted
...   | refl with then (Body.credit (get 0 xs) (number (get 1 xs)))
    {f = λ _ → bump "round" 64 >> return unit} {s = s} {y = x} {u = t} rest
...     | _ , middle′ , credited , tail =
  credit-sum-bound (get 0 xs) (number (get 1 xs)) bound {s = s} (Run.execution credited)

deposit-bounded : ∀ ctx xs s {x t es} → checked depositPublic ctx xs s ≡ accepted x t es →
  (balance (get 0 xs) t <ᵇ 2 ^ 128) ≡ true
deposit-bounded ctx xs s execution = subst (λ n → (n <ᵇ 2 ^ 128) ≡ true)
  (sym (credited-balance (checked-accounting depositPublic ctx xs s (λ ()) execution)))
  (deposit-sum-bound ctx xs {s = s}
    (deposit-amount-bound xs (checked-arguments depositPublic ctx xs s execution))
    (checked-execute depositPublic ctx xs s (λ ()) execution))

accepted-deposit : ∀ ctx xs s {x t es} → checked depositPublic ctx xs s ≡ accepted x t es →
  balance (get 0 xs) t ≡ balance (get 0 xs) s + number (get 1 xs) ×
  transfers es ≡ received (get 0 xs) (number (get 1 xs)) ∷ [] ×
  (balance (get 0 xs) t <ᵇ 2 ^ 128) ≡ true
accepted-deposit ctx xs s execution =
  credited-balance (checked-accounting depositPublic ctx xs s (λ ()) execution) ,
  Accounting.declared (checked-accounting depositPublic ctx xs s (λ ()) execution) ,
  deposit-bounded ctx xs s execution

accepted-device-withdrawal : ∀ c ctx xs s {x t es} →
  checked (device c withdrawUnshielded) ctx xs s ≡ accepted x t es →
  balance (get 0 xs) t + number (get 1 xs) ≡ balance (get 0 xs) s ×
  transfers es ≡ sent (get 0 xs) (number (get 1 xs)) ∷ [] ×
  (number (get 1 xs) ≤ᵇ balance (get 0 xs) s) ≡ true
accepted-device-withdrawal c ctx xs s execution =
  debited-balance (checked-accounting (device c withdrawUnshielded) ctx xs s (λ ()) execution) ,
  Accounting.declared (checked-accounting (device c withdrawUnshielded) ctx xs s (λ ()) execution) ,
  Accounting.funded (checked-accounting (device c withdrawUnshielded) ctx xs s (λ ()) execution)

accepted-grant-withdrawal : ∀ c ctx xs s {x t es} →
  checked (grant c withdrawUnshielded) ctx xs s ≡ accepted x t es →
  balance (get 0 xs) t + number (get 1 xs) ≡ balance (get 0 xs) s ×
  transfers es ≡ sent (get 0 xs) (number (get 1 xs)) ∷ [] ×
  (number (get 1 xs) ≤ᵇ balance (get 0 xs) s) ≡ true
accepted-grant-withdrawal c ctx xs s execution =
  debited-balance (checked-accounting (grant c withdrawUnshielded) ctx xs s (λ ()) execution) ,
  Accounting.declared (checked-accounting (grant c withdrawUnshielded) ctx xs s (λ ()) execution) ,
  Accounting.funded (checked-accounting (grant c withdrawUnshielded) ctx xs s (λ ()) execution)

other-runtime-unchanged : ∀ ctx (call : RuntimeCall) {s x t es} →
  dispatchedAction (RuntimeCall.request call) ≡ idle →
  Model.dispatch P ctx (RuntimeCall.request call) s ≡ accepted x t es →
  balanceMap t ≡ balanceMap s × transfers es ≡ []
other-runtime-unchanged ctx call isIdle execution =
  Accounting.updated idleEvidence , Accounting.declared idleEvidence
  where
  idleEvidence = subst (λ a → Accounting a _ _ _) isIdle (dispatch-accounting ctx call execution)

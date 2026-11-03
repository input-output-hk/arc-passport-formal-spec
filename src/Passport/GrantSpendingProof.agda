{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

module Passport.GrantSpendingProof (P : Primitives) where


import Conformance.FullAccount as Model
open Model.AccountSemantics P using (Entrypoint; construct; activation; device; grant;
  depositPublic; depositPrivate; submitRecovery; finaliseRecovery)
open import Conformance.FullAccountDeviceSecurity P using (DeviceCall; Authorisation; bodyWrites; deviceArguments; deviceCoin)
open import Conformance.FullAccountBody P
open import Conformance.FullAccountCrypto P
open import Conformance.FullAccountExecution using (Run; run; then)
open import Conformance.FullAccountGrant P
open import Conformance.FullAccountGrantSecurity P
open import Conformance.FullAccountLayouts
import Conformance.FullAccountDeviceSecurityProof P as Device
import Conformance.FullAccountGrantSecurityProof P as Grant
import Conformance.FullAccountSignatureBindingProof P as Binding
open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; _++_; length)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat.Base hiding (equal)
open import Data.Nat.Properties using (+-comm)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Passport.GrantEffects P
open import Passport.GrantEffectsProof P using (issue-result)
import Passport.GrantEffectsProof P as Effects
open import Passport.GrantSpending P
import Midnight.ContractDSL.SymbolicSigning as Signing
import Passport.Account as Account
open import Passport.AccountLifecycle P using (Environment; RuntimeCall; executionContext)
import Passport.AccountSecurity as AccountSecurity
import Passport.AccountSecurityProof as AccountSecurityProof
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.PropositionalEquality


private
  lookup-insert : ∀ id g entries → lookupMap id (insertMap id g entries) ≡ just g
  lookup-insert id g [] rewrite Grant.equal-refl id = refl
  lookup-insert id g (tuple (key ∷ value ∷ []) ∷ rest) with equal id key in same
  ... | true rewrite Grant.equal-refl id = refl
  ... | false rewrite same = lookup-insert id g rest
  lookup-insert id g (nat _ ∷ rest) = lookup-insert id g rest
  lookup-insert id g (bool _ ∷ rest) = lookup-insert id g rest
  lookup-insert id g (bytes _ ∷ rest) = lookup-insert id g rest
  lookup-insert id g (none ∷ rest) = lookup-insert id g rest
  lookup-insert id g (some _ ∷ rest) = lookup-insert id g rest
  lookup-insert id g (tuple [] ∷ rest) = lookup-insert id g rest
  lookup-insert id g (tuple (_ ∷ []) ∷ rest) = lookup-insert id g rest
  lookup-insert id g (tuple (_ ∷ _ ∷ _ ∷ _) ∷ rest) = lookup-insert id g rest

private
  issued-episode : ∀ xs {s t} → IssueResult xs s t → Episode
  issued-episode xs r = episode (issuanceOf (IssueArguments.id xs) (issuedRecord r))
    (IssueArguments.salt xs) (number (IssueArguments.cap xs)) []

  issue-opens : ∀ xs {s t} (r : IssueResult xs s t) → Opens (issued-episode xs r) (issuedRecord r)
  issue-opens xs r = record
    { identityKept = refl ; scopeCapKept = refl ; nonceKept = refl
    ; spentOpening = run [] (Binding.pure-runs (Device.spentCommit-pure (IssueArguments.salt xs) 0)
        (Run.execution (IssueResult.zeroOpening r)) (state [])) }

  insert-corresponds : ∀ ep g {eps entries} → Opens ep g → Corresponds eps entries →
    Corresponds (insertEpisode ep eps) (insertMap (episodeKey ep) g entries)
  insert-corresponds ep g opens empty = mapEntry opens empty
  insert-corresponds ep g opens (mapEntry {ep = oldEp} old rest) with equal (episodeKey ep) (episodeKey oldEp)
  ... | true = mapEntry opens rest
  ... | false = mapEntry old (insert-corresponds ep g opens rest)

  insert-bounded : ∀ ep {eps} → WithinCap ep → All.All WithinCap eps →
    All.All WithinCap (insertEpisode ep eps)
  insert-bounded ep bounded All.[] = bounded All.∷ All.[]
  insert-bounded ep {oldEp ∷ _} bounded (oldBound All.∷ rest) with equal (episodeKey ep) (episodeKey oldEp)
  ... | true = bounded All.∷ rest
  ... | false = oldBound All.∷ insert-bounded ep bounded rest

  archive-bounded : ∀ id {eps archived} → All.All WithinCap eps → All.All WithinCap archived →
    All.All WithinCap (remember (findEpisode id eps) archived)
  archive-bounded id All.[] archived = archived
  archive-bounded id {ep ∷ _} (bounded All.∷ rest) archived with equal id (episodeKey ep)
  ... | true = bounded All.∷ archived
  ... | false = archive-bounded id rest archived

  revoked-opens : ∀ ep g → grantActive g ≡ bool true → Opens ep g → Opens ep (revokedRecord g)
  revoked-opens ep (tuple (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ suffix)) active O = record
    { identityKept = Opens.identityKept O ; scopeCapKept = Opens.scopeCapKept O
    ; nonceKept = Opens.nonceKept O ; spentOpening = Opens.spentOpening O }
  revoked-opens ep (nat _) ()
  revoked-opens ep (bool _) ()
  revoked-opens ep (bytes _) ()
  revoked-opens ep none ()
  revoked-opens ep (some _) ()
  revoked-opens ep (tuple []) ()
  revoked-opens ep (tuple (_ ∷ [])) ()
  revoked-opens ep (tuple (_ ∷ _ ∷ [])) ()
  revoked-opens ep (tuple (_ ∷ _ ∷ _ ∷ [])) ()
  revoked-opens ep (tuple (_ ∷ _ ∷ _ ∷ _ ∷ [])) ()
  revoked-opens ep (tuple (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [])) ()
  revoked-opens ep (tuple (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [])) ()
  revoked-opens ep (tuple (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [])) ()

  spend-opens : ∀ {c op ctx ga xs s} (E : GrantCallEvidence c op ctx ga xs s) ep →
    SpentOpeningsAgree (salt ga) (spentPrev ga) (Episode.saltValue ep) (total ep) →
    Opens ep (GrantCallEvidence.grantRecord E) →
    let updated = settledGrant (GrantCallEvidence.grantRecord E)
          (suc (number (grantNonce (GrantCallEvidence.grantRecord E))))
          (Settlement.commitment (GrantCallEvidence.settlement E))
        charged = record ep { amounts = amountOf op xs ∷ Episode.amounts ep }
    in Opens charged updated × WithinCap charged
  spend-opens {op = op} {ga = ga} {xs} {s} E ep agreement O = record
    { identityKept = trans
        (cong₂ (λ epoch rest → issuance (episodeKey ep) epoch (proj₁ rest) (proj₂ rest))
          (SettledRecord.epochKept F)
          (cong₂ _,_ (SettledRecord.generationKept F) (SettledRecord.issuedKept F)))
        (Opens.identityKept O)
    ; scopeCapKept = trans (cong (number ∘ scopeCap) (SettledRecord.scopeKept F)) (Opens.scopeCapKept O)
    ; nonceKept = trans (SettledRecord.nonceSet F) (cong (nat ∘ suc ∘ number) (Opens.nonceKept O))
    ; spentOpening = subst (λ v → Run (spentCommit (Episode.saltValue ep) (total charged)) (state []) v (state []))
        (sym (SettledRecord.commitmentSet F))
        (run [] (Binding.pure-runs (Device.spentCommit-pure (Episode.saltValue ep) (total charged))
          (Run.execution (subst₂ (λ salt spent → Run (spentCommit salt spent) s (Settlement.commitment S) s)
            (proj₁ facts) (trans (proj₁ (proj₂ (proj₂ facts))) (+-comm (total ep) (amountOf op xs)))
            (Settlement.spentCommitted S))) (state []))) } ,
    subst₂ _≤_ (+-comm (total ep) (amountOf op xs)) (Opens.scopeCapKept O) (proj₂ (proj₂ (proj₂ facts)))
    where
    open import Function.Base using (_∘_)
    g = GrantCallEvidence.grantRecord E
    S = GrantCallEvidence.settlement E
    F = Grant.settled-record g (suc (number (grantNonce g))) (Settlement.commitment S)
      (LiveGrant.active (GrantCallEvidence.live E))
    charged = record ep { amounts = amountOf op xs ∷ Episode.amounts ep }
    opened = run [] (Binding.pure-runs (Device.spentCommit-pure (Episode.saltValue ep) (total ep))
      (Run.execution (Opens.spentOpening O)) s)
    facts = Grant.cumulative-spend E agreement opened

  revoke-map : ∀ id g {eps entries} → grantActive g ≡ bool true →
    Corresponds eps entries → lookupMap id entries ≡ just g →
    Corresponds eps (insertMap id (revokedRecord g) entries)
  revoke-map id g active empty ()
  revoke-map id g active (mapEntry {ep = ep} {g = old} O rest) found with equal id (episodeKey ep) in same
  ... | false = mapEntry O (revoke-map id g active rest found)
  ... | true with Grant.equal-sound id (episodeKey ep) same | just-injective found
  ... | refl | refl = mapEntry (revoked-opens ep old active O) rest

  spend-map : ∀ id g updated amount {eps entries} →
    (∀ ep → findEpisode id eps ≡ just ep → episodeKey ep ≡ id → Opens ep g → WithinCap ep →
      Opens (record ep { amounts = amount ∷ Episode.amounts ep }) updated ×
      WithinCap (record ep { amounts = amount ∷ Episode.amounts ep })) →
    Corresponds eps entries → All.All WithinCap eps → lookupMap id entries ≡ just g →
    Corresponds (charge id amount eps) (insertMap id updated entries) × All.All WithinCap (charge id amount eps)
  spend-map id g updated amount update empty All.[] ()
  spend-map id g updated amount update (mapEntry {ep = ep} {g = old} {eps = eps} O rest) (bounded All.∷ tailBounds) found
    with equal id (episodeKey ep) in same
  ... | false = mapEntry O (proj₁ advanced) , bounded All.∷ proj₂ advanced
    where
    advanced = spend-map id g updated amount
      (λ selectedEp selected key opens bound → update selectedEp selected key opens bound)
      rest tailBounds found
  ... | true with Grant.equal-sound id (episodeKey ep) same | just-injective found
  ... | refl | refl = mapEntry (proj₁ advanced) rest , proj₂ advanced All.∷ tailBounds
    where advanced = update ep refl refl O bounded

keep-accounted : ∀ {b s t} → cell "grants" t ≡ cell "grants" s → Accounted b s → Accounted b t
keep-accounted {b} same A = record
  { correspondence = subst (Corresponds (Book.current b)) (sym (cong fields same)) (Accounted.correspondence A)
  ; bounded = Accounted.bounded A }

issue-accounted : ∀ xs {b before source after} → cell "grants" source ≡ cell "grants" before →
  (r : IssueResult xs source after) → Accounted b before →
  Accounted (evolve (issueEpisode (issued-episode xs r)) b) after
issue-accounted xs {b} {before} {source} {after} same r A = record
  { correspondence = subst (Corresponds (insertEpisode ep (Book.current b)))
      (sym (cong fields (IssueResult.installed r)))
      (insert-corresponds ep (issuedRecord r) (issue-opens xs r)
        (subst (Corresponds (Book.current b)) (sym (cong fields same)) (Accounted.correspondence A)))
  ; bounded = insert-bounded ep z≤n (proj₁ (Accounted.bounded A)) ,
      archive-bounded (episodeKey ep) (proj₁ (Accounted.bounded A)) (proj₂ (Accounted.bounded A)) }
  where ep = issued-episode xs r

revoke-accounted : ∀ id {b before source after} → cell "grants" source ≡ cell "grants" before →
  RevokeResult id source after → Accounted b before → Accounted b after
revoke-accounted id {b} same r A = record
  { correspondence = subst (Corresponds (Book.current b)) (sym (cong fields (RevokeResult.installed r)))
      (revoke-map id (RevokeResult.old r) (RevokeResult.active r)
        (subst (Corresponds (Book.current b)) (sym (cong fields same)) (Accounted.correspondence A))
        (RevokeResult.recorded r))
  ; bounded = Accounted.bounded A }

clear-accounted : ∀ {b before after} → cell "grants" after ≡ tuple [] → Accounted b before →
  Accounted (evolve closeAll b) after
clear-accounted {b} same A = record
  { correspondence = subst (Corresponds []) (sym (cong fields same)) empty
  ; bounded = All.[] , ++⁺ (proj₁ (Accounted.bounded A)) (proj₂ (Accounted.bounded A)) }

spend-accounted : ∀ c op ctx ga xs {b s t} → (mutation : SpendMutation c op ctx ga xs s t) →
  (∀ ep → findEpisode (episodeKey ep) (Book.current b) ≡ just ep →
    Run (grantId c ctx ga) s (episodeKey ep) s →
    SpentOpeningsAgree (salt ga) (spentPrev ga) (Episode.saltValue ep) (total ep)) →
  Accounted b s → Accounted
    (evolve (spendAmount (GrantCallEvidence.identifier (SpendMutation.evidence mutation)) (amountOf op xs)) b) t
spend-accounted c op ctx ga xs {b} {s} {t} mutation agreements A = build
  (spend-map (GrantCallEvidence.identifier E) (GrantCallEvidence.grantRecord E) updated (amountOf op xs)
    advance (Accounted.correspondence A) (proj₁ (Accounted.bounded A))
    (Effects.lookup-found "grants" (GrantCallEvidence.identifier E) (GrantCallEvidence.recorded E)))
  where
  E = SpendMutation.evidence mutation
  updated = settledGrant (GrantCallEvidence.grantRecord E) (suc (number (grantNonce (GrantCallEvidence.grantRecord E))))
    (Settlement.commitment (GrantCallEvidence.settlement E))
  advance : ∀ ep → findEpisode (GrantCallEvidence.identifier E) (Book.current b) ≡ just ep →
    episodeKey ep ≡ GrantCallEvidence.identifier E → Opens ep (GrantCallEvidence.grantRecord E) → WithinCap ep →
    Opens (record ep { amounts = amountOf op xs ∷ Episode.amounts ep }) updated ×
      WithinCap (record ep { amounts = amountOf op xs ∷ Episode.amounts ep })
  advance ep selected key O bounded = spend-opens E ep
    (agreements ep
      (trans (cong (λ id → findEpisode id (Book.current b)) key) selected)
      (subst (λ id → Run (grantId c ctx ga) s id s) (sym key) (GrantCallEvidence.identified E))) O
  build : Corresponds (charge (GrantCallEvidence.identifier E) (amountOf op xs) (Book.current b))
      (insertMap (GrantCallEvidence.identifier E) updated (fields (cell "grants" s))) ×
      All.All WithinCap (charge (GrantCallEvidence.identifier E) (amountOf op xs) (Book.current b)) →
    Accounted (evolve (spendAmount (GrantCallEvidence.identifier E) (amountOf op xs)) b) t
  build (newMap , currentBounds) = record
    { correspondence = subst (Corresponds (charge (GrantCallEvidence.identifier E) (amountOf op xs) (Book.current b)))
        (sym (cong fields (SpendMutation.installed mutation))) newMap
    ; bounded = currentBounds , proj₂ (Accounted.bounded A) }

private
  observe-issue : ∀ xs {s t} (r : IssueResult xs s t) →
    observeBody issueGrant xs t ≡ issueEpisode (issued-episode xs r)
  observe-issue xs {s} {t} r = cong
    (λ found → issueEpisode (episode (issuanceOf (IssueArguments.id xs) (Data.Maybe.Base.fromMaybe none found))
      (IssueArguments.salt xs) (number (IssueArguments.cap xs)) []))
    (trans (cong (lookupMap (IssueArguments.id xs) ∘ fields) (IssueResult.installed r))
      (lookup-insert (IssueArguments.id xs) (issuedRecord r) (fields (cell "grants" s))))
    where open import Function.Base using (_∘_)

  kept-body-accounted : ∀ op → All.All (λ k → stringEqual "grants" k ≡ false) (bodyWrites op) →
    ∀ ctx xs coin entry {b before source v after} → cell "grants" source ≡ cell "grants" before →
    Run (body op ctx xs coin entry) source v after → Accounted b before → Accounted b after
  kept-body-accounted op outside ctx xs coin entry {before = before} {source} {after = after} same r A =
    keep-accounted (trans (Effects.cell-frame "grants" source after
      (Device.body-frame "grants" op ctx xs coin entry outside r)) same) A

body-accounted : ∀ op ctx xs coin entry {b before source v after} →
  cell "grants" source ≡ cell "grants" before → Run (body op ctx xs coin entry) source v after →
  Accounted b before → Accounted (evolve (observeBody op xs after) b) after
body-accounted withdrawUnshielded = kept-body-accounted withdrawUnshielded (refl All.∷ All.[])
body-accounted withdrawShielded = kept-body-accounted withdrawShielded All.[]
body-accounted withdrawToContract = kept-body-accounted withdrawToContract All.[]
body-accounted appendInbox = kept-body-accounted appendInbox (refl All.∷ refl All.∷ All.[])
body-accounted rotateEncKey = kept-body-accounted rotateEncKey (refl All.∷ All.[])
body-accounted addDevice = kept-body-accounted addDevice (refl All.∷ refl All.∷ All.[])
body-accounted removeDevice = kept-body-accounted removeDevice (refl All.∷ refl All.∷ All.[])
body-accounted issueGrant ctx xs coin entry {b} {after = after} same r A =
  subst (λ action → Accounted (evolve action b) after) (sym (observe-issue xs result))
    (issue-accounted xs same result A)
  where result = Effects.issue-body-result ctx xs coin entry r
body-accounted revokeGrant ctx xs coin entry same r A =
  revoke-accounted (get 0 xs) same (Effects.revoke-body-result ctx xs coin entry r) A
body-accounted revokeAllGrants ctx xs coin entry same r A =
  clear-accounted (Effects.clear-body-result ctx xs coin entry r) A
body-accounted publishRecovery =
  kept-body-accounted publishRecovery (refl All.∷ refl All.∷ refl All.∷ refl All.∷ refl All.∷ refl All.∷ All.[])
body-accounted cancelRecovery =
  kept-body-accounted cancelRecovery (refl All.∷ refl All.∷ refl All.∷ refl All.∷ All.[])

private
  IsKept : ∀ {s t} → GrantEffect s t → Set
  IsKept (kept _) = ⊤
  IsKept _ = Data.Empty.⊥

  kept-effect-accounted : ∀ {b s t} (effect : GrantEffect s t) →
    IsKept effect → Accounted b s → Accounted b t
  kept-effect-accounted (kept same) _ A = keep-accounted same A
  kept-effect-accounted (grantIssued _ _ _ _) ()
  kept-effect-accounted (grantRevoked _ _ _ _) ()
  kept-effect-accounted (cleared _) ()
  kept-effect-accounted (grantSpent _ _ _ _ _ _ _) ()

  grant-observed : ∀ c op ctx xs {s t id} → Run (grantId c ctx (parseGrantAuth c op xs)) s id s →
    observeAccepted (grant c op) ctx xs s t ≡ spendAmount id (amountOf op (Data.List.Base.take 3 xs))
  grant-observed c op ctx xs (run _ executed) rewrite executed = refl

  grant-execution : ∀ c op ctx xs → Withdrawal op → ∀ {s v t} →
    Run (Model.AccountSemantics.execute P (grant c op) ctx xs) s v t →
    Run (grantCall c op ctx (parseGrantAuth c op xs) (Data.List.Base.take 3 xs)) s v t
  grant-execution c withdrawUnshielded ctx xs unshieldedWithdrawal r = r
  grant-execution c withdrawShielded ctx xs shieldedWithdrawal r = r
  grant-execution c withdrawToContract ctx xs contractWithdrawal r = r

execute-accounted : ∀ {e} (runtime : RuntimeEntrypoint e) ctx xs {b s v t} →
  Run (Model.AccountSemantics.execute P e ctx xs) s v t →
  CallAgreement e ctx xs s b → Accounted b s →
  Accounted (evolve (observeAccepted e ctx xs s t) b) t
execute-accounted (activationEntry c) ctx xs r _ A =
  kept-effect-accounted (Effects.execute-effect (activationEntry c) ctx xs r) tt A
execute-accounted (deviceEntry c op) ctx xs {s = s} r _ A = body-accounted op ctx (deviceArguments op xs)
  (deviceCoin op ctx) (DeviceCall.callerEntry D)
  (Effects.cell-frame "grants" s (DeviceCall.authorisedState D)
    (Authorisation.unchanged (DeviceCall.authorised D) "grants" refl refl refl)) (DeviceCall.bodyRun D) A
  where D = Device.device-call-evidence c op ctx xs r
execute-accounted (grantEntry c op withdrawal) ctx xs {b} {s} {t = t} r agreement A =
  subst (λ action → Accounted (evolve action b) t)
    (sym (grant-observed c op ctx xs {s = s} {t = t}
      (GrantCallEvidence.identified (SpendMutation.evidence mutation))))
    (spend-accounted c op ctx (parseGrantAuth c op xs) (Data.List.Base.take 3 xs) mutation agreement A)
  where mutation = Effects.spend-mutation c op ctx (parseGrantAuth c op xs) (Data.List.Base.take 3 xs)
          withdrawal (grant-execution c op ctx xs withdrawal r)
execute-accounted publicDepositEntry ctx xs r _ A =
  kept-effect-accounted (Effects.execute-effect publicDepositEntry ctx xs r) tt A
execute-accounted privateDepositEntry ctx xs r _ A =
  kept-effect-accounted (Effects.execute-effect privateDepositEntry ctx xs r) tt A
execute-accounted submissionEntry ctx xs r _ A =
  kept-effect-accounted (Effects.execute-effect submissionEntry ctx xs r) tt A
execute-accounted finalisationEntry ctx xs r _ A =
  kept-effect-accounted (Effects.execute-effect finalisationEntry ctx xs r) tt A

module Rooted (address : Value) where
  open Histories address
  module Security = AccountSecurity P address (λ _ → Signing.attacker)
  module SecurityProof = AccountSecurityProof P address (λ _ → Signing.attacker)
  open Security using (Dispatched; AcceptedCall)

  private
    record Resolved (env : Environment) (call : RuntimeCall) (s : State) (v : Value)
        (t : State) (es : List Effect) : Set where
      constructor resolved
      field entrypoint : Entrypoint
            runtime : RuntimeEntrypoint entrypoint
            named : Model.AccountSemantics.lookupEntrypoint P (name (RuntimeCall.request call))
              (Model.AccountSemantics.entrypoints P) ≡ just entrypoint
            ran : Run (Model.AccountSemantics.execute P entrypoint (executionContext address env)
              (arguments (RuntimeCall.request call))) s v t

    dispatched : ∀ {env call s v t es e} → RuntimeEntrypoint e →
      Dispatched e env call s v t es → Resolved env call s v t es
    dispatched runtime d = resolved _ runtime (Security.Dispatched.resolved d)
      (run _ (Security.Dispatched.executed d))

    from-accepted : ∀ {env call s v t es requests} →
      AcceptedCall env call s v t es requests → Resolved env call s v t es
    from-accepted (Security.activated c d _) = dispatched (activationEntry c) d
    from-accepted (Security.deviceAuthorised c op d _ _ _) = dispatched (deviceEntry c op) d
    from-accepted (Security.grantAuthorised c op d withdrawal _ _ _) = dispatched (grantEntry c op withdrawal) d
    from-accepted (Security.depositedUnshielded d) = dispatched publicDepositEntry d
    from-accepted (Security.depositedShielded d) = dispatched privateDepositEntry d
    from-accepted (Security.recoverySubmitted d _ _ _ _) = dispatched submissionEntry d
    from-accepted (Security.recoveryFinalised d _) = dispatched finalisationEntry d

    accepted-attempt : ∀ env call {s v t es b} →
      Model.dispatch P (executionContext address env) (RuntimeCall.request call) s ≡ accepted v t es →
      AcceptedAgreement (executionContext address env) (RuntimeCall.request call) s b →
      Accounted b s → Accounted
        (observeSuccessful (executionContext address env) (RuntimeCall.request call) s t b) t
    accepted-attempt env call {s} {v} {t} {es} executed agreement A with SecurityProof.accepted-call env call
      (Account.transition (cong (Account.transaction s) executed))
    ... | _ , acceptedCall , _ with from-accepted acceptedCall
    ... | resolved e runtime named ran rewrite named =
      execute-accounted runtime (executionContext address env) (arguments (RuntimeCall.request call)) ran agreement A

  attempt-accounted : ∀ env call {s observation t b} →
    Account.Transition P (executionContext address env) (RuntimeCall.request call) s observation t →
    AttemptAgreement (executionContext address env) (RuntimeCall.request call) s b →
    Accounted b s → Accounted
      (observeAttempt (executionContext address env) (RuntimeCall.request call) s b) t
  attempt-accounted env call {s} {b = b} stepResult agreement A
    with Model.dispatch P (executionContext address env) (RuntimeCall.request call) s in executed
  ... | rejected err = subst (Accounted b)
    (cong Data.Product.Base.proj₂
      (trans (cong (Account.transaction s) (sym executed)) (Account.execution stepResult))) A
  ... | accepted v next es = subst
    (Accounted (observeSuccessful (executionContext address env) (RuntimeCall.request call) s next b))
    (cong Data.Product.Base.proj₂
      (trans (cong (Account.transaction s) (sym executed)) (Account.execution stepResult)))
    (accepted-attempt env call executed agreement A)

  trace-accounted : ∀ {s t} b (trace : Runs.Trace s t) →
    TraceAgreement b trace → Accounted b s → Accounted (runBook b trace) t
  trace-accounted b ε _ A = A
  trace-accounted b (Runs.event env call observation stepResult ◅ rest) (agreement , agreements) A =
    trace-accounted _ rest agreements (attempt-accounted env call stepResult agreement A)

  private
    constructorArguments : Account.Deployment → List Value
    constructorArguments d = Account.initialDeviceBoot d ∷ Account.encryptionKey d ∷ Account.initialRecoveryKey d ∷
      Account.initialRecoveryWrap d ∷ nat (Account.vetoWindowSeconds d) ∷ []

    then-branch : ∀ b {err x v t es} →
      (if b then x else rejected err) ≡ accepted {Value} v t es → x ≡ accepted v t es
    then-branch true ok = ok
    then-branch false ()

    same-after : ∀ {A : Set} {x y : A} {s t es fs} → accepted x s es ≡ accepted y t fs → s ≡ t
    same-after refl = refl

    deployment-accounted : ∀ ctx d {v s es} → Account.deploy P ctx d ≡ accepted v s es → Accounted emptyBook s
    deployment-accounted ctx d {s = s} deployed = record
      { correspondence = subst (Corresponds []) (sym (cong fields grantsEmpty)) empty
      ; bounded = All.[] , All.[] }
      where
      executed = then-branch (Model.validContext ctx)
        (then-branch (Model.validArguments (Model.AccountSemantics.schema P construct) (constructorArguments d)) deployed)
      grantsEmpty : cell "grants" s ≡ tuple []
      grantsEmpty = cong (cell "grants") (sym (same-after executed))

  rooted-accounted : ∀ {s} (history : Runs.History s) →
    HistoryAgreement history → Accounted (historyBook history) s
  rooted-accounted (Runs.rooted env d (Account.committed v es) initial deployed trace) agreement =
    trace-accounted emptyBook trace agreement (deployment-accounted (executionContext address env) d deployed)
  rooted-accounted (Runs.rooted env d (Account.reverted err) initial () trace)

  rooted-caps : ∀ {s} (history : Runs.History s) →
    HistoryAgreement history → BookBounded (historyBook history)
  rooted-caps history agreement = Accounted.bounded (rooted-accounted history agreement)

  rooted-episode-cap : ∀ {s} (history : Runs.History s) → HistoryAgreement history →
    ∀ ep → ep ∈ (Book.current (historyBook history) ++ Book.completed (historyBook history)) →
    total ep ≤ Episode.capValue ep
  rooted-episode-cap history agreement ep member =
    All.lookup (++⁺ (proj₁ bounded) (proj₂ bounded)) member
    where bounded = rooted-caps history agreement

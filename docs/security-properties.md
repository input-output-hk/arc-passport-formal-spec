# Additional security properties

Formalisation notes for P5′ and P11–P16 in
[PROMISES.md](https://github.com/midnightntwrk/passport/blob/security-promises/docs/plans/PROMISES.md#security-properties).
That document gives the user-facing requirements and invariants; this one records
proposed formal statements, their assumptions, and the available proof evidence.

## Assurance and modelling status

The Agda-like blocks below are **schematic**, not compiled definitions or proofs.
Unless noted otherwise, these properties remain proposed obligations.

The existing accounting model uses `M = ⟦architecture⟧` and traces from genesis,
with balance queries at the user boundary. Its
[balance definitions](https://github.com/input-output-hk/arc-passport-formal-spec/blob/e7dd04f1cdf910ed77a35dcfa5d7bd02df6ae246/src/Midnight/Passport/Properties.lagda.md#L155-L194)
and [preservation theorem](https://github.com/input-output-hk/arc-passport-formal-spec/blob/e7dd04f1cdf910ed77a35dcfa5d7bd02df6ae246/src/Midnight/Passport/Properties.lagda.md#L339-L345)
are mechanised. The theorem assumes local `Sound` and `PromptlyAccurate`,
`FlowPreserving`, `QuerySound`, and `QueryComplete`; it does not establish these
hypotheses for the account contract. Its `EventuallyAccurate` chooses a
value-neutral continuation with an enabled accurate answer, possibly with no
steps. This is may-liveness, not convergence on every fair execution.

The accounting theorem does not establish the promises for the concrete implementation.
See [modelling gaps](modelling-gaps-and-account-model.md#1-current-modelling-gaps)
for the model's scope. In the proposed UC statements, `≤UC` means simulator
existence against an ideal functionality with an explicit permitted-leakage port.

## 1. Properties

### P5' · Recovery-driven authority replacement

```agda
RecoverySafety = ∀ {s} (t : Trace M s₀ s) {r} →
  FinalisesRecovery r t →
    AuthorisedSubmission r t
  × BoundToAccountSuccessorRecoveryStateTime r t
  × VetoWindowElapsed r t × UncancelledPending r t
```

Submission binds the current recovery authority, successor device and recovery
keys, account, epoch/authorisation nonce, and signed time bound. Finalisation
requires an uncancelled pending record and an elapsed veto window, not fresh
signatures. Ordinary device-authorised encryption-key rotation is outside this
property. Let `k` be the number of guardian shares required for reconstruction
(`t+1` in the recovery protocol's threshold notation). Cryptographic authority
does not certify human consent: a colluding quorum of `k` guardians can
reconstruct it, and total device loss removes the veto.

The [recovery specification](recovery-specification.md#intended-properties)
develops a separate device-authority model and proof plan. Its scope excludes
guardian reconstruction, grants, asset accounting, and prover privacy. It is
not an established contract-security theorem.

### P11 · Transaction safety

```agda
TransactionSafety = ∀ {s} (t : Trace M s₀ s) {tx} →
  adopts tx ∈ᵗ t → SpendsFrom account tx →
    (LiveDeviceAuthorisation account tx t ⊎ LiveInScopeGrant account tx t)
  × AccountOperationStateBound tx t × WithinCaps tx t × NotReplayed tx t
```

Liveness of an authority is checked at adoption, including device/grant
revocation, grant expiry, and applicable epochs, generations, and nonces.
Unforgeability concerns fresh unauthorised operations under the scheme's
cryptographic and compromise assumptions, not exclusive production of signature
bytes: the [ECDSA policy](https://github.com/midnightntwrk/passport/blob/5d12798321d3daba37b1da90162ee1468daf38a6/docs/mps-mip/mips/mip-xxxx-signature-schemes.md#L238-L246)
accepts both `(r, s)` and `(r, n−s)` for the same single execution.

### P12 · Snapshot-aware value integrity

Reports carry `(account, asset, snapshot, amount, completeness)`.

```agda
SnapshotSound = ∀ r → Reports r →
  Finalised (snapshot r) ×
  (Complete r → amount r ≡ LedgerBalance (account r) (asset r) (snapshot r)) ×
  (LowerBound r → amount r ≤ LedgerBalance (account r) (asset r) (snapshot r))

SnapshotProgress = ∀ ρ → LedgerAndViewingDataAccessible ρ →
  ContinuedSyncResources ρ → FairSyncScheduling ρ →
    (∀ m → RelevantFinalisedMovement m ρ →
      Eventually (IncludedInCompleteReport m) ρ)
  × (∀ H → QuiescentAfter H ρ →
      Eventually (ReportsCompleteAtOrAfter H) ρ)
```

Soundness compares against the reported snapshot, not the latest balance.
Partial views must reconcile relevant debits before claiming a lower bound.
A historical balance is not a current spendability assertion (P11/P13).

`ρ` ranges over executions. Fair scheduling gives continuing service to enabled
fetch, scan, debit reconciliation, and reporting work; it does not assume success.
Inclusion means accounting for a movement, not merely fetching its event.
After quiescence at `H`, a complete report must cover all movements through `H`.
Fees are attributed to their payer and asset; custody-asset compensation is a
separately authorised spend.

The existing `Sound` has no asset, snapshot, or completeness fields. The
conditional accounting theorem proves neither `SnapshotSound` nor
`SnapshotProgress`; both require revised query semantics and concrete proofs.

### P13 · Funds availability

A recoverable holding has coin descriptions/openings, viewing material, and
membership/witness data reconstructible from valid private credentials or
recovery authority and authenticated chain data—not an assumed surviving
client-side coin store.

```agda
RecoverabilityPreserved = ∀ {s s' h}
  (t : Trace M s₀ s) (u : Trace M s s') →
  HonestlyAcquiredRecoverableHolding h t → SupportedEvolution u →
  ValidPrivateCredentialOrRecoveryAuthority t u →
  RecoverableFromRecoveryInputs (RemainingHoldings h u) (t ++ u)

Liveness = ∀ {s h} (t : Trace M s₀ s) →
  HonestlyAcquiredRecoverableHolding h t →
  ValidPrivateCredentialOrRecoveryAuthority t →
  ∃[ U ∈ Machine ⟦ Var User ⟧₀ I ] ∀ ρ →
    ExecutionFrom (U ∘ M) s ρ →
    RecoveryDataAndProvingAccess ρ → FeeResourcesAvailable ρ →
    FairChainAndClientProgress ρ →
    Eventually (ExecutesAuthorisedRequestedMove h) ρ
```

`SupportedEvolution` includes spends, key changes, crashes, and total device
loss. `RemainingHoldings` includes change, excluding authorised transfers and
fees charged to this account in the fee asset. Liveness requires a strategy that
succeeds on every execution satisfying the data, proving, fee, and fair-progress
assumptions, not just one favourable continuation. P11's authorisation limits
and P8's operator independence still apply.

The [custody baseline](https://github.com/midnightntwrk/passport/blob/5d12798321d3daba37b1da90162ee1468daf38a6/docs/mps-mip/mips/mip-xxxx-native-asset-custody.md#L723-L759)
has two distinct gaps. Poisoned outsider deposits fall outside honestly acquired
recoverable holdings; covering them needs description/encryption binding.
Losing the sole change description before inbox append can strand previously
recoverable value, violating P13. That mandatory durability obligation remains
open: recovery must survive a crash or total device loss in that window without
an extra client copy. Neither gap is fixed or proved here.

### P14 · Private proving

```agda
F-prove leak_P : Machine I (⟦ Var WITNESS-IPC ⟧₀ ⊗₀ AdvP)
RestrictedProverKnowledge = proofServerᴬ ≤UC F-prove leak_P

F-passport leak_modelled :
  Machine ⟦ Var CHAIN ⟧₀ (⟦ Var User ⟧₀ ⊗₀ ModelledAdv)
BoundedLeakage = ⟦architecture⟧ᴬ ≤UC F-passport leak_modelled
```

`leak_P` must be fixed per circuit/proving profile: an exhaustive budget of public
inputs, necessary witness fields, and request/transport metadata, justified by
the protocol. Missing budgets remain open obligations, not provider discretion.
The simulator receives that budget, **not just the statement**. Ordinary
proving exposes witnesses; statement-only delegation needs another mechanism.
Signing/recovery secrets must stay out of witnesses; see the
[recovery signature-gate rationale](https://github.com/midnightntwrk/passport/blob/5d12798321d3daba37b1da90162ee1468daf38a6/docs/mps-mip/mips/mip-xxxx-account-recovery.md#L843-L858).

`leak_modelled` covers joint observations at the claimed architecture boundary:
prover, chain, guardians, transport endpoints/timing, and logs, with explicit
corruption assumptions. Component budgets constrain the combined budget.
Omitting an observer narrows the claim; it cannot establish an everything-off-device
bound. Inherent public linkage is permitted, unrelated tracking is not.

### P15 · Guardian privacy

```agda
ThirdPartyDeniable = ∀ g g' →
  SamePublicContextAndAcceptedChainLeakage g g' →
  (recovery [ guardians g ]) ∣^ᶜ ≈ℰ (recovery [ guardians g' ]) ∣^ᶜ

GuardianBounded = guardianᴬ ≤UC F-guardian leak_G corruptionBound
```

`∣^ᶜ` keeps only the chain projection. Comparisons fix account/public context
and accepted leakage: recovery-configuration existence, public-share count,
session timing/frequency, and routine-versus-churn activity—not guardian
identities, roster, messages, or graph. This gives no network-anonymity claim.

`leak_G` needs an exhaustive protocol/transport-specific budget for account/session
identifiers, evaluation index, own share/reply/liveness information, necessary
requester-authentication fields, and endpoint/timing observations. Prior knowledge,
coordination, and traffic observations belong in the corruption model; removing
another guardian is not unconditionally indistinguishable.

Fewer than `k` shares are sub-quorum; `k` reconstruct recovery authority and viewing
capability. Bounds assume the share scheme, fresh sessions, and uncompromised
client secrets. Historical quorums can retain historical viewing, potentially
including current holdings if viewing material stays stable. P6's honest-handling
rules do not prevent malicious reconstruction. See the recovery protocol's
[messages](https://github.com/midnightntwrk/passport/blob/5d12798321d3daba37b1da90162ee1468daf38a6/docs/mps-mip/mips/mip-xxxx-account-recovery.md#L611-L645)
and [trust limits](https://github.com/midnightntwrk/passport/blob/5d12798321d3daba37b1da90162ee1468daf38a6/docs/mps-mip/mips/mip-xxxx-account-recovery.md#L1044-L1073).
Concrete leakage budgets and proofs remain open.

### P16 · Upgrade safety

```agda
UpgradeSafety = ∀ {s} (t : Trace M s₀ s) → upgrades ∈ᵗ t →
    AuthorizedUpgrade t
  × EnrolledDeviceAuthorisationCapabilityPreserved t
  × HoldingsPreservedWithPayerAndFeeAssetAccounting t
  × IdentityAnswersPreservedInSameLedgerCredentialContext t
```

Preservation concerns actual device authorisation capability for corresponding
operations, not just membership in a device set. Holdings exclude authorised
movements and fees attributed to the correct payer/asset. Identity answers are
compared in the same ledger and credential context. Account-gating alone proves
none of these preservation obligations.

## 2. Unpromised hazards

The [open questions in PROMISES.md](https://github.com/midnightntwrk/passport/blob/security-promises/docs/plans/PROMISES.md#open-questions)
include these candidate properties, not committed guarantees:

```agda
NonGriefability = ∀ {s s' d op} (t : Trace M s₀ s) (u : Trace M s s') →
  Outsider u → Authorized d s → AvailableVia d op s → AvailableVia d op s'

DeploymentAuthenticity = ∀ {s c} (t : Trace M s₀ s) →
  attaches c ∈ᵗ t → codeOf c ≡ canonicalCode
```

The sketches assume adopted ledger state is final. Reorg semantics remain open.

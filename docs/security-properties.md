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

The [symbolic signing model](conformance-testing-plan.md#symbolic-signing-and-adversarial-histories)
records trusted abstract approvals, signing, attacker-owned keys and permanent
compromise. Its checked results establish persistence and message-level issuance
provenance in deployment-rooted joint signing/contract histories.

The [concrete authorization layer](conformance-testing-plan.md#contract-level-authorization-evidence)
adds the source signing requests, verification gates and contract-level statements.
These are separate from the top-level promises below. Its ideal signing
interpretation requires available key/digest tokens, while request-level provenance
also requires agreement with the relevant honest issuances. Neither is a proof of
concrete cryptographic security. Approval remains an abstract input, not evidence
of human consent. Ledger-adoption correspondence, confidentiality, guardian
protocols, liveness and upgrades remain outside this layer.

## 1. Properties

### P5' · Recovery-driven authority replacement

*Recovery follows the rules you set.* Recovery must use the authority you
configured and respect the cancellation window. This trusts your recovery
quorum: the chain checks cryptographic authority, not your personal consent.
This is P5's safety counterpart, not a requirement to invoke recovery for
ordinary live-device-authorised encryption-key rotation.

Submission must verify the **current recovery authority** and proof of
successor-key possession, bound to the account, successor device key, successor
recovery authority, current epoch/authorisation nonce, and signed time bound.
Finalisation is permissionless enactment of that pending record after the veto
window, provided it has not been cancelled. It requires no fresh signature.

The full obligation below is schematic; the narrower checked subset is listed
separately.

```agda
RecoverySafety = ∀ {s} (t : Trace M s₀ s) {r} →
  FinalisesRecovery r t →
    AuthorisedSubmission r t
  × BoundToAccountSuccessorRecoveryStateTime r t
  × VetoWindowElapsed r t × UncancelledPending r t
```

These are the two obligations corresponding to **I-5′.1** (submission) and
**I-5′.2** (finalisation). The chain cannot certify an off-chain guardian
exchange or the human owner's consent. With `n` guardians and threshold
parameter `t`, reconstruction requires **t+1** shares; a colluding quorum can
recover legitimately under the cryptographic gate. Human-consent safety
therefore assumes the quorum is trusted and recovery authority is uncompromised.
A live device can cancel; in total loss the veto window is only a delay/alarm.

**Evidence:** [ordinary rotation](https://github.com/midnightntwrk/passport/blob/5d12798321d3daba37b1da90162ee1468daf38a6/contract/contracts/account.compact#L1220-L1247),
[submission, cancellation, and finalisation](https://github.com/midnightntwrk/passport/blob/5d12798321d3daba37b1da90162ee1468daf38a6/contract/contracts/account.compact#L2754-L2878).
**Checked/exercised subset:** the
[recovery specification's checked routes](recovery-specification.md#intended-properties)
give finite actual-admission trace exclusion for compromised **device keys**
after corrected recovery, positive guard-premised recovery/rotation, local
submission provenance and deadline/cancellation/replay/rejection results.
[Recovery conformance](conformance-recovery.md) exercises the source attack and
the stamped-map repair, including ordinary rotation, wrong/stale bindings,
deadline equality, cancellation after the deadline, and permissionless finalise.

That earlier admission-model exclusion assumes key-entry separation, a fixed
compromise set, an uncompromised successor, and no subsequent authorised enrolment
of a compromised key encoding. Its scope does not establish deployment, full
cancelled-submission occurrence provenance or model-to-circuit refinement.

**Checked pinned-main local counterpart:** the
[`source recovery statements`](../src/Conformance/FullAccountRecoverySecurityProperties.agda)
extract current recovery-key and successor-key verifier acceptance on the exact
source request, its stored epoch/nonce and signed time bound, pending installation,
cancellation, and finalisation's deadline and replacement effects.
The [`account history statements`](../src/Passport/AccountRecoveryOccurrenceProperties.agda)
then prove that a pending record in a deployment-rooted history comes from an
actual accepted submission occurrence, followed only by refused attempts or
accepted calls preserving it. There is no intervening accepted submission,
cancellation or finalisation. `finalisation-enacts-occurrence` identifies the
enacted successor and recovery key, and the checked deadline, with that occurrence.

This closes the local occurrence gap, not the top-level assurance gap.
Request-level symbolic provenance uses the stated signing-token and
relevant-request agreement premises. Concrete cryptographic realization,
guardian consent, trustworthy chain time, ledger adoption and timely cancellation
remain separate obligations.

The [`full-source exclusion statements`](../src/Passport/RevocationExclusionProperties.agda)
derive the recovery epoch advance and identify every later live device entry as
the installed successor or an actual subsequent insertion occurrence.
Exclusion of a queried device opening additionally requires separation from
that successor and those insertions. Explicit re-enrolment, successor reuse and
relevant collisions are not hidden by an unconditional permanent-key ban.

### P11 · Transaction safety

```agda
TransactionSafety = ∀ {s} (t : Trace M s₀ s) {tx} →
  adopts tx ∈ᵗ t → SpendsFrom account tx →
    (LiveDeviceAuthorisation account tx t ⊎ LiveInScopeGrant account tx t)
  × AccountOperationStateBound tx t × WithinCaps tx t × NotReplayed tx t
```

The top-level obligation requires authority to be live at adoption, including
device/grant revocation, grant expiry, and applicable epochs, generations and nonces.
Unforgeability concerns fresh unauthorised operations under the scheme's
cryptographic and compromise assumptions, not exclusive production of signature
bytes: the [ECDSA policy](https://github.com/midnightntwrk/passport/blob/5d12798321d3daba37b1da90162ee1468daf38a6/docs/mps-mip/mips/mip-xxxx-signature-schemes.md#L238-L246)
accepts both `(r, s)` and `(r, n−s)` for the same single execution.

**Checked local contract evidence:** the
[`device statements`](../src/Conformance/FullAccountDeviceSecurityProperties.agda)
derive live entry membership, verification, entry rolling and bounded nonce/round
increments from actual successful device calls. Activation instead requires the
unconsumed boot commitment; it verifies no signature.
The [`grant statements`](../src/Conformance/FullAccountGrantSecurityProperties.agda)
derive active/current/unexpired record checks, caller and object commitments,
recipient restrictions, per-call and presented cumulative caps, coin bounds,
verification, and the nonce/spent record stored in the actual final state.

These facts do not yet prove the adoption-level formula. Commitment matches need
appropriate opening agreement to identify intended keys and policies;
`cumulative-spend` takes agreement for the two relevant spent openings, not a
global injectivity axiom.

The [`whole-history spending statements`](../src/Passport/GrantSpendingProperties.agda)
now prove that every current or archived issuance episode stays within its cap,
and that its stored commitment and nonce match accumulated accepted spending.
`HistoryAgreement` supplies agreement only for the relevant spent-opening pairs;
it does not assume the caller's presented total already equals historical spending.
Reissue and reset preserve the accounting of earlier episodes rather than erasing
their spending. These remain local contract results, not ledger-adoption proofs.

This is the contract-level counterpart of P7's issuance-scoped cumulative
allowance (I-7.8), not a per-operation cap or rate limit. Fresh issuance requires
account authorization; it starts a separately bounded episode rather than
resetting the accounting of the previous issuance.

The [`revocation history statements`](../src/Passport/RevocationExclusionProperties.agda)
derive nondecreasing authorization nonce, device epoch and grant generation,
strictly increasing issuance stamps, and persistent stale-record exclusion.
A revoked identifier remains absent or inactive until an actual matching
device-authorized issuance occurrence; the corresponding source grant call
cannot succeed before that boundary. Reissuance is an explicit exception,
not inferred from equality of endpoint records.

Device `immediate-replay-collision` covers consecutive successful calls on the
same curve and operation: equal challenges imply distinct typed source preimages
with equal hashes. It is not a theorem that the same signature cannot verify a
different effective challenge, nor a whole-history/cross-operation replay theorem.

`exact-device-replay-refused` additionally proves that a successful device call
cannot be repeated verbatim from its final state when its body preserves the
device set and its current and rolled entries differ. This covers all device
operations except add/remove-device. `consumed-credentials-refused` excludes
authorization using the same account identity and decoded authentication
arguments at that state, even with a different challenge. Actual entry
separation is an explicit premise, not inferred from different counters; these
results cover neither intervening histories nor ledger adoption.

The [`ordinary device-removal statements`](../src/Passport/DeviceRemovalProperties.agda)
extract target membership, distinction from the caller's rolled entry, stored
count greater than one, exact removal and a one-step count decrement from a
committed source removal. The removed literal entry remains absent along later
runtime history unless an actual activation, rolling, enrolment or recovery
successor introduces it. A later device call whose source entry computation
yields that removed value is excluded before such reintroduction. This is
entry-specific: other openings for the same key may remain live. No permanent
key ban, count/cardinality equality or ledger-adoption result is established.

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

**Checked local precursor:** the
[`unshielded accounting statements`](../src/Passport/UnshieldedAccountingProperties.agda)
derive exact per-color accounting from actual runtime executions, for arbitrary
primitive backends. Accepted deposits credit the declared received amount;
device/grant withdrawals debit the declared sent amount with sufficient funding.
Other entrypoints preserve the balance map, and refused calls preserve the whole
state. From deployment, for every color:
`stored balance + cumulative declared sends = cumulative declared receives`.
Absent entries mean zero; the proof includes constructor initialization and
actual final states after authentication and operation tails.

This connects storage to emitted `receiveUnshielded`/`sendUnshielded` effects,
not to authenticated or adopted ledger assets. Native/model execution agreed on
42 scenarios across all three signing schemes. `SnapshotSound` still needs
ledger-adoption correspondence, fee attribution and snapshot/completeness-aware
reporting; `SnapshotProgress` additionally needs the synchronization and scheduling
model described above.

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

I-13.5–I-13.7 distinguish three obligations within `RecoverabilityPreserved`:
durable recovery information must already be available when a spend takes
effect, it must correctly describe the actual remaining holdings and support
recovery with the applicable key material, and an authorized but malicious
scoped grantee must not destroy recoverability of value outside its spending
authority. `SupportedEvolution` must therefore include adversarial choices by
such grantees, not only honest-client executions. Neither a later backfill
transaction nor an assumed surviving private coin store establishes crash safety;
atomic append alone does not establish description or encryption-key binding.
These are outcome requirements, not a mandate for a particular inbox or circuit.

The [custody baseline](https://github.com/midnightntwrk/passport/blob/5d12798321d3daba37b1da90162ee1468daf38a6/docs/mps-mip/mips/mip-xxxx-native-asset-custody.md#L723-L759)
has two distinct gaps. Poisoned outsider deposits fall outside honestly acquired
recoverable holdings; covering them needs description/encryption binding.
Losing the sole change description before inbox append can strand previously
recoverable value, violating P13. That mandatory durability obligation remains
open: recovery must survive a crash or total device loss in that window without
an extra client copy. Neither gap is fixed or proved here.

**Pinned-main counterexamples:** native probes at
`fc19e471536febb2133f20e817847251622dcdf5` exercised both shielded destination
paths on jubjub, k256 and P256. Authorized grant withdrawals accepted:

- ciphertext under the actual current key describing value 999 while the returned
  change had value 6; and
- ciphertext encrypted to a different real key while the separately signed
  `enc_pk` argument matched the current `enc_key`.

The supplied entry was appended atomically, but its contents were not bound to
the returned change or the declared recipient key. The
[grant bound/key guard](https://github.com/midnightntwrk/passport/blob/fc19e471536febb2133f20e817847251622dcdf5/contract/contracts/account.compact#L1931-L1938)
does not establish either relation. Device withdrawals in the same probes returned
change without appending an inbox entry; the examined client uses separate
withdrawal and backfill submissions.

The 123-observation probe included correct-encryption controls, exact spends,
stale-key refusals and replay preservation, using production signatures and
X25519/HKDF/AES-GCM. This is native execution evidence, not an on-chain attack or
a proof that no alternative recovery protocol could exist. The complete
durability/binding candidate is therefore **not established**: it needs an
enforced description/encryption relation against malicious authorized delegates,
and an implemented crash-safe device protocol. An append-only theorem or an
honest-client encryption law would not discharge those obligations.

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

**Checked restricted preservation:**
[`OutsiderPreservationProperties`](../src/Passport/OutsiderPreservationProperties.agda)
covers actual rooted local histories extended only by permissionless deposits
and refused runtime attempts. These steps retain enrolled device membership
and selected stored authority, published recovery and pending recovery cells.
Successful bootstrap and permissionless recovery finalisation are explicitly
excluded: they legitimately change authority.

The same development proves each accepted deposit consumes one round and bounds
their number by the remaining Uint64 round capacity. This is structural
preservation, **not** the `AvailableVia` conclusion above. Inbox capacity,
existing nonce exhaustion, fees/proving resources, time-dependent expiry and
native asset admission remain separate. Preserved recovery bytes need not be
decryptable or sufficient for recovery. A 15-observation native/model/VM smoke
exercised deposits, refusals, pending-record preservation and the excluded
bootstrap/finalisation boundaries.

The sketches assume adopted ledger state is final. Reorg semantics remain open.

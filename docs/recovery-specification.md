# Recovery authority-replacement specification

## Status and objective

The intended shared account-recovery contract is
[`Passport.AccountRecovery.contract`](../src/Passport/AccountRecovery.agda),
using the [contract specification DSL](contract-specification-dsl.md).
Its `Chain` instantiates the DSL's generic
[`Contract.Admissions`](../src/Midnight/ContractDSL/Contract.agda) traces;
these unrestricted executions underlie the device-authority and recovery-execution theorems.
All are checked under `--safe --without-K`; start at `src/Passport.agda`.
The historical source attack, concrete stamped-map repair, exercised gate, and
implementation assurance limits are recorded in
[recovery assurance](conformance-recovery.md).

The experiment compares an implementation-shaped account program with an intended
authority-replacement specification. It must support both legitimate recovery
and adversarial interleavings. A model that simply assumes that incrementing an
epoch revokes every old device would hide the principal counterexample target.

This develops the **device-authority subset** of
[P5′](security-properties.md#p5--recovery-driven-authority-replacement).
It does not establish the entire concrete Passport property: authentication
intent, concrete-model refinement, grant authority, resource replacement, and
deployment remain separate obligations.

### Reference versions and evidence

The original plan inspected categorical-crypto's `protocol-rewrite` reference
`579b54e72d453fd6287f05f90a32b933b8474390`. Historical gate evidence used
`protocol-rewrite-437dca12`. The rebase onto `main` retains its
`protocol-rewrite-f280e04f` dependency in `pagda.nix`; historical gate locks
do not certify this updated source or dependency snapshot.

The source-review reference is Passport `main` commit
`d3152081c35bb151d8fbf4fdfced0e23afa256a2`, inspected on 2026-10-14:

- [Device authentication](https://github.com/midnightntwrk/passport/blob/d3152081c35bb151d8fbf4fdfced0e23afa256a2/contract/contracts/account.compact#L839-L915).
- [Device enrolment and future-epoch commentary](https://github.com/midnightntwrk/passport/blob/d3152081c35bb151d8fbf4fdfced0e23afa256a2/contract/contracts/account.compact#L1273-L1353).
- [Recovery-session publication](https://github.com/midnightntwrk/passport/blob/d3152081c35bb151d8fbf4fdfced0e23afa256a2/contract/contracts/account.compact#L2689-L2780).
- [Recovery submission, cancellation, and finalisation](https://github.com/midnightntwrk/passport/blob/d3152081c35bb151d8fbf4fdfced0e23afa256a2/contract/contracts/account.compact#L2796-L2920).

The `account.compact` diff from the previous reference
`5d12798321d3daba37b1da90162ee1468daf38a6` leaves these circuit bodies and
their existing authentication/challenge helpers unchanged. Other changes add
P-256/WebAuthn support and caller-bound grants, including `spec_version = 3`;
this review does not extend the model to those features. This is a source-review
pin update, not an execution against the new revision. Historical conformance
runs and their implementation checkout remain pinned as recorded in the
[conformance report](conformance-recovery.md).

The sibling checkout inspected during planning was at `68bbde28`, which has no
recovery circuit. It is not the recovery implementation reference. Pin the
reference used for manual correspondence review rather than inferring behaviour
from whichever revision happens to be checked out.

The future-epoch counterexample below was subsequently executed against the
historical Compact reference, not merely a symbolic projection. The current package
adds a concrete repair and corrected-model trace proofs. See the
[conformance report](conformance-recovery.md) for the distinct evidence levels.

## Scope and architecture boundary

Model one account after bootstrap, at the account custody contract's authority
boundary. The account identifier remains explicit so cross-account binding can
be stated even though the main experiment involves one account.

The supplied initial ledger is an arbitrary represented `AccountLedger.State`.
The model does not construct bootstrap or impose a global state-validity or
reachability predicate. This retains initially pending recovery and unsafe old
device sets. Readiness guards determine positive execution; `Safe` is the
initial premise for authority preservation, while accepted resetting finalisation
needs only its existing safe-pending-successor premise. These conditional claims
must not be read as a bootstrap invariant or a deployment theorem.

Readiness is a model-level condition, not a complete concrete-input criterion:
the submission `post_epoch` cast, ABI widths, curve interpretation and
build-error/time-refusal distinction have explicit
[correspondence limits](conformance-recovery.md#ledger-primitive-boundary).
These are not hidden global state assumptions.

Include recovery submission, cancellation, finalisation, recovery-session
publication, device enrolment/removal, and ordinary device-authorised operations
that interfere with nonce or credential state. Ordinary encryption-key rotation
must not require recovery; its relevant authority effects belong to the ordinary
operation model.

Do not initially model guardian reconstruction, contact discovery, human consent,
prover privacy, asset accounting, fee availability, or wallet synchronisation.
Scoped grants are outside the first device-authority claim; that claim must not
be presented as exclusion of every possible account-spending authority. Extending
it to grants requires modelling their epoch and lifecycle rules.

Use the DSL's transactional semantics. Program execution proposes effects; the
blockchain protocol validates and commits the modelled account effects in one
selected atomic segment, with no checkpoint crossing those effects. This is not
a claim that Midnight rolls back fees or other guaranteed/successful segments.
The surrounding protocol admits adversarial transaction construction and
scheduling, not just calls from an honest client interpreter.

## Threat model and assumptions

The adversary may:

- Know a currently enrolled device's secret key.
- Invoke operations that this device currently authorises, including enrolment of
  arbitrary opaque entries.
- Construct its own transactions, replay requests, and use fresh signatures.
- Choose transaction ordering and submit permissionless finalisation.

For the authority-exclusion experiment, the legitimate recovery authority and
successor device key remain uncompromised. The checked exclusion theorems assume
[`TracePolicy`](../src/Conformance/RecoveryAuthorityDefinitions.agda) on the
subsequent trace: the certified input of every step, rejected ones
included, satisfies `InputPolicy`. All enrolment entries exclude compromised-key
encodings at every epoch/counter, regardless of which device authorised enrolment;
all recovery submissions select uncompromised successors. This is a theorem
hypothesis, not a contract-admission rule. Compromise of the old device is allowed:
excluding it is the point of recovery.

Initial cryptographic interpretation uses ideal authentication with explicit key
ownership/compromise and authorisation semantics. A verifying signature alone is
not defined to mean human consent. Public keys must satisfy the required validity
conditions; weak-key behaviour must not disappear behind an unqualified signature
assumption.

The chain supplies authenticated account identity and time, atomic finalised
account-effects segments, and the stated operation-specific admission/conflict
rules. Rejected segments leave the modelled committed account state unchanged;
fees and effects outside that segment are excluded. Scheduling occurs between
atomic account transitions, with no adversarial interleaving inside one.

No fairness or eventual inclusion is assumed for safety. Positive recovery
behaviour is conditional on submission/admission of the eligible operations, not
a guarantee that every adversarial run eventually recovers.

A recovery quorum capable of reconstructing the recovery authority can pass its
cryptographic gate. Human-consent claims require additional trust assumptions;
the on-chain model cannot certify an off-chain guardian conversation.

## State and representations

| State | Role |
|---|---|
| Account identifier | Bind credentials and authorisations to the account |
| Device epoch | Select the active credential generation |
| Device-entry set | Preserve actual membership, including dormant future-epoch entries |
| Device count | Represent lifecycle guards, not a proof of usable authority |
| Authorisation nonce | Bind fresh operations and recovery submissions |
| Recovery public key | Identify the current submission authority |
| Optional pending record | Store successor entry, successor recovery key, and earliest finalisation time |
| Recovery-publication status | Represent invalidation of the published recovery material |
| Veto-window parameter | Determine the delay from the signed upper time bound |

The chain resource supplies time; it is not an arbitrary client-controlled field
in account state. Round counters and other implementation fields may be projected
away only with an explicit account of their relevance to admission and
observations. They must not be omitted if the selected chain interpretation uses
them to validate a transaction.

For initial reasoning, entry derivation may use symbolic commitments whose
preimages include account, scheme, key, epoch, and use counter. The account's
enrolment program must nevertheless treat an entry as opaque: it must not inspect
or constrain a preimage that the actual circuit cannot inspect. Symbolic
collision-freedom is an idealisation to record, not a cryptographic theorem.

Keep scheme distinctions where they affect binding or validation. A shared
abstract authentication operation is acceptable only if the correspondence review
identifies the obligations for each concrete arm.

Submission provenance belongs to a history relation or ghost instrumentation,
not fictitious public storage. In particular, the pending record need not acquire
an implementation-visible identifier merely to make cancellation proofs easy.
Use an execution occurrence to distinguish a cancelled submission from a later
accepted submission with similar contents.

Initially restrict the comparison to non-overflowing executions, with explicit
bounds for epochs, nonces, use counters, device counts, and deadline addition.
Do not silently infer bounded-integer behaviour from unbounded-natural arithmetic.
Exhaustion behaviour needs a separate correspondence obligation before extending
the claim to those states.

## Operations and concrete transition requirements

### Submit recovery

Check that no recovery is pending, the supplied expected epoch and nonce match
current state, and the relevant keys are valid. Verify the current recovery
key's signature and the successor device's co-signature over the same bound
challenge. Bind account, successor device, successor recovery key, post-recovery
epoch, current nonce, and signed upper time bound. The successor recovery key must
differ from the current recovery key.

Require chain admission time to be at most the signed upper bound. Record the
successor entry at the next epoch and initial use counter, successor recovery
key, and deadline equal to the signed upper bound plus the veto window.

Submission does not itself replace device authority or advance `auth_nonce` in
the pinned circuit; it advances the round. A pending record prevents a second
submission until cancellation or finalisation.

### Cancel recovery

Require a live device authorisation and an existing pending record. Device
authorisation rolls the caller's entry and advances the nonce. Clear the pending
record without rotating the recovery key or removing the published recovery
material. If any check fails, all proposed effects roll back.

The pinned cancellation circuit has **no deadline check**. Cancellation remains
possible after the deadline until finalisation wins chain ordering. Do not infer
an expired cancellation right from comments describing a veto window.

### Finalise recovery

Require a pending record and chain time greater than or equal to its deadline.
Finalisation is permissionless and requires no fresh recovery or device signature.
It rechecks the pending recovery key's validity, increments the epoch, installs
the pending successor entry, sets the device count to one, replaces the recovery
key, invalidates the published recovery vector, clears pending state, and advances
the authorisation nonce and round.

The implementation-shaped program must preserve the pinned circuit's use of
`devices.insert(pending_entry)`: it does **not** clear existing entries. Setting
`device_count` to one must not be interpreted as changing set membership.

Finalisation does not require the current nonce to equal the nonce at submission.
Its authority comes from the accepted pending record. Ordinary device activity
can advance the nonce while recovery remains pending.

### Publish a recovery session

This device-authorised operation rotates the recovery key and published recovery
material. It is rejected while recovery is pending. Preserve that exclusion: a
pending record must not survive an unrelated replacement of its authorising
recovery key.

The recovery experiment can abstract the BUSS data payload while retaining the
publication guards relevant to acceptance. Any abstraction of session identifiers,
key freshness checks, or payload validation must be recorded in the manual review.

### Device and ordinary operations

Enrolment accepts an opaque derived entry and requires live device authorisation.
It must permit future-epoch entries in the implementation-shaped model because
the source does not enforce the client's current-epoch derivation obligation.

[`doAddDevice`](../src/Conformance/Recovery.agda) makes the source order explicit:
disclose the entry, check membership and assert absence, insert the entry, read
the device count, then write its checked `Uint<8>` increment.
[`AccountLedger`](../src/Conformance/AccountLedger.agda) supplies separate
`insertDevice` and bounded `writeDeviceCount` operations, not a compound
enrolment primitive. The model journal records membership, insertion, count read,
and count write in that order. An overflowing count write aborts the operation;
the tentative insertion is not committed.

Recovery's explicit `disclose` calls use the DSL's
[no-op annotation](contract-specification-dsl.md#2-the-small-effect-language).
They preserve correspondence sites but provide no information-flow guarantee.

Removal acts on a literal set entry, with the source's count and
surviving-authorising-device checks. Do not turn removal of one entry into
revocation of every entry associated with a key.
Removal and successor installation also use primitive ledger operations, with
explicit device-count writes. Application combinations are ordinary `Program`
helpers; the remaining representation and correspondence limits are listed at
the [ledger primitive boundary](conformance-recovery.md#ledger-primitive-boundary).

Ordinary authorised operations roll a credential and advance the nonce without
automatically cancelling pending recovery. Model representative operations by
their exact relevant state effects; justify the projection of unrelated payloads
rather than assuming that omitted operations cannot interfere.

## Intended properties

The following are the intended obligations. Checked local results cover the
subset below; statements about actual implementation history, cryptographic
intent, or resource replacement are not silently promoted to theorems.

| Checked route | Scope |
|---|---|
| `Conformance.RecoveryAuthority.accepted-recovery-trace-exclusion` | An actual accepted corrected finalisation resets an arbitrary old device set to a safe successor; every subsequent finite actual contract admission trace satisfying the explicit `TracePolicy` excludes compromised current-epoch device entries at every counter |
| `trace-compromised-call-impossible` | Under the same invariant/policy, an actual gated circuit using a compromised presented device key cannot evaluate successfully, even with a fresh signature |
| `Conformance.RecoveryExecution.submission-provenance`, `finalisation-provenance` | Actual DSL evaluation implies submission guard/signature equations and exact resulting state/journal; finalisation enacts the recorded pending successor |
| `submission-commits`, `finalisation-commits`, deadline theorems | Guard-premised actual transaction admission and chain-time obligations, including equality at the deadline |
| Cancellation, stale/pending/replay rejection, `rejection-is-atomic` | Seam-gated cancellation clears pending state; stale bindings and immediate cancelled/finalised replays reject; rejected admissions preserve committed account state |
| `positive-recovery`, `successor-authority`, `positive-rotation`, `rotation-commits` | Guard-premised non-vacuous recovery, recovered successor membership, and actual representative encryption-key rotation/admission |

The authority invariant fixes a `Compromised` key set and assumes `deviceEntry`
key separation across all epochs/counters. The unrestricted `Admissions` type
contains no authority policy or wallet premise. The separate `TracePolicy`
hypothesis in `RecoveryAuthorityDefinitions` requires `TransactionPolicy` at
every step, including rejected transactions: each certified input
must obey `InputPolicy`. Opaque enrolments may not encode compromised keys at
**any** epoch/counter; recovery submissions select uncompromised successor devices.
This is a theorem hypothesis, not a condition on contract admission or a claim
that a verifying signature proves human consent.
The old device set may be compromised before the resetting finalisation.

Proof definitions and assumptions are discoverable from the two advertised
modules and their separate `Definitions`/`Proof` modules. Positive guard records
expose signature equations, key-validity checks, finite-width bounds, and chain
conditions rather than assuming successful evaluation. The rotation guard also
records a concrete counter-width precondition which the existing natural-counter
model does not enforce.

### Submission provenance and binding

Every recovery finalisation enacts a pending record created by an accepted
submission authorised under the recovery authority current at that submission,
with successor possession and the required account/key/state/time bindings.
The record has not been cancelled or replaced in between.

**Status: locally checked; whole-history occurrence provenance remains open.**
`submission-provenance` exposes the signature-equation, binding and readiness
guards of a successful local submission; `submission-commits` connects it to
actual admission. `finalisation-provenance` exposes the consumed pending state.
These [checked claims](../src/Conformance/RecoveryExecution.agda) do not yet
prove that every finalisation in an arbitrary history traces to one particular
uncancelled submission occurrence. Authentication intent/unforgeability remains
an explicit external assumption, not a consequence of signature equations.

### Timing and cancellation safety

No finalisation commits before the recorded deadline. Equality is sufficient.
Given a submission at chain time `t`, accepted upper bound `u`, and window `v`,
`t <= u` and `deadline = u + v` imply the required minimum delay under the stated
non-overflow assumption.

Cancellation prevents that submission occurrence from being enacted. A subsequent
valid submission creates a separate obligation. After the deadline, cancel-first
and finalise-first executions must both be accounted for, with later operations
checked against the resulting state.

**Status: local deadlines, cancellation and replay checked; arbitrary-history
occurrence tracking remains open.** `submission-deadline`,
`finalisation-deadline`, `cancellation-clears`,
`cancelled-finalisation-rejected`, and the replay-rejection claims in
[`RecoveryExecution`](../src/Conformance/RecoveryExecution.agda) cover the
stated local guards/transitions. The gate executes cancel-first and
finalise-first interleavings; that is not a proof about every later history.

### Authority replacement

Immediately after finalisation, the successor is the sole device authority.
Until a subsequent authorised enrolment, another key cannot gain device authority
from a retained, duplicated, or future-epoch entry installed before finalisation.

This is stronger than stale-signature rejection. An old adversarial device may
know its key and sign a fresh request at the current nonce. The property must
exclude that request through authority state, not through a no-forgery assumption.

**Status: corrected-model trace exclusion checked under the explicit fixed
compromise, TracePolicy and key-separation assumptions of
[`RecoveryAuthority`](../src/Conformance/RecoveryAuthority.agda).**
`accepted-recovery-trace-exclusion` starts with an actual admitted finalisation
and covers subsequent accepted, rejected and stale-view admissions. The
source-shaped implementation/model attack has been **executed**, including
fresh post-finalisation old-key requests; a constructive Agda source-attack
reachability theorem is not claimed. Do not weaken the property or assume
honest adversarial enrolment to make it hold.

### Rejection preservation

Rejected submission, cancellation, finalisation, and device operations preserve
committed account state. This includes tentative credential consumption or nonce
increments performed before a later assertion fails. Reuse the DSL's atomicity
result rather than assuming separate ad hoc rollback rules.

**Status: checked at actual admission.** `rejection-is-atomic` in
[`RecoveryExecution`](../src/Conformance/RecoveryExecution.agda) binds the
existing DSL atomicity theorem. The harness also executes late-abort rollback
cases; it does not replace the theorem with a simulator-only rollback rule.

### Positive execution

An authorised, uncancelled pending recovery can finalise at or after its deadline
when admitted, including when the finalising caller is unrelated to the account.
The successor can then authorise a representative operation.

This prevents vacuous safety by universal rejection. It does not imply eventual
recovery on every run, immediate spendability of assets, recovery of private coin
data, or fairness of transaction inclusion.

**Status: checked local evaluation and admitted execution, and exercised.**
`positive-recovery`, `submission-commits`, `finalisation-commits`,
`successor-authority`, and `rotation-commits` in
[`RecoveryExecution`](../src/Conformance/RecoveryExecution.agda) establish a
successful recovery and successor operation under explicit readiness,
deadline, bounded-counter and signature-equation premises. The gate and
repaired simulator execute positive successor operations as well.

## Reachable future-epoch counterexample

Construct the attack from a legitimate post-bootstrap state, not a pre-populated
malicious set:

1. At epoch `e`, the adversary controls an enrolled device key `A`.
2. Using a valid ordinary enrolment operation, it adds an entry for `A` at epoch
   `e + 1` and an available use counter. The entry is dormant at epoch `e`.
3. The legitimate recovery authority and successor `S` authorise a recovery
   submission against the current state, with `S` distinct from `A`.
4. Chain time reaches the deadline and recovery finalises. The source-shaped
   transition increments the epoch and inserts `S`'s entry, retaining the planted
   entry for `A`.
5. Without any successor-authorised re-enrolment, the adversary signs a fresh
   operation under `A` at the current nonce. Its planted entry now matches the
   current epoch.

The target result is acceptance of the adversary's operation after recovery,
contradicting authority replacement. No signature forgery, signature replay, or
commitment collision is needed in the symbolic experiment.

The proof must establish reachability through the actual modelled guards,
transaction atomicity, and fresh nonce values. The informal source argument and
previous symbolic projection do not discharge these obligations.

The corrected model replaces the device-entry set with the successor singleton
at finalisation. The concrete repair instead stamps opaque map entries with the
contract-observed enrolment epoch; no Compact set-clearing operation is assumed.
The current-generation authority projection connects the designs in executable
conformance, but is not a checked refinement or a deployment/state-migration
result. See [the repair boundary](conformance-recovery.md#concrete-repair-boundary).

The corrected model must admit legitimate recovery and reject the same attack.
It must not achieve exclusion by disabling all post-recovery operations.

## Protocol and observation boundary

Account operations use the DSL's `Contract` API and its `Protocol.toProtocol`
adapter. A future resource-replacement theorem would additionally compose
explicit authentication/ZK and blockchain resources; those assumptions are not
supplied by certified transactions or by the upstream signature example.

Use categorical-crypto's existing concrete `UCSetup`. Follow the distinction in
`ChimericLedger.Property` and `Transfer` between local/internal properties and
interface-observable experiments.

Internal proofs may use submission provenance and ghost history. Observable
experiments must use only the chosen interface's information: requests the
experiment supplies, public chain observations, and transaction outcomes. Do not
add an omniscient public authorisation oracle or disclose honest secret keys to
make property transfer easy.

The future-epoch strategy provides a concrete observable test: plant an entry,
observe finalisation, attempt the old-key operation, and return whether it was
accepted. For a complete distinction, establish the legitimate recovery prefix
and its observations in both the source-shaped and corrected/specification
systems. Record the strategy's interaction bound for the quantitative API.

History-dependent properties need a stateful observer. The existing
`monitorᴹ` accumulates a predicate on a request/response pair; do not assume it
alone supplies arbitrary history analysis. Reuse upstream event-bound and
observation machinery where its interface fits.

The branch's `PrHit` samples activation boundaries and measures completed-run
hits; a run that hits and then diverges does not contribute in the same way as a
prefix-reachability event. Prove transition invariants for finite reachable
prefixes, and make the counterexample strategy terminate after its verdict.
Do not infer unconditional progress from a safety probability bound.

Observable properties may transfer under suitable resource emulation. Internal
state safety needs an additional observation-adequacy argument. No theorem should
claim that arbitrary internal authority state transfers merely from UC
indistinguishability. Cryptographic replacement results remain conditional until
the corresponding emulations and interface bindings are proved.

## Acceptance scenarios

| Scenario | Required observation or obligation |
|---|---|
| Valid submission, eligible finalisation, successor use | Successful non-vacuous recovery, with unrelated finalising caller allowed |
| Finalise before, at, and after deadline | Reject before; permit equality and later eligible calls |
| Cancel before finalise | Clear that pending submission and prevent its enactment |
| Cancel after deadline but before finalise | Permit cancellation under the pinned semantics |
| Finalise before old-device cancellation | Recheck cancellation against post-recovery authority; the corrected model excludes old authority |
| Cancel then replay old submission | Reject the stale authorisation; separately allow a freshly authorised submission |
| Ordinary device use while pending | Advance nonce without silently invalidating the pending record |
| Publish session while pending | Reject and roll back the complete operation |
| Wrong account, key, epoch, nonce, or time bound | Reject under the relevant binding and chain assumptions |
| Failed operation after tentative credential roll | Preserve committed account state |
| Future-epoch enrolment followed by recovery | Source-shaped counterexample; corrected-model exclusion |
| Ordinary encryption-key rotation | Remain available without invoking recovery |

## Implementation order and completion criteria

1. Establish the small transactional DSL, operation replay laws, and preliminary
   lock/device-operation milestones described in the
   [DSL design](contract-specification-dsl.md). Its separate Merkle privacy
   exercise does not enlarge this recovery authority claim.
2. Define the account state, authentication/chain interfaces, and source-shaped
   recovery and interfering operations. Record the manual source correspondence
   and abstraction assumptions.
3. **Executed; source reachability proof not claimed:** the future-epoch attack
   has an accepted fresh old-key operation in the source simulator/model and
   is rejected by the corrected model and repaired simulator.
4. **Checked locally and at admission:** corrected-model trace authority
   exclusion, readiness/provenance guards, deadlines, immediate cancellation,
   replay rejection, atomicity and positive execution are checked in the
   advertised modules. Whole-history submission-occurrence provenance remains
   open; authentication/key-separation/compromise assumptions are explicit.
5. **Actual-admission connection checked; UC/resource replacement open:** the
   results use the existing protocol relation and admission/refinement
   machinery. They do not prove a recovery UC replacement theorem, verified
   compiler refinement, or grant-authority exclusion.

The original first milestone's attack/rejection/positive-recovery executions
are now recorded by the gate. Corrected-model safety and positive-execution
theorems are independently checked in Agda; the source attack is executable
evidence, not a newly postulated or advertised source reachability proof.

Completion evidence should identify checked Agda modules, executed model
scenarios, the implementation revision reviewed, and remaining cryptographic or
chain assumptions. Manual correspondence remains the link to the actual
circuit; neither model execution nor a checked theorem is an implementation
acceptance test or a verified compilation result.

# Recovery authority-replacement specification

## Status and objective

This document specifies the first experiment using the
[contract specification DSL](contract-specification-dsl.md): recovery-driven
replacement of account authority. It records a proposed model and proof plan,
not an implemented Agda protocol or an established security theorem about the
Passport contract.

The experiment compares an implementation-shaped account program with an intended
authority-replacement specification. It must support both legitimate recovery
and adversarial interleavings. A model that simply assumes that incrementing an
epoch revokes every old device would hide the principal counterexample target.

The property develops [P5′ in the security-properties document](security-properties.md#p5--recovery-driven-authority-replacement).
That document distinguishes proposed obligations from existing mechanised
accounting results. This experiment is not an extension of the balance-routing
proof by assumption: it introduces concrete account-authority behaviour.

### Reference versions and evidence

Use categorical-crypto's `protocol-rewrite` branch temporarily, with inspected
reference `579b54e72d453fd6287f05f90a32b933b8474390`, and its existing concrete
`UCSetup`. The DSL design records the relevant interfaces and assurance boundary.

The implementation reference is Passport commit
`5d12798321d3daba37b1da90162ee1468daf38a6`, in particular:

- [Device authentication](https://github.com/midnightntwrk/passport/blob/5d12798321d3daba37b1da90162ee1468daf38a6/contract/contracts/account.compact#L830-L906).
- [Device enrolment and future-epoch commentary](https://github.com/midnightntwrk/passport/blob/5d12798321d3daba37b1da90162ee1468daf38a6/contract/contracts/account.compact#L1264-L1344).
- [Recovery-session publication](https://github.com/midnightntwrk/passport/blob/5d12798321d3daba37b1da90162ee1468daf38a6/contract/contracts/account.compact#L2650-L2738).
- [Recovery submission, cancellation, and finalisation](https://github.com/midnightntwrk/passport/blob/5d12798321d3daba37b1da90162ee1468daf38a6/contract/contracts/account.compact#L2754-L2878).

The sibling checkout inspected during planning was at `68bbde28`, which has no
recovery circuit. It is not the recovery implementation reference. Pin the
reference used for manual correspondence review rather than inferring behaviour
from whichever revision happens to be checked out.

Source inspection identifies a future-epoch counterexample candidate below. A
small symbolic projection of the membership and epoch rules accepted the planted
old-key entry after finalisation. This was neither Compact execution nor a
mechanised proof; the proposed experiment must establish the full reachable trace
and its observable consequence.

## Scope and architecture boundary

Model one account after bootstrap, at the account custody contract's authority
boundary. The account identifier remains explicit so cross-account binding can
be stated even though the main experiment involves one account.

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

For the authority-exclusion experiment, the legitimate recovery authority and the
successor device key remain uncompromised. The successor does not subsequently
authorise re-enrolment of the adversary. Compromise of the old device is allowed:
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

Removal acts on a literal set entry, with the source's count and
surviving-authorising-device checks. Do not turn removal of one entry into
revocation of every entry associated with a key.

Ordinary authorised operations roll a credential and advance the nonce without
automatically cancelling pending recovery. Model representative operations by
their exact relevant state effects; justify the projection of unrelated payloads
rather than assuming that omitted operations cannot interfere.

## Intended properties

These are proposed statements, not checked theorem names or results.

### Submission provenance and binding

Every recovery finalisation enacts a pending record created by an accepted
submission authorised under the recovery authority current at that submission,
with successor possession and the required account/key/state/time bindings.
The record has not been cancelled or replaced in between.

### Timing and cancellation safety

No finalisation commits before the recorded deadline. Equality is sufficient.
Given a submission at chain time `t`, accepted upper bound `u`, and window `v`,
`t <= u` and `deadline = u + v` imply the required minimum delay under the stated
non-overflow assumption.

Cancellation prevents that submission occurrence from being enacted. A subsequent
valid submission creates a separate obligation. After the deadline, cancel-first
and finalise-first executions must both be accounted for, with later operations
checked against the resulting state.

### Authority replacement

Immediately after finalisation, the successor is the sole device authority.
Until a subsequent authorised enrolment, another key cannot gain device authority
from a retained, duplicated, or future-epoch entry installed before finalisation.

This is stronger than stale-signature rejection. An old adversarial device may
know its key and sign a fresh request at the current nonce. The property must
exclude that request through authority state, not through a no-forgery assumption.

The source-faithful model is expected to refute this property through the
future-epoch candidate below. Do not weaken the property or assume honest
adversarial enrolment to make it hold.

### Rejection preservation

Rejected submission, cancellation, finalisation, and device operations preserve
committed account state. This includes tentative credential consumption or nonce
increments performed before a later assertion fails. Reuse the DSL's atomicity
result rather than assuming separate ad hoc rollback rules.

### Positive execution

An authorised, uncancelled pending recovery can finalise at or after its deadline
when admitted, including when the finalising caller is unrelated to the account.
The successor can then authorise a representative operation.

This prevents vacuous safety by universal rejection. It does not imply eventual
recovery on every run, immediate spendability of assets, recovery of private coin
data, or fairness of transaction inclusion.

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

Compare this with a corrected model that replaces the device-entry set with the
successor entry at finalisation. This is a specification-level correction and
comparison target, not a claim that clearing a Compact ledger set is available or
cheap. A concrete repair may instead need an enrolment-generation/schema change;
its implementation design and deployment are outside this experiment.

The corrected model must admit legitimate recovery and reject the same attack.
It must not achieve exclusion by disabling all post-recovery operations.

## Protocol and observation boundary

Implement account operations in the DSL and reuse its interpreter into
`Protocol`. Compose with ideal authentication/ZK and blockchain resources first.
These resources and their assumptions must be explicit; the upstream signature
example is not a completed off-the-shelf signature realisation proof.

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
3. Encode the reachable future-epoch attack as an explicit strategy and establish
   its accepted old-key operation and observable verdict.
4. State the intended authority-replacement specification and prove its safety and
   positive-execution obligations. Prove the corrected model satisfies the same
   exclusion property the source-shaped model violates.
5. Connect the local results to the existing protocol observation and UC machinery,
   separating proved model results from conditional resource-replacement claims.

The first substantive milestone is a reachable attack against the source-shaped
model, rejection of that attack by the corrected/specification model, and a
successful legitimate recovery in the same framework. There must be no newly
postulated security result standing in for these proofs.

Completion evidence should identify checked Agda modules, executed model
scenarios, the implementation revision reviewed, and remaining cryptographic or
chain assumptions. Manual correspondence remains the link to the actual
circuit; neither model execution nor a checked theorem is an implementation
acceptance test or a verified compilation result.

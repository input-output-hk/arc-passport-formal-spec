# Conformance testing: plan

Status: full-account local execution comparison against pinned Passport `main`,
plus the earlier custody/recovery DSL and monitor work. These have distinct
targets and proof boundaries. The [spike report](conformance-spike.md) and
[recovery assurance](conformance-recovery.md) retain the historical evidence;
they are not evidence about the newer target.

## Pinned-main full-account execution

Target: [`fc19e471536febb2133f20e817847251622dcdf5`](https://github.com/midnightntwrk/passport/tree/fc19e471536febb2133f20e817847251622dcdf5),
the latest fetched `main` when this work began.
[`passport-main-pins.json`](../conformance/harness/passport-main-pins.json)
records the source, generated artefacts, loaded dependency trees and Compact
0.35.0 identities. The runner checks the constructor plus the exact exported
impure-circuit surface and fails on pin or surface drift.

### Reading route and scope

Start at [`Passport`](../src/Passport.agda), which imports both routes and their
statement definitions explicitly.

1. [`Passport.Account`](../src/Passport/Account.agda): deployment, atomic
   transaction results and the full-state `Transition` relation.
2. [`FullAccountTypes`](../src/Conformance/FullAccountTypes.agda): values, ledger
   state, execution/effects, the effect monad and primitive interface.
   [`FullAccountLayouts`](../src/Conformance/FullAccountLayouts.agda) names the
   Compact tuple fields.
   [`FullAccountExecution`](../src/Conformance/FullAccountExecution.agda) supplies
   the accepted-execution witnesses used in the security statements.
   [`FullAccountCrypto`](../src/Conformance/FullAccountCrypto.agda) specifies
   typed preimages and authentication checks;
   [`FullAccountBody`](../src/Conformance/FullAccountBody.agda) and
   [`FullAccountGrant`](../src/Conformance/FullAccountGrant.agda) contain the
   source-ordered circuit execution.
   [`FullAccount`](../src/Conformance/FullAccount.agda) dispatches all entrypoints,
   validates the raw ABI and defines the 25-field ledger schema.
3. [`FullAccountProperties`](../src/Conformance/FullAccountProperties.agda):
   rejection atomicity and determinism by construction of the transition wrapper,
   plus rejection of old-epoch/old-generation records by the executable
   `validateGrantRecord` guard called by `authenticateGrant`.
   Implementations are separate in
   [`FullAccountProof`](../src/Conformance/FullAccountProof.agda).
   The grant claims assume the stated ledger advance; they do not prove that every
   successful compiled recovery or revocation performs it.
4. [`LifecycleProperties`](../src/Midnight/ContractDSL/LifecycleProperties.agda),
   [`SymbolicSigningProperties`](../src/Midnight/ContractDSL/SymbolicSigningProperties.agda)
   and [`AdversarialLifecycleProperties`](../src/Midnight/ContractDSL/AdversarialLifecycleProperties.agda):
   rooted histories, symbolic signing knowledge and their interleaving.
5. The [authorization statement map](#authorization-statement-map): source
   guards, dispatcher/request correspondence, provenance and recovery occurrences.
6. [Local history invariants](#local-history-invariants): grants-map mutations,
   accumulated spending, revocation/recovery exclusion, unshielded accounting
   and restricted outsider preservation.
7. [`VMProperties`](../src/Conformance/VMProperties.agda): explicit statements
   and separate proof references for interpreter/admission soundness, codec
   round trips and typed map/set correspondence. Their definitions are in
   [`VM`](../src/Conformance/VM.agda),
   [`VMEncoding`](../src/Conformance/VMEncoding.agda) and
   [`VMAccount`](../src/Conformance/VMAccount.agda). The interpreter uses the
   existing ledger DSL. These are local primitive results, not whole
   generated-circuit lowering proofs.
8. [`full-main.ts`](../conformance/harness/full-main.ts): runs the generated
   constructor/circuits and real production witnesses independently, invokes
   the compiled Agda account evaluator and concrete formal VM, and compares
   their observations.

The full-account evaluator describes local source execution, including immediate
time/context reads and native asset descriptions. It is not an extension of
the recovery slice's certified-transaction admission API: `Account.Transition`
does not certify a delayed on-chain replay. The earlier `Program`/`Contract`
admission theorems therefore do not automatically apply to this new relation.
`Transition` is the graph of the `step` function; determinism follows from that
equation. Rejection atomicity follows from `transaction` returning the original
state. These structural results are not evidence for circuit-specific invariants
or for the compiled implementation's transaction semantics.

### Deployment-rooted local histories

[`Lifecycle`](../src/Midnight/ContractDSL/Lifecycle.agda) is a universe-polymorphic
relational interface, independent of Passport, the VM and deterministic execution.
It separates the deployment-root relation from runtime invocation. `Deploy`'s
outcome records an instance-defined creation observation; interpreting roots as
successful creation, and excluding failures, is the instance's responsibility.
A `History` retains that deployment input/context/result and a standard-library
`Star` trace of labelled steps, each recording its environment, call and outcome. One identity indexes
the entire history. Generic runtime calls may have arbitrary supplied semantics;
the framework alone does not prohibit a call from resetting application state.

[`LifecycleProperties`](../src/Midnight/ContractDSL/LifecycleProperties.agda)
states conditional trace/history invariant rules, with proofs in
[`LifecycleProof`](../src/Midnight/ContractDSL/LifecycleProof.agda). The invariant,
its establishment by deployment and its preservation by steps are parameters,
not assumptions discharged for Passport.

[`AccountLifecycle`](../src/Passport/AccountLifecycle.agda) supplies the full-account
instance. Its primitive backend remains arbitrary. Invocation reuses the existing
full-state `Account.Transition` relation at the context formed from the history
identity and step environment. `RuntimeCall` carries membership in `runtimeNames`
from [`FullAccount`](../src/Conformance/FullAccount.agda), which lists only the
runtime entrypoints; the constructor entry is added separately to the full
entrypoint list. Runtime traces therefore retain refusals produced by known
entrypoints (argument, context, state, semantic or primitive), but cannot record
a constructor call, an unknown name or the dispatcher's unknown-circuit refusal.
`start` returns either a deployment error or a rooted history; `run` constructs
a trace from a state, and generic `extend` attaches it to a history with that
final state. A trace from an arbitrary state alone is not deployment-rooted.

The account environment supplies time, caller and coin witness; the fixed history
identity supplies `Context.self`. No monotone-time, witness-honesty, signature
security, fairness or native-admission assumption is imposed. Policies can later
be predicates on histories, and primitive laws can be explicit theorem parameters.
These are finite local histories, not ledger admission/adoption traces, infinite
executions or leakage projections. The [authorization layer below](#contract-level-authorization-evidence)
adds account-specific predicates and statements. The existing raw evaluator remains
an evaluation interface, not an unrestricted lifecycle relation.

### Symbolic signing and adversarial histories

[`SymbolicSigning`](../src/Midnight/ContractDSL/SymbolicSigning.agda) supplies a
generic symbolic model, independent of Passport and any particular signature
scheme. An `Interface` supplies key, request and message types, initial ownership
and an encoder. Each instance chooses how its request represents the target,
operation, arguments and authorization context. The encoder is **not assumed
injective**.

The selected symbolic policy is:

- Honest keys begin uncompromised; attacker-owned valid abstract keys are
  controlled from the outset. Key ownership is not current contract authority.
- Approval is a trusted abstract honest-party input, not an attacker action or
  proof of human/UI consent. Honest signing requires prior approval of the exact
  key/request pair. Approvals persist and may be used repeatedly.
- Compromise is explicit and permanent. A controlled key may sign arbitrary
  messages; an honest key may still perform approved signing after compromise.
- Signature tokens represent key/message capabilities, not unique signature
  bytes. Constructing a token value does not establish its availability.
  All issued tokens remain available for delay, reordering and replay.
- Recovery and successor keys use the same ownership/compromise model. Guardian
  exchanges, malformed concrete keys, curve/subgroup security and computational
  reductions are outside this model.

[`SymbolicSigningProperties`](../src/Midnight/ContractDSL/SymbolicSigningProperties.agda)
states checked persistence of control, approvals and signature knowledge.
For a trace from `initial`, every available token has a currently controlled key
or an actual honest signing event backed by prior approval. For an honest key
still uncompromised, only the honest-issuance alternative remains. This is
**message-level provenance**: with a colliding encoder, the approved request
need not be the request a later call intends.

A signing `Transition` records an event, its `Permitted` evidence and the state
change given by `apply`. The optional
[`SymbolicSigningExecution`](../src/Midnight/ContractDSL/SymbolicSigningExecution.agda)
supplies executable decisions and `step` when key/request/message equality is
decidable; `certify` converts successful execution into a model transition.
The semantic model and its property statements do not depend on those decisions.

[`AdversarialLifecycle`](../src/Midnight/ContractDSL/AdversarialLifecycle.agda)
interleaves signing transitions with the original lifecycle invocations.
`required before environment call` lists the tokens needed to construct an attempted
call from its before-state; invocation requires their availability, leaves them
available and retains the original outcome, including refusal. It adds no live-authority or acceptance
test. A rooted joint history retains the original deployment witness and starts
with empty signing knowledge. Its projections preserve the original contract
history and an initial-rooted signing trace.
[`AdversarialLifecycleProperties`](../src/Midnight/ContractDSL/AdversarialLifecycleProperties.agda)
states projection compatibility with history extension and lifts message-level
provenance to available and required tokens.

[`AccountSecurity.Histories`](../src/Passport/AccountSecurity.agda) supplies the
concrete account instance. Its `requiredTokens` uses the current ledger, actual
source request encodings and source verification gates, rather than a caller-chosen
token list. Each valid signature requires its key/digest token; invalid signatures
contribute none. A refused call can still contain valid signatures and therefore
require tokens. Activation, deposits and finalisation require no signature token.

This is an **ideal signing interpretation**, not a proof that arbitrary concrete
bytes can be produced only with the corresponding capability. The generic joint
model alone still implies no accepted-call safety; that needs the source guard
evidence below.

### Contract-level authorization evidence

#### Authorization statement map

Follow these statement modules in the order used by `Passport.agda`; each links
its definitions and separate proof implementation.

- [`FullAccountSignatureBindingProperties`](../src/Conformance/FullAccountSignatureBindingProperties.agda):
  exact source encodings, verifier extraction and conditional request provenance.
- [`FullAccountDeviceSecurityProperties`](../src/Conformance/FullAccountDeviceSecurityProperties.agda):
  live device authorization, bootstrap, state advancement and immediate replay boundaries.
- [`FullAccountGrantSecurityProperties`](../src/Conformance/FullAccountGrantSecurityProperties.agda):
  grant guards, presented caps and actual final settlement records.
- [`FullAccountRecoverySecurityProperties`](../src/Conformance/FullAccountRecoverySecurityProperties.agda):
  submission, cancellation, finalisation and pending-record effects.
- [`AccountRequestDispatchProperties`](../src/Passport/AccountRequestDispatchProperties.agda):
  the checked bridge from accepted runtime dispatch to actual source requests,
  required tokens and their availability.
- [`AccountSecurityProperties`](../src/Passport/AccountSecurityProperties.agda):
  separate per-path request computations and request-view provenance, composed
  with the dispatcher bridge rather than one whole-account evidence bundle.
  For its `Encodes` premise, the signature-binding module's `authorisation-message`
  uses device/grant challenge and verification evidence; `recovery-message`
  uses submission tag/hash evidence for both the recovery and successor keys.
- [`AccountRecoveryOccurrenceProperties`](../src/Passport/AccountRecoveryOccurrenceProperties.agda):
  actual submission occurrences and finalisation over deployment-rooted histories.

#### Assumptions and interpretation

These statements separate three obligations:

1. **Source execution.** Device, grant and recovery predicates describe the guards,
   signed requests and state updates of the actual full-account evaluator.
   Signature binding uses its challenge functions, k256 envelopes, WebAuthn hashes
   and recovery preimage, with equality statements connecting encoding to execution.
2. **Symbolic provenance.** Account histories require available tokens for complete
   source hash-and-sign requests. Message provenance distinguishes attacker-controlled
   keys from approved honest issuance. Request-level provenance additionally takes
   `IssuedAgreement`: the selected request fields agree with relevant honest
   issuances in this trace. It is not universal hash injectivity.
3. **Concrete realization and adoption.** Neither is supplied by the symbolic
   interpretation. Raw-digest ECDSA or Schnorr equation success is not an
   unforgeability theorem. A realization must account for effective-digest
   equivalence, including Schnorr reduction modulo the group order and ECDSA digest
   reduction. Existing tokens remain replayable; source state guards, not token
   consumption or signature-byte uniqueness, must prevent a second execution.

#### Caps, commitments and pending histories

Grant cap guards compare the presented previous spend and current amount.
`SpentOpeningsAgree` is an explicit agreement premise for the two relevant spent
openings, allowing those local numerical facts to be read as an accumulated total.
It is not a proof of SHA-256 binding or, by itself, a whole-history cap invariant.
Matching pending cells at two endpoints is not proof that a submission occurred
in the history or remained uncancelled between them. The checked
`AccountRecoveryOccurrenceProperties.pending-origin` and `Joint.joint-pending-origin` instead
identify an actual accepted submission in the deployment-rooted account trace,
followed only by refusals or accepted calls preserving the pending cells.
`finalisation-enacts-occurrence` ties the enacted successor and recovery key,
and the checked deadline, to that occurrence, excluding an intervening accepted submission,
cancellation or finalisation. The lower-level recovery endpoint-matching
statements are not used as substitutes for this history claim.

Device membership and the boot, grant-id, object and recipient checks are
commitment-level facts. Reading equal digests as the intended configured key,
asset or recipient additionally requires agreement of the relevant openings.
Those interpretations are not consequences of the numerical cap guards or of
signature provenance alone.

#### Native execution evidence

A compiled native authorization audit exercised **231 calls**: the existing 225
conformance fixtures plus six represented-state cumulative-cap boundaries
(equality and one above, for each curve). All **147 extracted signature tokens**
matched successful native verification equations or ECDSA checks over their
source-computed digests; complete outcomes, states and effects matched the fixtures.
The six added cap cases are synthetic represented states, not claimed reachable
grant histories. The audit made 3,437 primitive calls. A fresh full correspondence
run separately covered all 53 entrypoints with 225 observations and zero mismatches.

These results do not authenticate environment time, callers or coin witnesses,
establish guardian consent, model human approval, prove fairness, or bridge local
execution to ledger adoption. No such assumptions are silently added.

### Local history invariants

[`GrantEffectsProperties`](../src/Passport/GrantEffectsProperties.agda) extracts
actual issuance, revocation and settlement changes and classifies runtime
grants-map effects. Unlike `grant-final-state`'s identifier lookup and field facts,
its spend mutation describes the whole final map, supporting history induction.
The intermediate operation-body state may differ in other cells after device
authorization, but its grants cell agrees with the original before-state.

[`GrantSpendingProperties`](../src/Passport/GrantSpendingProperties.agda) proves
accumulated spending stays within each issuance cap, for current and archived
episodes, and that stored commitments/nonces match the history.
`HistoryAgreement` assumes only agreement of relevant spent-opening pairs;
initial zero spending and preservation are derived from source execution.
Reissue/reset archives earlier episodes rather than discarding their totals.
The native smoke covered 36 observations across six issuance episodes and all
three signing schemes, including exact caps, above-cap refusals and reissue.

[`RevocationExclusionProperties`](../src/Passport/RevocationExclusionProperties.agda)
derives nondecreasing source counters, strict recovery/revoke-all advances and
strictly ordered issuance stamps. Revoked identifiers remain disabled until
actual matching issuance occurrences; stale epoch/generation records remain
excluded. After recovery, live device entries originate in the installed
successor or actual subsequent insertion occurrences. Excluding a queried
opening requires `RelevantEntrySeparation` against precisely those entries,
not universal hash injectivity or an assumed authorization invariant.
Explicit reissue/re-enrolment remains possible.
The focused native smoke covered 22 observations, including those positive
reauthorization controls, with 63 counter comparisons and five rollback refusals.

[`UnshieldedAccountingProperties`](../src/Passport/UnshieldedAccountingProperties.agda)
connects actual final balance maps to the source's declared transfer effects.
For each color, every deployment-rooted history satisfies
`stored balance + cumulative sends = cumulative receives`. The proof derives
deposit bounds, withdrawal funding and other-entrypoint preservation from the
evaluator; it assumes no accounting-preservation callback. Refused attempts
preserve state and contribute no committed effects. This is a P12 precursor,
not authenticated ledger accounting, fee attribution or snapshot reporting.
Its native smoke covered 42 scenarios on all three signing schemes.

[`OutsiderPreservationProperties`](../src/Passport/OutsiderPreservationProperties.agda)
covers accepted permissionless deposits and refused attempts. Such extensions
preserve stored authority/recovery resources and enrolled device membership,
while each accepted deposit consumes one round. The statements expose that exact
cost and the finite Uint64 budget; successful bootstrap and finalisation are
explicitly excluded. The native smoke covered 15 reachable observations.
No availability, fee, proving-resource or liveness guarantee follows.

### Concrete execution comparison

The harness checks complete ledger state and outputs, exact refusal classes
and assertion messages, ordered ledger/context observations decoded from
implementation-produced VM operations, declared assets, recipients, shielded
commitments/nullifiers, Zswap descriptions and observed `held_coin` witnesses.
Original native VM transcripts are replayed with their caches and gas checks;
the separate one-op observation pass clears caches only to expose reads.
Constructor queries are captured from actual execution, with default-field
allocations distinguished from circuit assignments. No model-generated journal
is substituted for a concrete transcript.

[`VMConcrete`](../src/Conformance/VMConcrete.agda) supplies canonical
little-endian atom semantics; the compiled `VMMain` executes the original
concrete instruction sequence without calling the native opcode interpreter.
Every resulting VM root and strength flag is compared with native VM replay.
Map entry order alone is normalized.

The runtime's `createZswapOutput` also registers commitment/output-index pairs
**outside** VM execution. These are captured separately: all other context
fields must remain unchanged, and the complete before/after index maps must
equal the registrations derived from the model's independently computed
output commitments. They are neither discarded from comparison nor credited
to VM replay. This checks local descriptions, not Merkle qualification or
asset ownership.

### Exercised evidence

The integrated run of the working tree reported:

| Measure | Result |
|---|---:|
| Constructor and impure circuits | 53 |
| Concrete/model observations | 225 |
| Entrypoints missing successful or refused cases | 0 |
| Divergent observations | 0 |
| Fine-grained primitive calls | 1684 |

Cases cover bootstrap, all three authentication arms, device lifecycle, inbox,
unshielded custody, shielded exact/change sends to keys and contracts, grant
issuance/revocation/generation/expiry, recovery and post-recovery old authority.
Maximum-epoch/use-counter cases are explicitly synthetic represented states,
not claimed to have been reached by executing billions of transitions.
The JSON report records actual calls, signatures, witnesses, states, effects
and transcripts; signatures are not made deterministic by replacing production
signers. This is finite execution evidence, not universal equivalence.

Persistent SHA-256 and typed fixed-width preimage encoding are implemented
independently in [`independent-hash.ts`](../conformance/harness/independent-hash.ts),
including coin commitment/nullifier recipes used by the model backend.
The k256 published device-entry vector and integer/field/byte-width boundaries
have separate regression checks. Elliptic-curve arithmetic, signature
verification and Poseidon remain explicit runtime primitive dependencies.
The executable transport is non-`--safe`; the model and property modules
retain `--safe --without-K`.

### Reproduce and remaining boundary

Use a checkout of the exact target, its lockfile-installed dependencies, and
Compact 0.35.0 generated artefacts. Set `FULL_IMPL_DIR` to that checkout's
`contract` directory and `FULL_COMPACT_DIR` to the compiler directory. Then,
from the specification checkout:

```sh
env LC_ALL=C.UTF-8 pagda --useUntracked false check \
  src/Conformance/FullAccountMain.agda -- \
  --compile --compile-dir=_build/full-account +RTS -M3G -H1G -RTS
env LC_ALL=C.UTF-8 pagda --useUntracked false check \
  src/Conformance/VMMain.agda -- \
  --compile --compile-dir=_build/formal-vm +RTS -M3G -H1G -RTS
export FULL_MODEL_BIN="$PWD/_build/full-account/FullAccountMain"
export FORMAL_VM_BIN="$PWD/_build/formal-vm/VMMain"
export FULL_REPORT="$PWD/_build/full-account/report.json"
"$FULL_IMPL_DIR/node_modules/.bin/tsx" conformance/harness/full-main.ts
"$FULL_IMPL_DIR/node_modules/.bin/tsx" --test \
  conformance/harness/independent-hash.test.ts conformance/harness/vm-formal.test.ts
```

`FULL_CAPTURE_ONLY=1` is implementation capture **without** model conformance;
it must not be reported as agreement. The full-account wire is `full-v1`,
not the recovery monitor's `monitor-v1` or its Haskell/C ABI.

Compilation with `--skip-zk --feature-zkir-v3` and local runtime execution
succeeded. Full key generation and the local proof server could not fetch
`https://srs.midnight.network/bls_midnight_2p10`: sandbox policy returned
“Approval required for srs.midnight.network:443.” The cache was empty.
The local node became healthy, but that is not proof generation, asset
authentication or transaction admission evidence.

Still outside this evidence: universal Compact-to-Agda refinement, a proof
that the pinned WASM implements the formal VM semantics, authenticated native
effects and ZK/on-chain execution. The npm WASM package supplies no source
`gitHead`; its binary identity is pinned, not its source correspondence.
Historical recovery pins and the enrolled gate lock remain unchanged.

## 1. Goal

Compare the Passport implementation (`midnightntwrk/passport`, `contract/`) with
the executable Agda model on the behaviours that model covers. Conformance
supplements manual source correspondence with exercised, repeatable observations;
it does not replace correspondence for unexercised inputs or prove equivalence.

What conformance testing can establish: that on every exercised input sequence the
implementation's observable transitions (verdict, failure kind, resulting ledger state,
emitted signature material) are the ones the model prescribes. What it cannot establish:
the theorems themselves (those stay proofs over the model), distributional/privacy claims
(section 4.5), and anything about the proving system (the implementation side runs without
proofs).

## 2. Ideas

### 2.1 Two oracles

- **Oracle 1 — execute and compare.** The model is executable. Feed the same input sequence
  to the compiled model and to the implementation; compare outputs and post-states step by
  step. Strongest: detects any deviation on the exercised inputs. Requires the model to be a
  function of its inputs, including randomness.
- **Oracle 2 — decide an observed transition.** The model exposes
  `acceptable : State → Transition → State → Bool`. `Transition` includes the
  raw invocation or frozen candidate, account/time context and observed outcome.
  The implementation runs independently; monitoring needs no control over its
  randomness. It checks whether the supplied triple conforms, including accurately
  observed rejection or abort, rather than merely whether a transaction succeeded.

Both transition oracles are implemented. The
[runtime monitor](conformance-recovery.md#runtime-transition-monitor) also has
versioned bidirectional serialization, a Haskell API and a C ABI. Its certificates
still use model journals; successful simulator calls independently verify
implementation-produced VM transcripts. That is not a translation into model
events (see WP1), nor does VM replay authenticate declared coin effects.

### 2.2 Randomness is an input

Every coin flip in a model protocol (`CategoricalCrypto.Protocol.Calls.coin`) is read from
an externally supplied bit stream, and the implementation's randomness source is made
injectable so the harness drives both with the same bits. Then both sides are deterministic
functions of `(bits, calls)` and oracle 1 applies to randomised protocols. The spike validated
this on the client signer: 145 k bits per 40-step run, consumed bit-exactly by both sides.

Where the implementation's randomness cannot be captured (proof-server randomness, library
RNGs without injection), the random artefact is treated as an opaque witness input: the
harness obtains it from the implementation and feeds it to the model, which only verifies.

### 2.3 Primitives are parameters

The specification stays abstract over cryptography: a `Primitives` record (hash variants,
curve operations, decidable equalities) is a module parameter of the model. The proofs keep
using symbolic instances (constructor-injective digests); the conformance build instantiates
the same modules with real primitives. The instantiation lives in a non-`--safe` `Main`
module, because `{-# COMPILE #-}` is rejected under `--safe` (verified). Nothing in the
specification is weakened.

### 2.4 Ideal functionalities need little replacement

Core `Transaction` values carry a proof of successful `eval`. The monitor accepts
raw candidates instead: `decExecution` checks their claimed journal against the
build state and constructs a certified transaction only on success. Invalid
candidates are rejected before `Contract.admit`. This is re-execution, not a ZK
proof system. The Compact simulator also executes without ZK. Real cryptography
enters through hashes and curve arithmetic interpreted by the primitive backend.

## 3. Where we are

This table describes the earlier recovery slice. The newer pinned-main
full-account coverage and its separate execution relation are recorded above.

| Item | State | Evidence |
|---|---|---|
| `Program` DSL executable | yes: `eval`/`replay` are total functions | `src/Midnight/ContractDSL/Program.agda` |
| `Protocol` executable | yes: inductive `Calls`, structural `_∘ᵖ_`; exact rational `evalC` | pinned categorical-crypto `protocol-rewrite` |
| Compilation | MAlonzo works (`SmokeMain`, `Conformance.Main`); JS backend blocked | §4.2 |
| Coin injection executor | `Conformance.Coins` (`readCoins`, `stepCoins`, `runCoins`) | spike |
| Decidable execution / journal | `Conformance.CertificateDecision.decExecution`, `decRun`, `_≟ᴶ_` | runtime monitor |
| Implementation seam | compact-runtime simulator, no node/proof/zswap; block time set per call | `grants-offline.ts:221-258`, `sim.ts` at `5d12798` |
| Pinned implementation | Historical `7d21a277` (recovery `5d12798` plus signer injection); repaired stamped-map working tree at the same base plus fixed source/wallet digests | `conformance/harness/recovery-pins.json`, enrolled gate lock |
| Injectable implementation randomness | `JubjubDevice.sign(…, draw)` and `signRecoverSubmit(…, draw)`; deterministic settings retained in the gate baseline | historical `7d21a277`; gate pins |
| Coverage | custody/device/recovery jubjub model; twelve scenarios, generated counter-varied plants used after one to three recoveries, and seeded interleavings; concrete repair additionally exercises both authentication arms in `recovery-sim` | `docs/conformance-recovery.md` |
| Recovery counterexample/repair | Source circuits accept fresh old-key use of planted future entries; repaired circuits reject it under current-epoch stamped membership | generated/scenario gate plus both-arm simulator regressions |
| Reader-facing recovery proofs | Corrected account model has checked finite actual-admission device-authority exclusion and guard-premised recovery/rotation execution; concrete-model refinement remains open | `src/Passport.agda`, `Conformance.RecoveryAuthority` / `RecoveryExecution` |

## 4. Technical design

This section describes the recovery-slice DSL/monitor architecture and its
historical implementation seam. The full-account runner above uses the newer
object-form `createCircuitContext` API, all three authentication arms and local
shielded-effect descriptions; those descriptions are not authenticated assets.

### 4.1 Model side

**Layers.** `Semantics` (ledger operations with `prepare` and `DecEq-Res`) → `Program`
(effects `ledger`/`require`/`publish`/`atChain`) → `Contract` (entrypoints,
evaluation-certified transactions and atomic journal replay) → categorical
`Protocol`. `Conformance.Account` supplies the wallet invocation adapter;
`Conformance.Monitor` validates raw candidates before core admission.

**Ledger state.** Concrete records with lists standing in for `Map`/`Set`, compared up to
order (`_≈ᵇ_`), `Uint<n>` bounds enforced in `prepare` (`overflow` failure). Decidable
equality on every `Op`, `Res`, and on `Journal` (needed by `decExecution`).

**Circuits as programs.** One `Program` per exported circuit, asserting in the
implementation's order so that the *first* failing assert (and hence the abort message) and
the journal prefix before it line up. Assertion codes are an enumeration mapped to the
implementation's assert strings.

**Clients as protocols.** Randomised client logic (signers) is a `Protocol` that flips coins.
Because `Calls` is inductive, the implementation's unbounded loops (rejection sampling,
challenge grinding) become bounded loops ending in `dead`; the bound is chosen so the
`dead` mass is negligible (512 draws at acceptance ≈ 0.057 → < 10⁻¹²) and the harness
treats `dead` as a reportable `stuck`, never as agreement.

**Primitives record.** Everything cryptographic: `Bytes32`, `Point`, scalar modulus,
entry/challenge hashes mirroring the `pure circuit`s, `ecMulG`/`ecMul`/`ecAdd`, little-endian
hash reading, decidable equalities. `--safe` modules are parameterised by it;
`Conformance.Oracle` interprets it with an explicit trusted backend.

**Oracles.**
- `stepModel : ℕ → State → Request → List Bool → Maybe ((State × StepReport) × List Bool)`:
  one wallet activation on an injected bit stream, returning the unread remainder (which
  must be empty for agreement).
- `Conformance.Monitor.acceptable : State → Transition → State → Bool`:
  same-view invocation or validation/admission of supplied frozen evidence,
  followed by post-state/outcome comparison. Build and admission states remain
  distinct; aborts must carry the matching code and leave state untouched.

### 4.2 Backend and FFI

- **MAlonzo (GHC)** is the working backend. `-O0`, `-M3G -H1G` for closures without
  `UC.Model.Setup`; `-M8G` where agda-categories is pulled in.
- **JS backend is blocked**: the generated code for stdlib `Relation.Nullary.Decidable.Core.map′`
  loops (copattern `proof (map′ …)` passes `does (map′ …)` to `Reflects.of`, which matches on
  it; strict evaluation recurses). Every ℕ `_≟_`/`_≤?_` and hence `Contract.admit` is
  affected. Report upstream; do not work around in the spec.
- **CLI primitive calls** cross a process boundary: the model prints `? op args`,
  and the harness answers using the implementation's `pureCircuits` and runtime.
  `Main` supplies this transport through its GHC override; the safe checker and
  codecs take an explicit backend and do not import `Main`.
- **In-process integration** uses the stable `Passport.Monitor` Haskell facade
  or `passport_monitor.h` C ABI. Both delegate to compiled Agda and take an
  explicit deterministic crypto backend; failures remain distinct from `false`.
- **Wire format:** bidirectional `monitor-v1` tokens with strict structural
  parsing. Full-state implementation fixtures wrap observations in JSON; see
  [the API, build and fixture instructions](conformance-recovery.md#runtime-transition-monitor).

### 4.3 Implementation side

- **Seam.** `new Contract(witnesses)`, `createCircuitContext(name, address, coinPk, state, …, time)`,
  `impureCircuits[name](ctx, …args)`, post-state from `res.context.callContext.currentQueryContext.state`,
  read with `ledger(state)`. Failures are thrown with the circuit's assert string. Runs
  everything that does not touch Zswap; shielded twins need a node.
- **Randomness injection.** Signer draws are injectable (`draw`, `draw32`), default
  behaviour unchanged. Further sources to make injectable as slices widen: inbox
  X25519/AES-GCM nonces, deploy salts, k256 nonce (the Rust signer is already RFC6979).
- **Transcript.** Completed simulator calls expose
  `callProofDataTrace.publicTranscript`. The harness verifies those recorded VM
  operations/reads against the initial query context and checks their complete
  final VM state; changing a recorded read must be rejected. Decoding low-level
  VM instructions into the model's higher-level `Event`s remains WP1.

### 4.4 Harness

- Seeded PRNG generates the contract address, keys, the bit stream, and the call sequence
  (scenario classes with weights); a seed reproduces a run exactly.
- Per step: run implementation, run model with the same bits, compare verdict/abort code,
  signature `(R, s, grind)`, post-state up to order, and unread bits; then monitor the
  observed invocation triple. Exit non-zero on any disagreement.
- **Mutation check** is part of the definition of done for every slice: a deliberate model
  mutation (e.g. `≤`→`<` in a guard) must be reported by both oracles; otherwise the oracle
  is not observing the behaviour it claims to.
- Reporting: per-step line, scenario coverage counts, bits consumed, RPC count, wall time.

### 4.5 Randomness regimes

| Regime | Treatment | Example |
|---|---|---|
| Nuisance randomness in functional behaviour | inject the same bits into both sides; oracle 1 | signer nonce, grind loop |
| Uncapturable randomness | opaque witness: implementation produces, model verifies | proof-server randomness |
| Randomness the spec reasons about distributionally | not a conformance property; stays a theorem (`Pr`, `_≈adv[_]_`). Exact `evalC` masses allow statistical checks only for small-support coins | `secure-history-private` |

### 4.6 Ideal functionalities → real primitives

| Model resource | Replacement | Status |
|---|---|---|
| Evaluation-certified `Contract.Transaction` | re-execution + `decExecution` at the external candidate-validation boundary; no proof system | implemented in `Conformance.CertificateDecision` |
| ideal proof token (`coin`) | opaque proof bytes or omitted under the simulator | trivial |
| `SymbolicDigest.Digest` | `Bytes32` + `persistentHash` encoding via `Primitives` | done for the spike's own ledger; main spec's `MidnightLedger` still hardcodes the symbolic type (WP5) |
| symbolic authority key (`lockKey`) | JubJub Schnorr verify (`ecMulG s ≟ ecAdd R (ecMul pk c)`); k256 ECDSA | jubjub done; k256 open |
| `Midnight.Passport.Core` postulates | must become parameters before any of it can run | open (WP5) |
| Zswap / shielded coins, inbox encryption | not modelled; shielded twins cannot run off-node | out of scope |

## 5. Work packages

Ordered; each ends with the mutation check and a seeded multi-seed run.

**WP1 — Model-journal correspondence.** Successful simulator calls now have
implementation-produced transcript replay and recorded-read mutation checks.
The remaining task is to decode those VM transcripts into model `Journal`s and
validate their execution with `decExecution` before `Chain.admit`, establishing
the translation boundary rather than equating runtime replay with a model certificate.
The pinned-main runner now independently decodes concrete ledger/context effects
and compares them with full-account execution. This does not retrofit the
recovery monitor's certificates or prove universal generated-code refinement.

**WP2 — Independent primitives.** Bind `Primitives` to an implementation that is not the
system under test (`signer-rs` challenge path over JSON, or a native jubjub/SHA-256 library),
so encoding bugs in `persistentHash`/curve code become detectable. Acceptance: a
deliberately mis-encoded challenge on either side is reported.
The full-account backend now uses independent SHA-256 and fixed-width encoding.
Curve arithmetic/signature verification and Poseidon still share runtime code.

**WP3 — Widen the slice.** Done at `5d12798` ([`conformance-recovery.md`](conformance-recovery.md)):
`add_device`/`remove_device` with epoch, `rotate_enc_key`, recovery session, `recover_submit`/
`cancel`/`finalise` with chain time, the identity/small-order recovery-key guard, and a corrected
finalisation variant compared up to the entries it removes. That slice omitted
k256/grant execution and shielded flows. The pinned-main runner now models all
authentication arms, bootstrap, grant lifecycle and both custody forms; local
Zswap descriptions are exercised without claiming authenticated coin admission.

**WP4 — Generators.** Recovery histories now generate counter-varied future
plants and actually sign with them after finalisation, with exact dynamic
source/corrected divergence obligations and repaired rejection. Generic DSL
observer strategies and shrinking remain separate work, not part of this package.

**WP5 — Connect the main specification.** Parameterise `MidnightLedger`/`Lock`/`Merkle`
over a digest record so the advertised lock/Merkle models can be instantiated with real
hashes and compared against the circuits they approximate; replace `Midnight.Passport.Core`
postulates by parameters or retire the module. Acceptance: at least one advertised property's
model (e.g. `Lock.clear`) runs under the harness against a corresponding circuit.

**WP6 — Gate and CI.** The local pinned recovery gate is implemented in
`conformance/harness/gate.mjs`, with explicit input enrollment, input-drift
rejection, source-to-generated-JS checks, generated histories, and isolated
mutations. CI provisioning of the pinned toolchain/implementation artefacts is
not established; no hosted-CI or deployment pass is claimed.

**WP7 — JS backend.** File the `map′` divergence upstream; re-evaluate the single-process
design when fixed (removes the RPC layer and its gotchas).

## 6. Risks and limits

- **Shared oracle:** the historical runner shares hashing and curves; the
  full-account runner has independent SHA-256/encoding but still shares curves
  and Poseidon. Bugs in those shared primitives can remain invisible.
- **Bounded loops**: agreement is claimed only for runs within the bounds; `stuck` is
  reported, never silently accepted.
- **Abort matching by message substring**: brittle under message edits in the contract;
  mitigate by pinning the implementation commit (WP6).
- **Coverage drift**: the spec and the contract evolve independently; the conformance build
  must fail, not skip, when a modelled circuit's signature changes.
- **Toolchain**: RC compiler without launcher, SRS download blocked by proxy; `--skip-zk`
  suffices for the simulator but means proving is never exercised here.
- **Earlier slice omissions:** coin movements and checked successor/epoch casts
  were absent from the historical slice. They are explicit in the pinned-main
  full-account model; this does not establish external asset authentication.

## 7. Non-goals

Finite execution comparison does not establish a verified Compact compiler or
installed WASM, proof-system or distributional/privacy conformance, or correctness
for unexercised inputs. The explicit formal VM and local representation proofs
must not be presented as those stronger results.

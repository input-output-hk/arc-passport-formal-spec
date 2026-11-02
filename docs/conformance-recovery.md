# Recovery assurance and historical conformance

The historical result below concerns Passport
`5d12798321d3daba37b1da90162ee1468daf38a6`, with two signer-randomness injection
commits ending at `7d21a277be9f92e7bc36a1a296599b9420194c44`.
The executable `--safe` account model has its reader-facing intended contract in
[`Passport.AccountRecovery`](../src/Passport/AccountRecovery.agda), with circuit
bodies and wallet/conformance machinery in `src/Conformance`. The historical
comparator uses source-shaped insertion; the intended contract fixes authority
replacement. The [recovery specification](recovery-specification.md) describes
the threat model and obligations. Historical numbers and transcripts below are
not measurements of a repaired or deployed contract.
For current executable integration, start at the
[runtime transition monitor](#runtime-transition-monitor): checker, wire format,
Haskell/C APIs, crypto backend and serialized implementation fixtures.

The sections labelled historical predate the port to `main`'s certified-transaction
API. The committed recovery baseline was `26ab5df`; the historical runtime-monitor and
primitive-boundary records also describe the uncommitted work preserved with
that baseline. Those working-tree snapshots were not given commit identities.
The historical lock is not evidence for the rebased source or dependency pin.

## Certified-transaction port verification

The 2026-11-02 working-tree port rebases `feat/recovery-dsl` onto local `main`
`42636b9`, retaining the `f280e04f` categorical-crypto source pin. The upstream
library build was killed with exit 137 without a heap bound; setting its build
`GHCRTS` to `-M8G -H1G` completed the same pinned source build.

`src/Passport.agda` and compiled `Conformance.Main` passed under
`LC_ALL=C.UTF-8`, `pagda --useUntracked false check`, and `-M3G -H1G`, with no
warning-gate diagnostics. The compiled executable drove these simulator runs:

| Implementation / model | Scenarios | Generated seed 1 | Random seed 1 |
|---|---|---|---|
| Source / source-shaped | 12/12, 79 steps, no divergence | 30 steps, no divergence | 34 steps, no divergence |
| Source / corrected | 12/12, 79 steps, 2 expected divergences | 30 steps, 3 expected planted-use divergences | 34 steps, 1 expected divergence |
| Repaired / corrected | 12/12, 79 steps, no divergence | 30 steps, no divergence | 34 steps, no divergence |

Both source/source and repaired/corrected monitor runs passed 119 checks.
These cover raw candidate rejection, frozen replay, nonzero logical account
identities, target mismatch, and rejection atomicity. Freshly built typed Haskell,
static C and shared C monitor consumers passed; the Haskell consumer also checked
signed rotation and recovery submission through the real primitive backend for
both implementations.

The full pinned gate was not rerun or reenrolled; its historical lock remains
unchanged. These results do not establish ZK verification, full ledger/effects
authentication, or a Compact-transcript-to-Agda-journal refinement.

## Concrete repair boundary

The available sibling checkout `../arc-passport` is at `68bbde28` and exposes no
recovery circuit. The clean recovery conformance checkout is at `7d21a277`;
inspection of its available all-ref account history found no later repair of
this vulnerability. This is local-repository evidence, not an assertion about
all upstream revisions or deployed contracts.

The repair is uncommitted in
`.worktrees/recovery-authority-stamp`, based on `7d21a277`. Its `devices` ledger
is `Map<Bytes<32>, Uint<32>>`: the value records the epoch the **contract observed
at insertion**, not a client-chosen epoch hidden in the opaque entry preimage.
Activation, enrolment, credential rolling, and recovery successor installation
stamp entries; both jubjub and k256 authentication require the stamp to equal
the current epoch. Removal and duplicate checks also use current-generation
membership. A current authority may explicitly re-enrol a stale entry.

Finalisation increments a checked, non-wrapping epoch and stamps the successor.
It need not enumerate or clear retained entries: their old stamps make them
ineligible, including opaque future-epoch commitments planted before recovery.
Submission/finalisation explicitly reject epoch exhaustion rather than cycling
back to old authority generations. This is a ledger-schema change: old-schema
generated artefacts or deployments are not compatible and must not be reused.
No deployment or state-migration evidence is claimed.

The intended corrected model replaces the set with a singleton. The repaired
comparison instead projects the map to entries whose stamp equals the current
epoch. That ties the concrete design to authority replacement without claiming
physical deletion or a proved simulation relation. Scoped-grant authority
exclusion is outside this package.

## Checked formal scope

Start at [`src/Passport.agda`](../src/Passport.agda), then follow:

1. [`Passport.AccountRecovery.contract`](../src/Passport/AccountRecovery.agda):
   entrypoints, input types, device-authorisation challenges and dispatch, and
   shared `AccountLedger.State`/`accountLedger`. This is the recovery-relevant
   account slice, including interfering device, rotation and custody operations,
   not a separate deployed recovery contract. There is one assembly; the
   prominent `contract` fixes corrected finalisation. `assemble sourceShaped`
   is available only as the historical conformance comparator.
2. [`Contract.Admissions`](../src/Midnight/ContractDSL/Contract.agda):
   generic traces of evaluation-certified transactions.
   `AccountRecovery.Chain` instantiates the intended contract. Traces allow
   arbitrary submission times, ordering, certificate build views, and
   accepted/rejected steps, without a wallet or `TracePolicy` premise.
3. [`RecoveryExecution`](../src/Conformance/RecoveryExecution.agda) and
   [`RecoveryAuthority`](../src/Conformance/RecoveryAuthority.agda):
   explicit advertised statements and qualified references to separate proofs.
   Their `Definitions` modules expose guard records and authority assumptions.

The initial ledger is supplied after bootstrap; no constructor/deployment or
bootstrap-reachability theorem is claimed. No global validity predicate has been
added: every represented `State` remains covered by the existing conditional
statements, including unsafe old device sets and initially pending recovery.
Positive operations require their stated readiness guards and chain conditions.
Preservation starts with `Safe`; resetting finalisation instead requires a safe
pending entry and may begin with an unsafe device set. All formal modules on this
route retain `--safe --without-K`.

`accepted-recovery-trace-exclusion` starts from an **actual accepted**
corrected finalisation, even if the prior device set was compromised, and then
quantifies over finite actual contract admission traces satisfying a separate
`TracePolicy` hypothesis, including rejection and stale-view certificate replay.
Compromised presented keys cannot gain
current-epoch device authority at any counter; a companion theorem rules out
successful gated evaluation under those keys. This is not just stale-signature
rejection.

Assumptions are explicit: a fixed compromise set, key-entry separation across
epochs/counters, a safe pending successor, and `TracePolicy` for the subsequent
trace. Its `TransactionPolicy` requires the certified input of
every transaction (including rejected steps) to obey `InputPolicy`: opaque
enrolments exclude **any** compromised-key epoch/counter encoding and recovery
successors are uncompromised. This is a theorem hypothesis, not a restriction on
what the contract admits. Treating accepted honest-key
operations as honest intent requires authentication/unforgeability and trusted
recovery authority outside the theorem.
The DSL supplies atomic account-segment rejection, ordered replay, and chain
conditions; no deployed-chain emulation is proved.

The execution route proves guard-premised positive submission, finalisation,
and representative encryption-key rotation/admission; successor membership;
exact submission/finalisation state and journal shape; deadline conditions for
both explicit journals and actual accepted transactions (including stale build
views); seam-gated cancellation; stale/pending/immediate replay rejection;
and rejection atomicity. It does **not** prove whole-history cancelled-submission
occurrence provenance, cryptographic challenge binding/unforgeability, UC
replacement, or grant-authority exclusion. The source attack is executable
evidence, not a source-model reachability theorem.

The formal closure command is:
`pagda --useUntracked false check src/Passport.agda -- +RTS -M3G -H1G -RTS`.

### Ledger primitive boundary

[`AccountLedger.Op`](../src/Conformance/AccountLedger.agda) models cell access,
map membership/lookup/insertion, and set insertion/removal/reset. Application
combinations are ordinary `Program` functions in
[`Custody`](../src/Conformance/Custody.agda) and
[`Recovery`](../src/Conformance/Recovery.agda), not opaque ledger operations.
For example, `bumpRound` reads the scalar before its bounded replacement write;
`credit` records membership and, on the present branch, the balance value.
The historical generated Compact code's `_bump_round_0` and
`_credit_unshielded_0` confirm these `popeq` reads followed by `ins` writes.
This is primitive-level manual correspondence, not a verified compiler pass.

The representation still has explicit limits:

- Bounded writes model the selected `Uint` field limits; arbitrary represented
  initial states and natural-valued inputs are not automatically concrete ABI
  values. `SubmissionReady` describes model execution; matching the omitted
  submission `post_epoch` cast additionally requires
  `suc (deviceEpoch s) < 2^32`. This is a correspondence caveat, not an admission
  guard or a proved refinement. Rotation's existing statements retain the
  explicit `RotationReady.counterFits` premise for the likewise unmodelled
  `use_counter + 1` cast. Neither omitted cast is enforced by the model.
- `phi` projects the recovery map to four slots. Intermediate insertions into an
  empty map fill unrepresented slots with zero. No circuit reads these slots;
  successful publication writes all four, and aborts discard the working state.
  This does not model arbitrary map shapes.
- Pending-key clearing retains the source's key read but writes `ecMulG 0`.
  Equality with the source expression `ecMul(pending_recovery_pk, 0)` belongs to
  the concrete curve interpretation, not to the unconstrained `Primitives` record.
- Corrected `install` uses reset/insert/count-write to specify a singleton set.
  It is not the literal transcript of the stamped-map repair described above.

## Runtime transition monitor

Integration entry points: [Haskell facade](../conformance/monitor/Passport/Monitor.hs),
[C header](../conformance/monitor/passport_monitor.h),
[native build](../conformance/monitor/build.py),
[Haskell example](../conformance/monitor/tests/HaskellSmoke.hs),
[C example](../conformance/monitor/tests/c_smoke.c) and
[fixture consumer](../conformance/harness/monitor.ts).

[`Conformance.Monitor`](../src/Conformance/Monitor.agda) exposes
`acceptable : State → Transition → State → Bool`, parameterized by the crypto
primitives, the `Bytes32` challenge domain, and the finalisation variant.
It does not generate signatures or consume wallet randomness.

`Transition` distinguishes two observations:

- **Invocation:** a raw, already-signed call, account/time context and observed
  outcome. The checker evaluates the body, builds its model certificate and
  runs same-view admission.
- **Admission:** a frozen `Candidate`, account/time context and observed outcome.
  A candidate contains its transaction account, original build state, raw call
  and claimed journal. The checker validates that journal against the **build
  state**, then submits the certified transaction through `Contract.admit` at the observation's
  **initial state**. It never rebuilds the journal at admission time.

`true` means the observed outcome **and final state** match the model. It can
therefore confirm an accurately observed rejection or abort, not just an
accepted transaction. Rejection must preserve state; an invocation abort must
also match the normalized error code. Admission itself has no build-abort
outcome. State comparison retains the model's unordered set/map equality.
Agda's `Observed` is the Haskell/TypeScript `Outcome` and wire `OUTCOME`;
the DSL's internal evaluation `Outcome` is a different type. Transition
constructors place context before call/candidate and observed outcome.

Candidates are ordinary serialized evidence, not trusted Agda proofs. Validation
constructs an evaluation-certified transaction only after deciding the execution
relation. Invalid evidence is rejected at this external validation boundary;
it cannot inhabit the core `Contract.Transaction` type. The account result is
unit. This is neither a Compact transaction decoder nor a ZK-proof verifier.
The identity boundary is defined in [`Conformance.Monitor`](../src/Conformance/Monitor.agda):
the natural-valued **logical account identity** selects `Contract.self`, while
the candidate supplies its claimed target. The `Bytes32` module parameter `self`
is the separate **challenge domain**. Core admission checks the target identity
and replays at the submitted `now`.

### Serialization and executable adapter

[`Wire`](../src/Conformance/Wire.agda) supplies bidirectional codecs and command
dispatch; [`Main`](../src/Conformance/Main.agda) supplies transport and its
interactive crypto backend. The versioned token grammar is:

```text
monitor-v1 VARIANT SELF INITIAL call ACCOUNT TIME CALL OUTCOME FINAL
monitor-v1 VARIANT SELF INITIAL admit ACCOUNT TIME CANDIDATE OUTCOME FINAL
CANDIDATE = TX_ACCOUNT BUILD_STATE CALL J EVENT_COUNT EVENTS...
OUTCOME = ok | refused | fail CODE
```

`VARIANT` is `source` or `corrected`. `ACCOUNT` and `TX_ACCOUNT` are natural-valued
logical account identities; `SELF` is the separate 32-byte challenge domain.
The one-account simulator adapter uses logical account identity zero.
These are not interchangeable address encodings.
The concrete simulator adapter interprets `TIME` as Unix time in seconds.

[`Conformance.Wire`](../src/Conformance/Wire.agda) is the authoritative executable
codec. [Haskell `Codec`](../conformance/monitor/Passport/Monitor/Codec.hs) and
[TypeScript `wire.ts`](../conformance/harness/wire.ts) mirror that format.
In the grammar below, `name:TYPE` labels a value, and `{n}` means exactly `n`
repetitions; labels, braces and parentheses are not wire tokens. `INITIAL`,
`FINAL` and `BUILD_STATE` are `STATE`; account identities, times and counts are
`N`, `SELF` is `B32`, and `CODE` is one nonempty whitespace-free token.

```text
N = [0-9]+
B32 = [0-9a-f]{64}
B64 = [0-9a-f]{128}
FLAG = 0 | 1
POINT = x:N y:N
PHI = 0 | 4 phi1:N phi2:N phi3:N phi4:N
STATE =
  round:N nonce:N epoch:N deviceCount:N
  nDevices:N device:B32{nDevices}
  nBalances:N (color:B32 amount:N){nBalances}
  encKey:B32 recoveryPk:POINT phi:PHI phiLen:N session:B32 wrap:B64
  pending:FLAG pendingEntry:B32 pendingRecoveryPk:POINT notBefore:N vetoWindow:N

CALL = D color:B32 amount:N
     | F
     | U successor:POINT nextRecoveryPk:POINT expectedEpoch:N expectedNonce:N
         nowUpper:N recoveryR:POINT recoveryS:N successorR:POINT successorS:N grind:N
     | J GATED AUTH
AUTH = pk:POINT useCounter:N R:POINT s:N grind:N
GATED = W color:B32 amount:N recipient:B32
      | A entry:B32 | R entry:B32 | K encKey:B32
      | P recoveryPk:POINT session:B32 phi1:N phi2:N phi3:N phi4:N phiLen:N wrap:B64
      | C

EVENT = op OPERATION ARGUMENTS RESULT
      | publish N
      | require min N
      | require max N
EVENTS... = EVENT{EVENT_COUNT}
```

`D` deposits, `F` finalises recovery, `U` submits recovery, and `J` authorises a
gated call. Gated tags mean withdraw, add device, remove device, rotate key,
publish recovery session and cancel recovery, respectively. Journal operations
use the exact case-sensitive ledger constructor names:

| `OPERATION` | `ARGUMENTS` | `RESULT` |
|---|---|---|
| `readNonce`, `readRound`, `readEpoch`, `readDeviceCount`, `readVetoWindow`, `readNotBefore` | none | `count N` |
| `readBalance` | `B32` | `count N` |
| `readPending` | none | `flag FLAG` |
| `deviceMember`, `balanceMember` | `B32` | `flag FLAG` |
| `readRecoveryPk`, `readPendingRecoveryPk` | none | `point POINT` |
| `readSession`, `readPendingEntry` | none | `bytes B32` |
| `writeBalance` | `B32 N` | `unit -` |
| `insertDevice`, `removeDevice`, `setEncKey`, `writeSession`, `writePendingEntry` | `B32` | `unit -` |
| `resetDevices` | none | `unit -` |
| `writeNonce`, `writeRound`, `writeEpoch`, `writeDeviceCount`, `writeNotBefore`, `writePhiLen`, `insertPhi1`, `insertPhi2`, `insertPhi3`, `insertPhi4` | `N` | `unit -` |
| `writeRecoveryPk`, `writePendingRecoveryPk` | `POINT` | `unit -` |
| `writePending` | `FLAG` | `unit -` |
| `writeWrap` | `B64` | `unit -` |

Parsing requires decimal naturals, exact lowercase byte-string widths, Boolean
flags `0|1`, distinct set/map keys and complete input consumption. Normalization
canonicalizes tokens and numbers, not collection order. Structural validity
does not establish reachability, concrete ABI widths or curve-point validity.

| Command | Result |
|---|---|
| `check OBSERVATION` | `= true` or `= false`; malformed input is `= error ...` |
| `normalize OBSERVATION` | `= OBSERVATION` in canonical token form |
| `prepare VARIANT SELF TX_ACCOUNT STATE CALL` | `= candidate CANDIDATE` or `= fail CODE` |
| `step ...` | Existing wallet-generation oracle; separate from monitoring |

There is no `decide` compatibility command. A crypto request from the executable
is prefixed `? `; the host must supply the actual digest or affine-point reply.
Malformed backend replies fail explicitly, never become conformance `false`.
The in-process APIs below avoid this interactive transport.

### Haskell and C integration

[`Passport.Monitor`](../conformance/monitor/Passport/Monitor.hs) is the stable
handwritten Haskell facade:

```haskell
checkObservation :: CryptoBackend -> Observation -> IO (Either MonitorError Bool)
```

Named domain types cover states, calls, outcomes, candidates, journal events and
both transition kinds. `encodeObservation`/`decodeObservation` provide the wire
roundtrip; `checkSerialized`, normalization and `prepareCandidate` are also
exposed. The checker delegates to compiled Agda, not a second Haskell semantics.
Generated MAlonzo symbol names remain private build glue.

The explicit backend must implement the real entry/challenge hashes and curve
operations. Malformed input, backend failure and internal failure are distinct
from `Right False`; candidate preparation additionally reports `BuildAborted`.
The pure Agda primitive record requires a narrow deterministic IO bridge in
Haskell. It captures the backend per invocation, uses no global backend or
stdin, and forces results before returning. Backends must be referentially
transparent: pure evaluation may share results, so callback counts or mutable
crypto state must not affect answers.

#### Crypto request/reply protocol

[`Conformance.Oracle`](../src/Conformance/Oracle.agda) defines the primitive
interpretation. Requests are single whitespace-delimited lines using the same
`N`, `B32`, `B64` and `POINT` encodings as above. Names label arguments here,
not extra wire tokens:

| Request | Reply |
|---|---|
| `entry self:B32 pk:POINT epoch:N counter:N` | `B32` |
| `chal-w self:B32 R:POINT pk:POINT color:B32 amount:N recipient:B32 nonce:N grind:N` | `B32` |
| `chal-add self:B32 R:POINT pk:POINT entry:B32 nonce:N grind:N` | `B32` |
| `chal-rm self:B32 R:POINT pk:POINT entry:B32 nonce:N grind:N` | `B32` |
| `chal-rot self:B32 R:POINT pk:POINT encKey:B32 nonce:N grind:N` | `B32` |
| `chal-pub self:B32 R:POINT pk:POINT newRecoveryPk:POINT session:B32 phi1:N phi2:N phi3:N phi4:N phiLen:N wrap:B64 nonce:N grind:N` | `B32` |
| `chal-cancel self:B32 R:POINT pk:POINT nonce:N grind:N` | `B32` |
| `chal-submit self:B32 recoveryPk:POINT recoveryR:POINT successor:POINT successorR:POINT nextRecoveryPk:POINT postEpoch:N nonce:N nowUpper:N grind:N` | `B32` |
| `mulg scalar:N` | `POINT` |
| `mul point:POINT scalar:N` | `POINT` |
| `add left:POINT right:POINT` | `POINT` |

Digest byte order is the implementation's byte order; challenge numeric
interpretation is little-endian. Replies are raw tokens, without the executable's
`? ` or `= ` prefixes. Backend failures use the Haskell `Left`/C callback error
channel, not a substitute digest or point.

The reference [backend command](../conformance/harness/oracle.ts) uses
[`answerPrimitive`](../conformance/harness/model.ts) and the selected real Compact
implementation. It reads bare requests from stdin and writes bare replies.
`haskell-smoke --real OBSERVATION_FILE BACKEND_EXECUTABLE [ARG...]` connects this
backend through explicitly owned pipes; the fixture commands below include a
runnable example.

#### C ownership and native build

[`passport_monitor.h`](../conformance/monitor/passport_monitor.h) exposes
`passport_monitor_check`, `passport_monitor_normalize`,
`passport_monitor_prepare` and `passport_monitor_free`. C callers initialize the
GHC RTS, supply length-delimited UTF-8 and an explicit callback/userdata pair,
and free every library-owned output with `passport_monitor_free`. The header
specifies status codes, borrowed callback-buffer lifetimes and concurrency
requirements; no Haskell exception crosses this boundary.

Build from the repository/worktree root:

```sh
python3 conformance/monitor/build.py
```

The script discovers the project GHC environment, generates private bindings,
and builds static/shared libraries plus Haskell and C consumers under
`_build/monitor`. [`HaskellSmoke.hs`](../conformance/monitor/tests/HaskellSmoke.hs)
and [`c_smoke.c`](../conformance/monitor/tests/c_smoke.c) are executable usage
examples, including failure handling and C output ownership.

### Implementation fixtures and replay boundary

The harness's [`fixtures.ts`](../conformance/harness/fixtures.ts) couples a
serialized model observation with a full concrete simulator snapshot and its
execution context. The consumer checks the snapshot's model projection against
the supplied initial state and derives implementation arguments from the raw
call; it does not substitute a fresh state or re-sign the call.

The snapshot preserves address, logical account identity, time, coin public key
and the complete account `StateValue`, including fields omitted by the model.
Its `default-simulator-v1` environment explicitly fixes external balances,
remaining block fields and commitment indices to the pinned simulator defaults,
private state to empty, the `held_coin` witness to zero and the cost model to
the initial one. This is not arbitrary `ContractState`/Zswap reconstruction.

After compiling `Main` with the [model build command](#pinned-repeatable-gate),
export `IMPL_DIR` as the absolute implementation `contract/` directory and
`MODEL_BIN` as the absolute compiled `Main` path. From the worktree root:

```sh
RECOVERY_IMPLEMENTATION=source "$IMPL_DIR/node_modules/.bin/tsx" \
  conformance/harness/monitor.ts checks --fixtures _build/monitor/example-fixtures
RECOVERY_IMPLEMENTATION=source "$IMPL_DIR/node_modules/.bin/tsx" \
  conformance/harness/monitor.ts consume \
  _build/monitor/example-fixtures/model-signed-rotate.json
_build/monitor/haskell-smoke --real \
  _build/monitor/example-fixtures/model-signed-rotate.observation \
  "$IMPL_DIR/node_modules/.bin/tsx" conformance/harness/oracle.ts
```

Choose a fresh fixture directory: emission refuses to overwrite existing cases.
For the stamped-map implementation, select its directory and
`RECOVERY_IMPLEMENTATION=repaired`; the monitor variant becomes `corrected`.

Frozen model candidates and frozen concrete VM transcripts remain separate
evidence. The replay runner does not rebuild either at admission, and does not
resynchronize after discrepancies. Reachable intervening calls are distinguished
from synthetic field mutations. VM replay checks the recorded state operations
and applicable time conditions, but is **not full transaction admission**:
changing declared unshielded-input effects can still pass `runTranscript`.
Neither coin-effect validity nor a VM-transcript-to-Agda-journal refinement is
established by this monitor.

### Historical runtime monitor verification

Before the certified-transaction port, the uncommitted runtime-monitor package passed:

- `Passport.agda` closure and compiled `Main`; the warning gate and zero
  escape-hatch baseline remained unchanged.
- The documented native-library build, typed Haskell consumer and linked static
  and shared C consumers: model agreement/disagreement, serialization, frozen
  admission, malformed input, backend errors, callback isolation and ownership.
- Real signed-rotation and recovery-submission Haskell checks through the
  implementation crypto backend, for both source and repaired implementations.
- Source/source and repaired/corrected monitor runs: 114 checks each, including
  14 serialized fixture roundtrips and 10 frozen replay cases per run.
- The standalone fixture consumer on a serialized signed-rotation case;
  both actual-result conformance and supplied expected result matched.
- Historical source scenarios with the migrated monitor: 12/12 and 79 steps for
  each variant; zero source/source discrepancies and exactly the two annotated
  source/corrected discrepancies.
- Strict harness TypeScript checking and gate-script syntax checking.

The tests retain the effects-authentication negative control above. The full
historical pinned gate was **not** rerun or reenrolled. Its inventory now includes
the monitor and native consumers; changed inputs/schema require explicit
reviewed enrollment to a new lock filename. Historical locks were not changed.

## Pinned repeatable gate

`conformance/harness/gate.mjs` requires explicit paths and rejects implicit
`IMPL_DIR`, `MODEL_BIN`, or implementation-mode overrides. The fixed baseline in
`recovery-pins.json` identifies the historical source, the repaired source/wallet,
compiler installation, runtime/dependency tree, Node binary, seeds, and settings.
Enrollment additionally records the model binary, formal sources/build inputs,
Agda tooling, generated contract artefacts, and every harness source. HEAD alone
does not identify the uncommitted repair.

The repaired dependency snapshot was installed with `npm ci --ignore-scripts`
in its `contract/` directory. Historical and repaired installed dependency trees
are pinned separately: the historical tree has different optional-package and
esbuild-install artefacts, despite the same package lock. Runtime/signing source
content remains pinned; arbitrary dependency drift is rejected.
Compile `account`, `control`, and `faucet` with
`compactc --skip-zk --feature-zkir-v3 contracts/X.compact contracts/managed/X`.
The full repaired TypeScript build additionally needs the existing
`probe-block-time` circuit generated with the same flags. Build the model:

```
pagda --useUntracked false check src/Conformance/Main.agda -- --compile --compile-dir=_build/conformance --ghc-flag=-O0 +RTS -M3G -H1G -RTS
```

Use the supplied enrollment lock for repeat runs. The `pin` command below is
for an absent lock; it deliberately refuses to overwrite an existing one.
Enrollment is a trusted snapshot step, not permission to accept arbitrary
changed source.

The `/home/agent/...` compiler and pagda paths are examples from the checked
machine. Substitute paths to the same pinned installations; the gate compares
content fingerprints rather than trusting a filename or version label.

Run the following commands from the formal repository root:

```
node conformance/harness/gate.mjs pin \
  --source ../arc-passport-recovery-conformance/contract \
  --repaired .worktrees/recovery-authority-stamp/contract \
  --model _build/conformance/Main \
  --compiler /home/agent/.compact/versions/0.33.0-rc.2/aarch64-linux/compactc \
  --pagda /home/agent/.local/bin/pagda \
  --repair-sha256 f73e0e70502eb9fabea06d420d14af2a512dfbb4b125052c87abab29ed2ba0bb \
  --output conformance/recovery-gate-lock.json
node conformance/harness/gate.mjs run \
  --source ../arc-passport-recovery-conformance/contract \
  --repaired .worktrees/recovery-authority-stamp/contract \
  --model _build/conformance/Main \
  --compiler /home/agent/.compact/versions/0.33.0-rc.2/aarch64-linux/compactc \
  --pagda /home/agent/.local/bin/pagda \
  --pins conformance/recovery-gate-lock.json
```

Run mode revalidates every pin and recompiles both implementation sources into
isolated `.worktrees` directories, comparing generated JS and declarations to
the pinned artefacts. It then runs source/both-model and repaired/corrected-model
comparisons, the twelve acceptance scenarios, generated attack histories,
random interleavings, and the deadline/debit mutations serially. Mutant model
copies are isolated; original user sources are not rewritten.

Seeds 1–5 generate one to three recovery epochs, counter-varied future plants,
successor operations, and fresh old-key withdrawals **after** finalisation.
Random histories also track successful plants and attempt them after a matching
recovery. Historical source acceptance must disagree with the corrected model
on both oracles; repaired acceptance must reject the planted key and agree with
the corrected model. Neither agreement nor mutation detection is a theorem
over all generated or adversarial histories.

For manual diagnosis of the repaired implementation (without pin validation):

```
IMPL_DIR="$PWD/.worktrees/recovery-authority-stamp/contract" \
RECOVERY_IMPLEMENTATION=repaired MODEL_BIN="$PWD/_build/conformance/Main" \
.worktrees/recovery-authority-stamp/contract/node_modules/.bin/tsx \
  conformance/harness/recovery.ts --implementation repaired --variant corrected \
  --only all --seeds 1,2,3,4,5 --steps 60
```

`RECOVERY_IMPLEMENTATION=repaired` selects current-stamp membership observation;
`--implementation repaired` selects repaired verdict obligations. Use both.
Historical manual runs use `source` mode and the historical contract path;
the default historical path is a convenience, not the pinned gate interface.

| Current package route | Role |
|---|---|
| `src/Passport.agda` | Specification, advertised property, and supporting proof/semantic navigation |
| `Passport.AccountRecovery` / `Midnight.ContractDSL.Contract.Admissions` | Intended shared contract and generic admission traces instantiated by its `Chain`; post-bootstrap boundary |
| `Conformance.RecoveryAuthority` / `RecoveryExecution` | Checked public claims; their `Definitions` modules expose assumptions/guards, and `Proof` modules implement the proofs |
| `conformance/harness/impl.ts` / `driver.ts` | Source/repaired simulator modes, effective authority projections, both transition oracles, and implementation VM transcript verification |
| `conformance/harness/recovery.ts` / `mutation.ts` | Scenarios, generated post-finalisation planted use, random histories, and isolated deliberate model mutations |
| `conformance/harness/gate.mjs` / `recovery-pins.json` | Trusted enrollment and repeat-run validation against fixed source/tool/dependency/seed baselines |
| `conformance/recovery-gate-lock.json` | Exact enrolled working-tree/binary/harness/artifact snapshot |

## Historical exercised package results

Before the certified-transaction port, the complete pinned gate passed with enrollment lock
`conformance/recovery-gate-lock.json`, SHA-256
`890de710a603492af33ec04dc047893faf65caf0aed69aa94165788e65b97f83`.
The repaired account source is pinned at
`f73e0e70502eb9fabea06d420d14af2a512dfbb4b125052c87abab29ed2ba0bb`;
its base HEAD remains `7d21a277`, not a committed repair revision.

| Implementation / model | Scenarios | Generated histories | Random histories |
|---|---|---|---|
| Historical source / source-shaped | 12/12, 79 steps, no divergence | seeds 1–5, 108 steps, no divergence | seeds 1–5, 320 emitted steps, no divergence |
| Historical source / corrected | 12/12, 79 steps, exactly 2 annotated divergences | 108 steps, exactly 10 planted-use divergences | 320 emitted steps, exactly 6 annotated planted-use divergences |
| Repaired / corrected | 12/12, 79 steps, no divergence | 108 steps, every generated fresh planted withdrawal rejected; no divergence | 320 emitted steps, no divergence |

Random scheduling still requests 60 steps per seed; the extra observations
exercise successor and planted credentials after finalisation. Successful calls
also passed implementation-produced VM transcript verification and rejection of
a changed recorded read. Deadline mutation detection found one intended
before-deadline divergence on both oracles; debit mutation detection found three
intended full-balance divergences. A mutant driver's nonzero exit is expected;
the mutation check and complete gate exit successfully only on detection.

Additional exercised checks:

- `src/Passport.agda` closure: checked, with no warning-gate diagnostics;
  no new escape-hatch inventory matches in `src/Conformance`.
- `Conformance.Main` MAlonzo build: passed.
- Harness strict TypeScript check (`--noEmit --strict`, NodeNext): passed.
- Repaired `account`, `control`, `faucet`, and existing `probe-block-time`
  simulator artefacts compiled with `--skip-zk --feature-zkir-v3`.
- Repaired TypeScript build, `test:unit`, `test:grants-offline` (121/121),
  `test:recovery-offline`, and `test:recovery-sim`: passed. The last suite
  exercised direct both-arm future plants, counter variants, two recoveries,
  successor restamping, current/stale removal, and explicit authorised re-enrolment.

Node/deployment and Rust cross-implementation checks were not performed.
`WALLET_SEED` is absent, repaired generated directories contain no proving or
verifier keys, and the required
`signer-rs/target/debug/account-custody-signer` executable is absent.
Simulator agreement is not proof-system, fee, node, or deployment evidence.

### Contract-organisation scenario evidence (2026-10-14)

The contract-organisation package passed the reader-entrypoint check and the
compiled `Conformance.Main` consumer check. The compiled consumer was executed
from `conformance/harness` with:

```sh
../../../arc-passport-recovery-conformance/contract/node_modules/.bin/tsx \
  recovery.ts --implementation source --variant both --only scenarios
```

Both variants passed all 12 scenarios (79 steps each): source/source had no
divergence; source/corrected had exactly the two annotated divergences.
This is scenario evidence for the reorganised model, **not** a repeat of the
full pinned gate, a repaired-implementation run, or a new enrollment snapshot.
The historical gate locks and results above were not overwritten.

### Historical primitive-boundary refactor evidence

Before the certified-transaction port, a temporary compiled consumer built an actual
`AccountRecovery.Chain.makeTx` deposit certificate at round 0, with balance 10
and deposit amount 3, then submitted that same certificate through `admission`:

| Admission state | Before primitive extraction | After primitive extraction |
|---|---|---|
| Original build view | Accepted | Accepted |
| State after the first deposit | Accepted | Rejected |
| Only round changed to 1 | Accepted | Rejected |
| Only balance changed to 11 | Accepted | Rejected |
| Only encryption key changed | Accepted | Accepted |

Both accepted controls in the updated model ended at round 1 and balance 13.
An independent run of the historical Compact VM's actual deposit transcript
replayed against its original view to the exact final VM state, but rejected
replay against its post-state: the recorded balance read was 10 and the current
balance was 13. This exercises the hidden-read mismatch and its model correction;
it is not a complete VM-to-Agda journal refinement or a node/proof-system test.

The rebuilt `Conformance.Main` passed the scenario command above for both
variants: 12/12 scenarios and 79 steps each, with no source/source divergences
and exactly two annotated source/corrected divergences. The compiled
`SmokeMain` also passed all seven checks across lock, balance and Merkle clients,
including genuinely replayable balance transfers. No global replay prohibition
was introduced. Historical enrollment locks were not changed.

## Caveats

- **Shared oracle.** As in the spike, hashing and curve arithmetic are the implementation's own.
- **Bounded signer loops.** The bounds are 512 draws per nonce (two nonces for `recover_submit`) and 512 grinds.
- **Build errors versus time refusal.** The model checks time at admission,
  after evaluating the body. A later body error therefore wins over a failed
  time condition, whereas the source may stop at that earlier condition.
  Examples include submission deadline/round overflow, finalisation counter
  overflow, and an initially pending recovery with a future deadline and an
  identity pending key. The last case fails the model's key check before
  admission, but the source checks time first. These examples are not an
  exhaustive classification over arbitrary represented states.
- **Not modelled:**
  - the `post_epoch` and `use_counter + 1` casts. In particular, submission at
    epoch `2^32 − 1` can fail the source's `post_epoch` cast before challenge and
    signature checks. A later finalisation failure does not make that initial
    state unreachable;
  - coin movements;
  - `recovery_version`: a constant 1, which the harness asserts;
  - the `recovery_phi` map shape beyond "empty or slots 1–4", which the harness also asserts.
- **Oracle 2's Agda certificate still uses the model's journal.** The harness now
  additionally obtains the implementation's `callProofDataTrace.publicTranscript`
  on successful simulator calls. It runs the recorded VM program in verifying
  mode against its initial query context, compares the complete replayed VM state
  with the implementation's final state, and requires rejection after changing
  the first recorded read. This is implementation-produced evidence, but it is
  **not** a decoder from VM operations into Agda `Event`s, nor a proof that the
  VM transcript refines the model journal. Aborted calls expose no completed
  proof-data trace; their oracle remains verdict and unchanged-state comparison.
- **Simulator, not chain.** Verdicts come from the compact-runtime simulator without proofs.
  `[INFERENCE]` A node runs the same circuit logic, so its acceptance verdicts would match; proving
  and fees are not exercised.
- **Observation boundaries.** Historical source-versus-corrected comparison uses
  the harness's `retained` projection. Repaired comparison observes only entries
  stamped with the contract's current device epoch; it does not pretend retained
  map cells were physically cleared. Neither projection is a verified refinement.

## Historical appendix: original recovery conformance report

This appendix preserves the **pre-repair, pre-gate measurements and setup**.
Its 379-step totals, static random annotations, source-only inventory, and cost
figures do not describe the current package. Use
[the pinned gate](#pinned-repeatable-gate) and
[historical results](#historical-exercised-package-results) above for recorded execution.

### Original result

**The implementation at `5d12798` accepts the old key after finalisation.** An adversarial
device `A`, enrolled at epoch 0, enrols the entry `A@epoch 1, counter 0` through ordinary
`add_device_with_jubjub`. A legitimate `recover_submit` (recovery key plus successor `S`)
follows, the simulator clock passes the deadline, and `recover_finalise` succeeds. `A` then
signs a fresh `withdraw_unshielded_with_jubjub` at the current nonce, and the implementation
accepts it: the balance goes from 1000 to 0. This needs no forgery, replay or collision. It is the
[future-epoch counterexample](recovery-specification.md#reachable-future-epoch-counterexample), executed on the real
circuits.

- **Source-shaped model:** agrees with the implementation on every step. Twelve scenarios
  (79 steps) plus seeds 1–5 × 60 random steps give 379/379 steps on both oracles.
- **Corrected model:** diverges on exactly the two annotated steps and agrees on the other
  377. It admits legitimate recovery: scenarios 1, 2, 7 and 12 finalise and then let the
  successor authorise.
- **Mutation check:** dropping the deadline guard `timeAtLeast pending_not_before` from the
  model is reported on both oracles (finalising at deadline − 1). The spike's debit mutation
  is still detected too. Both mutations are reverted.
- **Model bugs found:** none. One modelling gap surfaced and was closed: the
  `challenge as Field` cast aborts on challenges that were never ground (historical design note 3 below).

#### Original attack scenario, verbatim

Source-shaped model:

```
── scenario 11/12 future-epoch-attack [source]: Future-epoch enrolment followed by recovery
  #01 t=T0+0       deposit 1000                                               impl=ok                             model=ok                             O1=agree  O2=accept
  #02 t=T0+0       owner enrols adversary device A (epoch 0, counter 0)       impl=ok                             model=ok                             O1=agree  O2=accept
  #03 t=T0+0       A enrols the dormant entry A@epoch 1, counter 0            impl=ok                             model=ok                             O1=agree  O2=accept
  #04 t=T0+0       recover_submit: recovery key + successor S co-sign         impl=ok                             model=ok                             O1=agree  O2=accept
  #05 t=T0+87000   recover_finalise at the deadline                           impl=ok                             model=ok                             O1=agree  O2=accept
  #06 t=T0+87000   A signs withdraw 1000 at the current nonce (epoch 1, counter 0) impl=ok                             model=ok                             O1=agree  O2=accept
  PASS future-epoch-attack
```

Corrected model:

```
── scenario 11/12 future-epoch-attack [corrected]: Future-epoch enrolment followed by recovery
  #01 t=T0+0       deposit 1000                                               impl=ok                             model=ok                             O1=agree  O2=accept
  #02 t=T0+0       owner enrols adversary device A (epoch 0, counter 0)       impl=ok                             model=ok                             O1=agree  O2=accept
  #03 t=T0+0       A enrols the dormant entry A@epoch 1, counter 0            impl=ok                             model=ok                             O1=agree  O2=accept
  #04 t=T0+0       recover_submit: recovery key + successor S co-sign         impl=ok                             model=ok                             O1=agree  O2=accept
  #05 t=T0+87000   recover_finalise at the deadline                           impl=ok                             model=ok                             O1=agree  O2=accept
  #06 t=T0+87000   A signs withdraw 1000 at the current nonce (epoch 1, counter 0) impl=ok                             model=fail unknownDevice             O1=DIVERGE (verdict model=fail unknownDevice; state round: model=6 impl=7; authNonce: model=3 impl=4; devices: model=["a8a9bf432ca72296e48d800a5a19d4809b3592cf61db79d8003108e93bd4c578"] impl=["2cc40677d15a7f3e6a00766b54c44ee9048bd553c682da34836eb7dafd1e0449","a8a9bf432ca72296e48d800a5a19d4809b3592cf61db79d8003108e93bd4c578"]; balances: model=[["e85edf1550ba9bad7a64eb1360f6b0a3f4abf42910abb9e80385d0389bc9bd4e","1000"]] impl=[["e85edf1550ba9bad7a64eb1360f6b0a3f4abf42910abb9e80385d0389bc9bd4e","0"]])  O2=REJECT  [expected divergence ✓]
  PASS future-epoch-attack
```

The corrected run's device diff shows `2cc4…`, `A@epoch 1, counter 1`, which the seam inserted
when it rolled the planted entry. The projection described below already hides the
retained pre-recovery entries, so the remaining difference is exactly the old key's new
authority.

Summary lines of the full run (`tsx recovery.ts --seeds 1,2,3,4,5 --steps 60`):

```
RESULT [source]: PASS — scenarios 12/12 as annotated (79 steps, 0 divergent, 0 of them annotated); random seeds 1,2,3,4,5: 300/300 steps agree on both oracles; 12740 primitive round trips; wall 27.5s
RESULT [corrected]: PASS — scenarios 12/12 as annotated (79 steps, 2 divergent, 2 of them annotated); random seeds 1,2,3,4,5: 300/300 steps agree on both oracles; 12706 primitive round trips; wall 26.4s
```

### Original per-scenario measurements

The scenarios are [the specification's acceptance table](recovery-specification.md#acceptance-scenarios). "impl" is the implementation's verdict
on the step that carries the row's observation. Each scenario also checks that this verdict is the
one the row requires. `refused` means a chain-time assert failed.

| # | Scenario | Observation (impl) | Source-shaped | Corrected |
|---|---|---|---|---|
| 1 | Valid submission, eligible finalisation, successor use | submit ok; finalise at the deadline ok (no signer); `S` rotates and enrols ok; old owner `unknownDevice` | 5/5 agree | 5/5 agree |
| 2 | Finalise before, at, after deadline | deadline − 1 `refused`; deadline ok; a second recovery finalised at deadline + 3600 ok | 5/5 | 5/5 |
| 3 | Cancel before finalise | cancel ok; finalise `noPending`; owner still authorises | 4/4 | 4/4 |
| 4 | Cancel after deadline, before finalise | cancel at deadline + 10 ok (no deadline check); finalise `noPending` | 3/3 | 3/3 |
| 5 | Finalise before old-device cancellation | old owner cancel `unknownDevice`; **old device `A` passes the seam through its planted entry** and fails only on `noPending` | 6/6 | 5/6: step 6 diverges as annotated (`unknownDevice`) |
| 6 | Cancel then replay old submission | verbatim replay `staleNonce`; fresh submission ok | 4/4 | 4/4 |
| 7 | Ordinary device use while pending | rotate, withdraw and enrol while pending all ok; pending kept; finalise ok with a moved nonce | 6/6 | 6/6 |
| 8 | Publish session while pending | `recoveryPending`, full rollback; after cancel, publish ok | 4/4 | 4/4 |
| 9 | Wrong account, key, epoch, nonce, time bound | foreign account `invalidRecoverySignature` / `challengeRange`; stranger recovery key and swapped successor `invalidRecoverySignature`; altered successor response `invalidSuccessorSignature`; raised `now_upper` `challengeRange`; `staleEpoch`; `staleNonce`; past bound `refused`; reused / identity successor recovery key `commitmentReused` / `identityKey`; identity successor `identityKey`; deadline overflow `overflow`; correct binding ok | 15/15 | 15/15 |
| 10 | Failed operation after tentative credential roll | `noPending`, `lastDevice`, `entryPresent`, `authorisingDevice`, `unknownDevice`, `insufficientBalance`, `phiEmpty`, `phiLength`, `phiSlot3`, `sessionZero`, `commitmentReused`, `identityKey`, `sessionReused`, each after the seam rolled the entry; state unchanged | 16/16 | 16/16 |
| 11 | Future-epoch enrolment followed by recovery | **old key's withdraw accepted** | 6/6 | 5/6: step 6 diverges as annotated (`unknownDevice`) |
| 12 | Ordinary encryption-key rotation | rotation ok before, during and after recovery | 5/5 | 5/5 |

Seeded runs: seeds 1–5 × 60 steps, with a veto window drawn per seed (93 990 s – 407 144 s).
The steps mix deposits, withdrawals, enrolment, future-epoch planting, removal, rotation,
stale counters, stranger signatures, publication (valid, malformed, and while pending), submission
(valid, stale nonce, stranger, past bound), replay, cancel, and finalisation just before and
at/after the deadline. Across the five seeds, 14 finalisations succeed, 5 are refused before
the deadline, and 25 find nothing pending. Both models agreed on these original 300 steps;
the original generator did not attempt planted credentials after recovery.

### Original reproduction setup (historical only)

These commands record the earlier checkout/setup, not current gate instructions.
For new checkouts, repository guidance requires worktrees inside `.worktrees`.
Current repaired setup uses the explicit path/mode commands above and below.

1. **Implementation revision.** `../arc-passport` is the `input-output-hk` fork and lacks the commit, so fetch it by hash
   without adding a remote, then create the worktree:
   ```
   git -C ../arc-passport fetch https://github.com/midnightntwrk/passport.git 5d12798321d3daba37b1da90162ee1468daf38a6
   git -C ../arc-passport worktree add ../arc-passport-recovery-conformance -b recovery-conformance 5d12798321d3daba37b1da90162ee1468daf38a6
   ```
   Branch `recovery-conformance` adds two commits on top, both made with `git commit --no-gpg-sign`. They make
   the nonce draws injectable and leave the defaults unchanged:
   - `1bff2a5`: the spike's `85f5db4`, cherry-picked: `sign(challenge, useCounter, draw)` and
     `randomJubjubScalar(draw32)`.
   - `7d21a27`: `signRecoverSubmit(recovery, successor, build, fields, draw = randomJubjubScalar)`,
     which draws the recovery nonce first and then the successor nonce.
2. **Compile and gate.** In `contract/`: `npm install`, then
   `compactc --skip-zk --feature-zkir-v3 contracts/X.compact contracts/managed/X` for `account`,
   `control` and `faucet`. The compiler is the spike's 0.33.0-rc.2, and the pins are unchanged at this revision.
   The offline suites passed before and after the two commits:
   - `test:unit`, `test:recovery-offline`, `test:recovery-sim`: PASS.
   - `test:grants-offline`: 121 passed.

   `test:crossimpl-offline` cannot run on this machine: it needs the Rust signer binary
   (`signer-rs/target/debug/…`), and there is no `cargo`.
3. **Model.**
   `pagda --useUntracked false check src/Conformance/Main.agda -- --compile --compile-dir=_build/conformance --ghc-flag=-O0 +RTS -M3G -H1G -RTS`
4. **Harness**, run from `conformance/harness/` with `<worktree>/contract/node_modules/.bin/tsx`:
   - `recovery.ts [--variant source|corrected|both] [--only scenarios|random] [--seeds 1,2,3] [--steps 40]`
   - `main.ts --seed N --steps N`: the custody run of the spike, now at `5d12798`.
   - `mutation.ts deadline` and `mutation.ts debit`.

   `IMPL_DIR` defaults to `../arc-passport-recovery-conformance/contract`.

### Original model and harness inventory

This records the historical layout. The current checker split and interfaces
are described in [Runtime transition monitor](#runtime-transition-monitor).

| File | Role |
|---|---|
| `src/Conformance/Primitives.agda` | Crypto record. Adds `Bytes64`, `zero32`, the add/remove/rotate/publish/cancel/submit challenges, and `fieldOrder` |
| `src/Conformance/Decidable.agda` | `via`: decidable equality along an encoding with a partial left inverse (stdlib `via-injection`). Keeps `Op`/`Name`/argument equality linear in size |
| `src/Conformance/AccountLedger.agda` | State extended with `enc_key`, `recovery_pk`, `recovery_phi` (`nothing` or the four slots), `recovery_phi_len`, `recovery_session`, `recovery_wrap`, `pending_*` and `veto_window`. New reads and writes with `Uint<8/32/64>` bounds. `Finalisation` (`sourceShaped`, `corrected`) selects `install` = `installSuccessor` (`devices.insert` plus `device_count = 1`) or `replaceDevices` |
| `src/Conformance/Custody.agda` | Assertion codes, the seam `authorise` (`require_authorised_with_jubjub`), `requireLive` (`require_live_jubjub_point`), `asField`, and the `deposit`/`doWithdraw` chips |
| `src/Conformance/Recovery.agda` | `doAddDevice`, `doRemoveDevice`, `doRotateEncKey`, `doPublish`, `doCancel`, `submitRecovery`, `finaliseRecovery`, in the source's assert order |
| `src/Conformance/Account.agda` | Wallet clients `sign`/`signPair` (two nonces, one grind), and `stepModel`/`decide` at a block time; consumes the single assembly in `Passport.AccountRecovery` for either conformance variant |
| `src/Conformance/Main.agda` | MAlonzo executable. The line protocol carries `VARIANT` and `TIME` |
| `conformance/harness/driver.ts` | Honest client: signs with the implementation's own builders and records the draws. Runner: both oracles plus the corrected-model projection |
| `conformance/harness/recovery.ts` | Twelve scenarios with `expect`/`diverges` annotations, and the seeded runs |
| `conformance/harness/{impl,model,main,mutation}.ts` | Simulator seam with the 5d12798 constructor; model RPC; custody run; mutation table |

- **Time.** `recover_submit`'s `!blockTimeGreaterThan(now_upper)` becomes
  `atChain (timeAtMost now_upper)`, and `recover_finalise`'s `!blockTimeLessThan(pending_not_before)`
  becomes `atChain (timeAtLeast pending_not_before)`. Admission therefore replays them against the
  submission's `now`. `stepModel` and `decide` take that time, and the harness passes the
  simulator's `time` for the same call. The two assert messages map to the settlement
  `refused`.
- **Corrected comparison.** A corrected finalisation drops the entries that the implementation
  keeps. Whenever a finalisation succeeds, the runner records the implementation's
  pre-finalisation entries as `retained`. It then compares the corrected model with the
  implementation state minus `retained`, on both oracles; `decide` is given the projected pre-
  and post-states. For the source-shaped model `retained` stays empty. As a result, legitimate
  recovery agrees, and only the use of a retained entry diverges.
- **Annotations.** A step with `diverges: [variant]` must diverge for that variant, and every
  other step must agree. `expect` lists the admissible implementation verdicts for the row's
  observation. Either kind of failure fails the run.

### Historical design notes

1. **Module layout (historical).** The original recovery spike passed
   `Finalisation` through `Conformance.Account` and called the assembly `passport`.
   The current reader-facing assembly is `Passport.AccountRecovery`, with its
   intended `contract` distinguished from `assemble sourceShaped`. The two
   executable variants still differ only in `install`. `Custody` holds the seam,
   assertion codes and custody chips; `Conformance.Account` holds wallets and
   oracles. The request grammar remains `S`/`U`/`X`.
2. **The custody harness moved to `5d12798`.** At that point its default `IMPL_DIR`
   changed with the constructor/state shape. Seeds 1–3 × 60 agreed 60/60.
3. **`challenge as Field` is modelled.** The spike listed it as unreachable. The wrong-account and
   tampered-argument rows make it reachable: a challenge recomputed over other arguments is not ground,
   so the cast aborts (`range error … exceeds maximum value … of Field type`) in about 55 % of cases.
   `Custody.asField` asserts `le h < q` with code `challengeRange`, at the cast's position in the
   seam and in `recover_submit`. These rows accept either rejection.
4. **Adversarially built calls are `raw` requests.** The model wallet signs only for its own account.
   Foreign-account signatures, tampered copies and verbatim replays therefore reach the model as
   `raw` calls built outside the wallet. Oracle 1 then compares verdict and state, but not the signature.
5. **"Unrelated finalising caller" is vacuous at the circuit level.** `recover_finalise` reads no
   caller and takes no signature, so the scenario shows that no signer is involved. The simulator
   runs it in the same context as every other call.
6. **Original generator limitation (now addressed).** Those seeded runs planted
   future-epoch entries without using them after finalisation; only scenarios 5
   and 11 attempted them. The current generated and random histories above do use
   planted credentials, with exact dynamic divergence obligations.
7. **Gate.** `test:crossimpl-offline` was not run, because it needs the Rust signer. The other offline suites
   were run.

### Original cost measurements

| | Size / time |
|---|---|
| Model (`--safe`) | 1013 LOC: Primitives 44, Decidable 17, AccountLedger 325, Coins 37, Custody 126, Recovery 126, Account 338 |
| Model `Main` | 326 LOC |
| Harness | 1468 LOC TS: driver 260, recovery 511, impl 326, model 115, main 116, mutation 69, prng 67 |
| Implementation change | 2 commits, +14/−9 lines (`signer.ts`, `recovery-gate.ts`) |
| Per-module warm check | 3–8 s |
| MAlonzo build | ≈ 10 s incremental (`-O0`) |
| Scenarios, one variant | ≈ 7 s, ≈ 3.3 k primitive round trips |
| Full run (12 scenarios + 5 × 60 random, both variants) | ≈ 54 s, ≈ 25 k primitive round trips |
| Mutation check | `deadline` ≈ 57 s, `debit` ≈ 20 s, mostly the mutant build |

Development iterations: two harness bookkeeping errors (adopting the successor after an early
finalisation; a fractional time step from an odd veto window) and the `as Field` cast
(historical design note 3). No model guard had to change.

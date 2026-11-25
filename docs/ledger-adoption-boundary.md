# Ledger adoption boundary

## Status and reading route

**This is a trust-boundary specification, not an adoption theorem or full P11.**
It identifies the additional correspondence needed to use Passport's existing
local withdrawal theorem for an execution actually committed by Midnight. The
candidate platform assumptions below are **not approved assumptions or established
truths**. No Agda bridge is added: a wrapper taking the desired local execution
as a premise would not establish the missing correspondence.

**Full-validation application remains BLOCKED.** The 2026-11-09 investigation
did execute native `LedgerState.apply`, including partial failure, but only with
three validation checks disabled and synthetic ledger funding. Those diagnostic
results are not authenticated adoption. All 141 sampled source transcripts were
checkpoint-free: no within-call authority-only prefix survived; complete calls
did survive failures of other segments. See [the measured scope](#partition-and-application-diagnostics)
and [the exact platform blocker](#current-platform-and-full-validation-blocker).

Read [Account](../src/Passport/Account.agda),
[TransactionSafetyProperties](../src/Passport/TransactionSafetyProperties.agda)
and [TransactionSafety](../src/Passport/TransactionSafety.agda) for the existing
specification and claim. The [proof](../src/Passport/TransactionSafetyProof.agda)
classifies the actual dispatched withdrawal; it does not choose an authorization
branch on the caller's behalf. [Conformance scope](conformance-testing-plan.md)
and the [cryptographic audit](cryptographic-assumptions-audit.md) explain the
separate execution and cryptographic boundaries. Start with the
[partition/application evidence](../conformance/ledger-partial-execution-evidence.json)
and its [runner](../conformance/harness/ledger-partial-execution.mjs).
The earlier [VM-only smoke](../conformance/harness/ledger-adoption-smoke.mjs)
and [result](../conformance/ledger-adoption-evidence.json) remain historical evidence.
The [commitment-binding audit](commitment-binding-audit.md) separately identifies
canonical encoding and opening-agreement obligations; authenticated context
does not discharge them.

The intended claim is deliberately narrow: **a fully applied Passport call,
placed in a deployment-rooted, correctly ordered source history, inherits the
existing theorem's conditional source-level conclusions**. Whether any given
ledger event meets that description remains an obligation. A submitted
transaction, a successful native circuit invocation, and a finalized but partly
successful transaction are not interchangeable evidence.

## Evidence identity and authority

Paths beginning `contract/` below are relative to the pinned implementation
checkout `/Users/andre/IOHK/arc-passport/.worktrees/formal-correspondence-main/`.
`node_modules/` paths are relative to its `contract/` directory. Formal source
references are at base `b87ccbeb556ace4b28265f49f0310c384f287451`.

| ID | Source and exact scope |
|---|---|
| E1 | Passport implementation [`fc19e471536febb2133f20e817847251622dcdf5`](https://github.com/midnightntwrk/passport/tree/fc19e471536febb2133f20e817847251622dcdf5/contract), especially `contracts/account.compact`, `src/wallet/witnesses.ts`, `package.json`, `package-lock.json`. [Main pins](../conformance/harness/passport-main-pins.json) identify source and generated artifacts. Compiler **0.35.0**, commit `debb05f9414b9d1e176741c2be289bb32233f0fc`, runtime **0.20.0**; the local generated-artifact evidence uses `--feature-zkir-v3 --skip-zk`, not generated proofs. |
| E2 | Installed **`@midnightntwrk/ledger-v9` 1.0.0-rc.5**, `ledger-v9.d.ts`: `CallContext`/`BlockContext`/`Effects` (lines 299–402), `QueryContext.runTranscript` (860–924), `WellFormedStrictness` (1286–1313), `LedgerState.apply` (1720–1752), `ContractCall` and prototypes (1969–2064), `TransactionContext`/`TransactionResult` (2179–2217), `SegmentSpecifier`/`Transaction` (2378–2508), `partitionTranscripts` (2619–2641). [Exact-version API distribution](https://unpkg.com/@midnightntwrk/ledger-v9@1.0.0-rc.5/ledger-v9.d.ts); [primary npm metadata](https://registry.npmjs.org/@midnightntwrk/ledger-v9/1.0.0-rc.5). API SHA-256 `6fa8f901365f2a4975c432a669034d67b7173d5a488e7bef2090abb2bd26035d`; native WASM SHA-256 `41204f5f7ea5931a2debef32065cc97837aacaf95c91591b1fe5f38e0f148d58`. |
| E3 | Installed **`@midnight-ntwrk/compact-runtime` 0.20.0**, `dist/circuit-context.js`, especially `createCircuitContext`, `createInitialQueryContext`, `createCallContext`, `queryLedgerState`; underlying **`@midnightntwrk/onchain-runtime-v4` 4.0.0-rc.3**. The context constructor accepts host-provided state, address, time and optional caller. Exact installed file hashes are in the result record; the runtime package identity is also covered by E1's pins. |
| E4 | Installed **`@midnight-ntwrk/midnight-js-contracts` 5.0.0-rc.2**, `dist/index.js`: `submitTx` (1974 onward), scoped submission (3050–3067), `createUnprovenLedgerCallTx` (3531–3588), `submitCallTx` documentation (3830 onward). It creates one `ContractCallPrototype` per call, attaches both transcript halves, obtains each deployed operation/verifier key, aggregates native offers by section, and refuses non-`SucceedEntirely` results before private-state persistence. SHA-256 `16a0f7566e9b27761cb34f256f005c7e8e757689bf273358d588b5c71ff26d7e` identifies the inspected installed file, rather than inferring its contents from a version label alone. |
| E5 | Historical implementation [`GRANTS-E2.md`, S12–S14](https://github.com/midnightntwrk/passport/blob/fc19e471536febb2133f20e817847251622dcdf5/contract/GRANTS-E2.md#composition-s13), and `contract/evidence/grants-e2-composition-grants-conformance-composition.json`. The recorded ordered pair advances grant nonce twice; its reversed pair is rejected with `ReadMismatch`, nonce unchanged. The prose also reports another run with one fallible call applied, but the cited JSON is the whole-rejection run. These are **historical reports**, not fresh results or universal semantics. Attribution: compiler **0.33.0-rc.2**, compact-js **2.5.5-rc.6**, midnight-js **5.0.0-beta.4**, node **2.1.0-2e92c4ae642c**, indexer **4.4.0-rc.2**, proof-server **9.0.0-rc.6**; not the E1 toolchain. |
| E6 | `contract/TOOLCHAIN-0.35.md` and `contract/infra/docker-compose.yml` identify the later localnet: node **2.1.0-rc.4**, indexer **4.4.0-rc.6-b5e6c809**, proof-server **9.0.0-rc.8**, with image digests and limited coinless execution evidence. That report expressly does not rerun the full grants/custody/recovery suites. It does not upgrade E5's attribution. |
| E7 | Primary upstream ledger revision [`67f9f97246339539af0091c4d8c6bc5ab236a191`](https://github.com/midnightntwrk/midnight-ledger/tree/67f9f97246339539af0091c4d8c6bc5ab236a191), tag `ledger-9.1.0.0-rc.5`: `ledger-wasm/package.json` declares version `1.0.0-rc.5`; `ledger/src/construct.rs` partitions at checkpoints; `ledger/src/semantics.rs` applies guaranteed state then independently commits successful fallible segments; `ledger-wasm/src/tx.rs` exposes the result. [Fetched excerpts and response hashes](../conformance/ledger-primary-source-evidence.json) fix the source inspection. This is version-corresponding source, **not a demonstrated build provenance for E2's binary**. |

The npm ledger package/metadata supplies no `gitHead`. E7 was successfully
retrieved during this investigation, superseding the earlier HTTP-504 obstacle.
Its package name is `@midnight/ledger-v9`, whereas the installed package is
`@midnightntwrk/ledger-v9`; no reproducible source-to-WASM match is established.
Binary observations below are attributed to the hashed E2 installation, not
inferred from Rust source alone. Neither source inspection, API documentation
nor sampled WASM behavior is an implementation-correctness proof.

## The execution unit to adopt

A **ledger application record** must identify the network/era, finalized block
hash and position, transaction/intent identity, target contract address, entrypoint,
physical segment, call/action position, logical execution section, relevant
predecessor and successor account state, transcript/effect descriptions, and the
actual section/segment result. E2 exposes both `logicalSegment` and
`physicalSegment` on events, `successfulSegments` on `TransactionResult`, and
separate guaranteed/fallible transcripts on `ContractCall`. Do not invent one
source step per transaction or use only a transaction-wide status flag.

**Do not interpret the Boolean from `successfulSegments` by its name.** In the
installed WASM, a partial result with native debug status `0: Ok, 1: Err` exposes
`[[0,false],[1,true]]`. E7's
[`successful_segments`](https://github.com/midnightntwrk/midnight-ledger/blob/67f9f97246339539af0091c4d8c6bc5ab236a191/ledger-wasm/src/tx.rs#L1895-L1910)
uses `v.is_err()`, not `v.is_ok()`. The evidence retains the raw map, native debug
result, events and actual state/asset deltas; it never calls `true` a success.

The candidate **source adoption unit** is one *complete source call*, with its
actual transcript halves and effects attributed to their ledger sections. A
physical segment may contain multiple calls. A call may have both guaranteed
and fallible parts. Therefore a call/segment identifier alone does not establish
that one whole `Account.Transition` occurred.

For a call to enter the narrow correspondence domain:

1. Its entire account-state change and its required native effects must have
   applied, not just its guaranteed prefix or an SDK-local post-state.
2. Its execution must admit a linearization point/order in which all source
   reads see the decoded predecessor, and its successor is the next account
   state in that order. Source-call order cannot be guessed from build order,
   JSON array order or signature creation time.
3. Its decoded context and call arguments must describe the same proved call;
   its private witnesses may be existential and need not be published, but must
   be bound by the proof statement, not supplied afterwards by an observer.
4. The preceding account trace must be complete from the matching deployment.
   Omitting an unmodeled state-changing fragment cannot be repaired by simply
   omitting its event from the history.

This is a domain restriction to be checked or proved, **not a claim that all
Passport ledger executions satisfy it**. In particular, splitting one source
call across phases and then failing its fallible part can leave a state that is
neither its source pre-state nor its full source successor. Such an execution
cannot be represented by either `committed` or `reverted` merely by choosing a
convenient label. If a ledger partial failure consists solely of other complete
calls plus zero-account-change failures, those complete calls may be projected
only after establishing that decomposition. Otherwise the whole-call bridge is
inapplicable beyond the fragment; a segment-level source semantics would be a
separate, unapproved extension.

No impossibility of serializing Passport's ledger executions has been proved
here. The missing result is a serialization/coverage argument for the actual
partitioning semantics, including every relevant committed state-changing
prefix, not just a selection of fully successful calls.

### Ordering, stale views and revocation

The current state at **application**, not the builder's historical view, is the
predecessor. E5's ordering refusal is a transcript read mismatch, not signature
invalidation. A still-valid signature or even a successful proof does not by
itself establish that a nonce, active flag, generation, device epoch or native
coin remains usable when the call lands.

An adopted revocation must precede the spend at the actual application order.
`FullAccountGrant.validateGrantRecord` checks active/epoch/generation in that
order; source recovery/revocation theorems concern those ordered occurrences.
A locally prepared or merely submitted revocation is not that occurrence.
A competing spend ordered first is not retroactively prohibited. After reissue,
identify the new issuance episode; do not reuse the previous episode's cap or
replay claim. Relevant device-entry separation still matters: neither address
identity nor platform order supplies it.

Unrelated global ledger activity can be ignored only when it leaves the projected
account state unchanged and its context consequences are incorporated. A delayed
transaction need not fail merely because *some* state changed; all its relevant
reads/effects must still match. Conversely, reads against a stale indexer snapshot
must not be treated as the authenticated application predecessor.

## Authentication and candidate obligations

The following are **candidate trusted-platform/compiler/proof-system
assumptions** if ultimately adopted by the user, or proof obligations if their
implementations are verified. None is discharged by this specification. They
are operational correspondences, not premises named “ledger withdrawals are safe.”

| ID | Required correspondence | Evidence and unresolved part |
|---|---|---|
| **A1 — deployment/code identity** | Authenticate network/era, account address, deployment state/schema, entrypoint and deployed verifier key against the pinned source/compiler artifacts. Track maintenance/key replacement; exclude or model upgrades rather than silently following a new program at the same address. | E1 pins local code; E4 reads deployed operations/keys; E6 has historical key-maintenance evidence. No current-chain deployment/key-root certificate or universal artifact/key correspondence is supplied. The local lifecycle fixes `self`; raw `Account.step` alone does not authenticate it. |
| **A2 — compilation and proof binding** | A valid contract proof under that deployed key binds the ABI input/output, public transcript, private witness outputs and communication commitment to a legal execution of the pinned source circuit. Lowering and VM replay preserve all relevant reads, assertions, writes and native-effect declarations, including partitioned execution. Choose an actual `Primitives` interpretation matching the native operations. | Existing formal VM results concern local opcode/representation behavior; conformance compares finite generated executions. Neither proves compiler correctness, constraint completeness, proof-system soundness, key generation correctness or WASM/source refinement. `--skip-zk` evidence is not proof verification. No extraction/public disclosure of secret witnesses is asserted. |
| **A3 — application-state/order correspondence** | Ledger replay uses authenticated current account state, validates recorded reads, enforces the protocol's actual action/section order, and produces decoded states that serialize complete source calls where this bridge is applied. Preserve failed-prefix effects explicitly rather than dropping them. | E2 distinguishes reference state in `TransactionContext` from application through `LedgerState.apply`. E5 and the fresh native ordering probe support particular read-mismatch behavior. They do not prove serializability of arbitrary multi-call/phase schedules, or fresh-state checking for every source read. |
| **A4 — context authentication** | `self` is the target account; `caller` is authenticated by the ledger's calling/user-authorization rules, not a witness or host field; all source time comparisons correspond to the ledger's admissible time observations. Account for absent/user/contract caller tags, cross-contract communications, reference-block identity, time-error margin and previous-block time. | E2 exposes `ownAddress`, optional `caller`, `secondsSinceEpoch`, `secondsSinceEpochErr`, `parentBlockHash`, `lastBlockTime` and balances. E3 and the fresh probe show that local context fields are host-controlled. A single source `blockTime : ℕ` must give **all** the call's comparison results, with any protocol time interval/margin justified. No direct equality to wall-clock time, monotone-time theorem or caller-authentication theorem is supplied. |
| **A5 — asset/effect and rollback correspondence** | Every applied native transfer/claim is reconciled with the same call's source effect, address, token kind/color, amount, recipient, commitment/nullifier, coin ownership and applicable segment. Validate inputs, membership and no double spend; bind contract-to-contract claims/receives and preserve multiplicity. Account for change outputs. Whole source state/effects must commit together within the bridge's domain; failed fallible effects must not be counted as transferred value. | E2 `Effects`, native offers, `addCalls` and segment-bound APIs expose the checks to relate; E4 assembles them; E5 reports missing-offer, reordered-call and coin-race refusals. The source `held_coin` is a private value, not evidence of ownership/unspentness. Local `receiveUnshielded` emits a claim without funding an account. No value-conservation, asset-authentication or full rollback refinement theorem follows. Fees/DUST are outside `Account.State` and must be separated, not silently attributed to a withdrawal. |
| **A6 — adoption/finality and data authenticity** | Select a specified finalized canonical ledger prefix under the actual network's finality rule; authenticate block/state/transaction/segment results and the relevant deployment. An indexer's response is either verified against that chain or an explicitly trusted read provider. Resolve inclusion, phase result, finality and local private-state persistence separately. | E2 application is an in-process API, not consensus. E4 waits for provider results and can throw after partial execution; a transport failure/timeout proves neither rollback nor success. E6 supplies historical node/indexer observations, not a finality theorem. No finality certificate, consensus security argument, reorganization policy or current authenticated receipt was obtained in this run. |

A2 concerns execution integrity, not the separate security realization of Passport
signatures. A valid proof of a circuit verifying a signature does not establish
that an uncompromised human approved its intended request. Likewise A4 authenticates
which caller/time the platform supplied; it does not show that a digest uniquely
binds an intended policy opening. Existing opening, separation and symbolic
signing premises remain visible and independent.

### Effect commitment and partial failure

E2 describes guaranteed execution first (including fee payment), followed by
fallible execution with rollback on failure. Its result type is
`success | partialSuccess | failure` with a segment-success map. The singular
wording of the transaction API comment does **not** establish that every fallible
segment rolls back together; E5's separate historical partial-application report
is a reason to retain segment-level results, not to flatten them. Exact rollback
granularity and cross-segment dependency rules still require version-matched
source or execution evidence.

For every mapped call, retain four distinct facts: (1) local circuit result,
(2) public VM replay result, (3) ledger section/segment result and installed
state/effects, (4) canonical finality. `Account.transaction` rolls a **local
rejected execution** back to the old account state and discards all its effects.
It does not say that a transaction rejected by an SDK, a failing fallible segment,
or a proof-provider exception rolls back all earlier ledger work. Nor does it
promise rollback of fees or wallet-local I/O. E4's decision not to persist private
state on a non-entire-success result cannot undo state already committed on chain.

If a fragment updates authorization counters but its transfer fails, or a native
transfer survives without the corresponding full source state update, report the
fragment and stop the whole-call correspondence. Do not classify it as a safe
withdrawal, erase it as a refusal, or resume the history from an invented state.
Those possibilities are obligations to rule out or model, not observed Passport
vulnerabilities asserted by this document.

## Concrete correspondence interface to the existing theorem

This is a specification of the missing interface, **not an implemented Agda
record with unproved fields**. Its inputs and outputs name existing definitions
so a future implementation has a precise target.

| Ledger-side input/check | Source-side output or equation | Gap |
|---|---|---|
| Authenticated deployment, target address and complete decoded initial state | `Account.Deployment`, `AccountLifecycle.Environment`, and `DeploymentSucceeded address env d (Account.committed value effects) s₀` | A1/A2/A5/A6; cannot start from an arbitrary represented snapshot. |
| Actual call identity/ABI and existence of its proof-bound private values | `RuntimeCall` with the actual `RawCall`; known runtime entrypoint membership; not the constructor | A1/A2. Public bytes may hide inputs; the bridge needs a sound existential correspondence, not observer-chosen openings. |
| Applied context, including authenticated caller/time and witnessed qualified coin | `executionContext address environment` with that environment's `time`, `callerValue`, `witnessedCoin` | A2/A4/A5, and compatibility of all time predicates with one source time. |
| Decoded predecessor, full source execution and fully installed successor/effects | `dispatch P ctx rawCall s ≡ accepted answer t effects`, hence `Account.Transition P ctx rawCall s (Account.committed answer effects) t` | A2/A3/A5 must derive this from proof/replay/commitment semantics. Taking this equation as an unexplained platform axiom would be the missing bridge, not a new proof. |
| All earlier complete calls in application order, with every account mutation covered | `Runs.History s`; the current transition becomes `RevocationExclusion.CommittedOccurrence s t` with exact environment/call/answer/effects | Root plus source transitions supports the existing lifecycle construction. Partial state-changing fragments block this history; ledger failures can simply be omitted only when account state truly did not change. A ledger-level failure is not automatically a source `reverted Error`. |
| This actual call resolves to a withdrawal; independently justified intended policy/spent openings | `WithdrawalCall event`, `HistoryAgreement h`, `IntendedOpening h event policy`, `ScopeAgreement h event policy`, `SpendAgreement h event policy` | These are the existing theorem's premises, not A1–A6 conclusions. Platform correctness cannot supply intended policy or collision/separation facts. |

Once those particular inputs are established, the existing application is exactly
`transaction-safety h event policy withdrawal historyAgreement intendedOpening
scopeAgreement spendAgreement`. Its conclusion is `TransactionSafety h event
policy`: the actual singleton signed request is classified as device or grant;
source authorization checks hold; device consumed-credential refusal is
conditional on old/rolled-entry separation and immediate, whereas the grant
branch has semantic scope, the historical issuance cap including this spend,
and conditional historical symbolic-token exclusion.

`safe-request-provenance` additionally needs the joint symbolic signing history,
availability of the actual required tokens and trace-local exact-request
agreement. Those are not consequences of an authenticated ledger receipt.
Native signature unforgeability/encoding realization, arbitrary-intervening-call
device replay, value/effect preservation and full adoption-level P11 remain
outside the existing conclusion.

### Why the earlier admission layer is not this bridge

[`Contract.Transaction`](../src/Midnight/ContractDSL/Contract.agda) carries an
`eval` certificate for a **different** `Program` language and a build view.
`Contract.admit` checks the target and atomically replays that language's journal
at `Submission.now`. [`AdmissionProperties.accepted-execution`](../src/Midnight/ContractDSL/AdmissionProperties.agda)
proves a fresh evaluation from successful replay; `rejection-atomic` proves
rollback in that model. [`Protocol`](../src/Midnight/ContractDSL/Protocol.agda)
wraps those same admissions, including publication suppression on rejection.

The full-account evaluator instead uses `Execution`, `Context` and its own
`Effect` list. Its immediate `readTimeLess`/`readTimeGreater` observations are
not `Program.atChain` deferred conditions. `Account.Transition` is the graph
of `step`, not an admission certificate. No semantics-preserving translation
from the full account/native partitioned transcripts to the earlier `Program`
has been established. Therefore neither `accepted-execution` nor the earlier
categorical protocol's reachability theorem can be imported as a proof of A2–A5.

## Executed evidence and precise limits

### Historical VM-only smoke

The 2026-11-06 [smoke result](../conformance/ledger-adoption-evidence.json)
executed the generated constructor and two `deposit_unshielded` calls, then
replayed and partitioned their real transcripts. Balances were `0 → 7 → 18`,
rounds `0 → 1 → 2`, and both 34/38-operation transcripts were wholly guaranteed.
Stale/reversed replay failed with a read mismatch; a bounded overflow was refused
locally. Host-supplied caller/time fields were retained. That run did **not**
execute `wellFormed`, `LedgerState.apply`, proofs or a node. Its two earlier
fixture corrections remain recorded. The following is new, separate evidence.

### Partition and application diagnostics

The [isolated runner](../conformance/harness/ledger-partial-execution.mjs)
uses the pinned generated contract, production witness construction and genuine
local source signatures, through the existing
[full scenarios](../conformance/harness/full-scenarios.ts). No formal VM is used
in this runner; the existing optional formal-comparison route remains separate.
It asserts exact decoded public-state equality, not just selected counters.

| Measured scope | Result |
|---|---|
| Main/full native scenario invocations, plus two positive grant spends per scheme | 141 successful nonconstructor calls; all **52** runtime entrypoints covered |
| Native standalone partition | 96 wholly guaranteed, 45 wholly fallible, **0 split calls**, **0 checkpoint operations** |
| Local builder outcomes | 147 accepted (including six constructors), 114 rejected; complete outcomes and origin labels retained |
| Diagnostic transaction attempts | 513: **192 success**, **105 partialSuccess**, **120 failure**, **96 pre-application `wellFormed` refusals** |
| Schedule records | 87: six whole-account partition probes, 69 adjacent-call pairs, 12 sender/receiver compositions; stale-competitor controls are additionally retained in `applications` |

The 126 main-suite calls and 15 calls for consecutive positive-grant scenarios
make up the 141 partition records. Twelve extra real `deposit_shielded` receiver
calls are composed with the sender probes; they are recorded in those schedules,
not counted as additional standalone entrypoint coverage. Whole-account batches
are **partition-only** probes, not complete histories applied to a ledger.

The standalone partition below was identical across jubjub, k256 and p256 for
the sampled branches. `G`/`F` describes the **entire** call, not an intrinsic
classification of the entrypoint: composition can change the chosen section.

| Source operation classes | Entrypoints | Sampled standalone section and operations |
|---|---:|---|
| Initial activation, each authentication arm | 3 | G 40 |
| Permissionless unshielded/shielded deposit | 2 | G 34 / G 33 |
| Device-authorized append inbox / rotate key / add device / remove device | 12 | G 64 / G 53 / G 66 / F 74 |
| Device unshielded withdrawal | 3 | G 94 |
| Device shielded withdrawal, to user or contract | 6 | Exact: G 63; change: F 75 |
| Device-authorized issue / revoke / revoke-all grants | 9 | Issue F 67, same-ID reissue F 71; revoke G 62; revoke-all G 61 |
| Grant unshielded withdrawal | 3 | G 80, including the source-accepted zero-value case |
| Grant shielded withdrawal, to user or contract | 6 | Exact: G 52; change: F 80 |
| Device-authorized publish recovery / cancel recovery | 6 | F 102 / F 74 |
| Recovery submit / finalise | 2 | F 69 / F 92 |

In E1, jubjub/k256 authorization updates the scratch device membership before
signature verification, whereas p256 verifies WebAuthn before that update
(`account.compact` 847–912; `account-p256.compact` 57–70). Successful device
authorization advances the device commitment, `auth_nonce` and `round`.
Grant settlement instead advances grant `nonce`, `spent_commit` and `round`,
not the device authorization counter (`account.compact` 1944–1968, 2008–2035;
`account-p256.compact` 332–343). Unshielded withdrawal then debits the mirror
balance and sends; shielded withdrawal declares coin effects and appends change
to the inbox when needed. The inspected source ordering does not itself prove
that a scratch prefix commits.

Every sampled transcript contains no `ckpt`, and the actual partitioner returned
one nonempty section per call. E7's
[`split_at`](https://github.com/midnightntwrk/midnight-ledger/blob/67f9f97246339539af0091c4d8c6bc5ab236a191/ledger/src/construct.rs#L767-L818)
explains why checkpoint-free calls are not split by that algorithm.
This supports **complete-call units for these samples**, not universal
serialization of all inputs, compiler outputs, compositions or authenticated
histories.

### What native application did and did not validate

The runner constructs real `ContractCallPrototype`/`Intent`/native offers,
calls `Transaction.eraseProofs().wellFormed`, and passes its returned
`VerifiedTransaction` to **the real native `LedgerState.apply`**.
The type name does not restore the disabled checks:

| `WellFormedStrictness` flag | Diagnostic value |
|---|---|
| `enforceBalancing` | **false** — no globally balanced fee/funding transaction |
| `verifyNativeProofs` | **false** — no verified shielded/native proofs |
| `verifyContractProofs` | **false** — no proof binding to a deployed Passport key |
| `enforceLimits` | true |
| `verifySignatures` | true |

Keeping transaction-signature checks enabled is **not** ledger verification of
Passport's private circuit signatures: that requires the disabled contract-proof
check. Synthetic state is installed with `LedgerState.updateIndex`; synthetic
native balances match the source mirror, and needed shielded input coins are
inserted into a private in-memory Zswap state. Operations use undeployed blank
`ContractOperation` objects. These are neither authenticated holdings nor a
deployment-rooted source history. Every application record repeats this boundary.

The all-five-flags-enabled negative control rejects a proof-erased activation
with `invalid balance -413620000000001 for token Dust in segment 0`.
That is an observed funding/balancing refusal, **not a successful proof check**
and not evidence about which proof error would occur next.

### Surviving state and failed sections

Each record links `before`/`after` to complete decoded public ledger snapshots
in `states`, including device set, authority counters, grant records and
`spent_commit`, mirror balances, inbox entries/count and recovery fields.
Native contract balances, Zswap roots/next leaf, UTXO-set hashes/deltas, events,
physical sections and native result text are retained separately. Coin inputs,
outputs and source effects are recorded with their transcript section.

- **Stale standalone calls:** all 126 structurally admissible samples reject
  their own transcript on the successor. Guaranteed failures report `failure`;
  fallible failures report `partialSuccess` with an empty successful guaranteed
  section. Public state, native balances, UTXOs and shielded state do not change.
- **Competing inbox appends:** two independently prepared copies of the same
  fresh call become wholly fallible under native joint partitioning. In separate
  segments, the first commits and the stale second fails: `round 2 → 3`,
  `auth_nonce 0 → 1`, `inbox_count 0 → 1`, one device-commitment advance, no
  balance/coin change. In one shared segment, the second failure rolls back both
  calls; even the first inbox/counter update does not survive.
- **Positive grant pair, all three schemes:** ordered spends of 3 then 3 commit
  nonce `0 → 2`, the corresponding spent commitments for `0 → 3 → 6`,
  round `3 → 5`, mirror/native balance `100 → 94`, and two UTXOs of 3.
  Reversing physical segments makes the nonce-1 call fail first, then the nonce-0
  call commit: nonce `0 → 1`, spent commitment for 3, round `3 → 4`, balance
  `100 → 97`, one UTXO of 3. Device set, `auth_nonce = 1` and inbox stay fixed.
  The failed first physical segment remains in the record.
- **Duplicate fresh grant spend:** separate segments retain exactly the first
  spend and one UTXO; putting both calls in one segment rolls back settlement,
  mirror/native debit and output together. No nonce-only/spent-only prefix
  survives either test.
- **Shielded settlement/change:** the jubjub grant sample has round `22 → 23`,
  grant nonce `2 → 3`, spent commitment for `3 → 7`, inbox `8 → 9`,
  unchanged `auth_nonce = 11` and device set, and Zswap next leaf `1 → 3`
  (recipient output plus change). Exact-spend branches have no change append.
  All three arms and both user/contract recipients are exercised.
- **Cross-contract receive:** all 12 sender-plus-real-`deposit_shielded`
  compositions apply successfully in this diagnostic mode; sender and receiver
  public post-states match their generated calls. A sender without matching
  receive is refused by `wellFormed`.
- **Asset failures:** 42 missing-offer attempts are refused before application.
  Fifteen positive unshielded withdrawals with funded source mirrors but absent
  native balance fail unchanged. Twelve shielded replays use an original
  reference state but an already-spent application state; all fail unchanged.
  The three zero-grant withdrawals accepted by the local circuit cannot form a
  ledger transaction here: the native UTXO check rejects zero-value output.
- **Ordered does not always mean successful:** three recovery submit/finalise
  pairs retain the submit but reject finalise. The transaction uses the first
  call's block context, before the elapsed window required by the later builder.
  Both builder contexts and the actual application context are recorded.
  Other pre-application pair refusals, including native causality checks, are
  retained rather than rewritten as successful source histories.

These are independent seeded diagnostic schedules, not one reconstructed chain.
Every attempted call, failed segment and retained whole call remains visible;
`retainedCompleteCalls` is a measured state match, not a proof certificate.
The observations refute “every transaction or segment corresponds to one source
call” but do **not** exhibit a surviving partial source call. They support the
narrow complete-call projection for the measured schedules only. The 114 local
builder refusals are separate from ledger failures and are not presented as
ledger rollback observations.

### Current platform and full-validation blocker

The [platform probe](../conformance/harness/ledger-platform-probe.mjs) and
[unaltered command evidence](../conformance/ledger-platform-evidence.json)
replace the old “no running stack” observation with a fresh setup investigation.
Docker worked; the default ports 9944/8088/6300 were initially closed, and the
exact E6 images were already cached. No new executable image was downloaded.
An isolated fresh **`--dev`** authority node on port 19945 started successfully:
`system_version = 2.1.0-1b2b31c7`, runtime spec 2001000/transaction 4, best
block 2 after 15 seconds. Its finalized head was still genesis at that observation.
This proves a local node can run, not that any Passport transaction was submitted
or finalized. The earlier non-authority launch remained at genesis.

Two independent proof paths were attempted:

1. The cached pinned proof-server image on isolated port 16301 exited before
   readiness while fetching SRS/native prover resources.
2. The pinned compiler's `zkir-v3 compile` on the real activation ZKIR selected
   `k = 14`, 13447 rows, then failed fetching `bls_midnight_2p14`; no prover or
   verifier key was generated. Existing generated artifacts have `--skip-zk`
   provenance and no Passport key files.

The exact blocked origin is **`https://srs.midnight.network:443`**. The direct
probe returned HTTP 403, “Approval required”, suggesting `sbx policy approval ls`;
`sbx` is not installed in this environment. Activation needs
`/bls_midnight_2p14`; proof-server startup additionally requested SRS powers
10–15 and `/zswap/10/{spend,output,sign}.prover`, `/dust/10/spend.prover`.
The user explicitly chose **Keep access blocked**. No further fetch, approval
bypass or policy change is part of this investigation.

Thus full validation is **BLOCKED at trusted proving material/key generation**.
A generated Passport verifier key, real contract/native proofs, an authenticated
deployment and a fee-balanced/funded transaction have not been supplied or
constructed. An indexer was not started after the prerequisite failed. Merely
starting one, or receiving a `VerifiedTransaction` with three checks disabled,
cannot fill that gap. A version-compatible, approved source of proving material
is needed before these later stages can be attempted honestly.

All containers created by the probes were removed; cleanup command statuses are
recorded. No existing chain, user keys, source implementation or sandbox policy
was changed. This worktree is retained because the full-validation criterion
was not achieved.

### Reproduction and remaining obligations

The changed-path diagnostic smoke exits 0 under Node v22.22.1:

```sh
node --import /Users/andre/IOHK/arc-passport/.worktrees/formal-correspondence-main/contract/node_modules/tsx/dist/loader.mjs \
  conformance/harness/ledger-partial-execution.mjs --diagnostic-apply \
  --output=conformance/ledger-partial-execution-evidence.json
```

`FULL_IMPL_DIR` selects the existing pinned implementation. The explicit
`--diagnostic-apply` switch acknowledges the disabled-check boundary. Evidence
contains source/tool/artifact hashes, runner/helper hashes, complete final-run
outcomes and earlier development-run failures/corrections as `previousAttempts`.
No receipt was hand-edited. No Agda check or new Agda bridge is claimed.

The platform probe was run with `--isolated-stack
--output=conformance/ledger-platform-evidence.json` before the user kept SRS
access blocked. **Do not rerun it under that decision:** it starts the prover
and attempts those downloads. Use its captured evidence until access is
explicitly reopened.

Before asserting full adoption correspondence, A1–A6 must still be independently
justified (or explicitly approved as trusted assumptions), the complete-call
projection must cover every intervening account mutation, and the existing
cryptographic/opening premises must still hold. No candidate assumption has been
approved by these tests. The completed investigation establishes finite partition
and disabled-validation application facts; the requested authenticated
full-application claim remains blocked.

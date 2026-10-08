# Contract specification DSL

## Status and purpose

This document records the design for an executable Agda language for specifying
Passport contract programs. Executable safety and ideal-resource history-privacy
experiments are described below; the broader API and security obligations remain
a design, not proofs about deployed circuits. Its intended Passport application is the
[recovery specification experiment](recovery-specification.md).

The goal is a language expressive enough to describe the programs implemented by
circuits, and convenient for proving properties and auditing source
correspondence. It is **not** a model of Compact, ZKIR, or their compilation
pipelines. The connection between a specification program and its actual circuit
will rely on manual review for the foreseeable future.

Use categorical-crypto's `protocol-rewrite` branch until its contents are merged.
The design was inspected against local commit
`579b54e72d453fd6287f05f90a32b933b8474390`. That revision was not fetchable from
GitHub when starting the prototype. The reproducible prototype dependency in
`pagda.nix` instead pins the published branch revision
`437dca12c85f096715fc06d9155146b3afc5f46e`, whose core `Protocol` API matches.
Keep this distinction explicit rather than depending on a moving branch or a
machine-local worktree. Relevant upstream modules are:

- `CategoricalCrypto.Protocol`: stateful programs with `St`, `init`, and `step`,
  using `Calls` for finite interactions, probabilistic choice, and divergence.
- `CategoricalCrypto.Protocol.Observe`: execution, observations, and event bounds.
- `CategoricalCrypto.UC.Model.Setup`: the existing concrete `UCSetup` instance.
- `CategoricalCrypto.Examples.ChimericLedger.Property` and `Transfer`: examples
  separating observable properties, internal-state properties, and their transfer.

### Checked prototype

The first implementation lives in [`src/Midnight/ContractDSL`](../src/Midnight/ContractDSL/).
The modules distinguish executable definitions from the wider pseudocode below:

| Module | Implemented definitions and checked results |
|---|---|
| [`Ledger.agda`](../src/Midnight/ContractDSL/Ledger.agda) | Minimal `Semantics` interface and generic `Execution`: result validation, `apply`, `same-view`, and `rebase` derived once |
| [`Program.agda`](../src/Midnight/ContractDSL/Program.agda) | Parameterized monadic programs, one traced `execute` with `eval` outcome projection, separate operation/assertion errors, publication, chain conditions and ordered replay; `replay-refinement` and `lift-Hoare` |
| [`Protocol.agda`](../src/Midnight/ContractDSL/Protocol.agda) | Parameterized contracts/communication, induced relation, certificate validation, atomic admission, declared-result `Observation.wrapper`, private `recipientAnswer` and upstream composition; `accepted-refinement`, `system-invariant`, `reachable-invariant` and `finishAdmission-public` |
| [`MidnightLedger.agda`](../src/Midnight/ContractDSL/MidnightLedger.agda) | Concrete shared lock/Merkle example operations, bounded counters, mutable root and flag contents |
| [`SymbolicDigest.agda`](../src/Midnight/ContractDSL/SymbolicDigest.agda), [`FixtureLedger.agda`](../src/Midnight/ContractDSL/FixtureLedger.agda) | Concrete symbolic hash algebra, separate four-member fixture root and fixture state initialization |
| [`BalanceLedger.agda`](../src/Midnight/ContractDSL/BalanceLedger.agda), [`Balance.agda`](../src/Midnight/ContractDSL/Balance.agda) | Independent two-account balance map, transfer/error/replay behavior and conservation lifted through the same generic admission/reachability proofs |
| [`MerkleState.agda`](../src/Midnight/ContractDSL/MerkleState.agda) | General matching-root success, root updates, stale membership rejection, fresh membership acceptance and mutable-flag regressions |
| [`Lock.agda`](../src/Midnight/ContractDSL/Lock.agda) | The [official lock example](https://docs.midnight.network/compact/reference/writing.md), `clear-safety`, `accepted-clear`, and the bounded-round invariant lifted to reachable system states |
| [`Smoke.agda`](../src/Midnight/ContractDSL/Smoke.agda) | Actual assembled lock, balance and mutable-root Merkle strategies: success, distinct operation/assertion failures, valid replay and current-state conflicts |

The central checked result is an exact **safety** lift. If every registered
program preserves an invariant under successful local evaluation, the assembled
`system` preserves it at every completed activation and reachable finite prefix,
including arbitrary `submitOther` transactions. Accepted replay is related back
to evaluation at the actual admission state, not just the client's old view.
Rejected transactions preserve the chain state. The lock example instantiates
this generic theorem rather than reproving its protocol invariant independently.

Some implementation choices deliberately keep this first proof small:

- `Op : Kind → Set` uses a small universe of result codes, interpreted by
  `El : Kind → Set`. Thus `o : Op k` returns `El k`; this avoids raising every
  protocol interface's universe. It is not a second schema abstraction.
- `apply` is derived from `prepare` by checking the recorded result. This captures
  exact reads, predicate dependencies, and delta increments with one semantics.
- The proof resource carries evidence and a derivation of the induced relation.
  Its soundness and completeness are proved, but it is **not zero knowledge**.
  Communication is parameterized by `CommunicationScheme`; the safety examples
  use `ExactCommunication.scheme`, an explicitly non-hiding tuple with a checked
  `binding` proof. The symbolic lock hash and certificates establish no cryptographic privacy.
- The safety model has one account, a fixed authenticated context, and one atomic
  segment. It uses upstream `Protocol`, composition, `Strategy`, and `AllLeaves`.
  The Merkle session wrapper below drives that same generic client and admission
  implementation, with an exact relational privacy lift under simulator-token
  resource premises, not a quantitative theorem for deployed schemes.

The core modules check with `--safe --without-K`, without added postulates or
termination escapes. `SmokeMain.agda` supplies only the executable IO wrapper.
The following commands were used from the repository root:

```sh
LC_ALL=C.utf8 timeout 1800 pagda --useUntracked false check \
  src/Midnight/ContractDSL/Smoke.agda -- +RTS -M3G -H1G -RTS
LC_ALL=C.utf8 timeout 1800 pagda --useUntracked false check \
  src/Midnight/ContractDSL/SmokeMain.agda -- --compile \
  --ghc-flag=-O0 --ghc-flag=-o --ghc-flag=./contract-dsl-smoke \
  +RTS -M3G -H1G -RTS
./contract-dsl-smoke
```

All three executable scenarios returned `true`. `pagda.nix` also pins
`agda-stdlib-meta` to `97e2f65f5c8a1cc07aacec32b4974668ef32979b`, matching the
published protocol branch's solver dependency.

### Ideal-resource Merkle history experiment

The executable implementation of [the second example](#9-second-target-history-privacy-and-a-correlation-only-leak)
uses the same pinned published upstream revision as the lock prototype:

| Module | Definitions and results |
|---|---|
| [`Merkle.agda`](../src/Midnight/ContractDSL/Merkle.agda) | Source-shaped `checkSecure` and `checkInsecure`, arbitrary natural-valued `FieldValue` input and arbitrary untrusted `Path`, computed symbolic root; insecure modification parameterized by a public pure classification function |
| [`MerkleFixture.agda`](../src/Midnight/ContractDSL/MerkleFixture.agda) | Four-known-member fixture and chosen `classify`, depth-10 paths, compatibility-premised `successful`/`admitted`, `fixture-successful`, `paired-tags`, wrong-leaf and wrong-root rejection |
| [`Privacy.agda`](../src/Midnight/ContractDSL/Privacy.agda) | Fixed honest Merkle session wrapper over generic `Interpreter.toProtocol` and `bridge`; actual generic statements/traces and admission verdicts, private mask/draft, `ProgramHistoryPrivacy`, `Coupling.step-public`, `lift-privacy`, `secure-history-private` |
| [`PrivacySmoke.agda`](../src/Midnight/ContractDSL/PrivacySmoke.agda) | Actual upstream composition and five separate session/prepare/submit activations, `single-tag-uniform`, `secure-joint-observable-equality`, four probability-one successful histories, `insecure-gap-one`, `insecure-not-private`, `fresh-pair-quarter` |
| [`PrivacyReplacement.agda`](../src/Midnight/ContractDSL/PrivacyReplacement.agda) | Parameterized resource replacement, `system-emulates`, generic robust-property `transfer`, shared resource `simulator`, `context-simulation`, relational `TwoWorld.transfer-private`/`transfer-closed`, and actual `ForProgram`/`ForProtocol` compiler adapters; exact and canonical negligible `UCSetup` instances |
| [`PrivacyReplacementExample.agda`](../src/Midnight/ContractDSL/PrivacyReplacementExample.agda) | Nonidentity negation simulator, different honest contexts, simulator-stable ideal relation, concrete correlation observer, and a counterexample when the ideal invariant is broken |
| [`PrivacySmokeMain.agda`](../src/Midnight/ContractDSL/PrivacySmokeMain.agda) | Executable exhaustive rational-distribution smoke |
| [`Observation.agda`](../src/Midnight/ContractDSL/Observation.agda) | Generic hidden-state call-tree coupling, `coupled-read` and `Relational.observations`, lifted with upstream `runWith⊥-bisim` |
| [`PublicBoundary.agda`](../src/Midnight/ContractDSL/PublicBoundary.agda) | Actual generic public-wrapper regressions: private Boolean inputs/results, explicit result declassification, publication/query leaks, failure traces, rejection and wrong-account checks |
| [`PublicBoundaryMain.agda`](../src/Midnight/ContractDSL/PublicBoundaryMain.agda) | Consumer-visible runtime readers of the changed assembled boundary |

`HistoryPrivacy` uses the **existing** `UC.Model.Setup` evaluation setoid on
machine runs. The theorem compares both verdict masses at every positive slack;
`Protocol.Machine.Agree.prAgree` connects those machine approximants to actual
`Protocol.Observe.runObs` distributions. `lift-privacy` quantifies over every
finite upstream strategy on the public session interface, including repeated
session starts and malformed scheduling. Its program/client premise is a
mask-preserving agreement of the selected entry identities and program bodies
for both fixed calls. The generic execution reports, statements and admission
verdicts then correspond, even though the private draft certificates differ.
This is sufficient, not completeness for every possible relational coupling.

The wrapper invokes `Interpreter.toProtocol` composed with the same `bridge`
as safety. Thus snapshot acquisition, actual evaluation, relation construction,
proving failure, authenticated account checking, replay and ledger state all
come from one implementation. Submission uses the draft actually returned by
the generic build, not a fixture-selected substitute.

`SimulatorCommunication.scheme` relates its Boolean artifact to its private
Boolean opening. Each preparation samples fresh communication randomness;
the ideal private proving resource separately samples a fresh proof token.
`PrivacyResources.seal-law` is literal pointwise equality with `idealStep`,
not a real-resource UC simulation premise. Verification currently receives the
generic private `Tx` and checks its certificate. The tokens do **not** implement
binding commitments, public proof verification, issuance or malicious-submission
security. No `CommunicationObligations.Binding` witness is supplied for the
simulator-token instance. These limitations belong to package 4, not a hidden
assumption that the tokens already implement ZK.

The observer sees the selected fixed code identity, account, unit public
arguments, all ledger operation arguments/results and publications, public
proof/communication tokens, acceptance/rejection and unit return values. It
does **not** see private resource requests, certificate evidence, selected caller
items, witness/path acquisition traffic, or the session mask. There is no claim
against the prover, private transport observers, timing observers, arbitrary
witness providers, or an adversarial writable tree. Every known fixture leaf
has a computed valid path. `flags.member` is a real read-only public query of
the immutable two-element Boolean set; the insecure query exposes the XOR tag,
not the item. Membership and replay are computed, not universal-success
fallbacks. Both variants preserve the same ledger state and return unit.

`Item = a | b | c | d` belongs only to the experiment fixture. It is not the
circuit's private input type, and total fixture `findItem` is not an assumption
about arbitrary witnesses. The modeled circuit takes `FieldValue = ℕ` (a named
symbolic abstraction, not Compact Field arithmetic) and an arbitrary `Path`,
and checks both private leaf equality and public root membership. Its contract
input domain is likewise `FieldValue`. The selected client converts known
example members into values/paths. Actual public journals and traces are derived
from the generic interpreter's execution, not a canned distribution.
The insecure modification takes a pure `(FieldValue → Bool)` classification
parameter. The fixture predicate compares with values 3 and 4; that predicate
is an experiment choice, not a classification claimed from Midnight's source.

The fixture models a depth-10 current-root tree with four occupied leaves and
empty padding, and collision-free symbolic node constructors. It does not
model historic roots, a private Set lookup, real Field encodings, or the
Midnight hash. Correspondence is manual source review against the
[official membership circuit](https://docs.midnight.network/concepts/how-midnight-works/keeping-data-private.md#making-use-of-merkle-trees),
[randomness-reuse warning](https://docs.midnight.network/concepts/how-midnight-works/keeping-data-private.md#randomness-and-rounds-in-commitments),
[ledger ADTs](https://docs.midnight.network/compact/data-types/ledger-adt.md),
and [disclosure semantics](https://docs.midnight.network/compact/reference/explicit-disclosure.md).
The cited private-data page is unversioned (reviewed 2026-10-07); the ADT
language/compiler versions and release caveats above still apply. No Compact
compiler correspondence or deployed circuit theorem is claimed.

### Generic resource replacement

`PrivacyReplacement.agda` proves replacement rather than only naming its
premise. `Transfer` is parameterized by the existing upstream `UCSetup`.
`Transfer.Replacement` takes real and ideal resource morphisms and a proof
`real ≤UC ideal`. The resources may have different adversary interfaces, but
must share their input and honest service interface.

For any honest context `context`, `InContext` defines:

```agda
realSystem  = context ∙ real
idealSystem = context ∙ ideal

system-emulates : realSystem ≤UC idealSystem
system-emulates = UC-compose emulates (≤UC-refl context)
```

The emulation assumption is on the **resource**, not on the assembled program.
`transfer` then uses upstream `UC.Robust.uc-preserves`:

```agda
transfer :
  (P : Predℰ A p) (Adm : Admissible C d) →
  ((s : (Y ⊗₀ Z) ⇒ (X ⊗₀ Z)) → ClosedUnder Adm s) →
  Robust P Adm idealSystem →
  Robust P Adm realSystem
```

Here `P` respects the setup's observational setoid, and the admissible
environments must remain admissible when composed with a simulator.
`transfer-unrestricted` supplies that closure proof when every environment is
allowed. These are the upstream property definitions, not a second security
notion or an assumption that the real system already satisfies the property.

The concrete entry points are:

- `ForProgram program self`: compiles any `Program A` using the existing
  `programToProtocol` and upstream `Protocol.Machine.morphism`.
- `ForContract contract self`: handles registered entry points and witnesses.
- `ForProtocol context`: also supports a client/session wrapper such as the
  Merkle experiment's stateful two-call client.
- Each supplies `WithResources real ideal emulates` for compiled resource
  morphisms, and `WithProtocols real ideal emulates` for actual protocols whose
  output interface explicitly separates adversary and honest service ports.
  The resulting module exports `realSystem`, `idealSystem`, `system-emulates`,
  `transfer`, and `transfer-unrestricted`.

The application context has a unit adversary interface; the resource's adversary
interface is retained by graded composition. `compiled-assembly` proves that,
for an ungraded backend, this construction is the compiled native
`context ∘ᵖ backend`, up to unit-grade coherence. The proof uses upstream
`morphismCompose`; it does not assume compiler compositionality.

`ExactTransfer` instantiates the theorem at `UC.Model.Setup.StdSetup`.
`ComputationalTransfer` instantiates the same theorem at
`UC.Model.Family.Canonicalᴺ.StdSetup`, retaining negligible rather than merely
vanishing error. The latter requires a certified family context and predicates
stable under its negligible observation equivalence; an exact probability-zero
claim is not automatically such a predicate. There is no automatic polynomial
compilation claim for arbitrary DSL programs.

This completes the conditional resource-replacement step. One still proves the
desired property in the **ideal** assembled model. A local state invariant needs
its observation/adequacy argument before applying `transfer`; UC alone does not
transport hidden state. Likewise, the Merkle two-world theorem must be formulated
as a simulator-closed observable experiment before this robust-property theorem
applies: the generic theorem does not silently turn its honest ideal-resource
premise into security against every simulator.

A concrete resource can remain a module parameter. No proof-system construction
or cryptographic assumption is postulated inside the implementation. To instantiate
the computational theorem with actual ZK/communication resources, supply their
emulation proofs, matching code/account and public/private boundaries, certified
polynomial interaction allowances and a separate computational-time/PPT
admissibility argument. Interaction allowances alone do not prove PPT security.

Verification on 2026-10-08: the replacement module checked with the canonical
3-GiB settings. A throwaway concrete `ForProgram (clear key) 7` instantiation
checked `transfer-unrestricted` and `compiled-assembly`, using reflexive resource
emulation as an executable sanity check, not as evidence for a real cryptographic
scheme. Its compiled native machine (equivalent by `compiled-assembly`) accepted
the correct-key scenario with mass `1/1` and returned the rejection verdict for
the wrong-key scenario with mass `1/1`. Direct approximant evaluation of the
generic graded machine was expensive: bounds 12 and 16 had not settled, and
bounds 24 and 100 timed out at 60 seconds. The successful runtime check used the
proved-equivalent native composition, not those inconclusive approximants.
The concrete-instance compilation used paired `-M8G -H1G`; the throwaway source
and generated executable were removed afterward.

Reproduce serially from the repository root:

```sh
LC_ALL=C.utf8 timeout 1800 pagda --useUntracked false check \
  src/Midnight/ContractDSL/PrivacySmoke.agda -- +RTS -M3G -H1G -RTS
LC_ALL=C.utf8 timeout 1800 pagda --useUntracked false check \
  src/Midnight/ContractDSL/PrivacyReplacement.agda -- +RTS -M3G -H1G -RTS
LC_ALL=C.utf8 timeout 1800 pagda --useUntracked false check \
  src/Midnight/ContractDSL/PrivacyReplacementExample.agda -- +RTS -M3G -H1G -RTS
LC_ALL=C.utf8 timeout 1800 pagda --useUntracked false check \
  src/Midnight/ContractDSL/Smoke.agda -- +RTS -M3G -H1G -RTS
LC_ALL=C.utf8 timeout 1800 pagda --useUntracked false check \
  src/Midnight/ContractDSL/PrivacySmokeMain.agda -- --compile \
  --ghc-flag=-O0 --ghc-flag=-o --ghc-flag=./contract-dsl-privacy-smoke \
  +RTS -M8G -H1G -RTS
./contract-dsl-privacy-smoke
```

The typechecks use the canonical paired 3-GiB heap settings. Compilation of
the upstream categorical dependency closure exhausted that heap; the documented
compile command retries with a paired 8-GiB maximum and 1-GiB initial heap.
The failed 3-GiB compilation left a truncated generated upstream Haskell file;
removing that generated file before the 8-GiB retry resolved the ensuing GHC
parse error. No library source or theorem was weakened.

Verification on 2026-10-07: `PrivacySmoke.agda`, `PrivacyReplacement.agda` and
the original `Smoke.agda` checked successfully against the pinned dependency.
All new mathematical modules use `--safe --without-K` (with guardedness for the
upstream machine layer), with no added postulates, holes or termination escapes.
The IO wrapper compiled, and running the actual composed-protocol distribution
smoke printed:

```text
secure (a,b), two accepted calls: 1/1
secure (a,c), two accepted calls: 1/1
insecure (a,b), two accepted calls: 1/1
insecure (a,c), two accepted calls: 1/1
secure observer true mass (a,b) vs (a,c): 0/1 vs 0/1
insecure observer true mass (a,b) vs (a,c): 0/1 vs 1/1
```

The warning gate found no `ModuleDoesntExport`, `UselessPublic`,
`UselessPrivate` or `DuplicateUsing`. Generated Haskell and the smoke executable
were removed after the run; the commands above reproduce them.

## Scope and non-goals

Use ordinary Agda for computation and a small explicit language for effects:

- Values, records, functions, pattern matching, and recursion remain ordinary
  Agda. Data-dependent iteration is permitted.
- Caller and witness inputs remain ordinary private records unless designated
  public; effects expose ledger operations, assertions, actual publication, and
  authenticated chain-context requirements.
- Programs have executable semantics and can be embedded into `Protocol`s that
  interact with ZK and blockchain resources.
- Local invariants and adversarial protocol properties concern the same program.

There is no requirement that every expressible program be realisable as a fixed
circuit. Static circuit bounds, constraint counts, code generation, verified
compilation, and a general-purpose automated verification framework are out of
scope. Producing executable model code does not mean generating executable
Compact or establishing correspondence with its compiler output.

### Coverage profile and Midnight correspondence references

The first application is a **post-bootstrap, single-account authority model**
with public ledger observations and one selected atomic segment. It is not yet
a specification of every Passport custody/grant/client feature or every Compact
program. Extend operation families and protocol resources only for features
needed by the claimed property; do not turn this into a compiler or VM project.

| Feature | Representation or required boundary |
|---|---|
| Values, records, generics, branches, local calls, loops | Ordinary Agda; circuit bounds and syntax parity are not requirements |
| Scalars and point map/set operations | Concrete cells or typed operations with source-matching dependencies |
| Counters, predicate queries, reset, nested/overlapping storage | Operation-specific preparation/admission; no fictitious non-overlap or exact-snapshot rule |
| Merkle paths, trees and history | Ordinary data/pure crypto plus root/history operations; historic membership is not current-root equality |
| Witness values and evolving private state | Private evidence; honest acquisition/response order and private-state persistence in the client protocol |
| Private circuit arguments and returned data | Separate caller inputs/public projection, communication binding, and recipient observations |
| Compact `disclose` and events | Annotation is not publication; model actual ledger/output/log sinks |
| Self and asserted time bounds | Bound account and authenticated admission conditions |
| Caller, submitter and token balances | Typed authenticated queries/conditions when needed; balance reads use the documented execution-start snapshot |
| Assets and coin operations | Coin data/crypto can be pure; global offers, ownership, nullifiers, mint authority, exact-once claims and qualification need transaction semantics |
| Cross-contract and multiple calls | Linked, ordered invocations in an atomic segment; not separate interleavable submissions |
| Constructors, defaults, sealed storage, bootstrap | Explicit initialization/lifecycle constraints; deployment registration/address allocation in the chain protocol if included |
| Hashes, signatures, curves, numeric types | Pure parameters or constrained relational witnesses; preserve encodings, weak-key checks, checked casts and modular versus bounded arithmetic |
| Program identity and upgrades | Fixed definitions initially; registries/composition must bind definition/version or verifier-key identity |
| Fees, checkpoints and multiple segments | Excluded from account rollback theorem unless modelled explicitly; no claim of whole-transaction rollback |

Primary correspondence references:

- [Compact language reference](https://docs.midnight.network/compact/reference/compact-reference.md),
  including [witness/private-state management](https://docs.midnight.network/compact/reference/compact-reference.md#declaring-witnesses-for-private-state-management)
  and [generated client state threading](https://docs.midnight.network/compact/reference/compact-reference.md#exports-of-the-generated-typescript-code).
- [Ledger ADTs](https://docs.midnight.network/compact/data-types/ledger-adt.md)
  for counters, collection operations, kernel queries and coin qualification.
- [Explicit disclosure](https://docs.midnight.network/compact/reference/explicit-disclosure.md)
  and [private-data patterns](https://docs.midnight.network/concepts/how-midnight-works/keeping-data-private.md)
  for actual public ledger observations and Merkle membership privacy.
- [Standard-library API](https://docs.midnight.network/compact/standard-library/exports.md)
  for crypto, numeric/curve domains, time and shielded/unshielded assets.
- [Transaction building blocks](https://docs.midnight.network/concepts/how-midnight-works/building-blocks.md)
  and [transaction semantics](https://docs.midnight.network/concepts/how-midnight-works/semantics.md)
  for communication commitments, call linking, global asset validation and
  atomicity/partial success.

Pin the application toolchain, runtime, ledger and source revision. At review,
the ADT page labels itself language **0.26.0/compiler 0.34.0**.
[Toolchain 0.34.0](https://docs.midnight.network/relnotes/compact/toolchain-0.34.0.md)
adds shielded operations in cross-contract callees;
[0.35.0/language 0.27.0](https://docs.midnight.network/relnotes/compact/toolchain-0.35.0.md)
adds `caller`, more curves/signatures, and runtime callee resolution, and changes
key validation. Its notes say ledger 9 is not yet on public networks and direct
public-network developers to 0.31.x. Some live reference descriptions lag those
release notes; do not merge different versions into an unsupported semantic
claim. These are correspondence caveats, not circuit-realisation restrictions.

## Language shape

Use a shallow embedding for pure computation and explicit typed operations for
effects. Keep the effect representation small enough to support both execution
and induction over the relevant operations. The [pseudocode specification](#pseudocode-specification)
below chooses an initial representation and interpreter. Exact imports, universe
levels, and API names remain implementation decisions.

| Capability | Specification meaning |
|---|---|
| Private input | Obtain a witness value without automatically making it public |
| Public input or disclosure | Bind a value into the designated public statement or ledger interaction |
| Ledger read | Observe state and record the ledger dependency needed for acceptance |
| Ledger update | Propose an update, visible to subsequent reads in this execution |
| Assertion | Restrict successful executions; failure aborts the proposed transaction |
| Chain-context requirement | Constrain authenticated account identity, time, or other admission context |

Cryptographic computations, such as entry derivation or signature verification,
may initially be parameterised pure operations with explicit assumptions. They
need not each become a monadic effect. Resource interfaces are introduced where
interaction or cryptographic replacement reasoning requires them.

Witness acquisition and witness validity are different. A client may consult
storage or another party to acquire a witness; those interactions belong to the
client protocol. The contract program constrains the value supplied. It must not
assume that a malicious witness provider follows the honest acquisition procedure.

A schematic program should remain recognisable to a reviewer of the circuit:

```text
finalise = do
  pending <- read pendingRecovery
  require (isPending pending)
  requireChainTimeAtLeast (deadline pending)
  requireLiveKey (successorRecoveryKey pending)
  modify deviceEpoch successor
  insert devices (successorEntry pending)
  write deviceCount 1
  write recoveryKey (successorRecoveryKey pending)
  clear pendingRecovery
  modify authNonce successor
```

This is illustrative pseudocode, not a complete transcription or compilable Agda.
In particular, `insert` must not silently mean replacing the whole set. An
abstraction may simplify representation, but must not repair the behaviour being
specified. Intended security properties are stated separately from the
implementation-shaped program.

## Transactional semantics

### Local evaluation and atomic commitment

Within one execution, reads see earlier proposed writes. Evaluation produces
failure, or a result together with proposed ledger effects, public information,
and conditions for admission. Proposed writes do not mutate authoritative chain
state during proof construction.

Within the selected account-effects segment, commitment occurs only after chain
acceptance. Evaluation failure or segment rejection commits none of its proposed
account-state changes, including writes before a later failed assertion. This
does not claim rollback of fees or effects in other guaranteed/successful
segments. External witness acquisition, actual publication already sent, and
other client-side I/O are not magically rolled back.

Segment atomicity is a reusable fact of this semantics and its selected blockchain
interpretation, not an assumption repeated inside each recovery proof. Midnight
supports checkpoints and partial success across phases/segments; exclude those
boundaries from the first account transition or model them explicitly.

### Ledger dependencies and admission context

Keep the description of ledger reads, conditions, and effects explicit. Do not
silently require the whole account snapshot to remain unchanged unless that is
the selected blockchain model: it may impose stronger conflict rules than the
implementation and eliminate relevant interleavings.

The initial blockchain interpretation must document its conflict and admission
rules. Manual correspondence review checks that they represent the relevant
Midnight behaviour. Dependencies that protect authorisation or pending recovery
must not be discarded merely to simplify execution.

Chain time is not an unchecked client input. For example, a signed upper time
bound is supplied data, whereas the requirement that admission time is at most
that bound is enforced by the chain interpretation. A successful check against
the client's clock while constructing a proof is not a substitute.

### Public and private information

Identify witness inputs, explicit disclosures, public ledger interactions, and
which participant sees each of them. An elaborate information-flow type system
is not required initially, but the observations must have precise semantics.

A witness value is not public merely because it is used in an Agda computation.
The same applies to caller-supplied circuit arguments: Compact treats them as
potentially private. A caller-visible result may be communication-bound without
being public plaintext on chain. A proof of secrecy must include the complete
specified transcript and communication binding, not just explicit publications.
Conversely, ledger updates, outputs, and acceptance or rejection may reveal
information. ZK privacy against a verifier does not provide privacy against a
delegated prover that receives the witness.

## One program, local and protocol interpretations

Successful evaluation defines the program's statement/witness relation,
schematically `R_C(x, w)`, for program `C`, public statement `x`, and private
witness `w`. Derive this relation from the program semantics rather than authoring
a separate circuit relation that can drift from the executable model.

The public statement must bind the program/relation identity and the proposed
ledger interaction sufficiently to prevent substitution of effects or
preconditions. The precise representation is part of the interpreter design.

A reusable operational interpreter supplies the surrounding interaction:

1. Acquire inputs and evaluate the program against the required ledger view.
2. Construct the statement, proposed operation effects, and input/result binding.
3. Interact with the ZK resource.
4. Submit the proof-bound transaction to the blockchain resource.
5. Observe rejection or atomic commitment.

The acceptance semantics must also cover adversarially constructed transactions.
Security cannot rely on a malicious prover using the honest interpreter.

Use `Protocol` as the target for clients, resource interactions, chain execution,
and scheduling between transactions. Do not equate the DSL with arbitrary
`Calls`: transaction effects have statement-binding and commitment semantics
that a general protocol call does not supply by itself. Reuse the existing
concrete `UCSetup`; do not construct a parallel semantic framework.

## Pseudocode specification

The following is **Agda-style design pseudocode**, not checked Agda. Omitted
imports, implicit parameters, record projections, and universe bookkeeping are
presentational omissions, not proposed postulates. Names not supplied by Agda or
categorical-crypto are proposed definitions or explicit model parameters. The
first implementation should settle their concrete types without adding axioms.

### 1. Typed ledger operations and ordinary input records

Use **one concrete ledger model** with a result-indexed `data Op`. Each
constructor is one kind of primitive operation, with its arguments. Preparation
and admission interpret that same syntax. This is not a model of Compact's
compiler or the Impact VM, nor a framework for assembling multiple primitive
families.

`State` is the concrete ledger state representation. Typed field references and
collection identifiers select locations in that state; they are data describing
the contract layout, not a record of arbitrary accessor functions. For example,
`FieldRef Uint64` can identify an authorisation nonce and `FieldRef Bool` a
pending-recovery flag. The operation vocabulary grows as the selected examples
need additional Compact primitives.

```agda
data Op : Set → Set where
  readField        : ∀ {A} → FieldRef A → Op A
  writeField       : ∀ {A} → FieldRef A → A → Op ⊤
  readRound        : CounterId → Op Uint64
  incrementCounter : CounterId → Uint16 → Op ⊤
  counterLessThan  : CounterId → Uint64 → Op Bool
  checkRoot        : TreeId → Digest → Op Bool
  flagMember       : SetId → Bool → Op Bool

record LedgerModel : Set₁ where
  field
    prepare : ∀ {X} → Op X → State → Error ⊎ (X × State)
    apply   : ∀ {X} → Op X → X → State → Maybe State
```

Running `o : Op X` can return an `X` and change ledger state, or fail.
`prepare` evaluates against the preparation view. `apply o x` validates the
previously claimed result `x` against the admission state, then performs the
update. The operation arguments and recorded result carry the dependencies
needed by the current primitives. Both handlers are executable definitions by
cases on `Op`; submitters cannot supply an arbitrary state transformer.

`LedgerModel` packages these handlers for the evaluator and replay.

`Op` is the family of **ledger** primitives, not the whole effect vocabulary.
Assertions, publication, and chain conditions are the other `Effect`
constructors below. Pure Agda computation requires no primitive. All
ledger-state-dependent computation passes through `Op`.

For fields, `getField`, `putField`, and `equalField` are concrete functions
defined by the layout's typed field references. Their relevant equations are
proved from those definitions, not supplied through a separate schema record:

```agda
prepare (readField f) s = inj₂ (getField f s , s)
apply (readField f) v s =
  if does (equalField f (getField f s) v) then just s else nothing
prepare (writeField f v) s = inj₂ (tt , putField f v s)
apply (writeField f v) tt s = just (putField f v s)
```

Examples' `read` and `write` notation wraps these primitives. Collection
membership, insertion, reset, and Merkle queries can have their own constructors
and handlers over the same `State`; they need not be reduced to field access.
In particular, do not assert that distinct operation arguments always address
independent storage. A collection reset and a membership query may overlap.
Prove frame properties only for the operations and locations that actually
satisfy them.

`readRound` prepares the exact counter value and admits only if it still
matches. For the delta and predicate operations, let concrete `counterGet` and
`counterPut` access the selected counter and let `addCounter` implement its
numeric failure rule:

```agda
prepare (incrementCounter c d) s =
  case addCounter (counterGet c s) d of λ where
    nothing  → inj₁ counterFailure
    (just v) → inj₂ (tt , counterPut c v s)
apply (incrementCounter c d) tt s =
  case addCounter (counterGet c s) d of λ where
    nothing  → nothing
    (just v) → just (counterPut c v s)

prepare (counterLessThan c b) s =
  inj₂ (counterGet c s <ᵇ b , s)
apply (counterLessThan c b) observed s =
  if (counterGet c s <ᵇ b) ==ᵇ observed then just s else nothing
```

The first counter scenarios stay below exhaustion rather than silently choosing
overflow semantics for every Compact version. Preparation and admission of an
increment add its delta to their respective current counter values. They return
unit and do not record the old count. A comparison records its Boolean result,
not the exact counter value.

Thus two blind increments prepared at zero can both commit and yield two, and a
true comparison may remain valid after the count changes. Encoding an increment
as an exact read followed by a replacement write would change that behaviour.
Passport's ordinary `Uint` field increments, which actually read then write the
field, must not be silently changed into blind counter operations.

Each entry point has typed **caller inputs**, which can be private, and a
private witness record. Compact exported circuit arguments are not automatically
public. The statement separately designates public input projections and binds
the full inputs and result through a communication commitment below.

```agda
record DeviceWitness : Set where
  field
    key        : PublicKey
    useCounter : ℕ
    signature  : Signature
```

For the initial experiment, assemble the witness in the client protocol before
evaluation; program access is ordinary record projection. This is not a
universal witness format or a secrecy theorem. If an application uses multiple
context-dependent witnesses, give its private evidence an ordered response
trace and specify the honest client's evolving private-state/context transition.
Do not constrain a malicious provider to follow that acquisition procedure.
Compact's returned private-state updates are threaded tentatively; distinguish
them from irreversible external I/O and from persistence after chain admission.

### 2. The small effect language

Pure computations construct programs using ordinary Agda. Fix a
`LedgerModel`, `PublicValue`, `Error`, and concrete chain conditions:

```agda
data Condition : Set where
  timeAtLeast : Time → Condition
  timeAtMost  : Time → Condition

record Context : Set where
  field
    account : AccountId
    time    : Time

holds : Condition → Context → Bool
holds (timeAtLeast t) ctx = t ≤ᵇ Context.time ctx
holds (timeAtMost  t) ctx = Context.time ctx ≤ᵇ t

data Effect : Set → Set₁ where
  ledger  : ∀ {X} → Op X → Effect X
  require : Bool → Error → Effect ⊤
  publish : PublicValue → Effect ⊤
  atChain : Condition → Effect ⊤

data Program (A : Set) : Set₁ where
  pure : A → Program A
  step : ∀ {X} → Effect X → (X → Program A) → Program A

_>>=_ : Program A → (A → Program B) → Program B
pure a   >>= f = f a
step e k >>= f = step e (λ x → k x >>= f)

perform : Effect A → Program A
perform e = step e pure

read c    = perform (ledger (readCell c))
write c v = perform (ledger (writeCell c v))
increment c d = perform (ledger (incrementCounter c d))
```

`assert`, `emitPublic`, and `requireAtChain` abbreviate `perform` of `require`,
`publish`, and `atChain`. This is notation, not another interpreter. `do` expands
using bind. Cryptographic computations can remain pure parameters.

`publish` records actual proposed publication. It is **not Compact's
`disclose(e)`**: that wrapper acknowledges possible disclosure at a sink and has
no disclosure effect by itself. Do not emit a value merely because the Compact
source wraps it in `disclose`. Ledger operations, explicit public outputs, and
structured event logs have their own observations. Event encodings can be
ordinary `PublicValue` data when their audience and ordering are specified.

`atChain` records a condition, not a read of the client's clock. Conditions are
data with decidable checking. The initial guards cover asserted inclusive time
bounds. To model Boolean time branching, constrain a proposed Boolean by the
corresponding positive or negative time condition. Additional authenticated
queries/conditions for caller, submitter, or initial token balances are added only
when needed; those values must not become unchecked caller inputs. Account
identity remains a bound invocation parameter checked again by admission.

### 3. A local evaluator with an ordered journal

Evaluation runs on a private working ledger view. Its journal preserves operation
order and records each operation and result, including read-after-write dependencies:

```agda
data Event : Set where
  operated  : ∀ {X} → Op X → X → Event
  published : PublicValue → Event
  required  : Condition → Event

Journal = List Event

record Finished (A : Set) : Set where
  constructor finished
  field
    value   : A
    working : State
    journal : Journal

Outcome A = Error ⊎ Finished A

prefix : Event → Outcome A → Outcome A
prefix e (inj₁ err)              = inj₁ err
prefix e (inj₂ (finished a s j)) = inj₂ (finished a s (e ∷ j))

eval : Program A → State → Outcome A
eval (pure a) s = inj₂ (finished a s [])
eval (step (ledger o) k) s =
  case prepare o s of λ where
    (inj₁ err)     → inj₁ err
    (inj₂ (x , t)) → prefix (operated o x) (eval (k x) t)
eval (step (require false err) k) s = inj₁ err
eval (step (require true  err) k) s = eval (k tt) s
eval (step (publish v) k) s =
  prefix (published v) (eval (k tt) s)
eval (step (atChain cond) k) s =
  prefix (required cond) (eval (k tt) s)
```

Evaluation is pure. Failure discards its proposed journal, not information already
sent during external acquisition or proving. Those observations belong to the
surrounding protocol, including on failed attempts. There is no unrecorded
ledger-read or arbitrary `State → State` program escape hatch.

### 4. Entry points, statements, and the ZK relation

Register a fixed family of entry points. A bound name selects one definition;
a submitter cannot replace it or choose an unbound program through private data.
Caller inputs and the result are separate from their public binding:

```agda
record Contract : Set₁ where
  field
    Name       : Set
    Input      : Name → Set
    PublicArgs : Name → Set
    Witness    : (n : Name) → Input n → Set
    Result     : Name → Set
    publicArgs : (n : Name) → Input n → PublicArgs n
    body       : (self : AccountId) (n : Name) (a : Input n) →
                 Witness n a → Program (Result n)

-- Model parameters: executable commitment with explicit binding/hiding
-- assumptions (or an explicit ideal resource), not an unqualified postulate.
communicate : (self : AccountId) (n : Name) →
              Input n → Result n → Opening → Commitment

record Statement : Set where
  field
    account       : AccountId
    name          : Name
    publicInputs  : PublicArgs name
    communication : Commitment
    journal       : Journal

record Evidence (x : Statement) : Set where
  field
    view    : State
    inputs  : Input (Statement.name x)
    witness : Witness (Statement.name x) inputs
    result  : Result (Statement.name x)
    opening : Opening

Rel : (x : Statement) → Evidence x → Set
Rel x e =
  publicArgs (Statement.name x) (Evidence.inputs e)
    ≡ Statement.publicInputs x
  × communicate (Statement.account x) (Statement.name x)
                (Evidence.inputs e) (Evidence.result e) (Evidence.opening e)
    ≡ Statement.communication x
  × Σ[ s ∈ State ]
      eval (body (Statement.account x) (Statement.name x)
                 (Evidence.inputs e) (Evidence.witness e))
           (Evidence.view e)
      ≡ inj₂ (finished (Evidence.result e) s (Statement.journal x))
```

The relation is induced by evaluation. It binds the ordered operation journal,
public input projection, and communication commitment to the actual inputs and
result. Keeping inputs or results in private evidence does not make them
unbound, nor does a public commitment expose their plaintext.

The honest client retains the inputs, result and opening with the prepared
transaction. Before treating a separately delivered result as authenticated, its
recipient checks the opening against the statement's communication commitment
and the intended account/name/inputs. Proof soundness alone asserts existence of
some satisfying evidence; authentication of this particular result additionally
uses commitment binding. State the recipient's ability to obtain/check the
opening in the client interface. A result intended for public observation is
published explicitly; a caller-private result is not automatically published.

The initial ledger view is mathematical witness material, not a trusted chain
snapshot. Replay authenticates each operation's dependency according to its
semantics, including observations after earlier updates. Start with a fixed
contract definition per resource instance. Registries, upgrades, or composed
contracts must additionally bind the selected definition/version or verification
key; they are not implicit in `Name`.

This initial interpretation exposes the whole operation journal, including
operation syntax, recorded results, publications, and conditions.
Instantiate it only where those are appropriate public-ledger observations.
Hidden or committed ledger operations require an appropriate public journal and
corresponding replay semantics. Neither the communication commitment nor
renaming `disclose` establishes Compact ledger privacy.

### 5. Proving, submission, and the protocol boundary

Keep proof generation and verification as resource operations parameterised by
`Rel`. Their implementation is not part of the DSL. At the interface level:

```agda
prove  : (x : Statement) → Evidence x → Request Proof
verify : Statement → Proof → Request Bool

data Tx : Set where
  transaction : Statement → Proof → Tx
```

#### Blockchain admission

Replay runs the recorded operations against a scratch copy of the current chain
state, with the same authenticated admission context throughout:

```agda
replay : Context → Journal → State → Maybe State
replay ctx [] s = just s
replay ctx (operated o x ∷ es) s =
  case apply o x s of λ where
    nothing  → nothing
    (just t) → replay ctx es t
replay ctx (published v ∷ es) s = replay ctx es s
replay ctx (required cond ∷ es) s =
  if holds cond ctx then replay ctx es s else nothing
```

Cell reads check exact observed values; blind deltas apply to current values;
predicate queries check the observed predicate result. An unconditional cell
write can overwrite a concurrently changed cell. None of these rules silently
requires whole-state snapshot equality. Each selected operation's conflict,
failure, and observation rules require manual source correspondence review.

No scratch update is committed if a later event in the selected atomic segment
fails. Commit replay's state, not the preparation working copy, which may retain
stale unrelated values. This handler models one atomic segment of account
effects, not arbitrary Midnight partial-success transactions or fee rollback.

```agda
admit : Context → State → Tx → Calls ZKIf (State × Verdict)
admit ctx s (transaction x π) =
  if Statement.account x ≟ᵇ Context.account ctx then
    call (verify x π) λ ok →
      if ok then
        case replay ctx (Statement.journal x) s of λ where
          nothing  → ret (s , rejected)
          (just t) → ret (t , accepted)
      else ret (s , rejected)
  else ret (s , rejected)
```

`Request` is interface pseudonotation: instantiate concrete `Iface` query/answer
sums and handle mismatched responses when implementing the wrapper. The code
above assumes typed resource answers for readability. It does not define an
actual ZK scheme or let a Boolean supplied by the transaction author replace
verification.

`admit` is a handler inside the blockchain protocol. The blockchain fixes `ctx`
for the activation, owns `s`, and commits only the returned state. Other
transactions cannot interleave inside this activation. The resource must not
offer a separate unauthenticated operation for applying a raw journal.

#### Constructing a Protocol from the programs

`toProtocol` interprets the entry-point programs of a fixed `Contract` as a
client protocol. A single fixed `Program A` is the special case of one entry
point with unit inputs/witness and result type `A`.

The definitions below live in `module Interpreter (C : Contract)
(self : AccountId) where`; at a call site, **`Interpreter.toProtocol C self`**
is the conversion from the contract's programs to a protocol. The interfaces
and `Rel` use that same fixed contract. Use concrete query
and answer sums, since upstream `Iface` does not have dependent response types:

```agda
data ServiceQuery : Set where
  snapshotRequest : AccountId → ServiceQuery
  proveRequest    : (x : Statement) → Evidence x → ServiceQuery
  submitRequest   : Tx → ServiceQuery

data ServiceAnswer : Set where
  snapshotAnswer : State → ServiceAnswer
  proofAnswer    : Maybe Proof → ServiceAnswer
  submitAnswer   : Verdict → ServiceAnswer

ServiceIf = ServiceAnswer ⇿ ServiceQuery

data ClientQuery : Set where
  build : (n : Name) (a : Input n) → Witness n a → Opening → ClientQuery
  submit : ClientQuery
  submitOther : Tx → ClientQuery

data ClientAnswer : Set where
  built : (n : Name) → Result n → Statement → ClientAnswer
  buildFailed : Error → ClientAnswer
  proofFailed busy noDraft : ClientAnswer
  submitted : Verdict → ClientAnswer

ClientIf = ClientAnswer ⇿ ClientQuery
```

`build` is a private caller interface, not a public chain observation. The caller
acquires the witness and samples the communication opening before using it.
`built` returns a **tentative** result, not evidence that the transaction has
committed. The caller already knows its inputs and opening and can check the
statement's communication binding. Public observers do not automatically get
these client messages.

These helper definitions construct the statement and evidence from the actual
successful program evaluation, rather than taking them on trust from the caller:

```agda
statement n a opening r j = record
  { account       = self
  ; name          = n
  ; publicInputs  = publicArgs n a
  ; communication = communicate self n a r opening
  ; journal       = j
  }

evidence n a w opening r view = record
  { view = view ; inputs = a ; witness = w
  ; result = r ; opening = opening
  }
```

The protocol holds at most one prepared transaction. Refuse a new build while
one is pending, and consume the pending transaction after a submission attempt;
these are explicit minimal client policies, not Compact requirements.

```agda
Draft = Maybe Tx

clientStep : Draft → ClientQuery →
             Calls ServiceIf (Draft × ClientAnswer)
clientStep nothing (build n a w opening) =
  call (snapshotRequest self) λ where
    (snapshotAnswer view) →
      case eval (body self n a w) view of λ where
        (inj₁ err) → ret (nothing , buildFailed err)
        (inj₂ (finished r working j)) →
          let x = statement n a opening r j
              e = evidence n a w opening r view
          in call (proveRequest x e) λ where
            (proofAnswer (just π)) →
              ret (just (transaction x π) , built n r x)
            (proofAnswer nothing) → ret (nothing , proofFailed)
            _ → dead
    _ → dead
clientStep (just tx) (build n a w opening) =
  ret (just tx , busy)
clientStep nothing submit = ret (nothing , noDraft)
clientStep (just tx) submit =
  call (submitRequest tx) λ where
    (submitAnswer v) → ret (nothing , submitted v)
    _ → dead
clientStep draft (submitOther tx) =
  call (submitRequest tx) λ where
    (submitAnswer v) → ret (draft , submitted v)
    _ → dead

toProtocol : Protocol ServiceIf ClientIf
toProtocol = record
  { St = Draft
  ; init = nothing
  ; step = clientStep
  }
```

`dead` handles a resource response of the wrong constructor, not an ordinary
transaction rejection. Well-formed resource implementations must answer with
the matching constructor; their interface-compliance property is separate from
ZK or ledger security. The exact `Evidence x` indexing and helper signatures
are to be elaborated in Agda; all fields needed by the relation are shown above.

This is the concrete link:
`body self n a w : Program (Result n)` is evaluated in `clientStep`, and
`clientStep` supplies the `step` field of `toProtocol`. The proof request binds
that same evaluation via `Rel`. Prove that every request generated by a
successful build satisfies `Rel`, and that a successful proof response stores
exactly the transaction subsequently submitted.

`submitOther` exposes the raw submission route even while a draft is pending.
It lets an environment submit independently constructed transactions between
`build` and `submit`; security must not assume every transaction came through
this honest builder. Time changes and other chain activity belong to the
blockchain resource's scheduling/context model. They must likewise remain
possible between activations. Nothing here allows interleaving inside an
atomic `admit`.

#### Closing the protocol with resources

```agda
zk      : Protocol unitᴵ ZKIf
bridge  : Protocol ZKIf ServiceIf

services = bridge ∘ᵖ zk
system   = toProtocol ∘ᵖ services
```

`bridge` is the blockchain/service wrapper: it owns chain state and authenticated
context. It answers `snapshotRequest` with the selected account view, forwards
`proveRequest` to its left ZK interface without changing chain state, and handles
`submitRequest` using `admit` above, committing only the returned state and
answering with its verdict. Specify the chain's context/progress mechanism in
the chosen resource model; the caller does not select trusted admission time.

Both proving and the verification call inside `admit` use the **same** left ZK
instance. This avoids accidentally composing independent proof-token resources.
The ZK implementation and chain context model are supplied resources, not
generated from the contract program.

Preparation/proving and submission are separate activations of `toProtocol`.
They are not collapsed into a single atomic call when resources are composed.
The resulting closed protocol is an executable model under the supplied
resources, not generated Compact code. Privacy claims use the designated public
observations, not an observer who already sees the private `build` request.

For an ideal resource, the required soundness property has the shape:

```agda
Verified x π → Σ[ e ∈ Evidence x ] Rel x e
```

This is an obligation of a resource model, not a new Agda postulate. A concrete
scheme may provide a bounded failure probability instead. No extractor is
implicit in this existence statement. Zero knowledge and prover leakage are
separate properties of the chosen resource and its interfaces.

### 6. Operation laws and local proof interface

Defining executable handlers does not by itself justify transferring a local
proof to admission. Each selected operation must establish these laws:

```agda
same-view :
  prepare o s ≡ inj₂ (x , t) →
  apply o x s ≡ just t

rebase :
  prepare o s₀ ≡ inj₂ (x , t₀) →
  apply o x s ≡ just t →
  prepare o s ≡ inj₂ (x , t)
```

`same-view` supports positive admission. `rebase` says an accepted operation
describes a valid execution with the same result on the **current** state.
It does not assert that the old and current states or updates are equal.
For a blind increment, `x` is unit, but `t₀` adds the delta to the old count
and `t` adds it to the current count. For a predicate query, the result must
still hold, not the original scalar value.

These are proof obligations for the concrete operation handlers, not axioms
that hold automatically for new constructors. Prove them for field read/write,
counter delta, and predicate operations. Also give each operation its intended
transition/failure specification and prove that preparation and admission
implement it; agreement on the same wrong semantics would not establish
correspondence. Frame/noninterference laws are operation-specific. An extension
with late-bound results must supply an
appropriate refinement proof instead of claiming these laws unchanged.

With those laws proved, use a successful-execution Hoare predicate and establish
the conditional interpreter theorem:

```agda
Hoare : (State → Set) → Program A →
        (A → State → Journal → Set) → Set
Hoare P p Q =
  ∀ s a t j → P s →
  eval p s ≡ inj₂ (finished a t j) → Q a t j

replay-refinement : OperationLaws model →
  eval p s₀ ≡ inj₂ (finished a t₀ j) →
  replay ctx j s ≡ just t →
  eval p s ≡ inj₂ (finished a t j)
```

`OperationLaws` packages the proved obligations above. `replay-refinement` is a
proposed theorem, not checked Agda and not the old exact-cell replay theorem
assumed for an enlarged syntax. Its induction uses each operation's `rebase`
law; replay additionally enforces the authenticated chain conditions. Prove
eligible same-view replay using `same-view` and satisfied conditions.

Together with resource soundness, this supports invariant preservation: choose
satisfying evidence, rebase its execution to the actual admission state, and
apply the local preservation proof there. Never apply a precondition known only
about a stale preparation view. Also prove bind/journal concatenation, monad laws
for the selected observational equality, and segment rejection preservation.
Positive execution requires separate existence, resource completeness, and
eligible-admission arguments; successful-only Hoare reasoning is not enough.

#### Central requirement: lift Program properties to the assembled system

The main correctness result is not merely agreement of two local interpreters.
Properties established about entry-point `Program`s must yield properties of
the **fully assembled `system`**, including proof construction, verification,
admission, and adversarial submission. The following are proposed theorem shapes,
not checked API names. The first prototype targets exact safety lifting with
explicit ideal resources; quantitative replacement and relational privacy are
separate results.

Define abstract program executions from successful `eval` runs at admission
state, satisfied chain conditions, and their account-state updates. Rejection
and administrative actions leave that state unchanged. Define a projection of
finite system executions that retains committed program transitions and their
relevant public events, erasing administrative stuttering steps.

```agda
system-refines-programs :
  ResourceAssumptions →
  ∀ execution →
  SystemExecution system execution →
  ProgramExecution C (project execution)
```

Quantify over the permitted environments and include `submitOther`: the theorem
must not assume that every submitted transaction was generated by the honest
builder. Establish the bridge in four steps:

1. Proof acceptance yields satisfying evidence for the fixed relation.
2. That evidence identifies a successful evaluation of the bound entry point,
   inputs, witness, result, and journal.
3. Operation laws and replay refinement reproduce that evaluation from the
   **actual admission state**, with chain guards checked in its context.
4. Atomic admission commits exactly the resulting state; rejected attempts and
   proof-building steps do not change the selected account state.

The resource assumptions include fixed program/account binding, proof soundness,
authenticated context, specified operation semantics, atomic segment commitment,
and absence of another unchecked route to mutate the account. State the exact
initialisation and any external actions. They must either appear in the abstract
semantics or be covered by an explicit rely condition. Fees and other segments
remain outside the selected account-state projection.

##### Invariants and trace safety

For a state predicate `I`, prove preservation by every allowed entry point and
all its inputs and witnesses, not just by honest invocations:

```agda
Preserves C I =
  ∀ self name inputs witness s result s′ journal →
  I s →
  eval (body C self name inputs witness) s
    ≡ inj₂ (finished result s′ journal) →
  I s′

lift-invariant :
  ResourceAssumptions →
  I initialAccountState →
  Preserves C I →
  ∀ s → Reachable system s → I (accountState s)
```

Use the initial invariant and execution refinement to derive the reachable-state
conclusion. Cover every entry point that can change the state relevant to `I`;
a proof for recovery alone cannot constrain an unrelated unchecked writer.

More generally, a safety property of all finite abstract program traces lifts to
the corresponding projected system traces. Define the abstraction for any ghost
history or provenance instrumentation explicitly. Recovery submission provenance,
cancellation, and stale-transaction rejection need this historical form rather
than only a predicate of the final state. Observations erased by the projection
are not covered by the lifted property.

##### Exact versus cryptographic refinement

Initially prove exact refinement for concrete ideal resources and prove those
resources meet the premises. Do not replace that instantiation with postulated
soundness or an unimplemented `system`.

A later quantitative theorem bounds violations by the relevant cryptographic
resource failure events and their interaction allowances. Keep those bounds
outside ordinary local preservation proofs. Distinguish this structural
interpreter theorem from replacement of a resource under UC emulation: the
latter transports appropriately observable claims, not arbitrary internal-state
predicates without an adequacy argument.

##### Successful execution is a separate direction

Forward refinement alone permits universal rejection. Also establish an
execution-realisation result: a successful program run can be realised by the
protocol when proof/resource completeness, admission eligibility, and the
required scheduling hold. Exercise an actual successful lock clear, as well as
rejected and stale transactions. This is conditional responsiveness, not eventual
execution against every adversarial scheduler; eventuality needs additional
progress/fairness assumptions.

##### Relational privacy lifting

The correlation example requires a separate two-execution theorem:

```agda
lift-privacy :
  PrivacyResourceAssumptions →
  ProgramHistoryPrivacy C client leakage →
  ProtocolHistoryPrivacy (assemble C client resources) leakage
```

The premise concerns the explicit program/client observations: operation
arguments and results, publications, outcomes, and session behaviour. It must
not already assume privacy of the assembled proof transcript. The lifting
argument accounts for the additional proof and communication-binding
observations through the specified ZK and hiding resources.

Prove it for joint histories, not merely equal single-invocation marginals.
The secure Merkle histories have matching permitted ledger effects; the
reused-mask histories already fail the program-level relational premise.
An observable public-tag distinguisher then refutes protocol privacy as well.
That refutation needs preservation of the relevant observation and successful
execution, not a converse inferred from safety refinement alone.


### 7. First example and discriminating checks

An authentication function is a pure model parameter here. Its cryptographic
meaning belongs to the signature assumptions, not to the DSL:

```agda
deviceAction : AccountId → CallerInputs → DeviceWitness → Program ⊤
deviceAction self args w = do
  e ← read epoch
  n ← read nonce
  let current = deriveEntry self (key w) e (useCounter w)
      next    = deriveEntry self (key w) e (suc (useCounter w))
  live ← read (deviceEntry current)
  assert live unknownDevice
  write (deviceEntry current) false
  write (deviceEntry next) true
  assert (verifySignature (key w) (challenge self args n)
                          (signature w)) invalidSignature
  write nonce (suc n)
  assert (payloadAllowed args) invalidPayload
```

This is a reduced semantic example, not a source-complete Passport operation;
key-validity checks, scheme details, and bounded arithmetic must be supplied for
the source-shaped model. The late assertion deliberately exercises rollback.

The initial implementation should establish:

1. A successful run, replay, and subsequent updated credential use.
2. Failure of the late assertion with no committed credential or nonce change.
3. Rejection when a recorded read no longer matches at admission.
4. Preservation of a concurrently changed cell that the transaction never touches.
5. Correct read-after-write behaviour during replay.
6. Admission-time rejection of an otherwise valid proof whose time guard fails.
7. No acceptance of altered journal effects under a proof for the original
   statement, under the explicit resource-binding assumption.
8. Two blind counter increments prepared against the same count both commit and
   sum their deltas; a counter predicate remains eligible when its result is
   unchanged despite a concurrent count change.
9. Private caller inputs are absent from the public statement except through
   designated projections, sink observations, and communication binding.
10. A recipient rejects a substituted returned value/opening under the original
    communication commitment, under its explicit binding assumption.

These exercise the semantics without imposing circuit-realisation restrictions
or making manual Compact correspondence into a compiler-verification project.

### 8. Official lock example: concrete program and proof target

Start with the `clear` circuit in Midnight's
[Writing a contract](https://docs.midnight.network/compact/reference/writing.md#local-state-and-computations)
lock example. This is **existing Compact source**, not proposed Agda:

```compact
export circuit clear(): [] {
  assert(state == State.SET, "Attempted to clear uninitialized value");
  const sk = secretKey();
  const pk = publicKey(round, sk);
  assert(authority == pk, "Attempted to clear without authorization");
  state = State.UNSET;
  round.increment(1);
}
```

The example declares `state: State`, `authority: Bytes<32>`, `value: Uint<64>`,
and `round: Counter`, and a `secretKey(): Bytes<32>` witness. Its `publicKey`
hashes `[pad(32, "midnight:examples:lock:pk"), round as Bytes<32>, sk]` with
`persistentHash`. These are a secret and its hash, not a digital-signature scheme.
The documentation's complete program pins **language 0.16**; preserve that
version caveat and review the implicit counter read and exact hash encoding
before using it as a correspondence reference for a newer toolchain. No
compilation or execution of the example is asserted here.

The proposed DSL target uses three disjoint scalar cells and a counter operation
family; `value` is retained so its preservation can be stated:

```agda
-- Proposed design pseudocode, not checked Agda.
-- readRound is an exact Counter read; incrementCounter is a delta update.
-- lockState, lockAuthority, lockValue are scalar cells.
-- publicKey : Uint64 → Bytes32 → Bytes32 preserves the source encoding.
clear : Bytes32 → Program ⊤
clear sk = do
  st ← read lockState
  assert (st == SET) uninitialised
  r ← perform (ledger (readRound lockRound))
  let pk = publicKey r sk
  a ← read lockAuthority
  assert (a == pk) unauthorised
  write lockState UNSET
  increment lockRound 1
```

For entry `clear`, `Input`, `PublicArgs`, and `Result` are unit; `Witness` is the
secret-key reply. No raw secret or intermediate `disclose` annotation is
published. Its statement binds the unit inputs/result and the ledger journal.
The constructor and other operations are not arbitrary repeatable clear
entry points: use the documented initialized state and, for the replay scenario,
faithful `set`/`clear` operations.

Write and prove the following concrete obligations:

1. **Accepted-transition safety.** From any admission state `s`, acceptance of
   a relation-bound `clear` implies `s.state = SET` and existence of a witness
   `sk` with `s.authority = publicKey s.round sk`. The committed state has
   `state = UNSET`, `round = s.round + 1`, and unchanged `authority` and `value`.
   A supplied witness with a different derived key fails, preserving committed
   state. This is a witness-relation property, not a claim that an adversary
   knows an extracted secret.
2. **Non-vacuous success.** Construct `s` with `state = SET`, `round = 0`,
   `authority = publicKey 0 sk₀`, and any value `v`. Evaluate `clear sk₀`,
   construct its statement/evidence, obtain a verifiable proof under resource
   completeness, and show eligible same-view admission with exactly the
   transition above. Universal rejection does not satisfy this obligation.
3. **Stale-round replay rejection.** Prepare a successful clear at round `r`.
   Admit an intervening clear and a documented set, returning the lock to `SET`
   at round `r + 1`. Submitting the old prepared statement is rejected because
   its exact round read is stale, even though the state flag is `SET` again.
   Rejection preserves the intervening state; its authority need not be assumed
   different merely to make the stale-read argument work.

Required assumptions are the operation laws and schema frame laws, fixed
account/entry identity and proof-bound journal, source-correct hash encoding,
the selected atomic-segment semantics, and a non-overflowing `Uint64` counter
increment. Soundness supports accepted-transition safety; completeness supports
the constructed positive run. A stronger claim excluding an adversary without
the secret needs appropriate preimage/knowledge assumptions, not just proof
soundness. The example is not a proof of unlinkability or prover privacy.

This is a small existing witness-gated program that exercises real dependencies,
admission, rejection and replay resistance before Passport's recovery lifecycle.
It needs no assets or cross-contract machinery. As a separate operation
discriminator, the official compiler's
[counter example](https://github.com/LFDT-Minokawa/compact/blob/66d355efffe9e77b3814cebc0d50a28c95494420/examples/adt/exports/counter.compact)
contains:

```compact
export circuit increment(amount: Uint<16>): [] {
  return c.increment(disclose(amount));
}
```

Model it as `increment c amount`, and prove two eligible increments prepared
from the same value produce `c + d₁ + d₂` when both commit under numeric bounds.
The frozen compiler source is a development snapshot, not a claim about every
released toolchain. Unlike `clear`, this circuit has no exact counter read; it
detects an incorrect read/replace interpretation of delta updates.

### 9. Second target: history privacy and a correlation-only leak

Midnight's [Private data: Making use of Merkle trees](https://docs.midnight.network/concepts/how-midnight-works/keeping-data-private.md#making-use-of-merkle-trees)
gives this **existing Compact circuit** with `items: MerkleTree<10, Field>` and
`findItem(item): MerkleTreePath<10, Field>`:

```compact
export circuit check(item: Field): [] {
  const path = findItem(item);
  assert(path.leaf == item, "path is not for this item");
  assert(items.checkRoot(disclose(merkleTreePathRoot<10, Field>(path))), "path must be valid");
}
```

The documentation supplies the membership check, not the following deliberately
insecure modification. The proposed variant leaks a correlation across calls
rather than the member itself. It is also grounded in the guide's
[warning about randomness reuse](https://docs.midnight.network/concepts/how-midnight-works/keeping-data-private.md#randomness-and-rounds-in-commitments),
but uses elementary masked bits rather than changing the commitment scheme.

#### Fixed fixture and functional equivalence

Fix an unchanged tree with four distinct, publicly known leaves `a`, `b`, `c`,
and `d`, valid paths for all four, and a common root `rt`. Define a public pure
predicate `classify`, false on `a,b` and true on `c,d`. For example, compare the
item with `c` and `d`; no private state access is needed. Give both variants an
immutable public `flags: Set<Boolean>` containing both Boolean values.

The insecure client samples a uniform private bit `mask` once per session and
reuses it in two calls. After the ordinary Merkle check, the insecure circuit
computes `tag = classify(item) xor mask` and adds this public ledger query:

```compact
// Proposed fragment; tag was computed from private item and session mask.
assert(flags.member(disclose(tag)), "invalid flag");
```

The leak is the **Set operation's public argument**, not `disclose` by itself.
For the fixed fixture the extra assertion always succeeds, and both variants
have the same acceptance, unit return, and unchanged ledger state. They need
not have the same cost, journal, or proof bytes. This is not a claim of
equivalence in arbitrary states where a flag has been removed.

Four leaves make the leaked classification coarser than identity. In the
two-history challenge below, the observer can nevertheless identify the
challenge world perfectly; a partial-information leak can completely violate
an indistinguishability property.

#### Programs and session protocol

```agda
-- Proposed concrete ledger primitives:
checkRoot     : TreeId → Digest → Op Bool
flagMember    : SetId → Bool → Op Bool

checkSecure : Field → MerklePath → Program ⊤
checkSecure item path = do
  assert (leaf path == item) wrongLeaf
  ok ← perform (ledger (checkRoot items (pathRoot path)))
  assert ok invalidPath

checkInsecure : Field → MerklePath → Bool → Program ⊤
checkInsecure item path mask = do
  checkSecure item path
  let tag = classify item xor mask
  member ← perform (ledger (flagMember flags tag))
  assert member invalidFlag
```

`Input check` contains the private item. Its witness contains the path, and for
the insecure variant the mask. Public arguments and result are unit.
`pathRoot` is a pure source-shaped computation. Both ledger primitives are
read-only: preparation returns the predicate result and unchanged state;
admission recomputes and checks that result. Prove their operation laws. The root query
reveals the root but not its private path, and `flagMember` reveals only the
masked bit. Do not model Merkle path acquisition as a public leaf lookup.

Mask sampling belongs to the **client protocol**, not the deterministic
transaction program. A schematic state transition is:

```agda
data Session : Set where
  unopened : Session
  active   : Bool → Session

-- Fragment of Protocol.step, before proof construction/submission:
step unopened beginSession =
  coin uniform-Bool λ mask → ret (active mask , sessionReady)

-- On each later check request, an active session supplies the same mask
-- in the private evidence passed to checkInsecure.
```

Complete this with the existing separate preparation/submission activations;
do not make the two transactions one atomic activation. Reset the session
between independent experiments, but not between its two calls. Proof and
communication-commitment randomness remain fresh per invocation; only the
deliberately exposed tag uses the reused mask.

The circuit cannot enforce honest random sampling or session reuse from this
witness alone. The experiment specifies that client behaviour. Its privacy
claim concerns the client/contract/resource composition, not arbitrary witness
providers or privacy against the prover. No new DSL randomness primitive is
required.

#### One observation versus a history

For either class, a single tag is uniformly random:

```text
Pr[classify(item) xor mask = false] = 1/2
Pr[classify(item) xor mask = true ] = 1/2
```

But two tags computed with the same mask satisfy:

```text
tag₁ xor tag₂ = classify(item₁) xor classify(item₂).
```

Thus the pair reveals whether the private members are in the same class even
though either tag alone reveals no class information. This marginal statement
concerns the tags; privacy of the rest of a single-call view still depends on
ZK and communication hiding. It is not enough to inspect each call separately.

#### The same history-privacy property for both variants

Sample a uniform challenge bit `choice` and an independent session mask.
World zero invokes `check(a); check(b)` using the two fixed leaves in the
same class; world one invokes `check(a); check(c)` using opposite classes:

```text
History(0) = [(a, path_a), (b, path_b)]
History(1) = [(a, path_a), (c, path_c)]

HistoryPrivacy(C, δ) =
  for every admissible D,
  | Pr[D(View_C(History(0))) = 1]
    - Pr[D(View_C(History(1))) = 1] | ≤ δ.
```

`C` includes the selected client session behaviour and resource composition.
Use the same public fixture, scheduling, metadata, account/entry identity, and
two successful admissions in both worlds. Compare histories **within each fixed
variant**, not the secure and insecure contracts' different code identities.

The observer receives the entire designated public view of both calls:
statements, journals, communication commitments, proofs, acceptance and unit
outputs. It may know all four leaves and their paths, and auxiliary information
fixed independently of `choice` and the mask. It does not receive the mask,
commitment openings, prover inputs, or caller channels carrying the selected
items. Exclude local path-search timing and other client/prover transport
observations rather than silently claiming to protect them.

In an exact ideal-resource model take `δ = 0`. For a computational family,
require a negligible bound at the selected admissible distinguisher class.
Interaction bounds alone do not establish polynomial-time security.

**Secure proof target.** Both histories generate the same root-query journals,
predicate results, unchanged states, and unit outputs. Use ZK simulation for
the two proofs, then hiding of the input/result communication commitments to
replace the private item history. State these assumptions for the joint
two-call view with the permitted auxiliary information: single-call marginals
alone are insufficient. If `ε_ZK-session` bounds replacement of the whole
two-proof view in each world and `ε_comm-session` bounds the commitment-history
hybrid, the probability gap is at most
`2 ε_ZK-session + ε_comm-session`. Derive those session bounds from the selected
resources rather than assuming composition for free. Under exact ideal ZK and
ideal hiding the gap is zero. Randomized commitments need not be bit-identical.

Construct successful evaluations and eligible admissions for every call in
both histories. The secure property must not hold merely because all calls
are rejected.

**Insecure negation target.** Read the two public `flagMember` arguments and
output their XOR. World zero produces `(false,false)` or `(true,true)`;
world one produces `(false,true)` or `(true,false)`, each pair with probability
one half. The observer's output is exactly `choice`, giving probability gap
**1**, bit-guessing success **1**, and advantage over random guessing **1/2**.
This refutes `HistoryPrivacy(insecureSystem, 0)` and every bound below one,
hence the same negligible-gap property for a security-parameter family.
There is no attack on the ZK primitive: the leakage is in public application
data.

As a diagnostic, resampling the mask independently for each invocation makes
all four tag pairs equally likely in both histories. Prove this distribution
fact separately; it is not by itself a privacy proof for the entire application.

This is application history privacy **derived from ZK**, not a proof that a
concrete SNARK is zero knowledge. Assumptions include source-matching public
observations, joint-view ZK and communication hiding, the specified client
randomness/state behaviour, and completeness for the successful runs.
Binding/soundness justify accepted membership separately. No hardness assumption
for the elementary XOR calculation is needed.

The executable ideal experiment above implements these variants with computed
symbolic current-root paths and a public Boolean-set query, not historic-root
semantics or an invented private Set query. The private-data page is unversioned;
the review date and application version caveats are recorded above. These are
manual correspondence examples, not verified Compact compiler translations or
established real-resource cryptographic theorems.


## Proof interface and resource assumptions

Start with small proof rules for sequential composition, reads and writes,
assertions, successful execution, and failure. Support preconditions,
postconditions, and preservation of invariants. Most contract proofs should be
local; protocol-level results account for adversarial interaction and composition.

The initial interpreter obligations are:

- Successful evaluation and communication binding establish the induced relation.
- Each selected operation satisfies its intended semantics and replay laws.
- Rejected or aborted segments preserve the modelled committed account state.
- The chain applies the effects bound to the accepted statement, not a substituted
  effect description.
- Admission checks use the specified chain context and ledger dependencies.
- The honest operational interpretation agrees with the local program semantics.
- Delivered caller results authenticate against the bound inputs/result commitment.
- Publication, witness acquisition, and private-state transitions have explicit
  observers and failure semantics; `disclose` annotations are not publication.

Keep cryptographic assumptions distinct:

- Proof soundness connects acceptance to satisfaction of the program relation.
- Knowledge soundness is required only for claims that need witness extraction.
- Resource completeness supports the non-vacuous positive execution obligations.
- Communication commitment binding authenticates a delivered input/result pair;
  hiding and zero knowledge are separate privacy assumptions.
- Signature security connects verification constraints to the appropriate
  authorisation assumptions; proof soundness alone does not establish consent.
- Zero knowledge bounds the specified observer's information, under the stated
  public leakage. It is not needed for every safety theorem.

Observable properties can be transported through suitable UC emulations. An
internal-state invariant does not transfer automatically: an observation-adequacy
argument is required where the theorem makes that connection. Historical
properties may require a stateful observer rather than a predicate on one
request/response pair.

## Manual correspondence review

For each implementation-shaped specification, record the implementation revision
and review the following against the actual circuit:

- Caller inputs, their public projection, witness trace, authentication gates,
  challenge bindings, and key validation.
- Assertion order, operation-specific dependencies/updates, and segment rollback.
- Public ledger observations, events, actual publication sinks, private material,
  and caller-result communication binding.
- Chain-time/context conditions and operation-specific validation at admission.
- Numeric widths, overflow/partial operations, storage representation, and
  cryptographic encodings abstracted by the model.
- Any omitted operation and why it cannot invalidate the claimed property.

Mathematical numbers, maps, and structured credentials are acceptable modelling
aids. If a representation detail affects a theorem, retain it or make the
corresponding restriction explicit. In particular, unbounded-natural arithmetic
does not establish correctness at bounded-integer exhaustion.

Manual review is the link to implementation, not a mechanised compiler theorem.
Keep separate labels for design obligations, checked model theorems, resource
assumptions, manual correspondence evidence, and executed implementation checks.

## Generic ZK remediation roadmap

The adversarial reviews found valid but partially disconnected components:
generic replay/safety proofs, an example-specific ideal privacy proof, and a
generic categorical resource-replacement theorem. The implementation is not yet
an end-to-end generic ZK specification tool. This roadmap supersedes the earlier
example-first milestone order; the checked examples remain regression targets.

The target author workflow is to supply ledger semantics, a `Program`/`Contract`,
a client policy, permitted observations, and a local relational proof. Generic
theorems should establish ideal-system privacy and transfer it to any resource
satisfying the specified UC-emulation assumption. No application should need
another interpreter, admission semantics, or contract-specific lifting proof.

### 1. Security contract and target theorem

Write precise interfaces and theorem signatures for the complete proof chain
before changing the interpreters. Distinguish private caller/prover inputs,
witnesses, openings and recipient outputs from public ledger effects, artifacts,
publications and outcomes. Specify adversary-controlled submission/scheduling
and explicitly permitted leakage.

Retain a two-world property over a generic experiment. Prove that one
resource-level simulation works uniformly across both challenge worlds, with
ideal privacy against the corresponding simulator class. Two unrelated
existential simulators do not establish real-world indistinguishability.
Reuse upstream `UCSetup`: use `Robust` when appropriate, and a shared-simulator
relational transfer lemma where that is the direct formulation.

Acceptance:

- Assume resource emulation, not privacy of the real assembled application.
- Make the ideal privacy premise dischargeable from a program/client relational
  proof rather than assuming the intended conclusion at another name.
- Account for both verdicts and divergence; do not identify rejection with
  nontermination.
- Separate exact and negligible-security statements.

**First work package:** settle this contract and check the exact shared-simulator
transfer argument against upstream APIs. Document the proposed public/private
boundary and the remaining interpreter obligations. This package does not claim
to unify the existing Merkle and generic interpreters or complete their
application-level privacy proof.

#### Package 1: public/private boundary and exact security contract

This is the target boundary for the generic tool, not a claim that the current
`Interpreter.ClientIf` already implements it. A contract instance fixes its
ledger semantics, registered code/verifier identity, client policy, recipient
authorization, observation policy and leakage function **before** selecting the
challenge world. Both worlds use the same typed resource service, public
interface, policy and adversary grade. They may use different honest contexts
(including different private inputs, randomness and persistent private state).
They must not select a world-dependent public interface or silently hide a
public operation by changing the observer.

| Boundary | Required information and access |
|---|---|
| Private caller/client | Circuit inputs not explicitly disclosed, private state, witness-provider requests/answers, fresh randomness and opening material. These requests are not adversary submissions. |
| Private prover service | Witnesses and successful-execution evidence, including any private inputs/results needed by the relation. They are sent only on the honest proving port; the public verifier must not require the submitter to re-supply that private certificate. |
| Private recipient | Results and communication openings, available only to the designated authorized recipient. A public commitment/artifact is not permission to read its plaintext. Recipient identity/authorization is fixed or included in declared leakage. |
| Public statement/effects | Code/verifier and account identity, entry point and disclosed arguments, ledger query arguments/results and deferred journal effects to the extent declared public, actual publications, public state changes and permitted snapshots. Public input equality is equality of this projection, not equality of private witnesses. |
| Public artifacts | Proof and communication encodings/handles, their lengths and lifecycle events where observable; submitted statement/artifact bindings; public opening/verification results when the policy exposes them. Artifact values need not be pointwise equal between worlds: their joint distribution must obey the ideal relation. |
| Public outcomes | Build/proving failure, explicit rejection, acceptance, recipient delivery notifications and other visible errors according to the policy. Divergence/absent response is a separate observation, never a synonym for rejection. |
| Adversary/scheduler | May choose public submissions, alter or substitute statements/artifacts, invoke exposed verification, replay according to the service contract, interleave calls and permitted external ledger updates, and choose authorized scheduling/time transitions. It cannot replace authenticated account identity or read private ports. Adaptive choices depend on the permitted public transcript, not on a challenge bit supplied out of band. |

Permitted leakage is an explicit projection of an execution/interaction trace.
It includes visible identity and routing, entry points/disclosed arguments,
public ledger traffic and state, publications, exposed artifact metadata and
outcomes, and declared scheduling/length information. Nothing is declassified
merely because it occurs in an Agda record. Witnesses, undisclosed inputs,
openings and recipient plaintext are excluded unless the application explicitly
declassifies them. An application that intentionally reveals a private predicate
through an error must either include that predicate in its leakage-equivalence
relation or fail the privacy premise. Already-emitted I/O stays in the trace
after an abort; rollback only discards deferred transaction effects.

The observer owns its verdict computation. It can encode acceptance, rejection,
failure or a predicate of the full public transcript as either Boolean verdict.
Security compares **both** verdict subprobabilities; the missing termination
mass is divergence. It does not assume successful execution or total response.
This is qualitative eventual observation, not a claim of step-by-step timing
privacy. Wall-clock timing and deadlines require a separate declared cost/time
semantics and leakage policy.

Current boundary repairs and remaining obligations:

- Package 3 parameterizes communication and supplies a declared result policy.
  `ClientIf` is private; `Observation.wrapper` exposes only a policy-selected
  public action interface and actual projected responses. Non-hiding tuple
  artifacts are confined to the named safety instance. The Merkle experiment
  wraps the same interpreter and stores its actual private draft.
- `Proof.certificate` and `ZKQuery` still contain private evidence. The unified
  honest session verifies its actual generic draft, but its displayed proof token
  is not an issued public proof artifact. Package 4 supplies private proving,
  public checking, statement/artifact binding and adversary ports. Its
  real-resource assumption is UC emulation, not equality with `idealStep`.
- `Privacy.PrivateExecution` retains successful fixture derivations, but the
  wrapper does not use them as a substitute for evaluation or admission.
  Histories still select two honest calls with a reused mask. Package 5 supplies
  generalized adaptive histories, persistent private state and nonidentity
  couplings; package 7 supplies evolving scheduling/time and probabilistic safety.
- `HistoryPrivacy` now concerns the unified interpreter wrapper. Its ideal
  `seal-law` is still literal tree equality, not a real ZK assumption. Package 6
  must connect its local proof to the generic ideal premise and apply the
  checked resource replacement theorem end to end.
- No present adapter establishes negligible-stable application privacy or PPT
  execution. Package 8 owns the certified-family, computation/message bounds
  and admissible simulator closure obligations.

#### Checked shared-simulator transfer

`PrivacyReplacement.Transfer.Replacement` now extracts the dummy simulator
**once from resource emulation**, using upstream `≤UC⇒dummy`:

```agda
real : A ⇒ T₀ X B
ideal : A ⇒ T₀ Y B
emulates : real ≤UC ideal
simulator : Y ⇒ X
resource-simulation : real ≈ᵁ sub simulator ∘ ideal

context-simulation :
  (context : B ⇒ T₀ Z C) →
  context ∙ real ≈ᵁ sub (simulator ⊗₁ id) ∘ (context ∙ ideal)
```

These signatures omit module qualifications for readability; the actual
signatures are checked Agda, generic over upstream `UCSetup`.
`context-simulation` uses `ext-cong` and the graded substitution commutation law.
It does **not** extract a simulator from the assembled context.
Thus the resource simulator is independent of `Program`, context, challenge
world, prefix/ancilla `W`, observer and schedule. A joint adversary may still
adapt to the public transcript: `regradeEnv` composes that same observer with
the same simulator.

For compatible `left right : B ⇒ T₀ Z C`, `Replacement.TwoWorld` checks:

```agda
transfer-observation :
  (W : ℐ.Obj) (e : Env (T₀ (W ⊗₀ (X ⊗₀ Z)) C)) →
  run W (left ∙ ideal)  (regradeEnv W (simulator ⊗₁ id) e) ≈Env
    run W (right ∙ ideal) (regradeEnv W (simulator ⊗₁ id) e) →
  run W (left ∙ real) e ≈Env run W (right ∙ real) e
```

This is the direct relational theorem; no binary relation is disguised as a
unary `Robust` predicate. `simulated-observation` supplies each endpoint of the
three-step transitivity proof. The middle premise mentions **only the ideal
resource** and a shared simulated observer; it is not assembled real privacy.
`transfer-private` takes that ideal equality for every resource-grade
`s : Y ⇒ X` and every admissible real-interface environment, regraded by
`s ⊗₁ id`. This formulation needs no separate closure assumption: stability
under that simulator class is in the ideal premise itself. It is usable even
when the policy is easier to express on real-interface observers.
`transfer-closed` alternatively takes ideal privacy for every admissible
ideal-interface environment, plus
`∀ s → ClosedUnder Adm (s ⊗₁ id)`. Its closure proof guarantees that the shared
simulated environment meets precisely that ideal premise. A narrower simulator
class can be used with `transfer-observation` by proving membership of the
extracted simulator; resource emulation alone does not supply such membership.

At `Exact.StdSetup` the readout compares true **and** false masses to every
positive rational slack (`≈ᵁ` includes every prefix). In particular, always
rejecting and diverging are not equivalent. Equal eventual verdict
subprobabilities preserve the missing termination mass without assuming either
world terminates. No finite settling budget is promised for arbitrary machines.
The existing `ComputationalTransfer` alias uses a different negligible-family
setoid; this exact theorem supplies no error bound, polynomial-time guarantee,
or PPT restriction for arbitrary DSL contexts.

#### Interpreter proof signatures still required

The following are **design obligations**, not Agda declarations, postulates,
implemented wrappers or claims about the current Merkle interpreter. They fix
what later packages must connect to the checked transfer.

Let `L` be a fixed leakage policy; let `C₀,C₁` be compiled honest contexts for
two invocations/histories of the same registered program/client policy. Let `R`
relate their private client states, ledger views and randomness, while requiring
equal public state and equal declared leakage. A local premise must establish:

```text
LocalRel(P, client, L, R) :=
  related initial states
  ∧ for every R-related pair and every paired allowed public action:
      a coupling of the ideal next-step subdistributions
      with equal emitted L-events and R-related resumptions
      and equal public failure/rejection/delivery observations
      and equal missing mass (including dead/nonresponse branches)
```

The coupling may complement a mask or relate distinct private states; it is not
restricted to pointwise equality at the same random seed. A program proof
cannot discharge this alone if a client emits additional private data: the
client-policy and resource-service relational obligations are explicit inputs.
`R` must also account for pending calls, public ledger state/snapshots, committed
effects and already-emitted interactions. For unbounded executions the lifting
needs a prefix-consistent coupling/simulation preserving both eventual verdict
masses; a terminating-only success lemma is not an adequate substitute.

The intended generic bridge signatures are:

```text
compile-observation :
  DeclaredBoundary(P, client, L) →
  public observations of compiled ideal execution
    = observations of the L-projected execution/interaction semantics

local-to-ideal :
  compile-observation
  → LocalRel(P, client, L, R)
  → IdealResourceRel(ideal, L, R)
  → SimulatorPolicyClosure(L, Adm)
  → ∀ s W e, Adm W (X ⊗ Z) e →
      run W (C₀ ∙ ideal) (regradeEnv W (s ⊗ id) e) ≈Env
      run W (C₁ ∙ ideal) (regradeEnv W (s ⊗ id) e)

resource-to-real :
  real ≤UC ideal → [the output of local-to-ideal] →
  ∀ W e, Adm W (X ⊗ Z) e →
      run W (C₀ ∙ real) e ≈Env run W (C₁ ∙ real) e
```

`IdealResourceRel` is a specification/proof of ideal services on related
requests: public artifact/checking behavior and private table/opening behavior,
including invalid submissions. It is not a privacy assumption on an assembled
real application. `SimulatorPolicyClosure` must justify the observer class used
by `local-to-ideal`, or the proof must directly quantify the regraded class.
`resource-to-real` is exactly the checked `TwoWorld.transfer-private`; the first
two bridges are pending packages 3–5. This chain makes the ideal premise
dischargeable by local program/client/service relations without assuming the
intended real conclusion.

#### Checked finite demonstration

`PrivacyReplacementExample.agda` uses upstream `StdUC` with the Cartesian
category of sets and its representable Boolean-test presheaf. It is a finite
deterministic idealization, not cryptography or a replacement runtime.
For resource input `b`, the ideal resource returns adversarial bit `b` and honest
payload `(b, not b)`; the real resource returns adversarial bit `not b` and the
same payload. Here `b` is allowed leakage: the hidden challenge is which context
is used, not the value of `b`. The nonidentity negation simulator proves resource
emulation.
The left context returns the verdict for the first payload component; the
right context returns the verdict for the complement of the second. They
disagree on unrestricted payloads, but the ideal invariant makes them private
for **every** simulator and prefix observer. `real-private` exercises
`transfer-private`, and `shared-observer-transfer` instantiates a concrete
observer comparing the adversarial bit with the acceptance verdict.

That observer returns true on the unsimulated ideal experiment and false on
the real experiment; `simulated-ideal-correlation` returns false on the ideal
experiment with the shared simulator. This deliberately exposes why an
honest-only ideal premise cannot be substituted. `contexts-sensitive` changes
the payload to `(b,b)` and proves the same observer distinguishes the contexts,
so the ideal relational premise is substantive. `rejection-not-divergence`
checks that the finite observation alphabet has a discriminating rejection
observer. Actual machine divergence is covered by the exact setup's two-sided
subprobability readout, not by interpreting this finite alphabet as execution.

Package-1 verification on 2026-10-08 was serial against the pinned dependency:
`PrivacyReplacement.agda`, its new importer `PrivacyReplacementExample.agda`,
`PrivacySmoke.agda` and `Smoke.agda` all passed the canonical
`LC_ALL=C.utf8 timeout 1800 pagda --useUntracked false check … --
+RTS -M3G -H1G -RTS` checks. The proof escape-hatch scan of
`src/Midnight/ContractDSL` was empty before and after. Successful check/compiler
outputs had no `ModuleDoesntExport`, `UselessPublic`, `UselessPrivate` or
`DuplicateUsing`.

The existing `PrivacySmokeMain.agda` and `SmokeMain.agda` were compiled with
`--compile --compile-dir=<temporary-directory> --ghc-flag=-O0` and executed,
not replaced by theorem-only or wiring-only tests. The first privacy compilation
exhausted the paired 3-GiB heap during upstream Haskell generation; its truncated
generated `Categories.Category.Monoidal.Interchange.Braided.hs` was removed,
and the paired `-M8G -H1G` retry succeeded. The generic program smoke then
compiled with `-M3G -H1G`, reusing that temporary dependency build.
The privacy run returned `1/1` successful mass in all four histories, secure
observer masses `0/1` versus `0/1`, and insecure masses `0/1` versus `1/1`.
The actual generic lock program/protocol run returned `true` for valid clear,
wrong-key/invalid-submission rejection, and stale-draft rejection after
clear/set interference. All temporary generated Haskell, objects and executables
were removed. These are model runtime regressions; they do not establish
privacy of the current plaintext generic client or a real cryptosystem.

A throwaway IO wrapper also compiled and executed the **new**
`PrivacyReplacementExample` itself. For each Boolean resource input it evaluated
`run ⊤ (context ∙ resource) correlationObserver (tt , b)` using the existing
`left`, `right`, `ideal`, `real` and `broken` definitions. The simulated ideal
observations used the existing
`regradeEnv ⊤ (R.simulator ⊗₁ ℐ.id) correlationObserver`; no output was replaced
by a literal or a theorem's claimed value. Observed output was:

```text
input false: raw ideal left/right true/true; real left/right false/false; shared-simulated ideal left/right false/false; broken payload left/right true/false
input true: raw ideal left/right true/true; real left/right false/false; shared-simulated ideal left/right false/false; broken payload left/right true/false
```

The wrapper's canonical check passed; compilation with `--compile`,
`--compile-dir=<temporary-directory>` and `--ghc-flag=-O0` first exhausted
the paired 3-GiB heap generating upstream `Braided.hs`. Removing that interrupted
generated file and retrying with paired `-M8G -H1G` completed successfully.
The successful compilation warning gate was empty. The wrapper source,
its `.agdai`, generated Haskell, objects and executable were removed after the
run. This runtime demonstration exercises the nonidentity simulator and the
counterexample-sensitive contexts; the lock/Merkle runs above separately
exercise the actual existing program/protocol paths.

Package 2 implements semantic parameterization without modifying the
shared-simulator resource theorem; package 3 implements the interpreter and
observation cutover. Packages 4–6 still owe artifact lifecycle, generalized
histories and the end-to-end application replacement bridge.

### 2. Parameterize the semantic core

**Status: completed and verified on 2026-10-08.** This package is semantic
reuse and current-state safety, not a repair of generic ZK privacy.

Implemented module split:

- `Ledger.Semantics` supplies only `State Kind Failure : Set`, `El : Kind → Set`,
  one ordinary indexed `Op : Kind → Set`, `prepare : Op k → State →
  Failure ⊎ (El k × State)`, and decidable equality of operation results.
- `Ledger.Execution L` derives `validate`, `apply`, `validate-self`,
  `same-view`, `validate-rebase` and `rebase`. Instances supply no separate
  admission-law proofs. Every admitted operation is a current-view execution.
- `Program L Assertion` and `Protocol L Assertion` share that instance and an
  application assertion-label type. Internal small result codes distinguish
  ledger results from unit-valued assertion/publication/chain effects; there
  is no `Set → Set` operation universe, `CellSchema`, receipt or generic VM.
  `operationError Failure` and `assertionError Assertion` remain distinct in
  `eval` and consumer `buildFailed` responses. Admission intentionally reports
  only `accepted`/`rejected`, preserving its existing atomic rejection boundary.
- `MidnightLedger` owns lock fields, symbolic digest-valued storage, numeric
  bounds and its single operation datatype. `checkRoot` reads `root s`;
  `updateRoot` updates it. `flagMember` reads `falseFlag`/`trueFlag`;
  `updateFlags` changes those contents. `SymbolicDigest` owns the hash algebra;
  `FixtureLedger` owns the example root/default fixture initialization.
  Imports are acyclic: generic core → no concrete instance; concrete ledger →
  generic interface and digest algebra; fixture → concrete ledger/algebra;
  consumers → chosen ledger plus parameterized core.
- Lock-specific `read`, `write`, and `increment` conveniences live in `Lock`.
  `PrivacyReplacement.ForProgram`/`ForContract` now take the selected semantics
  and assertion labels; `Transfer`, shared simulator, two-world transfer and
  the nonidentity simulator example are unchanged mathematically.

**Explicit semantic change and correspondence.** The previous Merkle
`successful v i mask s` and `admitted ... s ...` quantified over every state
because the root and both flags were global constants. They are false for
mutable roots/removed flags. Their statements now require
`Compatible s = (root s ≡ fixtureRoot) × (falseFlag s ≡ true) ×
(trueFlag s ≡ true)`. `fixture-compatible` and `fixture-successful` recover
the intended successful, same-state fixture executions. Privacy construction
uses this specialization; its privacy/safety boundaries and probability claims
are unchanged. For arbitrary roots, `MerkleState.matching-success` proves
success from exactly leaf/input equality and path-root/current-root equality.
The full generic replay refinement, Hoare lift, accepted refinement and
admission/reachable invariant theorems retain their strength. Lock clearing
preserves the additional root/flag fields as well as its original authority
and value frame; the concrete `ClearPost` uses a state record update.

The independent balance instance has no Midnight import. Its two-account map
implements exact balance reads and unit-result transfers with
`insufficientFunds`; a zero-amount program fails with the separate assertion
label `emptyTransfer`. `send-conserves` proves total conservation, and
`accepted-conserves`/`assembled-conserves` reuse the generic admission and
reachable-state invariant theorems. A three-unit transfer from `(10,2)` can
validly replay to `(7,5)`, then `(4,8)`, then `(1,11)`; the next replay rejects
atomically. Exact stale balance reads reject. There is no universal replay ban.

`MerkleState` exercises actual generic contracts: membership against the fixture
root accepts, root replacement with `merkleLeaf 9` accepts, the still-valid old
preparation certificate fails current-view replay/admission, and a fresh path
`path 9 []` succeeds against that new root. Removing the false flag rejects the
corresponding insecure membership and its journal. Maintenance entries in this
regression contract are intentionally unrestricted; they are not a claim about
the source contract's authorization/bootstrap policy.

Source limits remain explicit: symbolic hashes are not byte encodings or
cryptographic security; the two-account balance map is a minimal independent
reuse example, not a token implementation. Chain context still uses fixed
natural-valued account/time (package 7). Witness-carrying generic certificates
and the explicit non-hiding tuple remain the safety instance, not generic ZK
privacy. Packages 4–8 remain required as described below.

#### Package-2 verification

Serial canonical checks passed against pinned
`categorical-crypto-protocol-rewrite-437dca12`:
`Smoke.agda` (including the changed ledger/program/protocol, lock, Merkle,
fixture, mutable-state and balance closure), the public independent
`Balance.agda`, `PrivacySmoke.agda`, `PrivacyReplacementExample.agda`
(including `PrivacyReplacement`), `SmokeMain.agda` and
`PrivacySmokeMain.agda`. Commands used
`LC_ALL=C.utf8 timeout 1800 pagda --useUntracked false check … --
+RTS -M3G -H1G -RTS`. The warning gate
`ModuleDoesntExport|UselessPublic|UselessPrivate|DuplicateUsing` was empty
for successful checks and compilations. The
`src/Midnight/ContractDSL` escape-hatch scan was empty before and after.

The existing IO entry points compiled with
`--compile --compile-dir=<owned-temporary-directory> --ghc-flag=-O0`
and were executed. `SmokeMain` compiled with paired `-M3G -H1G`;
its actual assembled-protocol strategies returned:

```text
valid clear accepted (UNSET, round 1, value 99): true
wrong key fails and raw invalid submission rejects: true
clear/set interference then stale draft rejects (SET, round 1, value 100): true
balance transfer and valid replay accepted (alice 4, bob 8; total 12): true
balance insufficientFunds operation error differs from emptyTransfer assertion: true
balance repeated transfer rejects atomically when funds exhausted (alice 1, bob 11): true
Merkle matching root accepts; root update rejects old draft; fresh path accepts: true
```

`PrivacySmokeMain` first exhausted the paired 3-GiB heap generating upstream
`Categories.Category.Monoidal.Interchange.Braided.hs`. The interrupted owned
generated file was removed; the paired `-M8G -H1G` retry compiled successfully.
The runtime output retained the fixture's two successful admissions and
secure/insecure observation distinction:

```text
secure (a,b), two accepted calls: 1/1
secure (a,c), two accepted calls: 1/1
insecure (a,b), two accepted calls: 1/1
insecure (a,c), two accepted calls: 1/1
secure observer true mass (a,b) vs (a,c): 0/1 vs 0/1
insecure observer true mass (a,b) vs (a,c): 0/1 vs 1/1
```

All owned generated Haskell, objects and executables were removed after these
runs; no throwaway wrapper was needed. The new balance and root-change runs
exercise the parameterized generic compiler/interpreter rather than duplicating
their framework. These are mathematical model regressions, not deployed-chain
or real-cryptosystem verification.

Package 3 is described below. Resource/artifact lifecycle, generalized relational
histories, end-to-end Merkle privacy replacement, evolving context and
PPT/negligible adapters remain packages 4–8.

### 3. Unify interpretation and the observation boundary

**Implemented boundary cutover.** `Interpreter` takes a contract,
`CommunicationScheme` and account identity. The scheme fixes `Artifact`,
`Opening`, `encode`, `Opens` and honest `correct`. `Rel` checks declared public
arguments, this opening relation and the actual generic program evaluation.
`Opens` is the mathematical opening/verification relation, not a fabricated
computational verifier. `CommunicationObligations.Binding` separately requires
all valid openings of one artifact to agree on account, input and result.
`ExactCommunication.binding` proves it for the explicitly non-hiding tuple;
the simulator-token instance intentionally supplies no such proof.
`PublicBoundary.simulator-not-binding` refutes that obligation for two private
Boolean inputs. Its honest-path privacy cannot be confused with binding.

Package 4 must instantiate the abstract service obligations against this
**same** statement/relation: honest proving of `(x, e, Rel x e)` yields a public
artifact accepted for `x`; acceptance of the actually submitted `(x, artifact)`
implies `Σ (Evidence x) (Rel x)` without replacing it by an unrelated selected
certificate; checking a delivered opening establishes `Opens` for the actual
account/entry/input/result pair; binding is the independent uniqueness
obligation above. Issuance tables, recipient authorization, substitution,
malformed encodings and replay policy must be specified by those services.
Joint hiding/ZK is a common-interface resource-emulation assumption with one
simulator for both worlds, not deterministic token equality or a proof that
the already assembled application is private.

`Program.execute` produces one `ExecutionReport`: ordered observable
ledger queries (including arguments, results or operation failures),
publications, chain requirements and the existing evaluation outcome.
`eval` is its outcome projection, so the safety theorems use the same semantics.
Deferred journal effects still roll back on failure; the observable trace does
not disappear after a later assertion/proving failure.

Private `ClientIf` carries caller inputs, witnesses/openings and tentative
recipient results. `Observation` fixes `PublicResult` and `discloseResult`
before choosing a world. `publicAnswer` retains the actual statement, trace,
failure/proving failure, busy/no-draft and admission verdict; it exposes results
only through that declared policy. `recipientAnswer` retains the complete
result on the private caller/recipient boundary, not on the public response.
`wrapper` accepts public actions selected by a private client policy;
its requests are not private caller inputs masquerading as adversary queries.
`Observation.observation-correspondence` identifies its calls with projection
of actual `clientStep`. No result-authentication or recipient-authorization
theorem is claimed before the package-4 opening lifecycle.

`Privacy.core` is generic `toProtocol` composed with generic `bridge` and a
small private resource adapter. The honest session keeps the actual generic
draft and shared ledger state. It uses `Observation.publicAnswer`; there is no
second `PublicStatement`, evaluation or reduced `finish` admission algorithm.
`Interpreter.finishAdmission-public`, `Coupling.step-public`,
`Observation.coupled-read`, `Relational.observations` and `run-public` establish
public trace/outcome correspondence while coupling distinct private drafts.
`secure-history-private`, `secure-joint-observable-equality`,
`insecure-gap-one` and `insecure-not-private` concern this unified assembly.

Consumer checks in `PublicBoundary` include `silent-public-response-equal`
(distinct private Booleans to `pure tt`), `echo-public-response-equal`,
`recipient-false`/`recipient-true`, explicit public-result-policy checks,
`publication-leaks`/`query-leaks`, `abort-projection`,
`abort-publication-survives`/`abort-query-survives`, accepted/rejected
projection, no draft after failure, `wrong-account-rejected`,
`proof-failure-projection`, `occupied-projection`, `absent-projection`,
`operation-failure-projection` and `empty-assertion-projection`.
They exercise the assembled public wrapper, not constructed statements
disconnected from execution.

Scope remains the fixed honest two-call Merkle policy with the reused mask and
ideal simulator tokens. Generic failure projection and concrete abort/leak
regressions are not a generalized failure/privacy theorem. Malicious artifact
substitution and binding/hiding issuance remain **4**; arbitrary/adaptive
histories **5**; end-to-end real/ideal UC application **6**; evolving and
probabilistic safety **7**; computational/PPT adapter **8**.
There is no generic ZK-complete claim. **Next package: 4.**

#### Package-3 verification

All checks and compiler runs were serial, with `LC_ALL=C.utf8`, `timeout 1800`,
`pagda --useUntracked false check` and paired RTS heaps. Final checks passed for
`Smoke`, `Balance`, `PrivacySmoke`, `PrivacyReplacementExample` and
`PublicBoundary`. The warning gate
`ModuleDoesntExport|UselessPublic|UselessPrivate|DuplicateUsing` was empty.
The DSL escape-hatch baseline remained empty.

The exhaustive unified `PrivacySmoke` tree exhausted `-M3G -H1G`; the prescribed
paired `-M16G -H1G` retry passed (final warm check about 28 seconds).
`PublicBoundaryMain`, `PrivacySmokeMain` and `SmokeMain` compiled with
`--compile --ghc-flag=-O0` and explicit outputs in an owned temporary
`--compile-dir`. Privacy compilation likewise required the paired 16 GiB retry.
The initial heap exhaustion left a truncated generated upstream `Braided.hs`;
removing **that owned generated file** and regenerating it fixed the ensuing
GHC parse error. No source, Nix or CI workaround was introduced.

The changed public-boundary executable returned:

```text
private Boolean pure tt has equal public responses: true
private recipient receives distinct Boolean results: true
actual publication reveals supplied Boolean: true
actual ledger query argument reveals supplied Boolean: true
publication/query trace survives assertion failure: true
explicit public result policy preserves Boolean results: true
generic admission accepts valid and rejects premature chain condition: true
public operation/assertion failures remain distinct: true
```

The unified Merkle executable reported probability `1/1` for two accepted calls
in all four secure/insecure worlds. Secure observer true masses were
`0/1 vs 0/1`; insecure masses were `0/1 vs 1/1`, preserving the gap-one
refutation and reused-mask behavior. The safety executable returned `true`
for all seven existing lock, balance/error/replay and mutable-root scenarios.
Every executable exited zero. Owned generated Haskell, objects, binaries and
temporary logs were removed after recording these results.


### 4. Resource services and artifact lifecycle

Separate private proving requests from public statement/artifact verification.
Submission must not re-supply a private successful-execution certificate as a
substitute for checking the submitted artifact. Specify communication opening
and recipient-checking behaviour.

Supply an executable ideal resource with appropriate private tables/handles,
explicit adversary ports, and a common interface for an abstract real resource
with a UC-emulation premise. Permit replacing ZK/communication independently of
the ledger. Remove `PrivacyResources.seal-law` as the replacement interface;
equality with `idealStep` may remain an ideal-instance implementation fact.

Acceptance: model malformed submissions and substituted statements,
account/code bindings and openings. Specify replay behaviour without imposing a
universal ban on valid proof reuse; express application-level exact-once rules
with ledger operations. Distinguish soundness from knowledge/extraction
assumptions; constructive ideal witnesses do not establish computational
extraction.

### 5. General executions and relational histories

Replace successful, immutable, two-call histories with generic executions:
success/failure, state changes, admission conflicts, variable-length finite
histories, adaptive invocation under an explicit observer policy, persistent
private state, explicit randomness/reuse, and public state observations.

Distinguish deferred transaction effects from already emitted interactions:
rollback cannot erase an externally sent message. Generalize same-randomness
equality to a relational invariant or distributional coupling; retain pointwise
equality as an easy special case.

Acceptance: detect private-bit-dependent failure unless permitted leakage;
retain the reused-mask attack; prove a case requiring mask complementation;
ensure snapshots cannot reveal state changes omitted by the observation model.

### 6. End-to-end Merkle privacy replacement

Migrate Merkle to the generic machinery and remove duplicate client/admission/
proof infrastructure. Prove successful executions of both variants, secure
ideal-system privacy from the local relational premise, the insecure violation
of that same property, and secure privacy with an abstract UC-emulating real
resource. No concrete cryptographic construction is required.

Acceptance: the application theorem consumes resource emulation rather than
only reflexivity; contract-specific code supplies the program, fixture, leakage
policy and local proof; executable scenarios exercise the generic assembly.
This is the central integration milestone, not an optional example.

### 7. Align stateful and probabilistic safety

Let authenticated time/context evolve through a specified scheduling interface.
Keep account identity separate from scheduler-controlled time; do not permit
arbitrary identity replacement through an unconstrained `setContext`.
Extend safety to probabilistic branches using upstream machinery where possible.
Preserve atomic admission/rollback and add observation-adequacy lemmas for
internal-state assertions where their transfer requires them.

Acceptance: time guards fail before and succeed after the deadline; invalid
context transitions are excluded; randomized clients admit safety and privacy
proofs about the same assembled system.

### 8. Negligible families and computational claims

Add an adapter taking certified family contexts and interaction bounds.
Do not infer polynomial execution from arbitrary Agda programs. Instantiate
transfer with a concrete negligible-stable privacy property.

Separately specify computation/message-size bounds, admissible adversaries and
simulators, and closure under composition for a PPT interpretation. Expose
external assumptions explicitly; until justified, describe the result as
negligible-observation security rather than PPT security.

Acceptance: polynomial interactions are not confused with polynomial
computation; exact probabilities are not silently transported through negligible
equivalence; arbitrary DSL programs remain expressible, with stronger claims
requiring stronger premises.

### Verification, migration and dependencies

Settle package 1 before committing to interface changes. Packages 2–4 establish
the shared semantic/resource boundaries; package 5 supplies the relational
execution interface; package 6 integrates them. Packages 7–8 complete the
stateful/probabilistic and computational obligations. Do not expand abstractions
without a demonstrated need from these proof paths.

For every migration, preserve theorem statements or supply proved
correspondences, retain consumer-visible regression cases for leakage,
rejection, binding, replay and rollback, check affected proof closures, and run
the assembled examples. Distinguish checked theorems, resource premises,
manual Compact correspondence and runtime checks in the documentation. Remove
superseded bespoke implementations once their replacements pass.

Non-goals remain a VM, a verified Compact compiler, a universal storage schema,
automatic information-flow checking, or a general multiparty corruption
framework. After this cutover, proceed to one device-authorised recovery
transition and then the [recovery lifecycle](recovery-specification.md).

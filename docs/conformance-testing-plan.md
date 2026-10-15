# Conformance testing: plan

Status: executable custody/recovery conformance with remaining work below.
The [spike report](conformance-spike.md) records historical custody results;
[recovery assurance](conformance-recovery.md) records the recovery attack,
repair/gate boundary, and current limitations. Code is in `src/Conformance/`
and `conformance/harness/`.

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
- **Oracle 2 — decide an observed transition.** The model exposes a decision procedure
  `decide : State → Call → State′ → Verdict → Bool`. The implementation runs on its own;
  each observed transition is judged after the fact. Weaker (possibilistic: it accepts any
  outcome the model allows) but needs no control over the implementation's randomness and
  applies to relational specifications.

Both transition oracles are implemented. Oracle 2's Agda certificate currently
uses a model-produced journal; successful simulator calls additionally verify
the implementation-produced public VM transcript. That extra check is not a
translation into model events (see WP1).

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

The model's "ZK" resource verifies a witness-carrying certificate whose relation is
`eval body view ≡ inj₂ (finished …)`. That relation is decidable once journals have decidable
equality, so the model-side verifier is re-execution with the witness: no proof system, no
FFI. The implementation side needs no proving either, because the compact-runtime simulator
executes circuits without ZK. Real cryptography enters only through hashes and curve
arithmetic (challenge construction, device entries, signature verification), which are
ordinary pure functions.

## 3. Where we are

| Item | State | Evidence |
|---|---|---|
| `Program` DSL executable | yes: `execute`/`eval`/`replay` are total functions | `src/Midnight/ContractDSL/Program.agda` |
| `Protocol` executable | yes: inductive `Calls`, structural `_∘ᵖ_`; exact rational `evalC` | pinned categorical-crypto `protocol-rewrite` |
| Compilation | MAlonzo works (`SmokeMain`, `Conformance.Main`); JS backend blocked | §4.2 |
| Coin injection executor | `Conformance.Coins` (`readCoins`, `stepCoins`, `runCoins`) | spike |
| Decidable `Rel` / journal | `Conformance.Account.decRel`, `_≟ᴶ_` | spike |
| Implementation seam | compact-runtime simulator, no node/proof/zswap; block time set per call | `grants-offline.ts:221-258`, `sim.ts` at `5d12798` |
| Pinned implementation | Historical `7d21a277` (recovery `5d12798` plus signer injection); repaired stamped-map working tree at the same base plus fixed source/wallet digests | `conformance/harness/recovery-pins.json`, enrolled gate lock |
| Injectable implementation randomness | `JubjubDevice.sign(…, draw)` and `signRecoverSubmit(…, draw)`; deterministic settings retained in the gate baseline | historical `7d21a277`; gate pins |
| Coverage | custody/device/recovery jubjub model; twelve scenarios, generated counter-varied plants used after one to three recoveries, and seeded interleavings; concrete repair additionally exercises both authentication arms in `recovery-sim` | `docs/conformance-recovery.md` |
| Recovery counterexample/repair | Source circuits accept fresh old-key use of planted future entries; repaired circuits reject it under current-epoch stamped membership | generated/scenario gate plus both-arm simulator regressions |
| Reader-facing recovery proofs | Corrected account model has checked finite actual-admission device-authority exclusion and guard-premised recovery/rotation execution; concrete-model refinement remains open | `src/Passport.agda`, `Conformance.RecoveryAuthority` / `RecoveryExecution` |

## 4. Technical design

### 4.1 Model side

**Layers.** `Semantics` (ledger operations with `prepare` and `resultEq : Dec`) → `Program`
(effects `ledger`/`require`/`publish`/`atChain`) → `Contract` (named entry points) →
`Interpreter` (client, bridge, admission by journal replay) → categorical `Protocol`
assembly (`wallet ∘ᵖ system ctx s`). Conformance modules add nothing to these layers; they
instantiate them.

**Ledger state.** Concrete records with lists standing in for `Map`/`Set`, compared up to
order (`_≈ᵇ_`), `Uint<n>` bounds enforced in `prepare` (`overflow` failure). Decidable
equality on every `Op`, `El`, and on `Journal` (needed by `decRel`).

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
hash reading, decidable equalities. `--safe` modules are parameterised by it; `Main` binds it.

**Oracles.**
- `stepModel : ℕ → State → Request → List Bool → Maybe ((State × StepReport) × List Bool)`:
  one wallet activation on an injected bit stream, returning the unread remainder (which
  must be empty for agreement).
- `decide : ℕ → State → (n : Name) → Input n → State → Observed → Bool` (the `ℕ` is the block time): `eval`, certificate
  check via `decRel`, `admission`, then post-state/verdict comparison; aborts must carry the
  matching code and leave the state untouched.

### 4.2 Backend and FFI

- **MAlonzo (GHC)** is the working backend. `-O0`, `-M3G -H1G` for closures without
  `UC.Model.Setup`; `-M8G` where agda-categories is pulled in.
- **JS backend is blocked**: the generated code for stdlib `Relation.Nullary.Decidable.Core.map′`
  loops (copattern `proof (map′ …)` passes `does (map′ …)` to `Reflects.of`, which matches on
  it; strict evaluation recurses). Every ℕ `_≟_`/`_≤?_` and hence `finishAdmission` is
  affected. Report upstream; do not work around in the spec.
- **Primitive calls** therefore cross a process boundary: the model prints `? op args`
  lines, the harness answers (currently from the implementation's own `pureCircuits` and
  compact-runtime). Binding pattern: an ordinary Agda definition overridden by
  `{-# COMPILE GHC … #-}` with `{-# NOINLINE #-}` and a non-trivial body (`q ++ ""`), because
  MAlonzo erases unused arguments and inlines identities. No postulates.
- Wire format: whitespace-separated tokens (no JSON library in the GHC package set).

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
  signature `(R, s, grind)`, post-state up to order, and unread bits; then run `decide` on the
  observed transition. Exit non-zero on any disagreement.
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
| `Interpreter.zk` / `verified` (witness certificate) | re-execution + `decRel`; no proof system | done (spike) |
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
feed them to `decRel`/`admission`, establishing the translation's semantic
boundary rather than calling runtime replay an independent model certificate.

**WP2 — Independent primitives.** Bind `Primitives` to an implementation that is not the
system under test (`signer-rs` challenge path over JSON, or a native jubjub/SHA-256 library),
so encoding bugs in `persistentHash`/curve code become detectable. Acceptance: a
deliberately mis-encoded challenge on either side is reported.

**WP3 — Widen the slice.** Done at `5d12798` ([`conformance-recovery.md`](conformance-recovery.md)):
`add_device`/`remove_device` with epoch, `rotate_enc_key`, recovery session, `recover_submit`/
`cancel`/`finalise` with chain time, the identity/small-order recovery-key guard, and a corrected
finalisation variant compared up to the entries it removes. Remaining, in order of cost:
small-order *device* key scenario (via `ecMul`), k256 arm (secp256k1 primitives), grants
lifecycle (map of records). Shielded custody only when an off-node Zswap state becomes available.

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

- **Shared oracle** until WP2: hashing/curve bugs common to both sides are invisible.
- **Bounded loops**: agreement is claimed only for runs within the bounds; `stuck` is
  reported, never silently accepted.
- **Abort matching by message substring**: brittle under message edits in the contract;
  mitigate by pinning the implementation commit (WP6).
- **Coverage drift**: the spec and the contract evolve independently; the conformance build
  must fail, not skip, when a modelled circuit's signature changes.
- **Toolchain**: RC compiler without launcher, SRS download blocked by proxy; `--skip-zk`
  suffices for the simulator but means proving is never exercised here.
- **Not modelled**: coin movements (`receive/sendUnshielded`), the `use_counter+1` and
  `post_epoch` casts; listed per slice in the findings.

## 7. Non-goals

A verified Compact compiler, a VM, proof-system conformance, distributional/privacy
conformance, and any claim about flows the specification does not model.

# Conformance spike: unshielded custody under jubjub device auth

Can the Agda contract model be conformance-tested against the Passport implementation
(`arc-passport/contract`)? Slice: `deposit_unshielded` and `withdraw_unshielded_with_jubjub`
of `contracts/account.compact`, including the client signer `JubjubDevice.sign`.

The code has since been extended to the recovery slice and re-pinned to Passport `5d12798`
([`conformance-recovery.md`](conformance-recovery.md)). The results below are the spike's at
`68bbde28`; the custody run still agrees at `5d12798` (seeds 1–3 × 60). Since then, the seam and
the custody chips live in `Conformance.Custody`, the model protocol carries a variant and a
block time, `IMPL_DIR` defaults to the `5d12798` worktree, and the mutation check is
`tsx mutation.ts debit`.

## Result

- Seed 1, 30 steps: 30/30 steps agree on both oracles. Seeds 2–7, 60 steps each: 360/360.
- Every scenario class occurs: deposit, `Uint<128>` overflow, valid withdraw (including
  full balance), verbatim replay, stale `use_counter`, wrong signing key, unregistered key,
  insufficient funds, never-deposited colour.
- Mutation check (model debit guard `bal >= amount` weakened to `bal > amount`): both
  oracles flag exactly the two full-balance withdrawals; the source is restored afterwards.
- No implementation/spec discrepancy in this slice. After the harness infrastructure was
  fixed (see "Development divergences"), the first full run agreed; no model bug had to be fixed.

## Reproduce

1. Implementation worktree: `git -C ../arc-passport worktree add ../arc-passport-conformance-spike -b conformance-spike`.
   Commit `85f5db4` makes the nonce draw injectable: `sign(challenge, useCounter, draw = randomJubjubScalar)`
   and `randomJubjubScalar(draw32 = () => randomBytes(32))`; the default behaviour is unchanged.
2. Compiler: unzip `compactc_v0.33.0-rc.2_aarch64-unknown-linux-musl.zip` (release tag
   `compactc-v0.33.0-rc.2`) into `~/.compact/versions/0.33.0-rc.2/aarch64-linux/`. The zip has no
   `compact` launcher, so call `compactc --skip-zk --feature-zkir-v3 contracts/X.compact contracts/managed/X`
   for `account`, `control` and `faucet`. Then run `npm install`. `npm run test:grants-offline`
   reports 121 passed, both before and after the signer change.
3. Model: `pagda --useUntracked false check src/Conformance/Main.agda -- --compile --compile-dir=_build/conformance --ghc-flag=-O0 +RTS -M3G -H1G -RTS`
   (about 50 s).
4. Harness, from `conformance/harness/`: `<worktree>/contract/node_modules/.bin/tsx main.ts --seed 1 --steps 30`.
   Mutation check: `tsx mutation.ts --seed 1 --steps 30`. Environment overrides: `IMPL_DIR` and `MODEL_BIN`.

## Design

| File | Role |
|---|---|
| `src/Conformance/Primitives.agda` | Abstract crypto record: entry derivation, withdraw challenge, `ecMulG`/`ecMul`/`ecAdd`, little-endian hash reading |
| `src/Conformance/AccountLedger.agda` | `Semantics` instance with fields round, auth_nonce, device_epoch, device_count, devices (set) and balances (map); `Uint` bounds; set/map equality up to order; decidable equality of ops |
| `src/Conformance/Coins.agda` | `readCoins`/`stepCoins`/`runCoins`: runs closed protocols on an injected bit stream |
| `src/Passport/AccountRecovery.agda` | Shared account entrypoints, authorisation/dispatch and intended `Contract`; circuit bodies live in `Conformance.Custody` and `Conformance.Recovery` |
| `src/Conformance/Account.agda` | Bounded signers; wallet `Protocol`; `stepModel`; journal decidable equality; `decRel`; `decide`, consuming the shared contract assembly |
| `src/Conformance/Main.agda` | Non-safe executable that binds the primitives and runs the line protocol |
| `conformance/harness/*.ts` | Seeded driver (`main.ts`), simulator side (`impl.ts`), model subprocess (`model.ts`), PRNG, mutation check |

All modules except `Main` are `--safe --without-K`. `Midnight.ContractDSL.*` is reused unchanged:
`Program` (`eval`, `Journal`, `Error`), `Protocol` (`Contract`, `ExactCommunication`,
`Interpreter.system/admission/makeTx`).

- **Oracle 1 (execute and compare).** For each step the model runs `wallet ∘ᵖ system ctx s`.
  The wallet signs on coins, then the client builds a proof, the bridge admits it and replays it.
  The model starts from its own previous post-state and consumes exactly the coin bits that
  the implementation's signer drew. The harness compares the verdict (including the abort
  reason), the signature `(R, s, grind)` bit for bit, the post-state, and whether any bits are left unread.
- **Oracle 2 (decide).** `decide pre call post verdict` evaluates the circuit and checks the
  certificate with `decRel`, a decision procedure for `Interpreter.Rel` that uses journal and
  tuple decidable equality. It then runs `admission` and compares the result with the
  implementation's post-state and verdict. An abort must carry the matching code and leave the
  state unchanged. The `call` carries the implementation's own signature.

## Deviations from the brief

1. **Backend: MAlonzo plus a subprocess instead of the JS backend.** `agda --js` compiles
   `SmokeMain`, but running the result overflows the stack. The cause is in stdlib
   `Relation.Nullary.Decidable.Core.map′`: the copattern clause `proof (map′ …)` passes
   `does (map′ …)` as the implicit argument of `Reflects.of`, and `of` matches on that
   argument. The strict JS backend therefore recurses forever. Every ℕ `_≟_`/`_≤?_` goes
   through `map′`, including `finishAdmission` in `Midnight.ContractDSL.Protocol`. Admission
   cannot run under JS unless stdlib or `Midnight.*` is edited or the generated JS is patched,
   so the JS FFI probe was dropped. MAlonzo compiled and ran `SmokeMain` correctly.
2. **The model calls the harness for primitives.** MAlonzo cannot call JS, so the compiled
   model prints `? op args` and the harness answers with `pureCircuits` / compact-runtime.
   This is the shared-oracle caveat the brief already accepted. Scalars are reduced mod r_J
   exactly as the generated circuit code does.
   - `rpc` is an ordinary definition overridden by `COMPILE GHC` (no postulate).
   - Gotcha: with `rpc _ = ""`, MAlonzo erased the unused argument and turned the binding into
     a constant that was evaluated once. With `rpc q = q`, the compiler inlined it as an identity.
     The working stand-in is `q ++ ""` with `NOINLINE`.
3. **Wire format: whitespace token lines instead of JSON.** The GHC package set has no JSON
   library, and parsing tokens in Agda is trivial.
4. **Loop bounds: 512 draws and 512 grinds instead of 32 and 64.** Each iteration succeeds
   with probability ≈ r_J/2²⁵⁶ ≈ 0.057, so 32 draws would leave ≈ 15 % of the mass on `dead`.
5. **Compiler: `compactc --skip-zk`, called directly.** `npm run compile` was not used:
   fetching the SRS from `srs.midnight.network` returns 403 through this machine's proxy, and
   the simulator needs no proving keys.
6. **Commit made with `git commit --no-gpg-sign`.** The checkout signs commits and there is no
   key on this machine; git config was not touched.
7. **Small additions:**
   - `conformance/harness/package.json` (`"type": "module"`), needed for top-level await.
   - The contract address and keys come from the seeded PRNG instead of `sampleContractAddress`,
     so a seed reproduces the whole run.
   - A second wrong-key flavour: an unregistered pk as well as a stranger signing for the owner's pk.
   - Overflow deposits.

## Development divergences

All of them were harness or infrastructure faults; none was a model or implementation discrepancy:

- **Erased or inlined `rpc` (deviation 2).** The first withdrawal ended with `stuck` or with
  the model process exiting, because every primitive returned the same value.
- **Compile-time name clashes.** These were with `Program.Context.account` and with the record
  field `amount`.

## Caveats

- **Bounded loops.** `Calls` is inductive, so the model signer turns into `dead` after 512
  rejected draws or 512 grind attempts (mass < 10⁻¹²). Agreement is claimed only for runs in
  which the implementation stayed within those bounds. Exceeding them would show up as
  `stuck`, and the `rest 0` check confirms that the model consumed exactly the
  implementation's draws.
- **Shared oracle.** Hashing and EC arithmetic are the implementation's own, so a bug in
  `persistentHash`, in the jubjub arithmetic, or in their encodings cannot be detected. The
  contract logic around them (assert order, entry rotation, nonce binding, map/set updates,
  `Uint` bounds) and the signer algorithm (rejection sampling, grinding, `s = r + c·sk`) are
  modelled independently.
- **Not modelled:**
  - coin movements (`receiveUnshielded`/`sendUnshielded` effects);
  - the `use_counter + 1` `Uint<64>` cast;
  - the `Bytes<32> as Field` failure above the field modulus (unreachable once the challenge
    is ground below r_J).
- **Abort reasons** are compared by message substring.
- **Historical oracle 2 checked the model's own journal.** `decide` builds its
  statement from that journal. The recovery harness additionally verifies the
  implementation-produced public VM transcript; see
  [the recovery oracle boundary](conformance-recovery.md#caveats). It still does
  not translate the VM program into an Agda journal.

## What generalises

- Adding a circuit means writing a `Program`, any new `Op`s, a decoder and harness generators.
  The DSL, the protocol stack, `Coins` and the oracles stay as they are.
- `Coins.stepCoins` and `runCoins` work for any closed `Protocol` with coins, so any randomised
  client can be replayed against a recorded bit stream once its randomness is injectable.
- `decide` is a generic recipe: `eval` + `decRel` + `admission` + state equality up to order.
- The pattern of compiling the model with MAlonzo and serving its primitives over RPC carries
  over to any implementation language.

## Cost

| | Size / time |
|---|---|
| Model | 521 safe LOC + 230 LOC `Main` |
| Harness | 565 LOC TS |
| Per-module warm check | 3–9 s |
| MAlonzo build | ≈ 50 s (`-O0`) |
| Mutation check | ≈ 50 s, mostly the mutant build |
| 30-step run | 1.0 s, 601 primitive round trips, 82 k coin bits |
| 60-step run | ≈ 2.3 s |

Most of the effort went into infrastructure: the toolchain (missing launcher, SRS 403), the
JS backend investigation, and the MAlonzo FFI gotcha. The model itself checked with few
iterations.

## Next steps

1. **Complete journal correspondence.** The recovery harness can obtain and
   verify the simulator's `callProofDataTrace.publicTranscript`, including recorded
   reads. Translating its low-level stack/map operations into model `Event`s and
   proving or testing that translation against `decRel` remain separate work.
2. **Remove the shared oracle.** Bind the primitives to an independent implementation, for
   example `signer-rs` or a native Poseidon/jubjub library.
3. **Widen the slice.**
   - Add the device lifecycle (add/remove, epoch) and the small-order key (reachable through `ecMul`).
   - The k256 arm needs secp256k1 primitives.
   - Shielded custody needs Zswap and is out of reach off-node.
4. **Fix the JS-backend `map′` divergence upstream.** Report it to Agda or the stdlib; until it
   is fixed, MAlonzo is the viable backend.
5. **CI.** Running this in CI needs compactc, the implementation checkout and one MAlonzo
   build; the run itself is seconds.

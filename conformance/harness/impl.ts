// Implementation-side simulator and effective ledger observation.
// Default source mode executes the pinned historical Passport 5d12798 Set schema.
// RECOVERY_IMPLEMENTATION=repaired selects the stamped Map repair: only entries
// stamped with the contract's current epoch enter the observed authority set.
// Set/map decoding requires the selected schema; neither observation is a proved
// compiler or ledger refinement. Successful calls additionally verify their actual
// runtime VM transcript (not an independently decoded Agda Event journal).

import { createRequire } from 'node:module';
import { fileURLToPath, pathToFileURL } from 'node:url';

import { Prng } from './prng.ts';

export const IMPL_DIR =
  process.env.IMPL_DIR ?? fileURLToPath(new URL('../../../arc-passport-recovery-conformance/contract', import.meta.url));

// The slice of the implementation's API the harness drives.
export interface Point { x: bigint; y: bigint }
export type ChallengeBuilder = (sigR: Point, grindNonce: bigint) => Uint8Array;
export interface CallContext { contractAddress: Uint8Array; authNonce: bigint }
export interface JubjubAuthorisation { pk: Point; use_counter: bigint; sig_r: Point; sig_s: bigint; grind_nonce: bigint }
export interface Device {
  readonly sk: bigint;
  readonly pk: Point;
  bootCommitment(salt: Uint8Array): Uint8Array;
  entryAt(contractAddress: Uint8Array, epoch: bigint, counter: bigint): Uint8Array;
  sign(challenge: ChallengeBuilder, useCounter: bigint, draw?: () => bigint): JubjubAuthorisation;
}
export interface RecoverSubmitAuthorisation {
  successor_pk: Point; successor_recovery_pk: Point; expected_epoch: bigint; expected_nonce: bigint; now_upper: bigint;
  sig_r_recovery: Point; sig_s_recovery: bigint; sig_r_successor: Point; sig_s_successor: bigint; grind_nonce: bigint;
}
export type RecoverSubmitChallengeBuilder = (sigRRecovery: Point, sigRSuccessor: Point, grindNonce: bigint) => Uint8Array;
interface AlignedValue { value: Uint8Array[]; alignment: unknown[] }
type TranscriptOp = string | { popeq: { cached: boolean; result: AlignedValue } } | Record<string, unknown>;
interface QueryContext {
  state: unknown;
  effects: unknown;
  runTranscript(transcript: { gas: unknown; effects: unknown; program: TranscriptOp[] }, costModel: unknown): QueryContext;
}
interface CircuitResult {
  context: {
    callContext: { currentQueryContext: QueryContext; currentGasCost: unknown };
    costModel: unknown;
    callProofDataTrace: {
      circuitId: string;
      initialQueryContext: QueryContext;
      finalQueryContext: QueryContext;
      publicTranscript: TranscriptOp[];
    }[];
  };
}
interface ContractInstance {
  initialState(ctx: unknown, boot: Uint8Array, encKey: Uint8Array, recoveryPk: Point, wrap: Uint8Array, vetoWindow: bigint):
    Promise<{ currentContractState: unknown }>;
  impureCircuits: Record<string, (ctx: unknown, ...args: unknown[]) => Promise<CircuitResult>>;
}
interface LedgerMap<K, V> extends Iterable<[K, V]> { size(): bigint }
interface RawLedger {
  round: bigint;
  auth_nonce: bigint;
  device_epoch: bigint;
  device_count: bigint;
  devices: Iterable<Uint8Array | [Uint8Array, bigint]>;
  unshielded_balances: Iterable<[Uint8Array, bigint]>;
  enc_key: Uint8Array;
  recovery_pk: Point;
  recovery_phi: LedgerMap<bigint, bigint>;
  recovery_phi_len: bigint;
  recovery_session: Uint8Array;
  recovery_wrap: Uint8Array;
  recovery_version: bigint;
  pending_recovery: boolean;
  pending_entry: Uint8Array;
  pending_recovery_pk: Point;
  pending_not_before: bigint;
  veto_window: bigint;
}
type Phi = readonly [bigint, bigint, bigint, bigint];
export interface Impl {
  rt: {
    createConstructorContext(privateState: object, coinPk: { bytes: Uint8Array }): unknown;
    createCircuitContext(name: string, address: string, coinPk: { bytes: Uint8Array }, state: unknown, privateState: object,
      a: undefined, b: undefined, c: undefined, time: number): unknown;
    convertNumericToJubjubScalar(k: bigint): bigint;
    ecMulGenerator(k: bigint): Point;
    ecMul(p: Point, k: bigint): Point;
    ecAdd(p: Point, q: Point): Point;
    JUBJUB_SCALAR_MODULUS: bigint;
  };
  pureCircuits: {
    derive_device_entry_with_jubjub(self: { bytes: Uint8Array }, pk: Point, epoch: bigint, counter: bigint): Uint8Array;
    challenge_withdraw_unshielded_with_jubjub(self: { bytes: Uint8Array }, sigR: Point, pk: Point, color: Uint8Array,
      amount: bigint, recipient: { bytes: Uint8Array }, nonce: bigint, grind: bigint): Uint8Array;
    challenge_add_device_with_jubjub(self: { bytes: Uint8Array }, sigR: Point, pk: Point, entry: Uint8Array, nonce: bigint, grind: bigint): Uint8Array;
    challenge_remove_device_with_jubjub(self: { bytes: Uint8Array }, sigR: Point, pk: Point, entry: Uint8Array, nonce: bigint, grind: bigint): Uint8Array;
    challenge_rotate_enc_key_with_jubjub(self: { bytes: Uint8Array }, sigR: Point, pk: Point, key: Uint8Array, nonce: bigint, grind: bigint): Uint8Array;
    challenge_publish_recovery_session_with_jubjub(self: { bytes: Uint8Array }, sigR: Point, pk: Point, newRecoveryPk: Point,
      session: Uint8Array, phi1: bigint, phi2: bigint, phi3: bigint, phi4: bigint, phiLen: bigint, wrap: Uint8Array,
      nonce: bigint, grind: bigint): Uint8Array;
    challenge_recover_cancel_with_jubjub(self: { bytes: Uint8Array }, sigR: Point, pk: Point, nonce: bigint, grind: bigint): Uint8Array;
    challenge_recover_submit(self: { bytes: Uint8Array }, recoveryPk: Point, sigRRecovery: Point, successorPk: Point,
      sigRSuccessor: Point, successorRecoveryPk: Point, postEpoch: bigint, nonce: bigint, nowUpper: bigint, grind: bigint): Uint8Array;
  };
  ledger(state: unknown): RawLedger;
  Contract: new (witnesses: object) => ContractInstance;
  signer: {
    JUBJUB_R: bigint;
    JubjubDevice: new (sk: bigint) => Device;
    randomJubjubScalar(draw32?: () => Uint8Array): bigint;
    jubjubChallenges: {
      withdrawUnshielded(ctx: CallContext, pk: Point, color: Uint8Array, amount: bigint, recipient: Uint8Array): ChallengeBuilder;
      addDevice(ctx: CallContext, pk: Point, entry: Uint8Array): ChallengeBuilder;
      removeDevice(ctx: CallContext, pk: Point, entry: Uint8Array): ChallengeBuilder;
      rotateEncKey(ctx: CallContext, pk: Point, key: Uint8Array): ChallengeBuilder;
      publishRecoverySession(ctx: CallContext, pk: Point, newRecoveryPk: Point, session: Uint8Array, phi: Phi, phiLen: bigint,
        wrap: Uint8Array): ChallengeBuilder;
      recoverCancel(ctx: CallContext, pk: Point): ChallengeBuilder;
    };
  };
  gate: {
    signRecoverSubmit(recovery: Device, successor: Device, build: RecoverSubmitChallengeBuilder,
      fields: { successorRecoveryPk: Point; expectedEpoch: bigint; expectedNonce: bigint; nowUpper: bigint },
      draw?: () => bigint): RecoverSubmitAuthorisation;
    recoverSubmitChallenge(ctx: CallContext, recoveryPk: Point, successorPk: Point, successorRecoveryPk: Point,
      postEpoch: bigint, nowUpper: bigint): RecoverSubmitChallengeBuilder;
    recoverSubmitArgs(a: RecoverSubmitAuthorisation): unknown[];
  };
}

export async function loadImpl(): Promise<Impl> {
  // Dynamic imports: the implementation lives in a worktree chosen at run time (IMPL_DIR).
  const runtimePath = createRequire(`${IMPL_DIR}/package.json`).resolve('@midnight-ntwrk/compact-runtime');
  const rt = await import(pathToFileURL(runtimePath).href);
  const contract = await import(pathToFileURL(`${IMPL_DIR}/src/wallet/contract.ts`).href);
  const signer = await import(pathToFileURL(`${IMPL_DIR}/src/wallet/signer.ts`).href);
  const gate = await import(pathToFileURL(`${IMPL_DIR}/src/wallet/recovery-gate.ts`).href);
  // Untyped module namespaces from outside this package; Impl lists the members used.
  return { rt, pureCircuits: contract.pureCircuits, ledger: contract.ledger, Contract: contract.Contract, signer, gate } as unknown as Impl;
}

export const hex = (bytes: Uint8Array): string => Buffer.from(bytes).toString('hex');
export const unhex = (h: string): Uint8Array => new Uint8Array(Buffer.from(h, 'hex'));
export const showPoint = (p: Point): string => `${p.x} ${p.y}`;

/** The model's view of the ledger (Conformance.AccountLedger.State). */
export interface LedgerView {
  round: bigint;
  authNonce: bigint;
  deviceEpoch: bigint;
  deviceCount: bigint;
  devices: string[];
  balances: [string, bigint][];
  encKey: string;
  recoveryPk: Point;
  /** Empty, or the four slots 1..4. */
  phi: bigint[];
  phiLen: bigint;
  session: string;
  wrap: string;
  pending: boolean;
  pendingEntry: string;
  pendingRecoveryPk: Point;
  pendingNotBefore: bigint;
  vetoWindow: bigint;
}

export function encodeState(v: LedgerView): string {
  return [
    v.round, v.authNonce, v.deviceEpoch, v.deviceCount,
    v.devices.length, ...v.devices,
    v.balances.length, ...v.balances.flat(),
    v.encKey, showPoint(v.recoveryPk), v.phi.length, ...v.phi, v.phiLen, v.session, v.wrap,
    v.pending ? 1 : 0, v.pendingEntry, showPoint(v.pendingRecoveryPk), v.pendingNotBefore, v.vetoWindow,
  ].join(' ');
}

/** Parse an encoded state from `tokens` starting at `at`; returns the view and the next index. */
export function decodeState(tokens: string[], at: number): [LedgerView, number] {
  let i = at;
  const n = () => BigInt(tokens[i++]);
  const s = () => tokens[i++];
  const pt = (): Point => ({ x: n(), y: n() });
  const round = n(), authNonce = n(), deviceEpoch = n(), deviceCount = n();
  const devices = Array.from({ length: Number(n()) }, s);
  const balances = Array.from({ length: Number(n()) }, (): [string, bigint] => {
    const color = s();
    return [color, n()];
  });
  const encKey = s();
  const recoveryPk = pt();
  const phi = Array.from({ length: Number(n()) }, n);
  const phiLen = n(), session = s(), wrap = s(), pending = n() === 1n, pendingEntry = s();
  const pendingRecoveryPk = pt();
  const pendingNotBefore = n(), vetoWindow = n();
  return [{
    round, authNonce, deviceEpoch, deviceCount, devices, balances, encKey, recoveryPk, phi, phiLen, session, wrap,
    pending, pendingEntry, pendingRecoveryPk, pendingNotBefore, vetoWindow,
  }, i];
}

/** Order-insensitive rendering: sets and maps compare as sets and maps. */
export function canonical(v: LedgerView): string {
  return encodeState({
    ...v,
    devices: [...v.devices].sort(),
    balances: [...v.balances].sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0)),
  });
}

/** The fields of two views that differ, for divergence reports. */
export function stateDiff(model: LedgerView, impl: LedgerView): string {
  const m = decodeFields(canonical(model)), r = decodeFields(canonical(impl));
  const out: string[] = [];
  for (const k of Object.keys(m) as (keyof LedgerView)[]) if (m[k] !== r[k]) out.push(`${k}: model=${m[k]} impl=${r[k]}`);
  return out.join('; ');
}

function decodeFields(encoded: string): Record<keyof LedgerView, string> {
  const [v] = decodeState(encoded.split(' '), 0);
  return Object.fromEntries(Object.entries(v).map(([k, x]) => [k, typeof x === 'object' ? JSON.stringify(x, (_, y) => (typeof y === 'bigint' ? `${y}` : y)) : `${x}`])) as Record<keyof LedgerView, string>;
}

// Abort messages of the exercised asserts and casts, mapped to Conformance.Custody.errorCode;
// the two chain-time asserts are the model's admission refusals.
const ABORT_CODES: [string, string][] = [
  ['device key has small order', 'smallOrderKey'],
  ['recovery key has small order', 'smallOrderRecoveryKey'],
  ['recovery key is the identity', 'identityKey'],
  ['unknown device entry', 'unknownDevice'],
  // The repaired eligible-membership projection excludes stale-stamped entries.
  ['device authority epoch stale', 'unknownDevice'],
  ['invalid recovery signature', 'invalidRecoverySignature'],
  ['invalid successor co-signature', 'invalidSuccessorSignature'],
  ['invalid signature', 'invalidSignature'],
  ['no balance for color', 'noBalance'],
  ['insufficient balance', 'insufficientBalance'],
  ['device entry already present', 'entryPresent'],
  ['cannot remove last device', 'lastDevice'],
  ['cannot remove the authorising device', 'authorisingDevice'],
  ['recovery pending; cancel first', 'recoveryPending'],
  ['phi must not be empty', 'phiEmpty'],
  ['phi length out of range', 'phiLength'],
  ['unused phi slot 2 not zero', 'phiSlot2'],
  ['unused phi slot 3 not zero', 'phiSlot3'],
  ['unused phi slot 4 not zero', 'phiSlot4'],
  ['session nonce is zero', 'sessionZero'],
  ['session nonce reused', 'sessionReused'],
  ['recovery commitment reused', 'commitmentReused'],
  ['recovery already pending', 'alreadyPending'],
  ['stale epoch', 'staleEpoch'],
  ['stale authorisation nonce', 'staleNonce'],
  ['no recovery pending', 'noPending'],
  ['now bound is in the past', 'refused'],
  ['veto window still open', 'refused'],
  ['cast from Field or Uint value to smaller Uint value failed', 'overflow'],
  ['device epoch exhausted', 'overflow'],
  // `challenge as Field` over a challenge nobody ground (Conformance.Custody.asField).
  ['exceeds maximum value 52435875175126190479447740508185965837690552500527637822603658699938581184512 of Field type', 'challengeRange'],
];

export interface TranscriptEvidence { operations: number; reads: number; verified: boolean; tamperRejected: boolean }
export type Verdict = { ok: true; transcript?: TranscriptEvidence } | { ok: false; code: string; message: string };

/** `ok`, `refused` (a chain-time assert) or `fail CODE`: the model's settlement format. */
export const settled = (v: Verdict): string => (v.ok ? 'ok' : v.code === 'refused' ? 'refused' : `fail ${v.code}`);
/** The verdict as Oracle 2 observes it. */
export const observed = (v: Verdict): string => (v.ok ? 'ok' : `fail ${v.code}`);

/** Verify the implementation-produced VM program and its recorded reads, not a model journal. */
export function verifyTranscript(result: CircuitResult, circuit: string): TranscriptEvidence {
  const { context } = result;
  const trace = context.callProofDataTrace;
  if (trace.length !== 1 || trace[0].circuitId !== circuit) {
    throw new Error(`expected one root transcript for ${circuit}, received ${trace.length}`);
  }
  const proof = trace[0];
  const program = proof.publicTranscript;
  const reads = program.filter((op) => typeof op === 'object' && 'popeq' in op);
  if (program.length === 0 || reads.length === 0) throw new Error(`empty implementation transcript for ${circuit}`);
  const transcript = { gas: context.callContext.currentGasCost, effects: proof.finalQueryContext.effects, program };
  const replayed = proof.initialQueryContext.runTranscript(transcript, context.costModel);
  // Compare the complete VM state, including fields outside the model projection.
  const stateText = (state: unknown): string => {
    if (state === null || typeof state !== 'object' || !('toString' in state) || typeof state.toString !== 'function') {
      throw new Error('transcript state has no runtime rendering');
    }
    return state.toString();
  };
  if (stateText(replayed.state) !== stateText(proof.finalQueryContext.state)) {
    throw new Error(`implementation transcript replay changed the final state for ${circuit}`);
  }
  const at = program.findIndex((op) => typeof op === 'object' && 'popeq' in op);
  const op = program[at];
  if (typeof op !== 'object' || !('popeq' in op)) throw new Error('missing transcript read');
  const read = op.popeq;
  if (read === null || typeof read !== 'object' || !('cached' in read) || typeof read.cached !== 'boolean'
    || !('result' in read) || read.result === null || typeof read.result !== 'object'
    || !('value' in read.result) || !Array.isArray(read.result.value)
    || !read.result.value.every((bytes) => bytes instanceof Uint8Array)
    || !('alignment' in read.result) || !Array.isArray(read.result.alignment)) {
    throw new Error('invalid aligned transcript read');
  }
  const altered = structuredClone({
    popeq: { cached: read.cached, result: { value: read.result.value, alignment: read.result.alignment } },
  });
  if (altered.popeq.result.value.length === 0) throw new Error(`first transcript read has no value for ${circuit}`);
  const bytes = altered.popeq.result.value[0];
  if (bytes.length === 0) altered.popeq.result.value[0] = new Uint8Array([1]);
  else bytes[0] ^= 1;
  const mutated = [...program];
  mutated[at] = altered;
  let tamperRejected = false;
  try {
    proof.initialQueryContext.runTranscript({ ...transcript, program: mutated }, context.costModel);
  } catch {
    tamperRejected = true;
  }
  if (!tamperRejected) throw new Error(`implementation transcript verifier accepted a changed read for ${circuit}`);
  return { operations: program.length, reads: reads.length, verified: true, tamperRejected };
}

export interface Account {
  addressHex: string;
  address: Uint8Array;
  owner: Device;
  /** Simulator block time in seconds; every call runs at the current value. */
  now: number;
  view(): LedgerView;
  call(name: string, ...args: unknown[]): Promise<Verdict>;
}

export interface AccountOptions {
  recoveryPk: Point;
  vetoWindow: bigint;
  time: number;
}

const ZERO32 = new Uint8Array(32);

export const REPAIRED = process.env.RECOVERY_IMPLEMENTATION === 'repaired';

/** Observe eligible membership, not physical deletion of retained map cells. */
function eligibleDevices(l: RawLedger): string[] {
  const active: string[] = [];
  for (const item of l.devices) {
    if (item instanceof Uint8Array) {
      if (REPAIRED) throw new Error('repaired implementation exposes unstamped device entries');
      active.push(hex(item));
    } else {
      if (!REPAIRED) throw new Error('source implementation unexpectedly exposes stamped device entries');
      const [entry, epoch] = item;
      if (!(entry instanceof Uint8Array) || typeof epoch !== 'bigint') throw new Error('invalid stamped device entry');
      if (epoch === l.device_epoch) active.push(hex(entry));
    }
  }
  return active;
}

/** Deploy an account into the simulator and activate a jubjub owner device. */
export async function openAccount(impl: Impl, prng: Prng, opts: AccountOptions): Promise<Account> {
  const { rt, ledger, Contract, signer } = impl;
  const contract = new Contract({
    held_coin: (ctx: { privateState: unknown }) => [ctx.privateState, { nonce: ZERO32, color: ZERO32, value: 0n, mt_index: 0n }],
  });
  const coinPk = { bytes: prng.bytes(32) };
  const address = prng.bytes(32);
  const addressHex = hex(address);
  const owner = new signer.JubjubDevice(signer.randomJubjubScalar(() => prng.bytes(32)));
  const salt = prng.bytes(32);
  const init = await contract.initialState(rt.createConstructorContext({}, coinPk), owner.bootCommitment(salt), prng.bytes(32),
    opts.recoveryPk, prng.bytes(64), opts.vetoWindow);
  let state: unknown = init.currentContractState;

  const view = (): LedgerView => {
    const l = ledger(state);
    const phiMap = new Map([...l.recovery_phi]);
    const phi = phiMap.size === 0 ? [] : [1n, 2n, 3n, 4n].map((k) => {
      const v = phiMap.get(k);
      if (v === undefined || phiMap.size !== 4) throw new Error(`recovery_phi outside the modelled shapes: ${[...phiMap.keys()]}`);
      return v;
    });
    if (l.recovery_version !== 1n) throw new Error(`recovery_version ${l.recovery_version} (modelled as the constant 1)`);
    return {
      round: l.round,
      authNonce: l.auth_nonce,
      deviceEpoch: l.device_epoch,
      deviceCount: l.device_count,
      devices: eligibleDevices(l),
      balances: [...l.unshielded_balances].map(([c, a]): [string, bigint] => [hex(c), a]),
      encKey: hex(l.enc_key),
      recoveryPk: l.recovery_pk,
      phi,
      phiLen: l.recovery_phi_len,
      session: hex(l.recovery_session),
      wrap: hex(l.recovery_wrap),
      pending: l.pending_recovery,
      pendingEntry: hex(l.pending_entry),
      pendingRecoveryPk: l.pending_recovery_pk,
      pendingNotBefore: l.pending_not_before,
      vetoWindow: l.veto_window,
    };
  };

  const acct: Account = {
    addressHex, address, owner, now: opts.time, view,
    async call(name: string, ...args: unknown[]): Promise<Verdict> {
      const ctx = rt.createCircuitContext(name, addressHex, coinPk, state, {}, undefined, undefined, undefined, acct.now);
      let res: CircuitResult;
      try {
        res = await contract.impureCircuits[name](ctx, ...args);
      } catch (e: unknown) {
        const message = e instanceof Error ? e.message : String(e);
        const hit = ABORT_CODES.find(([needle]) => message.includes(needle));
        return { ok: false, code: hit ? hit[1] : 'other', message };
      }
      const transcript = verifyTranscript(res, name);
      state = res.context.callContext.currentQueryContext.state;
      return { ok: true, transcript };
    },
  };

  const activated = await acct.call('activate_initial_device_with_jubjub', owner.pk, salt);
  if (!activated.ok) throw new Error(`activation failed: ${activated.message}`);
  return acct;
}

// Full account StateValue fixtures, not reconstruction from the lossy LedgerView.
// Runtime-internal encoded values are version-pinned by the gate. No transaction
// decoder/refinement claim: this captures the simulator's public VM transcript.
// Context scope is explicit: account address, block time and coin public key are
// supplied. Parent hash/caller/time error/previous-block time, empty commitment
// indices and external asset balances use the pinned runtime's defaults; private
// state is {}, held_coin is the fixed zero witness, and cost model is initial.
// These fixtures do not claim arbitrary ContractState/Zswap/witness reconstruction.
// Replay checks VM reads, including recorded time predicates. The deterministic
// altered-unshieldedInputs control is accepted by this runtime: passing Effects
// through runTranscript does NOT authenticate effects or verify a transaction.
import {
  abortVerdict, hex, unhex, verifyTranscript,
  type CircuitResult, type Impl, type QueryContext, type RuntimeState, type Verdict,
} from './impl.ts';

export interface ConcreteSnapshot {
  schema: 'compact-state-v1';
  environment: 'default-simulator-v1';
  address: string;
  /** Decimal logical model identity, distinct from the runtime address. */
  account: string;
  coinPublicKey: string;
  time: number;
  /** Lossless StateValue.encode(), including fields omitted from LedgerView. */
  state: string;
}
export interface FrozenTranscript {
  schema: 'compact-transcript-v1';
  circuit: string;
  /** Only the runtime's initial/default cost model is supported by this adapter. */
  costModel: 'initial';
  build: ConcreteSnapshot;
  builtPost: ConcreteSnapshot;
  transcript: string;
}
export interface ConcreteExecution { verdict: Verdict; post: ConcreteSnapshot; frozen?: FrozenTranscript }
type Packed = null | boolean | number | string | Packed[];

/** A lossless tagged transport for the runtime's BigInt/Map/bytes/undefined data. */
export function encodeRuntimeValue(value: unknown): string {
  function pack(v: unknown): Packed {
    if (v === null || typeof v === 'boolean' || typeof v === 'string') return v;
    if (typeof v === 'number') { if (!Number.isFinite(v)) throw new Error('nonfinite runtime value'); return v; }
    if (v === undefined) return ['undefined'];
    if (typeof v === 'bigint') return ['bigint', String(v)];
    if (v instanceof Uint8Array) return ['bytes', hex(v)];
    if (v instanceof Map) return ['map', [...v].map(([k, x]) => [pack(k), pack(x)])];
    if (Array.isArray(v)) return ['array', v.map(pack)];
    if (typeof v === 'object' && Object.getPrototypeOf(v) === Object.prototype)
      return ['object', Object.entries(v).map(([k, x]) => [k, pack(x)])];
    throw new Error('unsupported non-data runtime value');
  }
  return JSON.stringify(pack(value));
}
export function decodeRuntimeValue(text: string): unknown {
  function unpack(v: unknown): unknown {
    if (v === null || typeof v === 'boolean' || typeof v === 'string' || typeof v === 'number') return v;
    if (!Array.isArray(v)) throw new Error('invalid runtime value');
    const [tag, body] = v;
    if (tag === 'undefined' && v.length === 1) return undefined;
    if (v.length !== 2) throw new Error('invalid runtime tagged value');
    if (tag === 'bigint' && typeof body === 'string' && /^-?[0-9]+$/.test(body)) return BigInt(body);
    if (tag === 'bytes' && typeof body === 'string' && /^(?:[0-9a-f]{2})*$/.test(body)) return unhex(body);
    if (!Array.isArray(body)) throw new Error('invalid runtime collection');
    if (tag === 'array') return body.map(unpack);
    if (tag === 'map') return new Map(body.map((entry: unknown): [unknown, unknown] => {
      if (!Array.isArray(entry) || entry.length !== 2) throw new Error('invalid runtime map entry');
      return [unpack(entry[0]), unpack(entry[1])];
    }));
    if (tag === 'object') {
      const out: Record<string, unknown> = {};
      for (const entry of body) {
        if (!Array.isArray(entry) || entry.length !== 2 || typeof entry[0] !== 'string' || Object.hasOwn(out, entry[0])) throw new Error('invalid runtime object entry');
        Object.defineProperty(out, entry[0], { value: unpack(entry[1]), enumerable: true, writable: true });
      }
      return out;
    }
    throw new Error('invalid runtime value tag');
  }
  return unpack(JSON.parse(text));
}
function stateValue(state: unknown): RuntimeState {
  if (state !== null && typeof state === 'object') {
    if ('encode' in state && typeof state.encode === 'function' && 'toString' in state && typeof state.toString === 'function') return state as RuntimeState;
    if ('state' in state) return stateValue(state.state);
  }
  throw new Error('expected StateValue or ChargedState');
}
export function captureState(state: unknown, address: string, coinPublicKey: string, time: number, account = '0'): ConcreteSnapshot {
  return { schema: 'compact-state-v1', environment: 'default-simulator-v1', address, account, coinPublicKey, time, state: encodeRuntimeValue(stateValue(state).encode()) };
}
export function restoreState(impl: Impl, snapshot: ConcreteSnapshot): RuntimeState {
  if (snapshot.schema !== 'compact-state-v1' || snapshot.environment !== 'default-simulator-v1' || !/^[0-9a-f]{64}$/.test(snapshot.address)
    || !/^[0-9]+$/.test(snapshot.account)
    || !/^[0-9a-f]{64}$/.test(snapshot.coinPublicKey) || !Number.isSafeInteger(snapshot.time) || snapshot.time < 0)
    throw new Error('invalid concrete state fixture');
  return impl.rt.StateValue.decode(decodeRuntimeValue(snapshot.state));
}
export async function buildConcrete(impl: Impl, initial: ConcreteSnapshot, circuit: string, args: unknown[]): Promise<ConcreteExecution> {
  const state = restoreState(impl, initial);
  const contract = new impl.Contract({
    held_coin: (ctx: { privateState: unknown }) => [ctx.privateState, { nonce: new Uint8Array(32), color: new Uint8Array(32), value: 0n, mt_index: 0n }],
  });
  const ctx = impl.rt.createCircuitContext(circuit, initial.address, { bytes: unhex(initial.coinPublicKey) }, state, {}, undefined, undefined, undefined, initial.time);
  if (!Object.hasOwn(contract.impureCircuits, circuit)) throw new Error(`unknown implementation circuit ${circuit}`);
  let result: CircuitResult;
  try { result = await contract.impureCircuits[circuit](ctx, ...args); }
  catch (error: unknown) { return { verdict: abortVerdict(error), post: { ...initial } }; }
  const evidence = verifyTranscript(result, circuit);
  const trace = result.context.callProofDataTrace[0];
  const post = captureState(trace.finalQueryContext.state, initial.address, initial.coinPublicKey, initial.time, initial.account);
  const frozen: FrozenTranscript = {
    schema: 'compact-transcript-v1', circuit, costModel: 'initial', build: { ...initial }, builtPost: post,
    transcript: encodeRuntimeValue({ gas: result.context.callContext.currentGasCost, effects: trace.finalQueryContext.effects, program: trace.publicTranscript }),
  };
  return { verdict: { ok: true, transcript: evidence }, post, frozen };
}

/** Admission only: never invokes the circuit, re-signs, prepares, or resynchronizes. */
export function replayConcrete(impl: Impl, initial: ConcreteSnapshot, frozen: FrozenTranscript): ConcreteExecution {
  if (frozen.schema !== 'compact-transcript-v1' || frozen.costModel !== 'initial') throw new Error('unsupported concrete transcript fixture');
  const state = restoreState(impl, initial);
  const ctx = impl.rt.createCircuitContext(frozen.circuit, initial.address, { bytes: unhex(initial.coinPublicKey) }, state, {}, undefined, undefined, undefined, initial.time);
  const transcript = decodeRuntimeValue(frozen.transcript);
  if (transcript === null || typeof transcript !== 'object' || !('gas' in transcript) || !('effects' in transcript)
    || !('program' in transcript) || !Array.isArray(transcript.program)) throw new Error('invalid concrete transcript');
  let admitted: QueryContext;
  try { admitted = ctx.callContext.currentQueryContext.runTranscript(transcript as ConcreteProgram, ctx.costModel); }
  catch (error: unknown) {
    return { verdict: { ok: false, code: 'refused', message: error instanceof Error ? error.message : String(error) }, post: { ...initial } };
  }
  return { verdict: { ok: true }, post: captureState(admitted.state, initial.address, initial.coinPublicKey, initial.time, initial.account) };
}
interface ConcreteProgram { gas: unknown; effects: unknown; program: (string | Record<string, unknown>)[] }

/** Synthetic controls for the pinned account schema, never labelled reachable histories. */
export function mutateConcreteCell(impl: Impl, snapshot: ConcreteSnapshot, field: 'round' | 'encKey', value: bigint | string): ConcreteSnapshot {
  const encoded = restoreState(impl, snapshot).encode();
  if (encoded === null || typeof encoded !== 'object' || !('tag' in encoded) || encoded.tag !== 'array'
    || !('content' in encoded) || !Array.isArray(encoded.content)) throw new Error('account root is not an array');
  const group: unknown = encoded.content[0];
  if (group === null || typeof group !== 'object' || !('tag' in group) || group.tag !== 'array'
    || !('content' in group) || !Array.isArray(group.content)) throw new Error('account base group is not an array');
  const cell: unknown = group.content[field === 'round' ? 0 : 1];
  if (cell === null || typeof cell !== 'object' || !('tag' in cell) || cell.tag !== 'cell'
    || !('content' in cell) || cell.content === null || typeof cell.content !== 'object' || !('value' in cell.content)
    || !Array.isArray(cell.content.value) || cell.content.value.length !== 1) throw new Error('unexpected account cell encoding');
  if (field === 'encKey') {
    if (typeof value !== 'string' || !/^[0-9a-f]{64}$/.test(value)) throw new Error('invalid synthetic encKey');
    cell.content.value[0] = unhex(value);
  } else {
    if (typeof value !== 'bigint' || value < 0n || value >= 1n << 64n) throw new Error('invalid synthetic round');
    // Compact's unsigned integer Value encoding is minimal little endian.
    const bytes: number[] = [];
    for (let n = value; n > 0n; n >>= 8n) bytes.push(Number(n & 255n));
    cell.content.value[0] = new Uint8Array(bytes);
  }
  const changed = { ...snapshot, state: encodeRuntimeValue(encoded) };
  restoreState(impl, changed); // Runtime structural validation, not a global model invariant.
  return changed;
}

export function mutateConcreteBalance(impl: Impl, snapshot: ConcreteSnapshot, color: string, amount: bigint): ConcreteSnapshot {
  if (amount < 0n || amount >= 1n << 128n) throw new Error('invalid synthetic balance');
  const root = restoreState(impl, snapshot).encode();
  if (root === null || typeof root !== 'object' || !('content' in root) || !Array.isArray(root.content)) throw new Error('invalid account root');
  const base: unknown = root.content[0];
  if (base === null || typeof base !== 'object' || !('content' in base) || !Array.isArray(base.content)) throw new Error('invalid account base');
  const balances: unknown = base.content[4];
  if (balances === null || typeof balances !== 'object' || !('tag' in balances) || balances.tag !== 'map'
    || !('content' in balances) || !(balances.content instanceof Map)) throw new Error('invalid account balances');
  let found = false;
  for (const [key, cell] of balances.content as Map<unknown, unknown>) {
    if (key === null || typeof key !== 'object' || !('value' in key) || !Array.isArray(key.value)
      || !(key.value[0] instanceof Uint8Array) || hex(key.value[0]).padEnd(64, '0') !== color) continue;
    if (cell === null || typeof cell !== 'object' || !('content' in cell) || cell.content === null || typeof cell.content !== 'object'
      || !('value' in cell.content) || !Array.isArray(cell.content.value) || cell.content.value.length !== 1) throw new Error('invalid balance cell');
    const bytes: number[] = [];
    for (let n = amount; n > 0n; n >>= 8n) bytes.push(Number(n & 255n));
    cell.content.value[0] = new Uint8Array(bytes);
    found = true;
    break;
  }
  if (!found) throw new Error('synthetic balance mutation requires an existing color');
  const changed = { ...snapshot, state: encodeRuntimeValue(root) };
  restoreState(impl, changed);
  return changed;
}

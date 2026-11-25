// Boundary for @midnightntwrk/onchain-runtime-v4 4.0.0-rc.3.
// This decodes concrete data, never executes an account model. VM admission and
// transaction/asset authentication are different claims; see replayAccountTranscript.
export type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
export interface Aligned { value: string[]; alignment: Json[] }
export type StateValue = { tag: 'null' } | { tag: 'cell'; content: Aligned }
  | { tag: 'array'; content: StateValue[] } | { tag: 'map'; content: [Aligned, StateValue][] }
  | { tag: 'boundedMerkleTree'; content: [number, [string, string][]] };
export type Key = { tag: 'stack' } | { tag: 'value'; value: Aligned };
export type PlainOpcode = 'lt' | 'eq' | 'type' | 'size' | 'new' | 'and' | 'or' | 'neg'
  | 'log' | 'root' | 'pop' | 'add' | 'sub' | 'member' | 'ckpt';
export type Instruction = { opcode: PlainOpcode }
  | { opcode: 'noop' | 'dup' | 'swap'; n: number }
  | { opcode: 'addi' | 'subi'; immediate: number }
  | { opcode: 'branch' | 'jmp'; skip: number }
  | { opcode: 'popeq'; cached: boolean; result: Aligned }
  | { opcode: 'push'; storage: boolean; value: StateValue }
  | { opcode: 'concat' | 'ins'; cached: boolean; n: number }
  | { opcode: 'rem'; cached: boolean }
  | { opcode: 'idx'; cached: boolean; pushPath: boolean; path: Key[] };
export interface DecodedCall {
  circuit: string;
  account: string;
  input: Aligned;
  output: Aligned;
  context: Json;
  commitmentIndices: Json;
  initialState: StateValue;
  finalState: StateValue;
  program: Instruction[];
  declaredEffects: Json;
}
export interface DecodedAccountTranscript {
  schema: 'compact-account-vm-v1';
  gas: Json;
  calls: DecodedCall[];
}
function fail(message: string): never { throw new Error(`account VM decoder: ${message}`); }
function object(v: unknown): Record<string, unknown> {
  if (v === null || typeof v !== 'object' || Object.getPrototypeOf(v) !== Object.prototype) return fail('expected plain object');
  return v as Record<string, unknown>;
}
function exact(v: unknown, keys: string[]): Record<string, unknown> {
  const o = object(v);
  if (Object.keys(o).length !== keys.length || keys.some(k => !Object.hasOwn(o, k))) fail(`expected keys ${keys.join(',')}`);
  return o;
}
function list(v: unknown): unknown[] { return Array.isArray(v) ? v : fail('expected array'); }
function text(v: unknown): string { return typeof v === 'string' ? v : fail('expected string'); }
function bool(v: unknown): boolean { return typeof v === 'boolean' ? v : fail('expected boolean'); }
function nat(v: unknown, bound = 0xffffffff): number {
  return typeof v === 'number' && Number.isSafeInteger(v) && v >= 0 && v <= bound ? v : fail('invalid instruction integer');
}
function bytes(v: unknown): string {
  if (!(v instanceof Uint8Array)) return fail('expected bytes');
  return Buffer.from(v).toString('hex');
}
function alignment(v: unknown): Json[] {
  return list(v).map((x): Json => {
    const o = exact(x, ['tag', 'value']);
    if (o.tag === 'option') return { tag: 'option', value: list(o.value).map(alignment) };
    if (o.tag !== 'atom') return fail('unknown alignment segment');
    const a = object(o.value);
    if (a.tag === 'field' || a.tag === 'compress') { exact(a, ['tag']); return { tag: 'atom', value: { tag: a.tag } }; }
    if (a.tag === 'bytes') { exact(a, ['tag', 'length']); return { tag: 'atom', value: { tag: 'bytes', length: nat(a.length) } }; }
    return fail('unknown alignment atom');
  });
}
export function decodeAligned(v: unknown): Aligned {
  const o = exact(v, ['value', 'alignment']);
  return { value: list(o.value).map(bytes), alignment: alignment(o.alignment) };
}
export function decodeStateValue(v: unknown): StateValue {
  const o = object(v);
  if (o.tag === 'null') { exact(o, ['tag']); return { tag: 'null' }; }
  exact(o, ['tag', 'content']);
  if (o.tag === 'cell') return { tag: 'cell', content: decodeAligned(o.content) };
  if (o.tag === 'array') return { tag: 'array', content: list(o.content).map(decodeStateValue) };
  if (o.tag === 'map') {
    if (!(o.content instanceof Map)) return fail('expected state map');
    return { tag: 'map', content: [...o.content].map(([k, x]) => [decodeAligned(k), decodeStateValue(x)]) };
  }
  if (o.tag === 'boundedMerkleTree') {
    const c = list(o.content);
    if (c.length !== 2 || !(c[1] instanceof Map)) return fail('invalid Merkle tree');
    const entries: [string, string][] = [...c[1]].map(([k, x]) => {
      if (typeof k !== 'bigint' || k < 0n || !Array.isArray(x) || x.length !== 2 || x[1] !== undefined) return fail('invalid Merkle leaf');
      return [String(k), bytes(x[0])];
    });
    return { tag: 'boundedMerkleTree', content: [nat(c[0]), entries] };
  }
  return fail('unknown state value');
}
const plain: Record<string, true> = { lt: true, eq: true, type: true, size: true, new: true, and: true, or: true, neg: true, log: true, root: true, pop: true, add: true, sub: true, member: true, ckpt: true };
export function decodeInstruction(v: unknown): Instruction {
  if (typeof v === 'string') return Object.hasOwn(plain, v) ? { opcode: v as PlainOpcode } : fail(`unknown opcode ${v}`);
  const o = object(v);
  const names = Object.keys(o);
  if (names.length !== 1) return fail('instruction must have one opcode');
  const opcode = names[0];
  const a = object(o[opcode]);
  switch (opcode) {
    case 'noop': case 'dup': case 'swap':
      exact(a, ['n']); return { opcode, n: nat(a.n, opcode === 'noop' ? 0xffffffff : 255) };
    case 'addi': case 'subi':
      exact(a, ['immediate']); return { opcode, immediate: nat(a.immediate) };
    case 'branch': case 'jmp':
      exact(a, ['skip']); return { opcode, skip: nat(a.skip) };
    case 'popeq':
      exact(a, ['cached', 'result']); return { opcode, cached: bool(a.cached), result: decodeAligned(a.result) };
    case 'push':
      exact(a, ['storage', 'value']); return { opcode, storage: bool(a.storage), value: decodeStateValue(a.value) };
    case 'concat': case 'ins':
      exact(a, ['cached', 'n']); return { opcode, cached: bool(a.cached), n: nat(a.n, opcode === 'ins' ? 255 : 0xffffffff) };
    case 'rem':
      exact(a, ['cached']); return { opcode, cached: bool(a.cached) };
    case 'idx':
      exact(a, ['cached', 'pushPath', 'path']);
      return { opcode, cached: bool(a.cached), pushPath: bool(a.pushPath), path: list(a.path).map(x => {
        const k = object(x);
        if (k.tag === 'stack') { exact(k, ['tag']); return { tag: 'stack' }; }
        if (k.tag !== 'value') return fail('unknown index key');
        exact(k, ['tag', 'value']); return { tag: 'value', value: decodeAligned(k.value) };
      }) };
    default: return fail(`unknown opcode ${opcode}`);
  }
}
/** Lossless data transport; tags disambiguate arrays, maps, bytes and bigint. */
export function runtimeData(v: unknown): Json {
  if (v === undefined) return { kind: 'undefined' };
  if (v === null || typeof v === 'string' || typeof v === 'boolean') return v;
  if (typeof v === 'bigint') return { kind: 'bigint', value: String(v) };
  if (typeof v === 'number') return Number.isFinite(v) ? v : fail('nonfinite number');
  if (v instanceof Uint8Array) return { kind: 'bytes', value: bytes(v) };
  if (v instanceof Map) return { kind: 'map', entries: [...v].map(([k, x]) => [runtimeData(k), runtimeData(x)]) };
  if (Array.isArray(v)) return { kind: 'array', items: v.map(runtimeData) };
  return { kind: 'object', entries: Object.entries(object(v)).map(([k, x]) => [k, runtimeData(x)]) };
}
function encodedState(v: unknown): StateValue {
  if (v !== null && typeof v === 'object' && 'state' in v) return encodedState(v.state);
  if (v !== null && typeof v === 'object' && 'encode' in v && typeof v.encode === 'function') return decodeStateValue(v.encode());
  return fail('expected runtime state');
}
function effects(v: unknown): Json {
  exact(v, ['claimedNullifiers', 'claimedShieldedReceives', 'claimedShieldedSpends', 'claimedContractCalls', 'shieldedMints', 'unshieldedMints', 'unshieldedInputs', 'unshieldedOutputs', 'claimedUnshieldedSpends']);
  return runtimeData(v);
}
/** Every instruction is decoded from the concrete public transcript itself. */
export function decodeAccountTranscript(_context: unknown, result: unknown): DecodedAccountTranscript {
  const r = object(result);
  const context = object(r.context);
  const call = object(context.callContext);
  const calls = list(context.callProofDataTrace).map(raw => {
    const t = object(raw), initial = t.initialQueryContext, final = t.finalQueryContext;
    if (initial === null || typeof initial !== 'object' || final === null || typeof final !== 'object'
      || !('block' in initial) || !('comIndices' in initial) || !('state' in initial)
      || !('state' in final) || !('effects' in final)) return fail('missing query contexts');
    return {
      circuit: text(t.circuitId), account: text(t.contractAddress), input: decodeAligned(t.input), output: decodeAligned(t.output),
      context: runtimeData(initial.block), commitmentIndices: runtimeData(initial.comIndices),
      initialState: encodedState(initial.state), finalState: encodedState(final.state),
      program: list(t.publicTranscript).map(decodeInstruction), declaredEffects: effects(final.effects),
    };
  });
  if (calls.length === 0) fail('missing call proof trace');
  return { schema: 'compact-account-vm-v1', gas: runtimeData(call.currentGasCost), calls };
}
/** Exact VM admission only; this does not authenticate a transaction's assets. */
export function replayAccountTranscript<R>(initial: { runTranscript(transcript: unknown, costModel: unknown): R }, transcript: unknown, costModel: unknown): R;
export function replayAccountTranscript(initial: unknown, transcript: unknown, costModel: unknown): unknown;
export function replayAccountTranscript(initial: unknown, transcript: unknown, costModel: unknown): unknown {
  if (initial === null || typeof initial !== 'object' || !('runTranscript' in initial) || typeof initial.runTranscript !== 'function') return fail('missing VM admission entry point');
  const t = exact(transcript, ['gas', 'effects', 'program']);
  list(t.program).forEach(decodeInstruction);
  effects(t.effects);
  return initial.runTranscript(transcript, costModel);
}

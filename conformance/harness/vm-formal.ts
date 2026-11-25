// Runs the safe Agda VM, not native runProgram and not the account model. The
// initial stack and original instructions come only from concrete execution.
import { spawn, type ChildProcessWithoutNullStreams } from 'node:child_process';
import { createInterface } from 'node:readline';
import { fileURLToPath } from 'node:url';
import { encodeValue, parseValue } from './full-model.ts';
import { nat, tuple, type Value } from './full-wire.ts';
import { decodeInstruction, decodeStateValue, type Aligned, type Instruction, type StateValue } from './vm-account.ts';

export const FORMAL_VM_BIN = process.env.FORMAL_VM_BIN
  ?? fileURLToPath(new URL('../../_build/formal-vm/VMMain', import.meta.url));
interface NativeValue { encode(): unknown }
interface NativeStack {
  length(): number;
  get(index: number): NativeValue | undefined;
  isStrong(index: number): boolean | undefined;
}
export interface FormalQuery { toVmStack(): NativeStack }
export interface FormalVMResult {
  admitted: true;
  finalStackMatches: boolean;
  pc: string;
  instructions: number;
  // Native hash-map iteration order is not a semantic map observation.
  mapComparison: 'key-sorted';
  encoding: 'canonical-le-atoms-v1';
  difference?: { actual: Value; expected: Value };
}
const fieldOrder = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001n;
function fail(message: string): never { throw new Error(`formal account VM: ${message}`); }
function object(value: unknown): Record<string, unknown> {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) return fail('expected object');
  return value as Record<string, unknown>;
}
function word(hex: string): bigint {
  if (!/^(?:[0-9a-f]{2})*$/.test(hex) || hex.endsWith('00')) return fail('noncanonical little-endian atom');
  let value = 0n;
  for (let i = hex.length; i > 0; i -= 2) value = (value << 8n) | BigInt(`0x${hex.slice(i - 2, i)}`);
  return value;
}
function aligned(value: Aligned): Value {
  const words = value.value.map(word);
  const alignment = value.alignment.map(segment => {
    const s = object(segment);
    if (s.tag !== 'atom') return fail('alignment options are outside the emitted account surface');
    const atom = object(s.value);
    if (atom.tag === 'field') return 0;
    if (atom.tag !== 'bytes' || typeof atom.length !== 'number' || !Number.isSafeInteger(atom.length)
      || atom.length < 0 || atom.length >= 524288) return fail('unsupported alignment atom');
    return atom.length + 2;
  });
  if (words.length !== alignment.length) return fail('atom/alignment arity mismatch');
  for (let i = 0; i < words.length; i++) {
    const bound = alignment[i] === 0 ? fieldOrder : 256n ** BigInt(alignment[i] - 2);
    if (words[i] >= bound) return fail('atom exceeds its alignment bound');
  }
  return tuple([tuple(words.map(nat)), tuple(alignment.map(n => nat(BigInt(n))))]);
}
function stateValue(value: StateValue): Value {
  switch (value.tag) {
    case 'null': return tuple([nat(0n)]);
    case 'cell': return tuple([nat(1n), aligned(value.content)]);
    case 'array':
      if (value.content.length > 16) return fail('array exceeds the account VM bound');
      return tuple([nat(2n), tuple(value.content.map(stateValue))]);
    case 'map': {
      const entries = value.content.map(([key, child]) => tuple([aligned(key), stateValue(child)]));
      const keys = entries.map(entry => JSON.stringify(entry.value[0]));
      if (new Set(keys).size !== keys.length) return fail('duplicate map key');
      return tuple([nat(3n), tuple(entries)]);
    }
    case 'boundedMerkleTree': return fail('account transcripts do not use BMT instructions');
  }
}
function instruction(op: Instruction): Value {
  const args = (...values: Value[]): Value => tuple(values);
  const n = (x: number): Value => nat(BigInt(x));
  const b = (x: boolean): Value => ({ tag: 'bool', value: x });
  switch (op.opcode) {
    case 'noop': return args(n(0), n(op.n));
    case 'dup': return args(n(1), n(op.n));
    case 'swap': return args(n(2), n(op.n));
    case 'lt': return args(n(3));
    case 'eq': return args(n(4));
    case 'type': return args(n(5));
    case 'size': return args(n(6));
    case 'new': return args(n(7));
    case 'and': return args(n(8));
    case 'or': return args(n(9));
    case 'neg': return args(n(10));
    case 'pop': return args(n(11));
    case 'add': return args(n(12));
    case 'sub': return args(n(13));
    case 'member': return args(n(14));
    case 'ckpt': return args(n(15));
    case 'popeq': return args(n(16), b(op.cached), aligned(op.result));
    case 'addi': return args(n(17), n(op.immediate));
    case 'subi': return args(n(18), n(op.immediate));
    case 'push': return args(n(19), b(op.storage), stateValue(op.value));
    case 'branch': return args(n(20), n(op.skip));
    case 'jmp': return args(n(21), n(op.skip));
    case 'concat': return args(n(22), b(op.cached), n(op.n));
    case 'ins': return args(n(23), b(op.cached), n(op.n));
    case 'rem': return args(n(24), b(op.cached));
    case 'idx': return args(n(25), b(op.cached), b(op.pushPath), tuple(op.path.map(k => k.tag === 'stack'
      ? { tag: 'none' } : aligned(k.value))));
    case 'log': case 'root': return fail(`unsupported account instruction ${op.opcode}`);
  }
}
function snapshot(query: FormalQuery): Value {
  const stack = query.toVmStack();
  const items: Value[] = [];
  for (let i = stack.length() - 1; i >= 0; i--) {
    const native = stack.get(i), strong = stack.isStrong(i);
    if (!native || strong === undefined) return fail('incomplete native VM stack');
    items.push(tuple([{ tag: 'bool', value: strong }, stateValue(decodeStateValue(native.encode()))]));
  }
  return tuple(items);
}
// The only normalization is hash-map entry order. Arrays, aligned atoms, flags,
// scalar bounds, path order, and instruction order remain exact.
function canonicalState(value: Value): Value {
  if (value.tag !== 'tuple') return fail('malformed formal state');
  const [tag, content] = value.value;
  if (!tag || tag.tag !== 'nat') return fail('missing formal state tag');
  if (tag.value === '0' && value.value.length === 1) return value;
  if (tag.value === '1' && value.value.length === 2) return value;
  if ((tag.value !== '2' && tag.value !== '3') || value.value.length !== 2 || content.tag !== 'tuple') return fail('malformed formal container');
  if (tag.value === '2') return tuple([tag, tuple(content.value.map(canonicalState))]);
  const entries = content.value.map(entry => {
    if (entry.tag !== 'tuple' || entry.value.length !== 2) return fail('malformed formal map entry');
    return tuple([entry.value[0], canonicalState(entry.value[1])]);
  });
  entries.sort((a, b) => {
    const left = JSON.stringify(a.value[0]);
    const right = JSON.stringify(b.value[0]);
    return left < right ? -1 : left > right ? 1 : 0;
  });
  return tuple([tag, tuple(entries)]);
}
function canonicalStack(value: Value): Value {
  if (value.tag !== 'tuple') return fail('malformed formal stack');
  return tuple(value.value.map(item => {
    if (item.tag !== 'tuple' || item.value.length !== 2 || item.value[0].tag !== 'bool') return fail('malformed formal stack item');
    return tuple([item.value[0], canonicalState(item.value[1])]);
  }));
}
export interface NativeCommitmentContext {
  unchangedContextFields: boolean;
  before: [string, string][];
  after: [string, string][];
}
/** createZswapOutput registers output indices outside VM instructions. Preserve
 * those exact updates for independent model-effect comparison; all other
 * context fields must remain unchanged. No context field is left unchecked. */
export function observeNativeCommitments(replayed: FormalQuery, final: FormalQuery): NativeCommitmentContext {
  const observations = [replayed, final].map(query => {
    const stack = query.toVmStack(), native = stack.get(0), strong = stack.isStrong(0);
    if (!native || strong === undefined) return fail('missing native context root');
    const context = decodeStateValue(native.encode());
    if (context.tag !== 'array' || context.content[1]?.tag !== 'map') return fail('invalid commitment context layout');
    const indices: [string, string][] = context.content[1].content.map(([key, value]) => {
      if (key.value.length !== 1 || JSON.stringify(key.alignment) !== '[{"tag":"atom","value":{"tag":"bytes","length":32}}]'
        || value.tag !== 'cell' || value.content.value.length !== 1
        || JSON.stringify(value.content.alignment) !== '[{"tag":"atom","value":{"tag":"bytes","length":8}}]')
        return fail('invalid native commitment/index encoding');
      const index = word(value.content.value[0]);
      if (key.value[0].length > 64 || index >= 1n << 64n) return fail('native commitment/index exceeds width');
      return [key.value[0].padEnd(64, '0'), String(index)];
    });
    // decodeStateValue allocated this tree; the live runtime context is untouched.
    context.content[1] = { tag: 'map', content: [] };
    return { context: canonicalState(stateValue(context)), strong, indices };
  });
  return {
    unchangedContextFields: observations[0].strong === observations[1].strong
      && JSON.stringify(observations[0].context) === JSON.stringify(observations[1].context),
    before: observations[0].indices, after: observations[1].indices,
  };
}

interface Pending { resolve(value: unknown): void; reject(error: Error): void }
export class FormalVM {
  readonly child: ChildProcessWithoutNullStreams;
  private readonly pending: Pending[] = [];
  private stderr = '';
  private failure?: Error;
  constructor(binary = FORMAL_VM_BIN) {
    this.child = spawn(binary, [], { stdio: ['pipe', 'pipe', 'pipe'] });
    this.child.stderr.on('data', (data: Buffer) => { this.stderr = (this.stderr + data.toString('utf8')).slice(-131072); });
    const failPending = (error: Error): void => {
      this.failure = error;
      for (const request of this.pending.splice(0)) request.reject(error);
    };
    this.child.on('error', failPending);
    this.child.on('close', (code, signal) => failPending(new Error(`formal VM closed (code=${code}, signal=${signal}): ${this.stderr}`)));
    createInterface({ input: this.child.stdout }).on('line', line => {
      const request = this.pending.shift();
      if (!request) { failPending(new Error('unsolicited formal VM response')); this.child.kill(); return; }
      try { request.resolve(JSON.parse(line)); } catch (error: unknown) { request.reject(error instanceof Error ? error : new Error(String(error))); }
    });
  }
  private request(line: string): Promise<unknown> {
    if (this.failure) return Promise.reject(this.failure);
    const { promise, resolve, reject } = Promise.withResolvers<unknown>();
    this.pending.push({ resolve, reject });
    this.child.stdin.write(`${line}\n`, error => { if (error) reject(error); });
    return promise;
  }
  async compare(initial: FormalQuery, rawProgram: unknown[], final: FormalQuery): Promise<FormalVMResult> {
    const program = rawProgram.map(decodeInstruction);
    const start = snapshot(initial), expected = canonicalStack(snapshot(final));
    const request = `vm-v1 ${program.length + 1} ${encodeValue(start)} ${encodeValue(tuple(program.map(instruction)))}`;
    const response = object(await this.request(request));
    if (response.tag !== 'accepted' || typeof response.pc !== 'string' || !/^(0|[1-9][0-9]*)$/.test(response.pc))
      return fail(`safe Agda interpreter did not admit concrete program: ${JSON.stringify(response)}`);
    if (response.pc !== String(program.length)) return fail('formal interpreter halted at the wrong program counter');
    const actual = canonicalStack(parseValue(response.stack));
    const finalStackMatches = JSON.stringify(actual) === JSON.stringify(expected);
    return { admitted: true, finalStackMatches, pc: response.pc,
      instructions: program.length, mapComparison: 'key-sorted', encoding: 'canonical-le-atoms-v1',
      ...(finalStackMatches ? {} : { difference: { actual, expected } }) };
  }
  close(): void { this.child.stdin.end(); }
}

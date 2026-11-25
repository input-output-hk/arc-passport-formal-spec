import { spawn, type ChildProcessWithoutNullStreams } from 'node:child_process';
import { createInterface } from 'node:readline';
import { fileURLToPath } from 'node:url';
import { bytes, bytesType, fromValue, nat, toValue, tuple } from './full-wire.ts';
import type { FullRequest, FullState, TypeInfo, Value } from './full-wire.ts';
import { invoke, record } from './full-impl.ts';
import type { FullImplementation, Module } from './full-impl.ts';
import { independentPersistentHash } from './independent-hash.ts';

export interface FullEffect { tag: string; arguments: Value[] }
export interface ModelError { kind: 'assertion' | 'bounds' | 'decoding' | 'primitive'; message: string; bits?: string }
export type ModelOutcome =
  | { tag: 'accepted'; output: Value; state: FullState; effects: FullEffect[] }
  | { tag: 'rejected'; error: ModelError };
export const FULL_MODEL_BIN = process.env.FULL_MODEL_BIN
  ?? fileURLToPath(new URL('../../_build/full-account/FullAccountMain', import.meta.url));
export function parseValue(input: unknown): Value {
  const x = record(input, 'wire value');
  switch (x.tag) {
    case 'none': return { tag: 'none' };
    case 'some': return { tag: 'some', value: parseValue(x.value) };
    case 'nat':
      if (typeof x.value !== 'string' || !/^(0|[1-9][0-9]*)$/.test(x.value)) throw new Error('invalid natural wire value');
      return { tag: 'nat', value: x.value };
    case 'bool':
      if (typeof x.value !== 'boolean') throw new Error('invalid Boolean wire value');
      return { tag: 'bool', value: x.value };
    case 'bytes':
      if (!Array.isArray(x.value) || x.value.some(b => typeof b !== 'number' || !Number.isInteger(b) || b < 0 || b > 255)) throw new Error('invalid byte wire value');
      return { tag: 'bytes', value: x.value as number[] };
    case 'tuple':
      if (!Array.isArray(x.value)) throw new Error('invalid tuple wire value');
      return { tag: 'tuple', value: x.value.map(parseValue) };
    default: throw new Error('unknown wire value tag');
  }
}
export function encodeValue(v: Value): string {
  switch (v.tag) {
    case 'nat': return `n ${v.value}`;
    case 'bool': return `b ${v.value ? 1 : 0}`;
    case 'bytes': return `y ${v.value.length}${v.value.length ? ` ${v.value.join(' ')}` : ''}`;
    case 'tuple': return `t ${v.value.length}${v.value.length ? ` ${v.value.map(encodeValue).join(' ')}` : ''}`;
    case 'none': return 'z';
    case 'some': return `s ${encodeValue(v.value)}`;
  }
}
export function encodeFullRequest(request: FullRequest): string {
  if (!/^[A-Za-z_][A-Za-z_0-9]*$/.test(request.call.name) || request.state.ledger.some(([name]) => !/^[A-Za-z_][A-Za-z_0-9]*$/.test(name)))
    throw new Error('invalid full account token identifier');
  return ['full-v1', request.call.name, encodeValue(tuple(request.call.arguments)), encodeValue(request.context.self),
    request.context.blockTime, encodeValue(request.context.caller), encodeValue(request.context.heldCoin), request.state.ledger.length,
    ...request.state.ledger.flatMap(([name, value]) => [name, encodeValue(value)])].join(' ');
}
function parseOutcome(input: unknown): ModelOutcome {
  const x = record(input, 'model result');
  if (x.tag === 'rejected') {
    const e = record(x.error, 'model error');
    if ((e.kind !== 'assertion' && e.kind !== 'bounds' && e.kind !== 'decoding' && e.kind !== 'primitive') || typeof e.message !== 'string'
      || (e.bits !== undefined && typeof e.bits !== 'string')) throw new Error('invalid model error');
    return { tag: 'rejected', error: { kind: e.kind, message: e.message, ...(e.bits === undefined ? {} : { bits: e.bits }) } };
  }
  if (x.tag !== 'accepted') throw new Error('unknown model outcome');
  const s = record(x.state, 'model state');
  if (!Array.isArray(s.ledger) || !Array.isArray(x.effects)) throw new Error('invalid model state/effects');
  const ledger: [string, Value][] = s.ledger.map(pair => {
    if (!Array.isArray(pair) || pair.length !== 2 || typeof pair[0] !== 'string') throw new Error('invalid model ledger pair');
    return [pair[0], parseValue(pair[1])];
  });
  const effects = x.effects.map(effect => {
    const e = record(effect, 'model effect');
    if (typeof e.tag !== 'string' || !Array.isArray(e.arguments)) throw new Error('invalid model effect');
    return { tag: e.tag, arguments: e.arguments.map(parseValue) };
  });
  return { tag: 'accepted', output: parseValue(x.output), state: { ledger }, effects };
}
interface Descriptor {
  alignment(): unknown[];
  toValue(v: unknown): Uint8Array[];
  fromValue(v: Uint8Array[]): unknown;
}
function descriptor(v: unknown): Descriptor {
  const x = record(v, 'runtime descriptor');
  if (typeof x.alignment !== 'function' || typeof x.toValue !== 'function' || typeof x.fromValue !== 'function') throw new Error('invalid runtime descriptor');
  return {
    alignment: () => {
      const a = invoke(x, 'alignment'); if (!Array.isArray(a)) throw new Error('invalid descriptor alignment'); return a;
    },
    toValue: value => {
      const a = invoke(x, 'toValue', value);
      if (!Array.isArray(a) || a.some(b => !(b instanceof Uint8Array))) throw new Error('invalid descriptor encoding');
      return a as Uint8Array[];
    },
    fromValue: value => invoke(x, 'fromValue', value),
  };
}
function joined(types: Descriptor[]): Descriptor {
  return {
    alignment: () => types.flatMap(t => t.alignment()),
    toValue: input => {
      if (!Array.isArray(input) || input.length !== types.length) throw new Error('primitive tuple arity mismatch');
      return types.flatMap((t, i) => t.toValue(input[i]));
    },
    fromValue: input => types.map(t => t.fromValue(input)),
  };
}
const pointType = (curve: string): TypeInfo => ({ 'type-name': curve === 'jubjub' ? 'JubjubPoint' : curve === 'k256' ? 'Secp256k1Point' : 'Secp256r1Point' });
function littleEndian(n: bigint): Uint8Array {
  return Uint8Array.from({ length: 32 }, (_, i) => Number((n >> BigInt(8 * i)) & 255n));
}
function integer(v: Value): bigint {
  if (v.tag !== 'nat') throw new Error('expected primitive natural');
  return BigInt(v.value);
}
function inverse(n: bigint, modulus: bigint): bigint {
  let a = ((n % modulus) + modulus) % modulus, b = modulus, x = 1n, y = 0n;
  while (b !== 0n) { const q = a / b; [a, b] = [b, a - q * b]; [x, y] = [y, x - q * y]; }
  if (a !== 1n) throw new Error('noninvertible ECDSA scalar');
  return ((x % modulus) + modulus) % modulus;
}
export function answerFullPrimitive(impl: FullImplementation, name: string, args: Value[]): Value {
  const rt = impl.runtime;
  const arity = (n: number) => { if (args.length !== n) throw new Error(`primitive ${name} arity mismatch`); };
  if (name === 'persistentHash') {
    const parts: [string, Value][] = args.map(a => {
      if (a.tag !== 'tuple' || a.value.length !== 2 || a.value[0].tag !== 'bytes') throw new Error('invalid typed hash preimage');
      return [Buffer.from(a.value[0].value).toString('utf8'), a.value[1]];
    });
    return bytes(independentPersistentHash(parts));
  }
  if (name === 'transientHash') {
    const types = args.map(() => descriptor(rt.CompactTypeField));
    const out = invoke(rt, 'transientHash', joined(types), args.map(integer));
    if (typeof out !== 'bigint') throw new Error('invalid transientHash result');
    return nat(out);
  }
  if (name === 'degradeToTransient') {
    arity(1); const out = invoke(rt, name, fromValue(bytesType(32), args[0]));
    if (typeof out !== 'bigint') throw new Error('invalid degrade result'); return nat(out);
  }
  if (name === 'upgradeFromTransient') {
    arity(1); const out = invoke(rt, name, integer(args[0]));
    if (!(out instanceof Uint8Array)) throw new Error('invalid upgrade result'); return bytes(out);
  }
  const curve = /^(jubjub|k256|p256)-(coordinates|mulg|mul|add|ecdsa)$/.exec(name);
  if (curve) {
    const [, c, op] = curve;
    const prefix = c === 'jubjub' ? 'ec' : c === 'k256' ? 'secp256k1' : 'secp256r1';
    const p = (v: Value) => fromValue(pointType(c), v);
    if (op === 'coordinates') {
      arity(1); const point = p(args[0]);
      const x = invoke(rt, c === 'jubjub' ? 'jubjubPointX' : `${prefix}PointX`, point);
      const y = invoke(rt, c === 'jubjub' ? 'jubjubPointY' : `${prefix}PointY`, point);
      if (typeof x !== 'bigint' || typeof y !== 'bigint') throw new Error('invalid point coordinate');
      return tuple([bytes(littleEndian(x)), bytes(littleEndian(y))]);
    }
    if (op === 'mulg') { arity(1); return toValue(pointType(c), invoke(rt, `${prefix}MulGenerator`, integer(args[0]) % integerModulus(rt, c))); }
    if (op === 'mul') { arity(2); return toValue(pointType(c), invoke(rt, `${prefix}Mul`, p(args[0]), integer(args[1]) % integerModulus(rt, c))); }
    if (op === 'add') { arity(2); return toValue(pointType(c), invoke(rt, `${prefix}Add`, p(args[0]), p(args[1]))); }
    arity(3);
    if (c === 'jubjub') throw new Error('ECDSA is not a Jubjub primitive');
    const sig = args[1];
    if (sig.tag !== 'tuple' || sig.value.length !== 2 || args[0].tag !== 'bytes') throw new Error('invalid ECDSA arguments');
    const r = integer(sig.value[0]), s = integer(sig.value[1]), modulus = integerModulus(rt, c);
    if (r <= 0n || r >= modulus || s <= 0n || s >= modulus) return { tag: 'bool', value: false };
    const digest = args[0].value.reduce((n, byte) => n * 256n + BigInt(byte), 0n);
    const inv = inverse(s, modulus);
    const a = invoke(rt, `${prefix}MulGenerator`, digest * inv % modulus);
    const b = invoke(rt, `${prefix}Mul`, p(args[2]), r * inv % modulus);
    const q = record(invoke(rt, `${prefix}Add`, a, b), 'ECDSA result point');
    const x = invoke(rt, `${prefix}PointX`, q);
    if (typeof x !== 'bigint') throw new Error('invalid ECDSA point');
    return { tag: 'bool', value: q.identity !== true && x % modulus === r };
  }
  if (name === 'coinCommitment' || name === 'coinNullifier') {
    arity(2);
    let kind: Value = { tag: 'bool', value: false }, address = args[1];
    if (name === 'coinCommitment') {
      if (args[1].tag !== 'tuple' || args[1].value.length !== 2 || args[1].value[0].tag !== 'bool') throw new Error('invalid coin recipient');
      [kind, address] = args[1].value;
    }
    // Stdlib domain, fixed-width coin encoding, and selected recipient bytes;
    // no generated account method or runtime coin callback participates.
    const domain = bytes(Buffer.from(name === 'coinCommitment' ? 'midnight:zswap-cc[v1]' : 'midnight:zswap-cn[v1]'));
    return bytes(independentPersistentHash([
      ['Bytes<21>', domain], ['ShieldedCoinInfo', args[0]], ['Boolean', kind], ['Bytes<32>', address],
    ]));
  }
  throw new Error(`unknown primitive ${name}`);
}
function integerModulus(runtime: Module, curve: string): bigint {
  const value = runtime[curve === 'jubjub' ? 'JUBJUB_SCALAR_MODULUS' : curve === 'k256' ? 'SECP256K1_SCALAR_MODULUS' : 'SECP256R1_SCALAR_MODULUS'];
  if (typeof value !== 'bigint') throw new Error('missing curve modulus');
  return value;
}
export class FullModel {
  private readonly child: ChildProcessWithoutNullStreams;
  private readonly lines: AsyncIterator<string>;
  private stderr = '';
  rpcCount = 0;
  readonly primitiveFailures: { name: string; message: string }[] = [];
  constructor(readonly impl: FullImplementation, bin = FULL_MODEL_BIN) {
    this.child = spawn(bin, [], { stdio: ['pipe', 'pipe', 'pipe'] });
    this.child.stderr.on('data', (chunk: Buffer) => { this.stderr += chunk.toString(); });
    this.child.on('error', error => { this.stderr += error.message; });
    this.child.stdin.on('error', error => { this.stderr += error.message; });
    this.lines = createInterface({ input: this.child.stdout })[Symbol.asyncIterator]();
  }
  async step(request: FullRequest): Promise<ModelOutcome> {
    this.child.stdin.write(`${encodeFullRequest(request)}\n`);
    for (;;) {
      const { value, done } = await this.lines.next();
      if (done) throw new Error(`full account model exited: ${this.stderr}`);
      if (value.startsWith('{')) return parseOutcome(JSON.parse(value));
      if (!value.startsWith('? ')) throw new Error(`unexpected full model output ${value}`);
      const rpc = record(record(JSON.parse(value.slice(2))).oracle, 'oracle request');
      if (typeof rpc.name !== 'string' || !Array.isArray(rpc.arguments)) throw new Error('invalid oracle request');
      this.rpcCount++;
      try {
        const reply = answerFullPrimitive(this.impl, rpc.name, rpc.arguments.map(parseValue));
        this.child.stdin.write(`${encodeValue(reply)}\n`);
      } catch (error: unknown) {
        this.primitiveFailures.push({ name: rpc.name, message: error instanceof Error ? error.message : String(error) });
        this.child.stdin.write('error\n');
      }
    }
  }
  close(): void { this.child.stdin.end(); }
}

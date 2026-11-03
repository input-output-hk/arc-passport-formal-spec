import { decodeAligned, decodeInstruction, decodeStateValue, type Aligned, type Instruction, type StateValue } from './vm-account.ts';
import { type AccountInfo, type LedgerInfo, type TypeInfo, type Value, toValue } from './full-wire.ts';

interface RuntimeValue { encode(): unknown }
interface RuntimeStack {
  length(): number;
  get(index: number): RuntimeValue | undefined;
  isStrong(index: number): boolean | undefined;
  removeLast(): void;
}
interface Descriptor {
  fromValue(value: Uint8Array[]): unknown;
  alignment(): unknown[];
}
export interface ObservationRuntime {
  runProgram(stack: RuntimeStack, program: unknown[], costModel: unknown): { stack: RuntimeStack; events: unknown[] };
  CompactTypeField: Descriptor;
  CompactTypeBoolean: Descriptor;
  CompactTypeJubjubPoint: Descriptor;
  CompactTypeSecp256k1Point: Descriptor;
  CompactTypeSecp256r1Point: Descriptor;
  CompactTypeSecp256k1Scalar: Descriptor;
  CompactTypeSecp256r1Scalar: Descriptor;
  CompactTypeBytes: new (length: number) => Descriptor;
  CompactTypeUnsignedInteger: new (maximum: bigint, length: number) => Descriptor;
}
export interface ObservableQuery {
  toVmStack(): RuntimeStack;
}
export interface AccountEffect { tag: string; arguments: Value[] }
interface Origin { root: 'context' | 'effects' | 'ledger' | 'derived'; path: Aligned[] }
export interface InstructionObservation {
  pc: number;
  instruction: Instruction;
  operands: { strong: boolean; value: StateValue }[];
  resultStack: { strong: boolean; value: StateValue }[];
  reads: Aligned[];
}
export interface AccountObservations {
  instructions: InstructionObservation[];
  ledgerEffects: AccountEffect[];
  publicEffects: AccountEffect[];
  // VM instructions acting on the effects/context stack remain separate. This
  // interpreter does not pretend they authenticate assets or private witnesses.
  otherRoots: { pc: number; root: 'context' | 'effects'; path: Aligned[] }[];
}
function reject(message: string): never { throw new Error(`account VM observation: ${message}`); }
function snapshot(stack: RuntimeStack): { strong: boolean; value: StateValue }[] {
  const out: { strong: boolean; value: StateValue }[] = [];
  for (let i = 0; i < stack.length(); i++) {
    const v = stack.get(i), strong = stack.isStrong(i);
    if (!v || strong === undefined) reject('incomplete runtime stack');
    out.push({ strong, value: decodeStateValue(v.encode()) });
  }
  return out;
}
function natural(a: Aligned): bigint {
  if (a.value.length !== 1) return reject('expected integer key');
  const bs = Buffer.from(a.value[0], 'hex');
  let n = 0n;
  for (let i = bs.length - 1; i >= 0; i--) n = (n << 8n) | BigInt(bs[i]);
  return n;
}
const fieldNames: string[][] = [
  ['round', 'enc_key', 'inbox', 'inbox_count', 'unshielded_balances', 'spec_version', 'devices', 'device_epoch', 'device_count', 'auth_nonce'],
  ['boot', 'booted', 'grants', 'grant_generation', 'recovery_pk', 'recovery_phi', 'recovery_phi_len', 'recovery_session', 'recovery_wrap', 'recovery_version', 'pending_recovery', 'pending_entry', 'pending_recovery_pk', 'pending_not_before', 'veto_window'],
];
function fieldAt(info: AccountInfo, path: Aligned[]): LedgerInfo {
  if (path.length !== 2) return reject('non-field ledger path');
  const group = Number(natural(path[0])), slot = Number(natural(path[1]));
  const name = fieldNames[group]?.[slot];
  const field = info.ledger.find(f => f.name === name);
  if (!field) return reject(`unknown account field ${group}/${slot}`);
  return field;
}
function asCell(value: StateValue): Aligned {
  if (value.tag !== 'cell') return reject('expected cell operand');
  return value.content;
}
function decodeABI(rt: ObservationRuntime, type: TypeInfo, value: Aligned): Value {
  const input = value.value.map(x => Uint8Array.from(Buffer.from(x, 'hex')));
  const expectedAlignment: unknown[] = [];
  function decode(t: TypeInfo): unknown {
    let descriptor: Descriptor | undefined;
    switch (t['type-name']) {
      case 'Field': descriptor = rt.CompactTypeField; break;
      case 'Uint': {
        const maximum = (t as TypeInfo & { maxval?: unknown }).maxval;
        const bits = [8, 32, 64, 128].find(n => maximum === Number((1n << BigInt(n)) - 1n));
        if (bits === undefined) return reject('unsupported account Uint bound');
        descriptor = new rt.CompactTypeUnsignedInteger((1n << BigInt(bits)) - 1n, bits / 8);
        break;
      }
      case 'Boolean': descriptor = rt.CompactTypeBoolean; break;
      case 'Bytes': descriptor = new rt.CompactTypeBytes(t.length!); break;
      case 'JubjubPoint': descriptor = rt.CompactTypeJubjubPoint; break;
      case 'Secp256k1Point': descriptor = rt.CompactTypeSecp256k1Point; break;
      case 'Secp256r1Point': descriptor = rt.CompactTypeSecp256r1Point; break;
      case 'Secp256k1Scalar': descriptor = rt.CompactTypeSecp256k1Scalar; break;
      case 'Secp256r1Scalar': descriptor = rt.CompactTypeSecp256r1Scalar; break;
      case 'Tuple': return t.types!.map(decode);
      case 'Struct': return Object.fromEntries(t.elements!.map(f => [f.name, decode(f.type)]));
      default: return reject(`unsupported ABI atom ${t['type-name']}`);
    }
    expectedAlignment.push(...descriptor.alignment());
    return descriptor.fromValue(input);
  }
  const native = decode(type);
  if (input.length !== 0 || JSON.stringify(expectedAlignment) !== JSON.stringify(value.alignment)) reject('ABI alignment/arity mismatch');
  return toValue(type, native);
}
const fieldArgument = (name: string): Value => ({ tag: 'bytes', value: [...Buffer.from(name, 'utf8')] });

/**
 * Independent concrete observation. Each non-control opcode is interpreted by
 * the pinned VM's single-instruction primitive, not by an account model. Cache
 * flags are cleared ONLY in this observational pass because each primitive call
 * starts a fresh cache. Exact cache/gas/admission belongs to runTranscript with
 * the original program, never to the result returned here.
 */
export function interpretAccountTranscript(rt: ObservationRuntime, initial: ObservableQuery, program: unknown[], costModel: unknown, info: AccountInfo, captureInstructionStacks = false): AccountObservations {
  let stack = initial.toVmStack();
  if (stack.length() !== 3) reject('unexpected query stack layout');
  const origins: (Origin | undefined)[] = [
    { root: 'context', path: [] }, { root: 'effects', path: [] }, { root: 'ledger', path: [] },
  ];
  const observations: AccountObservations = { instructions: [], ledgerEffects: [], publicEffects: [], otherRoots: [] };
  let pendingCallerRead = false;
  for (let pc = 0; pc < program.length;) {
    const raw = program[pc], op = decodeInstruction(raw), oldStack = stack;
    const before = captureInstructionStacks ? snapshot(stack) : [];
    const ledgerStart = observations.ledgerEffects.length;
    let skip = 0, reads: Aligned[] = [];
    const originAt = (depth: number): Origin | undefined => origins[origins.length - 1 - depth];
    const valueAt = (depth: number): StateValue => {
      const value = oldStack.get(oldStack.length() - 1 - depth);
      return value ? decodeStateValue(value.encode()) : reject('stack underflow');
    };
    if (op.opcode === 'branch' || op.opcode === 'jmp') {
      if (op.opcode === 'branch') {
        const v = asCell(valueAt(0));
        // VM Branch tests the canonical zero cell, not Compact Boolean decoding.
        skip = v.value.length === 1 && v.value[0] === '' ? 0 : op.skip;
        stack.removeLast(); origins.pop();
      } else skip = op.skip;
    } else {
      let interpreted: unknown = raw;
      if (typeof raw === 'object' && raw !== null) {
        const body = Object.values(raw)[0] as Record<string, unknown>;
        if ('cached' in body) interpreted = { [op.opcode]: { ...body, cached: false } };
        if (op.opcode === 'popeq') interpreted = { popeq: { cached: false, result: null } };
      }
      const result = rt.runProgram(stack, [interpreted], costModel);
      stack = result.stack;
      reads = result.events.flatMap(ev => {
        if (ev === null || typeof ev !== 'object' || !('tag' in ev)) return reject('invalid VM event');
        if (ev.tag !== 'read') return [];
        if (!('content' in ev)) return reject('missing read content');
        return [decodeAligned(ev.content)];
      });
      if (op.opcode === 'popeq' && (reads.length !== 1 || JSON.stringify(reads[0]) !== JSON.stringify(op.result))) reject('recorded VM read differs');
      switch (op.opcode) {
        case 'push': origins.push(undefined); break;
        case 'dup': origins.push(originAt(op.n)); break;
        case 'swap': {
          const a = origins.length - 1, b = origins.length - 2 - op.n;
          [origins[a], origins[b]] = [origins[b], origins[a]]; break;
        }
        case 'idx': {
          const dynamic = op.path.filter(k => k.tag === 'stack').length;
          const container = originAt(dynamic);
          let depth = 0;
          const keys = op.path.map(k => k.tag === 'value' ? k.value : asCell(valueAt(depth++)));
          origins.splice(origins.length - dynamic - 1);
          let current = container;
          for (const key of keys) {
            if (op.pushPath) origins.push(current, undefined);
            current = current ? { root: current.root, path: [...current.path, key] } : undefined;
          }
          origins.push(current);
          if (current?.root === 'context' && current.path.length === 1 && natural(current.path[0]) === 6n) {
            if (pendingCallerRead) reject('overlapping optional caller reads');
            pendingCallerRead = true;
            const v = stack.get(stack.length() - 1);
            if (!v) reject('missing caller result');
            const rawCaller = decodeStateValue(v.encode());
            let caller: Value = { tag: 'none' };
            if (rawCaller.tag !== 'null') {
              const type: TypeInfo = { 'type-name': 'Struct', name: 'PublicAddress', elements: [
                { name: 'is_left', type: { 'type-name': 'Boolean' } },
                { name: 'left', type: { 'type-name': 'Bytes', length: 32 } },
                { name: 'right', type: { 'type-name': 'Bytes', length: 32 } },
              ] };
              const value = decodeABI(rt, type, asCell(rawCaller));
              if (value.tag !== 'tuple' || value.value[0]?.tag !== 'bool') reject('invalid public address');
              const isContract = value.value[0].value;
              caller = { tag: 'some', value: { tag: 'tuple', value: [value.value[0], value.value[isContract ? 1 : 2]] } };
            }
            observations.publicEffects.push({ tag: 'contextRead', arguments: [fieldArgument('caller'), caller] });
          }
          break;
        }
        case 'popeq': {
          const source = originAt(0);
          if (source?.root === 'ledger') {
            const field = fieldAt(info, source.path.slice(0, 2));
            if (source.path.length === 2 && field.storage === 'Cell') observations.ledgerEffects.push({ tag: 'readCell', arguments: [fieldArgument(field.name), decodeABI(rt, field.type!, op.result)] });
            else if (source.path.length === 3 && field.storage === 'Map') observations.ledgerEffects.push({ tag: 'mapLookup', arguments: [fieldArgument(field.name), decodeABI(rt, field.key!, source.path[2]), decodeABI(rt, field.value!, op.result)] });
            else reject('unsupported ledger observation path');
          } else if (source?.root === 'context' && source.path.length === 1 && natural(source.path[0]) === 0n) {
            observations.publicEffects.push({ tag: 'contextRead', arguments: [fieldArgument('self'), decodeABI(rt, { 'type-name': 'Bytes', length: 32 }, op.result)] });
          } else if (source?.root !== 'derived' && !pendingCallerRead) reject('unaccounted public read');
          pendingCallerRead = false;
          origins.pop(); break;
        }
        case 'member': {
          const source = originAt(1);
          if (source?.root === 'ledger') {
            const field = fieldAt(info, source.path), key = asCell(valueAt(0));
            const top = stack.get(stack.length() - 1);
            if (!top) reject('missing membership result');
            const b = natural(asCell(decodeStateValue(top.encode())));
            if (b !== 0n && b !== 1n) reject('invalid membership Boolean');
            observations.ledgerEffects.push({ tag: field.storage === 'Set' ? 'setMember' : 'mapMember', arguments: [fieldArgument(field.name), decodeABI(rt, field.storage === 'Set' ? field.type! : field.key!, key), { tag: 'bool', value: b === 1n }] });
          } else if (source && source.root !== 'derived') observations.otherRoots.push({ pc, root: source.root, path: source.path });
          origins.splice(origins.length - 2, 2, source?.root === 'ledger' ? { root: 'derived', path: [] } : undefined); break;
        }
        case 'ins': {
          let depth = 0;
          for (let i = 0; i < op.n; i++) {
            const key = asCell(valueAt(depth + 1)), source = originAt(depth + 2), value = valueAt(depth);
            if (source?.root === 'ledger' && i === 0) {
              const path = [...source.path, key];
              if (path.length === 2) {
                const field = fieldAt(info, path);
                if (field.storage === 'Cell') observations.ledgerEffects.push({ tag: 'writeCell', arguments: [fieldArgument(field.name), decodeABI(rt, field.type!, asCell(value))] });
                else {
                  const reconstructed = originAt(0);
                  if (reconstructed?.root === 'ledger' && JSON.stringify(reconstructed.path) === JSON.stringify(path)) {
                    // ins reinstalls the collection already changed by rem.
                  } else if (value.tag === 'map' && value.content.length === 0) observations.ledgerEffects.push({ tag: 'reset', arguments: [fieldArgument(field.name)] });
                  else reject('collection replacement is neither reconstruction nor reset');
                }
              } else if (path.length === 3) {
                const field = fieldAt(info, source.path);
                if (field.storage === 'Cell' || (field.storage === 'Set' && value.tag !== 'null')) reject('invalid collection insertion');
                observations.ledgerEffects.push({ tag: field.storage === 'Set' ? 'setInsert' : 'mapInsert', arguments: field.storage === 'Set'
                  ? [fieldArgument(field.name), decodeABI(rt, field.type!, key)]
                  : [fieldArgument(field.name), decodeABI(rt, field.key!, key), decodeABI(rt, field.value!, asCell(value))] });
              } else if (path.length === 1) {
                const reconstructed = originAt(0);
                if (reconstructed?.root !== 'ledger' || JSON.stringify(reconstructed.path) !== JSON.stringify(path)) reject('unaccounted ledger group replacement');
              } else reject('unaccounted ledger update');
            } else if (source && source.root !== 'ledger' && source.root !== 'derived' && i === 0) observations.otherRoots.push({ pc, root: source.root, path: [...source.path, key] });
            else if (!source && i === 0) reject('update without root provenance');
            depth += 2;
          }
          const parent = originAt(op.n * 2);
          origins.splice(origins.length - op.n * 2 - 1, op.n * 2 + 1, parent); break;
        }
        case 'rem': {
          const source = originAt(1);
          if (source?.root === 'ledger') {
            const field = fieldAt(info, source.path);
            if (field.storage !== 'Set') reject('account has no map removal operation');
            observations.ledgerEffects.push({ tag: 'setRemove', arguments: [fieldArgument(field.name), decodeABI(rt, field.type!, asCell(valueAt(0)))] });
          }
          origins.splice(origins.length - 2, 2, source); break;
        }
        case 'pop': origins.pop(); break;
        case 'addi': case 'subi': case 'neg': case 'type': case 'size': case 'new': case 'root':
          origins.splice(origins.length - 1, 1, undefined); break;
        case 'lt': {
          const left = originAt(1), right = originAt(0);
          const leftTime = left?.root === 'context' && left.path.length === 1 && natural(left.path[0]) === 2n;
          const rightTime = right?.root === 'context' && right.path.length === 1 && natural(right.path[0]) === 2n;
          if (leftTime || rightTime) observations.publicEffects.push({ tag: 'contextRead', arguments: [
            fieldArgument(leftTime ? 'blockTimeLessThan' : 'blockTimeGreaterThan'),
            { tag: 'nat', value: String(natural(asCell(valueAt(leftTime ? 0 : 1)))) },
          ] });
          if (!leftTime && !rightTime) reject('unaccounted comparison read');
          origins.splice(origins.length - 2, 2, { root: 'derived', path: [] }); break;
        }
        case 'eq': case 'and': case 'or': case 'add': case 'sub': case 'concat':
          origins.splice(origins.length - 2, 2, undefined); break;
        case 'log': return reject('account does not emit VM log instructions');
        case 'noop': case 'ckpt': break;
      }
    }
    if (origins.length !== stack.length()) reject('provenance stack mismatch');
    if (pc + 1 + skip > program.length) reject('branch past program');
    observations.publicEffects.push(...observations.ledgerEffects.slice(ledgerStart));
    observations.instructions.push({ pc, instruction: op, operands: before, resultStack: captureInstructionStacks ? snapshot(stack) : [], reads });
    pc += 1 + skip;
  }
  if (pendingCallerRead || origins.length !== 3 || origins[2]?.root !== 'ledger' || origins[2].path.length !== 0) reject('incomplete account observation');
  return observations;
}

/** Ledger and observable context projection, preserving their interleaving.
 * Asset declarations/private witness preimages are explicitly reported apart. */
export function compareAccountEffects(concrete: AccountObservations, model: AccountEffect[]): { ledgerMatches: boolean; publicMatches: boolean; unrepresented: AccountEffect[] } {
  const ledgerTags: Record<string, true> = { readCell: true, writeCell: true, mapMember: true, mapLookup: true, mapInsert: true, setMember: true, setInsert: true, setRemove: true, reset: true };
  return {
    ledgerMatches: JSON.stringify(concrete.ledgerEffects) === JSON.stringify(model.filter(e => Object.hasOwn(ledgerTags, e.tag))),
    publicMatches: JSON.stringify(concrete.publicEffects) === JSON.stringify(model.filter(e => Object.hasOwn(ledgerTags, e.tag) || e.tag === 'contextRead')),
    unrepresented: model.filter(e => !Object.hasOwn(ledgerTags, e.tag) && e.tag !== 'contextRead'),
  };
}

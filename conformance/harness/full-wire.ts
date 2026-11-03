// Canonical data boundary shared with Conformance.FullAccountTypes. ABI metadata
// controls only representation; it never supplies model transition semantics.
export type Value =
  | { tag: 'nat'; value: string }
  | { tag: 'bool'; value: boolean }
  | { tag: 'bytes'; value: number[] }
  | { tag: 'tuple'; value: Value[] }
  | { tag: 'none' }
  | { tag: 'some'; value: Value };
export interface TypeInfo {
  'type-name': string;
  length?: number;
  /** JSON number is used only to discriminate the four exact account widths. */
  maxval?: number;
  name?: string;
  elements?: { name: string; type: TypeInfo }[];
  types?: TypeInfo[];
}
export interface CircuitInfo {
  name: string; pure: boolean; proof: boolean;
  arguments: { name: string; type: TypeInfo }[];
  'result-type': TypeInfo;
}
export interface LedgerInfo {
  name: string; storage: 'Cell' | 'Map' | 'Set';
  type?: TypeInfo; key?: TypeInfo; value?: TypeInfo;
}
export interface AccountInfo {
  circuits: CircuitInfo[];
  ledger: LedgerInfo[];
  witnesses: unknown[];
  'compiler-version': string;
  'compiler-commit': string;
  'runtime-version': string;
}
export interface FullState { ledger: [string, Value][] }
export interface RawCall { name: string; arguments: Value[] }
export interface FullContext {
  self: Value; blockTime: string; caller: Value; heldCoin: Value;
}
export interface FullRequest { call: RawCall; context: FullContext; state: FullState }
export const nat = (n: bigint): Value => {
  if (n < 0n) throw new Error('negative model natural');
  return { tag: 'nat', value: String(n) };
};
export const bytes = (value: Uint8Array): Value => ({ tag: 'bytes', value: [...value] });
export const tuple = (value: Value[]): Extract<Value, { tag: 'tuple' }> => ({ tag: 'tuple', value });
const boolean = (value: boolean): Value => ({ tag: 'bool', value });
const field: TypeInfo = { 'type-name': 'Field' };
const flag: TypeInfo = { 'type-name': 'Boolean' };
export const bytesType = (length: number): TypeInfo => ({ 'type-name': 'Bytes', length });
export const qualifiedCoinType: TypeInfo = {
  'type-name': 'Struct', name: 'QualifiedShieldedCoinInfo', elements: [
    { name: 'nonce', type: bytesType(32) }, { name: 'color', type: bytesType(32) },
    { name: 'value', type: field }, { name: 'mt_index', type: field },
  ],
};
export const constructorInfo: CircuitInfo = {
  name: 'constructor', pure: false, proof: false,
  arguments: [
    { name: 'initial_device_boot', type: bytesType(32) },
    { name: 'encryption_key', type: bytesType(32) },
    { name: 'initial_recovery_pk', type: { 'type-name': 'JubjubPoint' } },
    { name: 'initial_recovery_wrap', type: bytesType(64) },
    { name: 'veto_window_seconds', type: { 'type-name': 'Uint' } },
  ],
  'result-type': { 'type-name': 'Tuple', types: [] },
};
function members(t: TypeInfo): { name: string; type: TypeInfo }[] {
  if (t['type-name'] === 'Struct') return t.elements!;
  if (t['type-name'] === 'JubjubPoint') return [{ name: 'x', type: field }, { name: 'y', type: field }];
  if (t['type-name'] === 'Secp256k1Point' || t['type-name'] === 'Secp256r1Point')
    return [{ name: 'x', type: field }, { name: 'y', type: field }, { name: 'identity', type: flag }];
  throw new Error(`not a compound ABI type: ${t['type-name']}`);
}
export function toValue(t: TypeInfo, v: unknown): Value {
  if (t['type-name'] === 'Struct' && ['ContractAddress', 'UserAddress', 'ZswapCoinPublicKey'].includes(t.name ?? '')) {
    if (v === null || typeof v !== 'object' || !('bytes' in v) || !(v.bytes instanceof Uint8Array)) throw new Error('invalid native address');
    return bytes(v.bytes);
  }
  switch (t['type-name']) {
    case 'Bytes':
      if (!(v instanceof Uint8Array)) throw new Error('expected ABI bytes');
      return bytes(v);
    case 'Boolean':
      if (typeof v !== 'boolean') throw new Error('expected ABI boolean');
      return boolean(v);
    case 'Field': case 'Uint': case 'Secp256k1Scalar': case 'Secp256r1Scalar':
      if (typeof v !== 'bigint') throw new Error(`expected ABI integer: ${t['type-name']}`);
      return nat(v);
    case 'Tuple':
      if (!Array.isArray(v) || v.length !== t.types!.length) throw new Error('ABI tuple arity mismatch');
      return tuple(t.types!.map((x, i) => toValue(x, v[i])));
    default:
      if (v === null || typeof v !== 'object') throw new Error('expected ABI compound value');
      return tuple(members(t).map(({ name, type }) => {
        if (!(name in v)) throw new Error(`missing ABI member ${name}`);
        return toValue(type, (v as Record<string, unknown>)[name]);
      }));
  }
}
export function fromValue(t: TypeInfo, v: Value): unknown {
  if (t['type-name'] === 'Struct' && ['ContractAddress', 'UserAddress', 'ZswapCoinPublicKey'].includes(t.name ?? ''))
    return { bytes: fromValue(bytesType(32), v) };
  switch (t['type-name']) {
    case 'Bytes':
      if (v.tag !== 'bytes' || v.value.some(x => !Number.isInteger(x) || x < 0 || x > 255)) throw new Error('invalid wire bytes');
      return Uint8Array.from(v.value);
    case 'Boolean':
      if (v.tag !== 'bool') throw new Error('invalid wire boolean');
      return v.value;
    case 'Field': case 'Uint': case 'Secp256k1Scalar': case 'Secp256r1Scalar':
      if (v.tag !== 'nat' || !/^(0|[1-9][0-9]*)$/.test(v.value)) throw new Error('invalid wire natural');
      return BigInt(v.value);
    case 'Tuple':
      if (v.tag !== 'tuple' || v.value.length !== t.types!.length) throw new Error('wire tuple arity mismatch');
      return t.types!.map((x, i) => fromValue(x, v.value[i]));
    default: {
      const fields = members(t);
      if (v.tag !== 'tuple' || v.value.length !== fields.length) throw new Error('wire struct arity mismatch');
      return Object.fromEntries(fields.map(({ name, type }, i) => [name, fromValue(type, v.value[i])]));
    }
  }
}
export function rawCall(info: CircuitInfo, args: unknown[]): RawCall {
  if (args.length !== info.arguments.length) throw new Error(`raw ${info.name} arity mismatch`);
  return { name: info.name, arguments: info.arguments.map(({ type }, i) => toValue(type, args[i])) };
}
const ordered = (xs: Value[]): Value[] => xs.sort((a, b) => JSON.stringify(a).localeCompare(JSON.stringify(b)));
export function observeLedger(info: AccountInfo, ledger: Record<string, unknown>): FullState {
  return { ledger: info.ledger.map(f => {
    const v = ledger[f.name];
    if (f.storage === 'Cell') return [f.name, toValue(f.type!, v)];
    if (v === null || typeof v !== 'object' || !(Symbol.iterator in v)) throw new Error(`noniterable ledger ${f.name}`);
    const items = [...v as Iterable<unknown>];
    if (f.storage === 'Set') return [f.name, tuple(ordered(items.map(x => toValue(f.type!, x))))];
    return [f.name, tuple(ordered(items.map(pair => {
      if (!Array.isArray(pair) || pair.length !== 2) throw new Error('invalid concrete map pair');
      return tuple([toValue(f.key!, pair[0]), toValue(f.value!, pair[1])]);
    })))];
  }) };
}
/** Map iteration order is not part of the public map abstraction. Nothing else
 * is discarded: zero-valued entries, inactive grants and absent Maybe payloads
 * remain observable. */
export function canonicalState(info: AccountInfo, state: FullState): FullState {
  const names = state.ledger.map(([name]) => name);
  if (new Set(names).size !== names.length || info.ledger.some(f => !names.includes(f.name)) || names.length !== info.ledger.length)
    throw new Error('model state does not expose the entire ledger');
  return { ledger: info.ledger.map(f => {
    const value = state.ledger.find(([name]) => name === f.name)![1];
    if (f.storage === 'Cell') return [f.name, value];
    if (value.tag !== 'tuple') throw new Error('invalid model collection');
    return [f.name, tuple(ordered([...value.value]))];
  }) };
}

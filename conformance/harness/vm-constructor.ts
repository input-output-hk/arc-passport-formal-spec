import { decodeInstruction, runtimeData, type Instruction } from './vm-account.ts';
import type { AccountInfo, TypeInfo, Value } from './full-wire.ts';
import type { AccountObservations } from './vm-observe.ts';
import type { FormalQuery } from './vm-formal.ts';

interface Query extends FormalQuery {
  query(program: unknown[], costModel: unknown, gasLimit?: unknown): QueryResult;
  runTranscript(transcript: unknown, costModel: unknown): Query;
  readonly effects: unknown;
  readonly state: unknown;
  readonly block: unknown;
  readonly comIndices: unknown;
  readonly address: string;
}
interface QueryResult {
  context: Query;
  events: { tag: string; content: unknown }[];
  gasCost: Record<'readTime' | 'computeTime' | 'bytesWritten' | 'bytesDeleted', bigint>;
}
export interface ConstructorRuntime {
  QueryContext: { prototype: Query };
}
export interface CapturedQuery {
  initial: Query;
  final: Query;
  program: unknown[];
  costModel: unknown;
  gas: QueryResult['gasCost'];
}
export interface ConstructorCapture<T> {
  result: T;
  queries: CapturedQuery[];
  initial: Query;
  final: Query;
  costModel: unknown;
  transcript: { gas: QueryResult['gasCost']; effects: unknown; program: unknown[] };
  allocation: unknown[];
  body: unknown[];
}
let capturing = false;

/** Capture the actual constructor's query calls; no source copy or model run.
 * The generated constructor does not return its local partialProofData. The
 * wrapper observes precisely the calls queryLedgerState makes, then restores
 * the original prototype even when the constructor throws. */
export async function captureConstructorQueries<T>(runtime: ConstructorRuntime, construct: () => Promise<T>): Promise<ConstructorCapture<T>> {
  if (capturing) throw new Error('constructor query capture is not reentrant');
  const prototype = runtime.QueryContext.prototype;
  const descriptor = Object.getOwnPropertyDescriptor(prototype, 'query');
  if (!descriptor || typeof descriptor.value !== 'function' || !descriptor.configurable) throw new Error('unsupported QueryContext.query prototype');
  const query = prototype.query;
  const queries: CapturedQuery[] = [];
  capturing = true;
  try {
    Object.defineProperty(prototype, 'query', { ...descriptor, value: function (this: Query, program: unknown[], costModel: unknown, gasLimit?: unknown): QueryResult {
      const result = query.call(this, program, costModel, gasLimit);
      const reads = result.events.filter(e => e.tag === 'read');
      let read = 0;
      const recorded = program.map(op => {
        if (op !== null && typeof op === 'object' && 'popeq' in op) {
          const body = op.popeq;
          if (body === null || typeof body !== 'object') throw new Error('invalid constructor popeq');
          if (read >= reads.length) throw new Error('constructor query has missing read event');
          return { popeq: { ...body, result: reads[read++].content } };
        }
        return op;
      });
      if (read !== reads.length) throw new Error('constructor query has surplus read events');
      recorded.forEach(decodeInstruction);
      queries.push({ initial: this, final: result.context, program: recorded, costModel, gas: result.gasCost });
      return result;
    } });
    const result = await construct();
    if (queries.length < 25) throw new Error('constructor allocation transcript is incomplete');
    const costModel = queries[0].costModel;
    const gas: QueryResult['gasCost'] = { readTime: 0n, computeTime: 0n, bytesWritten: 0n, bytesDeleted: 0n };
    for (let i = 0; i < queries.length; i++) {
      const q = queries[i];
      if (q.costModel !== costModel || (i > 0 && contextEncoding(q.initial) !== contextEncoding(queries[i - 1].final))) throw new Error('constructor query context discontinuity');
      for (const k of ['readTime', 'computeTime', 'bytesWritten', 'bytesDeleted'] as const) gas[k] += q.gas[k];
    }
    const initial = queries[0].initial, final = queries[queries.length - 1].final;
    // Declaration allocation is an independently checked compiler prefix, not
    // erased account effects. Body effects are compared with the model later.
    const allocation = queries.slice(0, 25).flatMap(q => q.program);
    const body = queries.slice(25).flatMap(q => q.program);
    checkAllocationShape(queries.slice(0, 25));
    return { result, queries, initial, final, costModel, transcript: { gas, effects: final.effects, program: [...allocation, ...body] }, allocation, body };
  } finally {
    Object.defineProperty(prototype, 'query', descriptor);
    capturing = false;
  }
}
function integer(op: Instruction): bigint {
  if (op.opcode !== 'push' || op.storage || op.value.tag !== 'cell' || op.value.content.value.length !== 1) throw new Error('invalid allocation field index');
  const bs = Buffer.from(op.value.content.value[0], 'hex');
  let n = 0n;
  for (let i = bs.length - 1; i >= 0; i--) n = (n << 8n) | BigInt(bs[i]);
  return n;
}
function checkAllocationShape(queries: CapturedQuery[]): void {
  for (let n = 0; n < 25; n++) {
    const ops = queries[n].program.map(decodeInstruction);
    const [index, key, value, leaf, parent] = ops;
    if (ops.length !== 5 || index.opcode !== 'idx' || index.cached || !index.pushPath || index.path.length !== 1
      || index.path[0].tag !== 'value' || index.path[0].value.value.length !== 1
      || value.opcode !== 'push' || !value.storage || leaf.opcode !== 'ins' || leaf.cached || leaf.n !== 1
      || parent.opcode !== 'ins' || !parent.cached || parent.n !== 1) throw new Error(`constructor allocation instruction drift at ${n}`);
    const group = integer({ opcode: 'push', storage: false, value: { tag: 'cell', content: index.path[0].value } });
    if (group !== BigInt(n < 10 ? 0 : 1) || integer(key) !== BigInt(n < 10 ? n : n - 10)) throw new Error('constructor allocation field order drift');
  }
}

function contextEncoding(query: Query): string {
  function encoded(state: unknown): unknown {
    if (state !== null && typeof state === 'object') {
      if ('state' in state) return encoded(state.state);
      if ('encode' in state && typeof state.encode === 'function') return state.encode();
    }
    throw new Error('invalid constructor query state');
  }
  return JSON.stringify(runtimeData([encoded(query.state), query.effects, query.block, query.comIndices, query.address]));
}

/** Allocation is a separate source-level declaration phase. Check its actual
 * values, not only field names, before comparing the constructor body journal. */
export function assertConstructorAllocation(info: AccountInfo, observed: AccountObservations): void {
  const names = [
    'round', 'enc_key', 'inbox', 'inbox_count', 'unshielded_balances', 'spec_version', 'devices', 'device_epoch', 'device_count', 'auth_nonce',
    'boot', 'booted', 'grants', 'grant_generation', 'recovery_pk', 'recovery_phi', 'recovery_phi_len', 'recovery_session', 'recovery_wrap', 'recovery_version', 'pending_recovery', 'pending_entry', 'pending_recovery_pk', 'pending_not_before', 'veto_window',
  ];
  function initial(type: TypeInfo): Value {
    switch (type['type-name']) {
      case 'Uint': case 'Field': return { tag: 'nat', value: '0' };
      case 'Boolean': return { tag: 'bool', value: false };
      case 'Bytes': return { tag: 'bytes', value: Array.from({ length: type.length! }, () => 0) };
      case 'JubjubPoint': return { tag: 'tuple', value: [{ tag: 'nat', value: '0' }, { tag: 'nat', value: '1' }] };
      default: throw new Error(`unsupported declaration initializer ${type['type-name']}`);
    }
  }
  const expected = names.map(name => {
    const field = info.ledger.find(f => f.name === name);
    if (!field) throw new Error(`missing constructor declaration ${name}`);
    const key: Value = { tag: 'bytes', value: [...Buffer.from(name, 'utf8')] };
    return field.storage === 'Cell' ? { tag: 'writeCell', arguments: [key, initial(field.type!)] } : { tag: 'reset', arguments: [key] };
  });
  if (JSON.stringify(observed.publicEffects) !== JSON.stringify(expected)) throw new Error('constructor declaration initialization mismatch');
}

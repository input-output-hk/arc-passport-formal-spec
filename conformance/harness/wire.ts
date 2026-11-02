// Version-one monitor data. Candidates are validated outside the core contract;
// only matching circuit executions become certified DSL transactions.
import { decodeState, encodeState, type LedgerView, type Point } from './impl.ts';

export type Variant = 'source' | 'corrected';
export type Outcome = { kind: 'accepted' } | { kind: 'rejected' } | { kind: 'aborted'; code: string };
/** Receiving contract instance identity; SELF is the distinct Bytes32 crypto address. */
export interface Context { account: bigint; time: bigint }
export type GateCall =
  | { kind: 'withdraw'; color: string; amount: bigint; recipient: string }
  | { kind: 'add' | 'remove'; entry: string }
  | { kind: 'rotate'; key: string }
  | { kind: 'publish'; recoveryPk: Point; session: string; phi: bigint[]; phiLen: bigint; wrap: string }
  | { kind: 'cancel' };
export interface Authorisation { pk: Point; useCounter: bigint; r: Point; s: bigint; grind: bigint }
export type RawCall =
  | { kind: 'deposit'; color: string; amount: bigint }
  | { kind: 'finalise' }
  | { kind: 'gated'; gate: GateCall; auth: Authorisation }
  | { kind: 'submit'; successor: Point; recoveryPk: Point; epoch: bigint; nonce: bigint; nowUpper: bigint;
      recoveryR: Point; recoveryS: bigint; successorR: Point; successorS: bigint; grind: bigint };
export type OperationName = keyof typeof OPERATIONS;
export type Atom = string | bigint | boolean | Point;
export type Result = { kind: 'count'; value: bigint } | { kind: 'flag'; value: boolean }
  | { kind: 'point'; value: Point } | { kind: 'bytes'; value: string } | { kind: 'unit' };
export type Event = { kind: 'op'; name: OperationName; args: Atom[]; result: Result }
  | { kind: 'publish'; value: bigint } | { kind: 'require'; bound: 'min' | 'max'; time: bigint };
export interface Candidate { account: bigint; buildState: LedgerView; call: RawCall; journal: Event[] }
export type Transition = { kind: 'invocation'; context: Context; call: RawCall; outcome: Outcome }
  | { kind: 'admission'; context: Context; candidate: Candidate; outcome: Outcome };
export interface Observation { variant: Variant; self: string; initial: LedgerView; transition: Transition; final: LedgerView }
export type Preparation = { kind: 'candidate'; candidate: Candidate } | { kind: 'aborted'; code: string };
type AtomKind = 'n' | 'b32' | 'b64' | 'flag' | 'point';
interface OperationSchema { args: readonly AtomKind[]; result: Result['kind'] }
const count = { args: [], result: 'count' } as const;
const unitN = { args: ['n'], result: 'unit' } as const;
const unitB = { args: ['b32'], result: 'unit' } as const;
const unitP = { args: ['point'], result: 'unit' } as const;
const OPERATIONS = {
  readNonce: count, readRound: count, readEpoch: count, readDeviceCount: count, readVetoWindow: count, readNotBefore: count,
  readBalance: { args: ['b32'], result: 'count' }, readPending: { args: [], result: 'flag' },
  deviceMember: { args: ['b32'], result: 'flag' }, balanceMember: { args: ['b32'], result: 'flag' },
  readRecoveryPk: { args: [], result: 'point' }, readPendingRecoveryPk: { args: [], result: 'point' },
  readSession: { args: [], result: 'bytes' }, readPendingEntry: { args: [], result: 'bytes' },
  writeBalance: { args: ['b32', 'n'], result: 'unit' }, insertDevice: unitB, removeDevice: unitB, setEncKey: unitB,
  resetDevices: { args: [], result: 'unit' }, writeNonce: unitN, writeRound: unitN, writeEpoch: unitN,
  writeDeviceCount: unitN, writeNotBefore: unitN, writePhiLen: unitN, writeRecoveryPk: unitP, writePendingRecoveryPk: unitP,
  writeSession: unitB, writePendingEntry: unitB, writePending: { args: ['flag'], result: 'unit' },
  insertPhi1: unitN, insertPhi2: unitN, insertPhi3: unitN, insertPhi4: unitN, writeWrap: { args: ['b64'], result: 'unit' },
} as const satisfies Record<string, OperationSchema>;

class Reader {
  at = 0;
  readonly tokens: string[];
  constructor(text: string) { this.tokens = text.trim().split(/\s+/); }
  token(): string { const t = this.tokens[this.at++]; if (t === undefined) throw new Error('truncated monitor input'); return t; }
  expect(t: string): void { if (this.token() !== t) throw new Error(`expected ${t}`); }
  nat(): bigint { const t = this.token(); if (!/^[0-9]+$/.test(t)) throw new Error(`invalid natural ${t}`); return BigInt(t); }
  bytes(size: number): string { const t = this.token(); if (!new RegExp(`^[0-9a-f]{${size * 2}}$`).test(t)) throw new Error(`invalid Bytes${size}`); return t; }
  flag(): boolean { const t = this.token(); if (t !== '0' && t !== '1') throw new Error('invalid flag'); return t === '1'; }
  point(): Point { return { x: this.nat(), y: this.nat() }; }
  state(): LedgerView { const [s, next] = decodeState(this.tokens, this.at); this.at = next; return s; }
  size(): number { const n = this.nat(); if (n > BigInt(this.tokens.length - this.at)) throw new Error('invalid sequence length'); return Number(n); }
  done(): void { if (this.at !== this.tokens.length) throw new Error('trailing monitor input'); }
}
function gate(r: Reader): GateCall {
  switch (r.token()) {
    case 'W': return { kind: 'withdraw', color: r.bytes(32), amount: r.nat(), recipient: r.bytes(32) };
    case 'A': return { kind: 'add', entry: r.bytes(32) };
    case 'R': return { kind: 'remove', entry: r.bytes(32) };
    case 'K': return { kind: 'rotate', key: r.bytes(32) };
    case 'P': return { kind: 'publish', recoveryPk: r.point(), session: r.bytes(32), phi: [r.nat(), r.nat(), r.nat(), r.nat()], phiLen: r.nat(), wrap: r.bytes(64) };
    case 'C': return { kind: 'cancel' };
    default: throw new Error('invalid gated call');
  }
}
function raw(r: Reader): RawCall {
  switch (r.token()) {
    case 'D': return { kind: 'deposit', color: r.bytes(32), amount: r.nat() };
    case 'F': return { kind: 'finalise' };
    case 'J': return { kind: 'gated', gate: gate(r), auth: { pk: r.point(), useCounter: r.nat(), r: r.point(), s: r.nat(), grind: r.nat() } };
    case 'U': return { kind: 'submit', successor: r.point(), recoveryPk: r.point(), epoch: r.nat(), nonce: r.nat(), nowUpper: r.nat(), recoveryR: r.point(), recoveryS: r.nat(), successorR: r.point(), successorS: r.nat(), grind: r.nat() };
    default: throw new Error('invalid raw call');
  }
}
const pt = (p: Point): string => `${p.x} ${p.y}`;
function encodeGate(g: GateCall): string {
  switch (g.kind) {
    case 'withdraw': return `W ${g.color} ${g.amount} ${g.recipient}`;
    case 'add': return `A ${g.entry}`;
    case 'remove': return `R ${g.entry}`;
    case 'rotate': return `K ${g.key}`;
    case 'publish': if (g.phi.length !== 4) throw new Error('publication requires four phi slots'); return `P ${pt(g.recoveryPk)} ${g.session} ${g.phi.join(' ')} ${g.phiLen} ${g.wrap}`;
    case 'cancel': return 'C';
  }
}
export function encodeCall(c: RawCall): string {
  switch (c.kind) {
    case 'deposit': return `D ${c.color} ${c.amount}`;
    case 'finalise': return 'F';
    case 'gated': return `J ${encodeGate(c.gate)} ${pt(c.auth.pk)} ${c.auth.useCounter} ${pt(c.auth.r)} ${c.auth.s} ${c.auth.grind}`;
    case 'submit': return `U ${pt(c.successor)} ${pt(c.recoveryPk)} ${c.epoch} ${c.nonce} ${c.nowUpper} ${pt(c.recoveryR)} ${c.recoveryS} ${pt(c.successorR)} ${c.successorS} ${c.grind}`;
  }
}
export function decodeCall(text: string): RawCall { const r = new Reader(text); const c = raw(r); r.done(); return c; }
function outcome(r: Reader): Outcome {
  switch (r.token()) {
    case 'ok': return { kind: 'accepted' };
    case 'refused': return { kind: 'rejected' };
    case 'fail': return { kind: 'aborted', code: r.token() };
    default: throw new Error('invalid outcome');
  }
}
export const encodeOutcome = (o: Outcome): string => o.kind === 'accepted' ? 'ok' : o.kind === 'rejected' ? 'refused' : `fail ${o.code}`;
export function decodeOutcome(text: string): Outcome { const r = new Reader(text); const o = outcome(r); r.done(); return o; }
function atom(r: Reader, k: AtomKind): Atom {
  switch (k) { case 'n': return r.nat(); case 'b32': return r.bytes(32); case 'b64': return r.bytes(64); case 'flag': return r.flag(); case 'point': return r.point(); }
}
function event(r: Reader): Event {
  switch (r.token()) {
    case 'publish': return { kind: 'publish', value: r.nat() };
    case 'require': { const bound = r.token(); if (bound !== 'min' && bound !== 'max') throw new Error('invalid time bound'); return { kind: 'require', bound, time: r.nat() }; }
    case 'op': {
      const name = r.token();
      if (!Object.hasOwn(OPERATIONS, name)) throw new Error(`unknown operation ${name}`);
      const op = name as OperationName;
      const schema: OperationSchema = OPERATIONS[op];
      const args = schema.args.map((k) => atom(r, k));
      r.expect(schema.result);
      let result: Result;
      switch (schema.result) {
        case 'count': result = { kind: 'count', value: r.nat() }; break;
        case 'flag': result = { kind: 'flag', value: r.flag() }; break;
        case 'point': result = { kind: 'point', value: r.point() }; break;
        case 'bytes': result = { kind: 'bytes', value: r.bytes(32) }; break;
        case 'unit': r.expect('-'); result = { kind: 'unit' }; break;
      }
      return { kind: 'op', name: op, args, result };
    }
    default: throw new Error('invalid journal event');
  }
}
function encodeAtom(a: Atom): string { return typeof a === 'object' ? pt(a) : typeof a === 'boolean' ? (a ? '1' : '0') : String(a); }
function encodeEvent(e: Event): string {
  switch (e.kind) {
    case 'publish': return `publish ${e.value}`;
    case 'require': return `require ${e.bound} ${e.time}`;
    case 'op': return ['op', e.name, ...e.args.map(encodeAtom), e.result.kind, e.result.kind === 'unit' ? '-' : encodeAtom(e.result.value)].join(' ');
  }
}
function candidate(r: Reader): Candidate {
  const account = r.nat(), buildState = r.state(), call = raw(r);
  r.expect('J'); const count = r.size();
  return { account, buildState, call, journal: Array.from({ length: count }, () => event(r)) };
}
export function encodeCandidate(c: Candidate): string { return `${c.account} ${encodeState(c.buildState)} ${encodeCall(c.call)} J ${c.journal.length}${c.journal.length ? ` ${c.journal.map(encodeEvent).join(' ')}` : ''}`; }
export function decodeCandidate(text: string): Candidate { const r = new Reader(text); const c = candidate(r); r.done(); return c; }
export function encodeObservation(o: Observation): string {
  const t = o.transition;
  const text = `monitor-v1 ${o.variant} ${o.self} ${encodeState(o.initial)} ${t.kind === 'invocation' ? 'call' : 'admit'} ${t.context.account} ${t.context.time} ${t.kind === 'invocation' ? encodeCall(t.call) : encodeCandidate(t.candidate)} ${encodeOutcome(t.outcome)} ${encodeState(o.final)}`;
  decodeObservation(text); // Reject malformed programmatically constructed values, not merely decoded text.
  return text;
}
export function decodeObservation(text: string): Observation {
  const r = new Reader(text); r.expect('monitor-v1');
  const variant = r.token(); if (variant !== 'source' && variant !== 'corrected') throw new Error('invalid variant');
  const self = r.bytes(32), initial = r.state(), tag = r.token();
  if (tag !== 'call' && tag !== 'admit') throw new Error('invalid transition');
  const context = { account: r.nat(), time: r.nat() };
  const payload = tag === 'call' ? { kind: 'invocation' as const, call: raw(r) } : { kind: 'admission' as const, candidate: candidate(r) };
  const transition: Transition = { ...payload, context, outcome: outcome(r) };
  const final = r.state(); r.done(); return { variant, self, initial, transition, final };
}
export function decodePreparation(text: string): Preparation {
  const r = new Reader(text); const tag = r.token();
  if (tag === 'candidate') { const c = candidate(r); r.done(); return { kind: 'candidate', candidate: c }; }
  if (tag === 'fail') { const code = r.token(); r.done(); return { kind: 'aborted', code }; }
  throw new Error(`invalid preparation response: ${text}`);
}

// Executable Compact adapter. Public state, output, declared native effects,
// Zswap inputs/outputs and VM transcripts are captured from the implementation.
// Local simulation does not authenticate coin ownership or construct a ZK proof.
import { createRequire } from 'node:module';
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { randomBytes } from 'node:crypto';
import { encodeRuntimeValue } from './concrete.ts';
import { FULL_IMPL_DIR, assertMainPins, type MainPins } from './full-pins.ts';
import {
  bytes, constructorInfo, observeLedger, qualifiedCoinType, rawCall, toValue, tuple,
  type AccountInfo, type CircuitInfo, type FullRequest, type FullState, type LedgerInfo, type TypeInfo, type Value,
} from './full-wire.ts';
import { decodeAccountTranscript, replayAccountTranscript } from './vm-account.ts';
import type { DecodedAccountTranscript } from './vm-account.ts';
import { interpretAccountTranscript } from './vm-observe.ts';
import type { AccountObservations, ObservableQuery, ObservationRuntime } from './vm-observe.ts';
import { assertConstructorAllocation, captureConstructorQueries } from './vm-constructor.ts';
import type { ConstructorRuntime } from './vm-constructor.ts';
import { observeNativeCommitments, type FormalVM, type FormalVMResult, type NativeCommitmentContext } from './vm-formal.ts';

export const rnd = (n = 32): Uint8Array => new Uint8Array(randomBytes(n));
export const hex = (b: Uint8Array): string => Buffer.from(b).toString('hex');
export type Module = Record<string, unknown>;
export function record(v: unknown, label = 'object'): Module {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) throw new Error(`expected ${label}`);
  return v as Module;
}
export function invoke(module: Module, name: string, ...args: unknown[]): unknown {
  const f = module[name];
  if (typeof f !== 'function') throw new Error(`missing implementation function ${name}`);
  return Reflect.apply(f, module, args);
}
function typeInfo(v: unknown): TypeInfo {
  const x = record(v, 'ABI type');
  if (typeof x['type-name'] !== 'string') throw new Error('missing ABI type name');
  const type: TypeInfo = { 'type-name': x['type-name'] };
  if (x['type-name'] === 'Uint') {
    if (typeof x.maxval !== 'number' || ![8, 32, 64, 128].some(bits => x.maxval === Number((1n << BigInt(bits)) - 1n)))
      throw new Error('unsupported account Uint metadata width');
    type.maxval = x.maxval;
  }
  if (x.length !== undefined) {
    if (!Number.isInteger(x.length) || typeof x.length !== 'number') throw new Error('invalid ABI length');
    type.length = x.length;
  }
  if (x.name !== undefined) {
    if (typeof x.name !== 'string') throw new Error('invalid ABI struct name');
    type.name = x.name;
  }
  if (x.elements !== undefined) type.elements = argumentsInfo(x.elements);
  if (x.types !== undefined) {
    if (!Array.isArray(x.types)) throw new Error('invalid ABI tuple');
    type.types = x.types.map(typeInfo);
  }
  return type;
}
function argumentsInfo(v: unknown): { name: string; type: TypeInfo }[] {
  if (!Array.isArray(v)) throw new Error('invalid ABI arguments');
  return v.map(a => {
    const x = record(a);
    if (typeof x.name !== 'string') throw new Error('invalid ABI argument name');
    return { name: x.name, type: typeInfo(x.type) };
  });
}
export function parseAccountInfo(v: unknown): AccountInfo {
  const x = record(v);
  if (!Array.isArray(x.circuits) || !Array.isArray(x.ledger) || !Array.isArray(x.witnesses)
    || typeof x['compiler-version'] !== 'string' || typeof x['compiler-commit'] !== 'string' || typeof x['runtime-version'] !== 'string')
    throw new Error('invalid account compiler metadata');
  const circuits: CircuitInfo[] = x.circuits.map(c => {
    const a = record(c);
    if (typeof a.name !== 'string' || typeof a.pure !== 'boolean' || typeof a.proof !== 'boolean') throw new Error('invalid circuit metadata');
    return { name: a.name, pure: a.pure, proof: a.proof, arguments: argumentsInfo(a.arguments), 'result-type': typeInfo(a['result-type']) };
  });
  const ledger: LedgerInfo[] = x.ledger.map(f => {
    const a = record(f);
    if (typeof a.name !== 'string' || (a.storage !== 'Cell' && a.storage !== 'Map' && a.storage !== 'Set')) throw new Error('invalid ledger metadata');
    return { name: a.name, storage: a.storage,
      ...(a.type === undefined ? {} : { type: typeInfo(a.type) }),
      ...(a.key === undefined ? {} : { key: typeInfo(a.key) }),
      ...(a.value === undefined ? {} : { value: typeInfo(a.value) }) };
  });
  return { circuits, ledger, witnesses: x.witnesses, 'compiler-version': x['compiler-version'],
    'compiler-commit': x['compiler-commit'], 'runtime-version': x['runtime-version'] };
}
export interface StateValue { encode(): unknown }
export interface ChargedState { state: StateValue }
export type AccountState = StateValue | ChargedState;
export function stateEncoding(state: unknown): unknown {
  const value = record(state, 'runtime state');
  if (typeof value.encode === 'function') return invoke(value, 'encode');
  if ('state' in value) return stateEncoding(value.state);
  throw new Error('expected StateValue or ChargedState');
}
export interface QueryContext extends ObservableQuery { state: AccountState; effects: unknown; runTranscript(program: unknown, costModel: unknown): QueryContext }
export interface ConcreteContext {
  callContext: { currentQueryContext: QueryContext; currentGasCost: unknown; currentPrivateState?: unknown; currentZswapLocalState?: unknown };
  callProofDataTrace: { circuitId: string; initialQueryContext: QueryContext; finalQueryContext: QueryContext; publicTranscript: unknown[]; zswapLocalState?: unknown }[];
  costModel: unknown;
}
export interface ConcreteResult { result: unknown; context: ConcreteContext; gasCost: unknown }
export type NativeExecutionObserver = (account: FullAccount, label: string, result: ConcreteResult) => void;
export interface ContractInstance {
  initialState(context: unknown, ...args: unknown[]): Promise<{ currentContractState: { data: AccountState }; currentPrivateState: unknown; currentZswapLocalState: unknown }>;
  impureCircuits: Record<string, (context: unknown, ...args: unknown[]) => Promise<ConcreteResult>>;
}
export interface WitnessObservation { name: 'held_coin'; color: Value; coin: Value }
export interface FullImplementation {
  root: string; runtime: Module; signer: Module; p256: Module; fixtures: Module; recovery: Module; witnesses: Module;
  contractModule: Module; contract: ContractInstance; info: AccountInfo; pins: MainPins; witnessCalls: WitnessObservation[];
}
export async function loadFullImplementation(root = FULL_IMPL_DIR): Promise<FullImplementation> {
  const require = createRequire(`${root}/package.json`);
  const load = (path: string) => import(pathToFileURL(path).href);
  const [runtime, contractModule, signer, p256, fixtures, recovery, witnesses] = await Promise.all([
    load(require.resolve('@midnight-ntwrk/compact-runtime')),
    load(`${root}/src/wallet/contract.ts`), load(`${root}/src/wallet/signer.ts`), load(`${root}/src/wallet/signer-p256.ts`),
    load(`${root}/src/tests/p256-fixtures.ts`), load(`${root}/src/wallet/recovery-gate.ts`), load(`${root}/src/wallet/witnesses.ts`),
  ]);
  const Constructor = contractModule.Contract;
  if (typeof Constructor !== 'function') throw new Error('missing generated account Contract');
  // Generated module namespaces carry this known in-process API; their byte
  // identities and all exported runtime entrypoints are checked immediately.
  const witnessCalls: WitnessObservation[] = [];
  const production = record(invoke(witnesses, 'makeWitnesses'));
  const observedWitnesses = { ...production, held_coin: (...args: unknown[]): unknown => {
    const result = invoke(production, 'held_coin', ...args);
    if (!Array.isArray(result) || result.length !== 2) throw new Error('invalid production held_coin result');
    if (!(args[1] instanceof Uint8Array)) throw new Error('invalid production held_coin color');
    witnessCalls.push({ name: 'held_coin', color: bytes(args[1]), coin: toValue(qualifiedCoinType, result[1]) });
    return result;
  } };
  const contract = Reflect.construct(Constructor, [observedWitnesses]) as ContractInstance;
  const info = parseAccountInfo(JSON.parse(readFileSync(`${root}/contracts/managed/account/compiler/contract-info.json`, 'utf8')));
  const pins = assertMainPins(root, info, Object.keys(contract.impureCircuits));
  return { root, runtime, contractModule, contract, info, pins, signer, p256, fixtures, recovery, witnesses, witnessCalls };
}
export interface ConcreteError { kind: 'assertion' | 'bounds' | 'decoding' | 'primitive' | 'witness' | 'runtime'; message: string; original: string }
export interface ConcreteAccepted {
  tag: 'accepted'; output: Value; state: FullState;
  stateValue: string; nativeEffects: string; zswap: string;
  vm: DecodedAccountTranscript | null; vmObservations: AccountObservations[]; runtimeReplay: boolean;
  formalVM: FormalVMResult[];
  nativeCommitments: NativeCommitmentContext[];
  constructorAllocation?: AccountObservations;
  transcripts: { circuit: string; program: string; effects: string; initialState: string; finalState: string }[];
}
export interface ConcreteRejected { tag: 'rejected'; error: ConcreteError; state: FullState; stateValue: string }
export type ConcreteOutcome = ConcreteAccepted | ConcreteRejected;
export interface FullObservation {
  label: string; environment: 'compact-runtime-simulator'; request: FullRequest;
  origin: 'reachable-history' | 'synthetic-represented-state';
  outcome: ConcreteOutcome; witnesses: WitnessObservation[];
}
function errorOf(error: unknown): ConcreteError {
  const original = error instanceof Error ? error.message : String(error);
  const assertion = /(?:failed assert|assertion failed|Assertion failed):?\s*(.*)/i.exec(original);
  if (assertion) return { kind: 'assertion', message: assertion[1].trim(), original };
  if (/held_coin witness:/.test(original)) return { kind: 'witness', message: original, original };
  if (/range error|out of range|result of (?:addition|subtraction)|overflow|cast from Field or Uint value to smaller Uint/i.test(original)) return { kind: 'bounds', message: original, original };
  if (/expected .*arguments|expected type|invalid.*argument|type error/i.test(original)) return { kind: 'decoding', message: original, original };
  return { kind: 'runtime', message: original, original };
}
export class FullAccount {
  origin: FullObservation['origin'] = 'reachable-history';
  state: AccountState | undefined;
  privateState: unknown;
  readonly address = rnd();
  readonly coinKey = rnd();
  time = 1_800_000_000;
  heldCoin: unknown = { nonce: new Uint8Array(32), color: new Uint8Array(32), value: 0n, mt_index: 0n };
  readonly observations: FullObservation[] = [];
  constructor(readonly impl: FullImplementation, readonly formalVM?: FormalVM,
    readonly observeExecution?: NativeExecutionObserver) {
    this.privateState = invoke(impl.witnesses, 'emptyCoinStore');
  }
  ledger(): Module {
    if (!this.state) throw new Error('account has not been constructed');
    return record(invoke(this.impl.contractModule, 'ledger', this.state), 'account ledger');
  }
  context(): FullRequest['context'] {
    return { self: bytes(this.address), blockTime: String(this.time), caller: { tag: 'none' }, heldCoin: toValue(qualifiedCoinType, this.heldCoin) };
  }
  async call(label: string, name: string, args: unknown[]): Promise<FullObservation> {
    const constructor = name === 'constructor';
    const info = constructor ? constructorInfo : this.impl.info.circuits.find(c => c.name === name && !c.pure);
    if (!info) throw new Error(`unknown full account circuit ${name}`);
    const pre = this.state ? observeLedger(this.impl.info, this.ledger()) : { ledger: [] };
    const witnessStart = this.impl.witnessCalls.length;
    const request: FullRequest = { call: rawCall(info, args), context: this.context(), state: pre };
    const preEncoded = this.state ? encodeRuntimeValue(stateEncoding(this.state)) : encodeRuntimeValue(undefined);
    let outcome: ConcreteOutcome;
    let circuitReturned = false;
    try {
      if (constructor) {
        const context = invoke(this.impl.runtime, 'createConstructorContext', this.privateState, { bytes: this.coinKey });
        // Native constructor queries are observed in memory; the generated
        // constructor/source/artifacts remain unchanged.
        const captured = await captureConstructorQueries(this.impl.runtime as unknown as ConstructorRuntime, async () => {
          const result = await this.impl.contract.initialState(context, ...args);
          circuitReturned = true;
          return result;
        });
        const result = captured.result;
        const runtime = this.impl.runtime as unknown as ObservationRuntime;
        const admitted = replayAccountTranscript(captured.initial, captured.transcript, captured.costModel);
        if (encodeRuntimeValue(stateEncoding(admitted.state)) !== encodeRuntimeValue(stateEncoding(result.currentContractState.data)))
          throw new Error('constructor original VM transcript replay differs from its result');
        const allocation = interpretAccountTranscript(runtime, captured.initial as unknown as ObservableQuery,
          captured.allocation, captured.costModel, this.impl.info);
        assertConstructorAllocation(this.impl.info, allocation);
        const body = interpretAccountTranscript(runtime, captured.queries[24].final as unknown as ObservableQuery,
          captured.body, captured.costModel, this.impl.info);
        const formalVM = this.formalVM ? [await this.formalVM.compare(captured.initial, captured.transcript.program, admitted)] : [];
        const nativeCommitments = [observeNativeCommitments(admitted, captured.final)];
        this.state = result.currentContractState.data;
        this.privateState = result.currentPrivateState;
        outcome = { tag: 'accepted', output: tuple([]), state: observeLedger(this.impl.info, this.ledger()),
          stateValue: encodeRuntimeValue(stateEncoding(this.state)), nativeEffects: encodeRuntimeValue(captured.final.effects),
          zswap: encodeRuntimeValue(result.currentZswapLocalState), vm: null, vmObservations: [body], runtimeReplay: true,
          constructorAllocation: allocation, formalVM, nativeCommitments,
          transcripts: [{ circuit: 'constructor', program: encodeRuntimeValue(captured.transcript.program),
            effects: encodeRuntimeValue(captured.transcript.effects), initialState: encodeRuntimeValue(stateEncoding(captured.initial.state)),
            finalState: encodeRuntimeValue(stateEncoding(captured.final.state)) }] };
      } else {
        if (!this.state) throw new Error('circuit before constructor');
        const context = invoke(this.impl.runtime, 'createCircuitContext', {
          circuitId: name, contractAddress: hex(this.address), coinPublicKeyOrZswapState: { bytes: this.coinKey },
          contractState: this.state, privateState: this.privateState, time: this.time,
        });
        const result = await this.impl.contract.impureCircuits[name](context, ...args);
        circuitReturned = true;
        this.observeExecution?.(this, label, result);
        const final = result.context.callContext;
        const output = toValue(info['result-type'], result.result);
        const vm = decodeAccountTranscript(context, result);
        const vmObservations: AccountObservations[] = [];
        const formalVM: FormalVMResult[] = [];
        const nativeCommitments: NativeCommitmentContext[] = [];
        for (const trace of result.context.callProofDataTrace) {
          const admitted = replayAccountTranscript(trace.initialQueryContext, {
            gas: final.currentGasCost, effects: trace.finalQueryContext.effects, program: trace.publicTranscript,
          }, result.context.costModel);
          if (encodeRuntimeValue(stateEncoding(admitted.state)) !== encodeRuntimeValue(stateEncoding(trace.finalQueryContext.state)))
            throw new Error('exact runtime transcript replay differs from concrete poststate');
          // This is the pinned runtime API, not unchecked external JSON.
          const runtime = this.impl.runtime as unknown as ObservationRuntime;
          vmObservations.push(interpretAccountTranscript(runtime, trace.initialQueryContext, trace.publicTranscript, result.context.costModel, this.impl.info));
          if (this.formalVM) formalVM.push(await this.formalVM.compare(trace.initialQueryContext, trace.publicTranscript, admitted));
          nativeCommitments.push(observeNativeCommitments(admitted, trace.finalQueryContext));
        }
        const transcripts = result.context.callProofDataTrace.map(trace => ({
          circuit: trace.circuitId, program: encodeRuntimeValue(trace.publicTranscript),
          effects: encodeRuntimeValue(trace.finalQueryContext.effects),
          initialState: encodeRuntimeValue(stateEncoding(trace.initialQueryContext.state)),
          finalState: encodeRuntimeValue(stateEncoding(trace.finalQueryContext.state)),
        }));
        this.state = final.currentQueryContext.state;
        if (final.currentPrivateState !== undefined) this.privateState = final.currentPrivateState;
        outcome = { tag: 'accepted', output, state: observeLedger(this.impl.info, this.ledger()),
          stateValue: encodeRuntimeValue(stateEncoding(this.state)), nativeEffects: encodeRuntimeValue(final.currentQueryContext.effects),
          zswap: encodeRuntimeValue(final.currentZswapLocalState), vm, vmObservations, runtimeReplay: true, formalVM, nativeCommitments, transcripts };
      }
    } catch (error: unknown) {
      if (circuitReturned) throw new Error(`post-execution validation failed for ${label} (${name})`, { cause: error });
      // Neither a failed builder's mutated scratch context nor its private
      // effects are installed as committed account state.
      outcome = { tag: 'rejected', error: errorOf(error), state: pre, stateValue: preEncoded };
    }
    const observation: FullObservation = { label, environment: 'compact-runtime-simulator', origin: this.origin, request, outcome,
      witnesses: this.impl.witnessCalls.slice(witnessStart) };
    this.observations.push(observation);
    return observation;
  }
  setCoin(coin: { nonce: Uint8Array; color: Uint8Array; value: bigint; mt_index: bigint }): void {
    this.heldCoin = coin;
    this.privateState = invoke(this.impl.witnesses, 'withCoin', this.privateState, { ...coin, mtIndex: coin.mt_index });
  }
}

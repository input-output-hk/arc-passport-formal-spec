// Native generated-circuit/ledger-VM evidence, deliberately not ledger adoption.
// Run with the pinned implementation's tsx loader; see docs/ledger-adoption-boundary.md.
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { createRequire } from 'node:module';
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { loadFullImplementation, stateEncoding } from './full-impl.ts';

const impl = await loadFullImplementation();
const require = createRequire(`${impl.root}/package.json`);
const native = await import(pathToFileURL(require.resolve('@midnightntwrk/ledger-v9')).href);
const rt = impl.runtime;
const address = '11'.repeat(32);
const coinKey = { bytes: new Uint8Array(32).fill(2) };
const color = new Uint8Array(32).fill(3);
const time = 1_800_000_000;
const privateState = impl.witnesses.emptyCoinStore();
const initial = await impl.contract.initialState(rt.createConstructorContext(privateState, coinKey),
  new Uint8Array(32).fill(4), new Uint8Array(32).fill(5),
  { x: 0n, y: 1n }, new Uint8Array(64).fill(6), 60n);
const s0 = initial.currentContractState.data;
const context = state => rt.createCircuitContext({ circuitId: 'deposit_unshielded',
  contractAddress: address, coinPublicKeyOrZswapState: coinKey,
  contractState: state, privateState, time });
const balance = state => {
  const ledger = impl.contractModule.ledger(state);
  return { round: ledger.round, balance: ledger.unshielded_balances.member(color)
    ? ledger.unshielded_balances.lookup(color) : 0n };
};
const serialize = x => JSON.stringify(x, (_, v) => typeof v === 'bigint' ? v.toString() :
  v instanceof Map ? [...v] : v instanceof Uint8Array ? Buffer.from(v).toString('hex') : v);
const unchanged = serialize(stateEncoding(s0));
const first = await impl.contract.impureCircuits.deposit_unshielded(context(s0), color, 7n);
const s1 = first.context.callContext.currentQueryContext.state;
const second = await impl.contract.impureCircuits.deposit_unshielded(context(s1), color, 11n);
const s2 = second.context.callContext.currentQueryContext.state;
assert.deepEqual(balance(s0), { round: 0n, balance: 0n });
assert.deepEqual(balance(s1), { round: 1n, balance: 7n });
assert.deepEqual(balance(s2), { round: 2n, balance: 18n });

const nativeContext = (state, block) => {
  const q = new native.QueryContext(new native.ChargedState(native.StateValue.decode(stateEncoding(state))), address);
  q.block = block;
  return q;
};
const observations = [];
for (const [label, result, predecessor, stale] of [
  ['first', first, s0, s1], ['second', second, s1, s0],
]) {
  assert.equal(result.context.callProofDataTrace.length, 1);
  const trace = result.context.callProofDataTrace[0];
  const transcript = { program: trace.publicTranscript, effects: trace.finalQueryContext.effects,
    gas: result.context.callContext.currentGasCost };
  const cost = native.CostModel.initialCostModel();
  const q = nativeContext(predecessor, trace.initialQueryContext.block);
  const replayed = q.runTranscript(transcript, cost);
  assert.equal(serialize(replayed.state.state.encode()), serialize(stateEncoding(trace.finalQueryContext.state)));
  let staleError;
  try { nativeContext(stale, trace.initialQueryContext.block).runTranscript(transcript, cost); }
  catch (e) { staleError = String(e); }
  assert.match(staleError ?? '', /mismatch between expected .* and actual .* read/);
  const partition = native.partitionTranscripts([
    new native.PreTranscript(nativeContext(predecessor, trace.initialQueryContext.block), trace.publicTranscript),
  ], native.LedgerParameters.initialParameters())[0];
  observations.push({ label, operations: trace.publicTranscript.length,
    nativeLedgerReplayMatchesGeneratedState: true, staleError,
    partition: partition.map(t => t === undefined ? null : { operations: t.program.length, effects: t.effects }) });
}
// The public runtime context constructor accepts caller/time supplied by its host.
// This demonstrates a trust boundary, NOT a forged ledger-authorized caller.
const suppliedCaller = { tag: 'contract', address: '22'.repeat(32) };
const hostContext = rt.createInitialQueryContext(s1, address, time + 999, undefined, suppliedCaller);
assert.deepEqual(hostContext.block.caller, suppliedCaller);
assert.equal(hostContext.block.secondsSinceEpoch, BigInt(time + 999));

const overflowPredecessor = serialize(stateEncoding(s1));
let overflowError;
try { await impl.contract.impureCircuits.deposit_unshielded(context(s1), color, (1n << 128n) - 1n); }
catch (e) { overflowError = String(e); }
assert.match(overflowError ?? '', /range|overflow|addition|cast/i);
assert.equal(serialize(stateEncoding(s0)), unchanged);
assert.equal(serialize(stateEncoding(s1)), overflowPredecessor);
assert.deepEqual(balance(s1), { round: 1n, balance: 7n });
const files = ['node_modules/@midnightntwrk/ledger-v9/ledger-v9.d.ts',
  'node_modules/@midnightntwrk/ledger-v9/midnight_ledger_wasm_v9_bg.wasm',
  'node_modules/@midnight-ntwrk/midnight-js-contracts/dist/index.js',
  'node_modules/@midnight-ntwrk/compact-runtime/dist/circuit-context.js'];
console.log(JSON.stringify({ schema: 1, environment: 'generated-circuit + native ledger-v9 QueryContext; no node/prover',
  implementationRevision: impl.pins.sourceRevision, node: process.version,
  versions: { compiler: impl.info['compiler-version'], runtime: impl.info['runtime-version'],
    ledger: JSON.parse(readFileSync(`${impl.root}/node_modules/@midnightntwrk/ledger-v9/package.json`)).version },
  sha256: Object.fromEntries(files.map(p => [p, createHash('sha256').update(readFileSync(`${impl.root}/${p}`)).digest('hex')])),
  states: [s0, s1, s2].map(balance), observations,
  hostContext: { suppliedCaller, observedCaller: hostContext.block.caller,
    suppliedTime: time + 999, observedTime: hostContext.block.secondsSinceEpoch },
  overflow: { error: overflowError, predecessorUnchanged: true },
  limits: ['No wellFormed/VerifiedTransaction/LedgerState.apply or network submission was exercised.',
    'Partition output is a native local observation; no fallible ledger application or authenticated context is asserted.',
    'No source-to-native refinement or proof-system soundness result follows.'] },
  (_, v) => typeof v === 'bigint' ? v.toString() : v instanceof Map ? [...v] : v, 2));

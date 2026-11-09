// Native partitioning and explicitly unauthenticated LedgerState.apply diagnostics.
// No proof, funding, finality or adoption claim is made by this runner.
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { createRequire } from 'node:module';
import { existsSync, readFileSync, writeFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { loadFullImplementation, stateEncoding, hex } from './full-impl.ts';
import { fullScenarios, grantPartitionPairs } from './full-scenarios.ts';
import { decodeRuntimeValue } from './concrete.ts';

const diagnostic = process.argv.includes('--diagnostic-apply');
const output = process.argv.find(x => x.startsWith('--output='))?.slice(9);
const impl = await loadFullImplementation();
const require = createRequire(`${impl.root}/package.json`);
const native = await import(pathToFileURL(require.resolve('@midnightntwrk/ledger-v9')).href);
const rt = impl.runtime;
const cost = native.CostModel.initialCostModel();
const params = native.LedgerParameters.initialParameters();
const stringify = (x, space) => JSON.stringify(x, (_, v) => typeof v === 'bigint' ? v.toString() :
  v instanceof Uint8Array ? hex(v) : v instanceof Map ? [...v] : v, space);
const hash = x => createHash('sha256').update(x).digest('hex');
const states = {}, captures = [], partitions = [], applications = [], schedules = [];
const applicationStates = new Map();
const snapshot = state => {
  const encoding = stateEncoding(state);
  const id = hash(stringify(encoding));
  if (!states[id]) {
    const ledger = impl.contractModule.ledger(rt.StateValue.decode(encoding));
    states[id] = Object.fromEntries(impl.info.ledger.map(f => [f.name,
      f.storage === 'Cell' ? ledger[f.name] : [...ledger[f.name]]]));
  }
  return id;
};
const query = (capture, state = capture.trace.initialQueryContext.state) => {
  let q = new native.QueryContext(new native.ChargedState(native.StateValue.decode(stateEncoding(state))), capture.address);
  q.block = capture.trace.initialQueryContext.block;
  for (const [commitment, index] of capture.trace.initialQueryContext.comIndices) q = q.insertCommitment(commitment, index);
  return q;
};
const pre = c => new native.PreTranscript(query(c), c.trace.publicTranscript);
const partition = cs => native.partitionTranscripts(cs.map(pre), params);
const effectsEmpty = () => new native.QueryContext(new native.ContractState().data, '00'.repeat(32)).effects;
function replayParts(c, parts) {
  let q = query(c);
  const before = snapshot(q.state), sections = [];
  for (let i = 0; i < 2; i++) {
    const t = parts[i];
    q.effects = effectsEmpty();
    if (t) q = q.runTranscript(t, cost);
    sections.push({ section: i === 0 ? 'guaranteed' : 'fallible', operations: t?.program.length ?? 0,
      state: snapshot(q.state), effects: t?.effects ?? null, gas: t?.gas ?? null });
  }
  assert.equal(snapshot(q.state), snapshot(c.trace.finalQueryContext.state));
  return { before, sections, complete: snapshot(q.state) };
}
function capture(account, label, result) {
  assert.equal(result.context.callProofDataTrace.length, 1);
  const trace = result.context.callProofDataTrace[0];
  const c = { label, circuit: trace.circuitId, address: hex(account.address), trace,
    zswap: result.context.callContext.currentZswapLocalState, time: account.time };
  c.parts = partition([c])[0];
  captures.push(c);
  let staleError;
  try { query(c, trace.finalQueryContext.state).runTranscript({ program: trace.publicTranscript,
    effects: trace.finalQueryContext.effects, gas: result.context.callContext.currentGasCost }, cost); }
  catch (e) { staleError = String(e); }
  assert.match(staleError ?? '', /mismatch between expected .* and actual .* read/);
  partitions.push({ label, circuit: c.circuit, address: c.address,
    transcriptHash: hash(stringify(trace.publicTranscript)), operations: trace.publicTranscript.length,
    checkpointFree: !trace.publicTranscript.includes('ckpt'),
    checkpoints: trace.publicTranscript.flatMap((op, i) => op === 'ckpt' ? [i] : []),
    ...replayParts(c, c.parts), staleError, localCoins: c.zswap });
}
const strictness = new native.WellFormedStrictness();
const strictnessRecord = s => Object.fromEntries(['enforceBalancing', 'verifyNativeProofs', 'verifyContractProofs', 'enforceLimits', 'verifySignatures'].map(k => [k, s[k]]));
const fullStrictness = strictnessRecord(strictness);
// This opt-in laboratory lane cannot establish authenticated adoption. Proofs
// are erased, balances are synthetic, and no fee funding is supplied.
if (diagnostic) {
  strictness.enforceBalancing = false;
  strictness.verifyNativeProofs = false;
  strictness.verifyContractProofs = false;
}
const coinInfo = coin => ({ nonce: hex(coin.nonce), type: hex(coin.color), value: coin.value });
const qualifiedCoin = coin => ({ ...coinInfo(coin), mt_index: coin.mt_index });
const encryptionKey = native.ZswapSecretKeys.fromSeed(new Uint8Array(32).fill(17)).encryptionPublicKey;
function seededLedger(c, state = c.trace.initialQueryContext.state, balanceOverride) {
  let chain = new native.ZswapChainState();
  for (const coin of c.zswap.inputs) {
    assert.equal(coin.mt_index, 0n, 'scenario uses one locally qualified coin');
    [chain] = chain.tryApply(native.ZswapOffer.fromOutput(native.ZswapOutput.newContractOwned(coinInfo(coin), 0, c.address)));
  }
  chain = chain.postBlockUpdate(new Date(c.time * 1000), 600n);
  const ledger = impl.contractModule.ledger(rt.StateValue.decode(stateEncoding(state)));
  const balances = balanceOverride ?? new Map([...ledger.unshielded_balances].map(([color, value]) => [{ tag: 'unshielded', raw: hex(color) }, value]));
  return new native.LedgerState('undeployed', chain).updateIndex(c.address,
    new native.ChargedState(native.StateValue.decode(stateEncoding(state))), balances);
}
function makeTx(cs, parts, segmentIds, state, { omitOffers = false } = {}) {
  let tx = native.Transaction.fromParts('undeployed');
  const intents = new Map(), shielded = new Map(), outputKeys = new Set();
  const addOffer = (segment, offer) => shielded.set(segment, shielded.has(segment) ? shielded.get(segment).merge(offer) : offer);
  for (let i = 0; i < cs.length; i++) {
    const c = cs[i], [g, f] = parts[i], id = segmentIds[i];
    const op = new native.ContractOperation();
    let intent = intents.get(id) ?? native.Intent.new(new Date((c.time + 600) * 1000));
    intent = intent.addCall(new native.ContractCallPrototype(c.address, c.circuit, op, g, f,
      c.trace.privateTranscriptOutputs, c.trace.input, c.trace.output, native.communicationCommitmentRandomness(), c.circuit));
    if (!omitOffers) {
      for (const [section, t] of [[0, g], [id, f]]) {
        if (!t) continue;
        const outputs = [...t.effects.claimedUnshieldedSpends].filter(([[, recipient]]) => recipient.tag === 'user')
          .map(([[type, recipient], value]) => ({ owner: recipient.address, type: type.raw, value }));
        if (outputs.length) {
          const key = section === 0 ? 'guaranteedUnshieldedOffer' : 'fallibleUnshieldedOffer';
          intent[key] = native.UnshieldedOffer.new([], [...(intent[key]?.outputs ?? []), ...outputs], []);
        }
        for (const coin of c.zswap.inputs) {
          const input = native.ZswapInput.newContractOwned(qualifiedCoin(coin), section, c.address, state.zswap);
          if (t.effects.claimedNullifiers.includes(input.nullifier)) addOffer(section, native.ZswapOffer.fromInput(input));
        }
        for (const { coinInfo: coin, recipient } of c.zswap.outputs) {
          const output = recipient.is_left ? native.ZswapOutput.new(coinInfo(coin), section, hex(recipient.left.bytes), encryptionKey)
            : native.ZswapOutput.newContractOwned(coinInfo(coin), section, hex(recipient.right.bytes));
          const key = `${section}:${output.commitment}`;
          if (!outputKeys.has(key) && (t.effects.claimedShieldedReceives.includes(output.commitment) || t.effects.claimedShieldedSpends.includes(output.commitment))) {
            addOffer(section, native.ZswapOffer.fromOutput(output));
            outputKeys.add(key);
          }
        }
      }
    }
    intents.set(id, intent);
  }
  for (const [id, intent] of intents) tx = tx.addIntent({ tag: 'specific', value: id }, intent);
  for (const [id, offer] of shielded) tx = tx.addZswapOffer(id === 0 ? { tag: 'guaranteedOnly' } : { tag: 'specific', value: id }, offer);
  return tx.eraseProofs();
}
function apply(label, cs, parts, segmentIds, state, options = {}) {
  let stage = 'assemble';
  const reference = options.referenceState ?? state;
  const before = snapshot(state.index(cs[0].address).data);
  const record = { label, evidenceLayer: 'proof-erased, fee-unbalanced synthetic ledger; NOT adoption',
    calls: cs.map((c, i) => ({ label: c.label, physicalSegment: segmentIds[i], builderBlock: c.trace.initialQueryContext.block,
      guaranteed: parts[i][0]?.program.length ?? 0, fallible: parts[i][1]?.program.length ?? 0 })),
    applicationBlock: cs[0].trace.initialQueryContext.block, before, strictness: strictnessRecord(strictness) };
  try {
    const tx = makeTx(cs, parts, segmentIds, reference, options);
    record.serializedTransactionSha256 = hash(tx.serialize());
    stage = 'wellFormed';
    const verified = tx.wellFormed(reference, strictness, new Date(cs[0].time * 1000));
    stage = 'apply';
    const block = cs[0].trace.initialQueryContext.block;
    const [next, result] = state.apply(verified, new native.TransactionContext(reference, block));
    stage = 'observeApplied';
    applicationStates.set(record, next);
    Object.assign(record, { stage: 'apply', result: result.type, error: result.error,
      rawSuccessfulSegments: result.successfulSegments, nativeResult: result.toString(),
      after: snapshot(next.index(cs[0].address).data), nativeBalanceBefore: state.index(cs[0].address).balance,
      nativeBalanceAfter: next.index(cs[0].address).balance, zswapFirstFreeBefore: state.zswap.firstFree,
      zswapFirstFreeAfter: next.zswap.firstFree,
      zswapHashBefore: hash(state.zswap.serialize()), zswapHashAfter: hash(next.zswap.serialize()),
      utxoHashBefore: hash(stringify([...state.utxo.utxos].map(x => stringify(x)).sort())),
      utxoHashAfter: hash(stringify([...next.utxo.utxos].map(x => stringify(x)).sort())),
      utxoCreated: [...next.utxo.delta(state.utxo)[0]], utxoRemoved: [...next.utxo.delta(state.utxo)[1]],
      accountStates: Object.fromEntries([...new Set(cs.map(c => c.address))].map(address => [address,
        { before: snapshot(state.index(address).data), after: snapshot(next.index(address).data) }])),
      events: result.events.map(e => ({ source: e.source, content: e.content })) });
  } catch (e) {
    if (stage === 'observeApplied') throw e;
    Object.assign(record, { stage, error: String(e), result: 'exception', after: before });
  }
  applications.push(record);
  return record;
}
function unchanged(r) {
  assert.equal(r.after, r.before, r.label);
  if (r.stage === 'apply') {
    assert.equal(stringify(r.nativeBalanceAfter), stringify(r.nativeBalanceBefore), r.label);
    assert.equal(r.zswapHashAfter, r.zswapHashBefore, r.label);
    assert.equal(r.utxoHashAfter, r.utxoHashBefore, r.label);
  }
}
function zeroOutput(c) {
  return c.parts.some(t => t && [...t.effects.claimedUnshieldedSpends.values()].includes(0n));
}
function expectStructuralRefusal(r) {
  assert.equal(r.stage, 'wellFormed', r.label);
  assert.equal(r.result, 'exception', r.label);
  assert.match(r.error, /zero-value utxo|claimed_unshielded_spends|all contract-associated|causality violation/, r.label);
  unchanged(r);
}
const evidence = { schema: 1, startedAt: new Date().toISOString(), implementationRevision: impl.pins.sourceRevision,
  node: process.version, versions: { compiler: impl.info['compiler-version'], runtime: impl.info['runtime-version'],
    ledger: JSON.parse(readFileSync(`${impl.root}/node_modules/@midnightntwrk/ledger-v9/package.json`)).version },
  fullValidation: { status: 'not-established', strictness: fullStrictness },
  diagnosticOptIn: diagnostic, partitions, applications, schedules, states };
if (output && existsSync(output)) {
  const previous = JSON.parse(readFileSync(output, 'utf8'));
  evidence.previousAttempts = [...(previous.previousAttempts ?? []), {
    startedAt: previous.startedAt, result: previous.result, failure: previous.failure,
    partitions: previous.partitions.length, applications: previous.applications.length,
    runnerSha256: previous.runnerSha256,
  }];
}
async function receiverCall(sender) {
  const sent = sender.zswap.outputs.find(o => !o.recipient.is_left && hex(o.recipient.right.bytes) !== sender.address);
  assert(sent, 'contract-recipient output missing');
  const address = hex(sent.recipient.right.bytes), circuit = 'deposit_shielded';
  const initial = captures.find(c => c.address === sender.address).trace.initialQueryContext.state;
  const context = rt.createCircuitContext({ circuitId: circuit, contractAddress: address,
    coinPublicKeyOrZswapState: { bytes: new Uint8Array(32).fill(19) },
    contractState: initial, privateState: impl.witnesses.emptyCoinStore(), time: sender.time });
  const result = await impl.contract.impureCircuits[circuit](context, sent.coinInfo, new Uint8Array(192).fill(23));
  return { label: `${sender.label}: receiving account deposit`, circuit, address, time: sender.time,
    trace: result.context.callProofDataTrace[0], zswap: result.context.callContext.currentZswapLocalState };
}
try {
  const suite = await fullScenarios(impl, undefined, capture);
  for (const x of suite.expectations) assert.equal(x.actual, x.expected, x.label);
  suite.observations.push(...await grantPartitionPairs(impl, capture));
  evidence.builderOutcomes = suite.observations.map(o => {
    const encoding = decodeRuntimeValue(o.outcome.stateValue);
    return { label: o.label, circuit: o.request.call.name, origin: o.origin, result: o.outcome.tag,
      state: encoding === undefined ? null : snapshot(rt.StateValue.decode(encoding)),
      ...(o.outcome.tag === 'rejected' ? { error: o.outcome.error } : {}) };
  });
  evidence.surface = { expected: impl.pins.surface.filter(x => x !== 'constructor'),
    partitioned: [...new Set(captures.map(c => c.circuit))].sort() };
  assert.deepEqual(evidence.surface.partitioned, [...evidence.surface.expected].sort());
  assert(partitions.every(p => p.checkpointFree && p.sections.filter(s => s.operations > 0).length === 1));
  const first = captures[0], firstBase = seededLedger(first);
  try {
    makeTx([first], [first.parts], [1], firstBase).wellFormed(firstBase, new native.WellFormedStrictness(), new Date(first.time * 1000));
    throw new Error('proof-erased full-validation control unexpectedly accepted');
  } catch (e) {
    assert(!String(e).includes('unexpectedly accepted'));
    evidence.fullValidation.negativeControl = { input: 'proof-erased activation, no deployed key or fee funding', error: String(e) };
  }
  for (const c of captures) {
    if (diagnostic) {
      const base = seededLedger(c);
      const ordered = apply(`${c.label}: ordered standalone`, [c], [c.parts], [1], base);
      const stale = apply(`${c.label}: stale standalone`, [c], [c.parts], [1], seededLedger(c, c.trace.finalQueryContext.state));
      if (zeroOutput(c) || c.circuit.startsWith('withdraw_shielded_to_contract')) {
        expectStructuralRefusal(ordered);
        expectStructuralRefusal(stale);
      } else {
        assert.equal(ordered.result, 'success', ordered.label);
        assert.equal(ordered.after, snapshot(c.trace.finalQueryContext.state), ordered.label);
        assert.equal(stale.result, c.parts[0] ? 'failure' : 'partialSuccess', stale.label);
        unchanged(stale);
      }
      if (c.circuit.startsWith('withdraw_'))
        expectStructuralRefusal(apply(`${c.label}: missing native offer`, [c], [c.parts], [1], base, { omitOffers: true }));
      if (c.circuit.startsWith('withdraw_unshielded') && !zeroOutput(c)) {
        const unfunded = apply(`${c.label}: mirror funded but native balance absent`, [c], [c.parts], [1],
          seededLedger(c, c.trace.initialQueryContext.state, new Map()));
        assert(['failure', 'partialSuccess'].includes(unfunded.result), unfunded.label);
        unchanged(unfunded);
      }
      if (c.circuit.startsWith('withdraw_shielded_with_') && ordered.result === 'success') {
        const after = applicationStates.get(ordered);
        const raced = after.updateIndex(c.address, query(c).state, base.index(c.address).balance);
        const spent = apply(`${c.label}: coin already spent, original public state`, [c], [c.parts], [1], raced, { referenceState: base });
        assert(['failure', 'partialSuccess'].includes(spent.result), spent.label);
        unchanged(spent);
      }
      if (c.circuit.startsWith('withdraw_shielded_to_contract')) {
        const receiver = await receiverCall(c), pair = [c, receiver], paired = partition(pair);
        const state = base.updateIndex(receiver.address, query(receiver).state, new Map());
        schedules.push({ label: `${c.label}: matching receiving account`, calls: pair.map((x, i) => ({ label: x.label, ...replayParts(x, paired[i]) })) });
        const matched = apply(`${c.label}: composed with actual receive`, pair, paired, [1, 1], state);
        if (matched.result === 'exception') expectStructuralRefusal(matched);
        else {
          assert.equal(matched.result, 'success', matched.label);
          for (const x of pair) assert.equal(matched.accountStates[x.address].after, snapshot(x.trace.finalQueryContext.state));
        }
      }
      if (c.label.endsWith('grant pair: spend 1') || c.label.endsWith(': append inbox')) {
        const twice = [c, c], paired = partition(twice);
        assert(paired.every(p => !p[0] && p[1]), 'duplicate probe must exercise real fallible partitions');
        const separate = apply(`${c.label}: competing stale calls in separate segments`, twice, paired, [1, 2], base);
        assert.equal(separate.result, 'partialSuccess', separate.label);
        assert.equal(separate.after, snapshot(c.trace.finalQueryContext.state), separate.label);
        separate.retainedCompleteCalls = [c.label];
        separate.failedCallWithNoPublicStateChange = `${c.label} (second prepared copy)`;
        const same = apply(`${c.label}: competing stale calls in one segment`, twice, paired, [1, 1], base);
        assert.equal(same.result, 'partialSuccess', same.label);
        unchanged(same);
      }
    }
  }
  // Whole-account batch partitioning can differ from independently partitioning
  // each call. Preserve every prefix, including failed calls' surviving halves.
  for (const address of new Set(captures.map(c => c.address))) {
    const cs = captures.filter(c => c.address === address);
    const parts = partition(cs);
    schedules.push({ label: `${cs[0].label.split(':')[0]} full builder history batch`,
      calls: cs.map((c, i) => ({ label: c.label, ...replayParts(c, parts[i]) })) });
    for (let i = 0; i + 1 < cs.length; i++) {
      const pair = cs.slice(i, i + 2);
      if (snapshot(pair[0].trace.finalQueryContext.state) !== snapshot(pair[1].trace.initialQueryContext.state)) continue;
      // Coinless pairs isolate ordering without fabricating multi-coin funding.
      if (pair.some(c => c.zswap.inputs.length || c.zswap.outputs.length)) continue;
      const paired = partition(pair);
      schedules.push({ label: `${pair[0].label} -> ${pair[1].label}`, calls: pair.map((c, j) => ({ label: c.label, ...replayParts(c, paired[j]) })) });
      if (diagnostic) {
        const base = seededLedger(pair[0]);
        const ordered = apply(`${pair[0].label}: ordered pair`, pair, paired, [1, 2], base);
        const reverse = apply(`${pair[0].label}: reordered physical segments`, pair, paired, [2, 1], base);
        for (const r of [ordered, reverse]) {
          if (r.result === 'exception') expectStructuralRefusal(r);
          else if (r.result === 'success') assert.equal(r.after, snapshot(pair[1].trace.finalQueryContext.state), r.label);
          else if (r.result === 'failure') unchanged(r);
          else {
            assert.equal(r.result, 'partialSuccess', r.label);
            assert.equal(r.after, snapshot(pair[0].trace.finalQueryContext.state), r.label);
            r.retainedCompleteCalls = [pair[0].label];
            r.failedCallWithNoPublicStateChange = pair[1].label;
          }
        }
      }
    }
  }
  evidence.result = 'PASS';
} catch (e) {
  evidence.result = 'FAIL';
  evidence.failure = e.stack ?? String(e);
  process.exitCode = 1;
} finally {
  evidence.completedAt = new Date().toISOString();
  evidence.sha256 = Object.fromEntries(['node_modules/@midnightntwrk/ledger-v9/ledger-v9.d.ts',
    'node_modules/@midnightntwrk/ledger-v9/midnight_ledger_wasm_v9_bg.wasm',
    'node_modules/@midnight-ntwrk/midnight-js-contracts/dist/index.js'].map(p => [p, hash(readFileSync(`${impl.root}/${p}`))]));
  evidence.runnerSha256 = hash(readFileSync(new URL(import.meta.url)));
  evidence.harnessSha256 = Object.fromEntries(['full-impl.ts', 'full-scenarios.ts'].map(p =>
    [p, hash(readFileSync(new URL(p, import.meta.url)))]));
  evidence.summary = {
    sourceInvocations: partitions.length, runtimeEntrypoints: evidence.surface?.partitioned.length,
    checkpointFree: partitions.filter(p => p.checkpointFree).length,
    whollyGuaranteed: partitions.filter(p => p.sections[0].operations > 0).length,
    whollyFallible: partitions.filter(p => p.sections[1].operations > 0).length,
    diagnosticAttempts: applications.length,
    results: Object.fromEntries(['success', 'partialSuccess', 'failure', 'exception'].map(result =>
      [result, applications.filter(a => a.result === result).length])),
    schedules: schedules.length,
  };
  evidence.limits = ['No ZK proof was generated or verified; no balanced/funded Passport transaction was applied.',
    'Synthetic per-call state/coin seeding is not deployment-rooted source history or authenticated holdings.',
    'VM partitions and diagnostic LedgerState.apply cannot establish consensus finality or universal complete-call serialization.'];
  const json = stringify(evidence, 2) + '\n';
  if (output) writeFileSync(output, json);
  console.log(stringify({ result: evidence.result, partitions: partitions.length, applications: applications.length,
    schedules: schedules.length, states: Object.keys(states).length, failure: evidence.failure, output }, 2));
}

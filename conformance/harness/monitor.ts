// Deterministic runtime-monitor, fixture and frozen-transcript checks. Run via the
// pinned gate or its tsx runner. Literal source/source and repaired/corrected are
// distinct runs; this file never applies the historical corrected projection.
import assert from 'node:assert/strict';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { Client, option, type Planned } from './driver.ts';
import {
  decodeRuntimeValue, encodeRuntimeValue, mutateConcreteBalance, mutateConcreteCell, replayConcrete, restoreState,
  type ConcreteSnapshot,
} from './concrete.ts';
import { consumeFixture, decodeFixture, encodeFixture, type ImplementationFixture } from './fixtures.ts';
import { canonical, hex, loadImpl, openAccount, projectState, REPAIRED, type Impl } from './impl.ts';
import { answerPrimitive, Model } from './model.ts';
import { Prng } from './prng.ts';
import { ReplayRunner, sameConcreteState, type FrozenCase, type ReplayResult } from './replay.ts';
import {
  decodeCall, decodeCandidate, decodeObservation, decodeOutcome, encodeCall, encodeCandidate, encodeObservation,
  type Event, type Observation, type RawCall, type Variant,
} from './wire.ts';

const impl = await loadImpl();
const model = new Model(impl);
const variant: Variant = REPAIRED ? 'corrected' : 'source';
const mode = process.argv[2] ?? 'checks';
const fixtures = option('fixtures', '');
const passed: string[] = [];
const saved: [string, ImplementationFixture][] = [];
function check(value: boolean, label: string): void { assert.ok(value, label); passed.push(label); }
async function expectError(action: () => unknown | Promise<unknown>, label: string): Promise<void> {
  let failed = false;
  try { await action(); } catch { failed = true; }
  check(failed, label);
}
async function roundtrip(name: string, fixture: ImplementationFixture): Promise<void> {
  const encoded = encodeFixture(fixture), decoded = decodeFixture(encoded);
  check(encodeFixture(decoded) === encoded, `${name}: fixture codec roundtrip`);
  const result = await consumeFixture(impl, model, decoded);
  check(result.conforms && result.expectedMatches, `${name}: supplied state and signed inputs execute and check`);
  saved.push([name, decoded]);
}
async function modelFixture(p: Planned, initial: ConcreteSnapshot): Promise<ImplementationFixture> {
  const pre = projectState(impl, restoreState(impl, initial));
  const answer = await model.step(variant, initial.address, initial.time, pre, p.request, p.bits);
  if (answer.kind !== 'answer') throw new Error(answer.text);
  let call = decodeCall(p.call);
  if (answer.sig) {
    const values = answer.sig.split(' ').map(BigInt);
    if (call.kind === 'gated') {
      assert.equal(values.length, 4);
      call = { ...call, auth: { ...call.auth, r: { x: values[0], y: values[1] }, s: values[2], grind: values[3] } };
    } else if (call.kind === 'submit') {
      assert.equal(values.length, 7);
      call = { ...call, recoveryR: { x: values[0], y: values[1] }, recoveryS: values[2],
        successorR: { x: values[3], y: values[4] }, successorS: values[5], grind: values[6] };
    } else throw new Error('unexpected model signature');
  }
  check(answer.restBits === 0, `${p.label}: independent wallet consumes exact coins`);
  return { schema: 'monitor-fixture-v1', initial, observation: { variant, self: initial.address, initial: pre,
    transition: { kind: 'invocation', context: { account: BigInt(initial.account), time: BigInt(initial.time) }, call, outcome: decodeOutcome(answer.settled) }, final: answer.post } };
}
async function requireAdmission(result: ReplayResult, transactionAccepted: boolean, label: string): Promise<void> {
  check(result.conforms, `${label}: Agda agrees with concrete frozen replay`);
  check(result.observation.transition.outcome.kind === (transactionAccepted ? 'accepted' : 'rejected'), `${label}: expected settlement`);
  if (!transactionAccepted) {
    check(canonical(result.observation.initial) === canonical(result.observation.final), `${label}: projected rejected atomicity`);
    check(sameConcreteState(impl, result.fixture.initial, result.state), `${label}: full rejected atomicity`);
  }
  await roundtrip(label, result.fixture);
}

try {
  if (mode === 'consume') {
    const path = process.argv[3];
    if (!path) throw new Error('monitor.ts consume FIXTURE.json');
    const result = await consumeFixture(impl, model, decodeFixture(await readFile(path, 'utf8')));
    console.log(JSON.stringify({ conforms: result.conforms, expectedMatches: result.expectedMatches,
      observation: encodeObservation(result.observation) }));
    if (!result.conforms || !result.expectedMatches) process.exitCode = 1;
  } else {
    if (mode !== 'checks') throw new Error('monitor.ts checks [--fixtures DIR] | consume FIXTURE.json');
    const prng = new Prng(0x4d4f4e49);
    const recovery = new impl.signer.JubjubDevice(impl.signer.randomJubjubScalar(() => prng.bytes(32)));
    const acct = await openAccount(impl, prng, { recoveryPk: recovery.pk, vetoWindow: 60n, time: 1_800_000_000 });
    const client = new Client(impl, acct, prng);
    const initial = acct.snapshot();
    const color = hex(prng.bytes(32));
    const deposit: RawCall = { kind: 'deposit', color, amount: 5n };

    // Model-side wallet/raw fixtures carry full supplied state and are consumed by
    // actual Compact code. No signatures are regenerated in the consumer.
    const depositFixture = await modelFixture(client.deposit('model-deposit', Buffer.from(color, 'hex'), 5n), initial);
    await roundtrip('model-deposit', depositFixture);
    await expectError(() => consumeFixture(impl, model, {
      ...depositFixture, observation: { ...depositFixture.observation, self: '00'.repeat(32) },
    }), 'fixture crypto domain must match concrete account address');
    check(await model.check({
      ...depositFixture.observation,
      transition: { ...depositFixture.observation.transition,
        context: { ...depositFixture.observation.transition.context, account: 7n } },
    }), 'invocation supports nonzero logical account identity');
    const rotated = client.gated('model-signed-rotate', { kind: 'rotate', key: prng.bytes(32) }, acct.owner);
    const signedFixture = await modelFixture(rotated, initial);
    await roundtrip('model-signed-rotate', signedFixture);
    const successor = client.device(), newRecovery = client.device();
    const submitPlan = client.submit('model-recovery-submit', { recoverySk: recovery.sk, successor,
      successorRecoveryPk: newRecovery.pk, nowUpper: BigInt(initial.time) + 10n });
    const recoveryFixture = await modelFixture(submitPlan, initial);
    await roundtrip('model-recovery-submit', recoveryFixture);

    const runner = new ReplayRunner(impl, model, initial, variant);
    const funded = await runner.invoke(deposit);
    check(funded.conforms, 'reachable funding invocation');
    const fundedState = runner.state;
    const frozen = await runner.freeze(deposit);
    check(encodeCandidate(decodeCandidate(encodeCandidate(frozen.candidate))) === encodeCandidate(frozen.candidate), 'frozen model candidate journal roundtrip');
    const same = await runner.admit(frozen);
    await requireAdmission(same, true, 'deposit-sameview');
    const repeated = await runner.admit(frozen);
    await requireAdmission(repeated, false, 'deposit-repeat-reachable');
    check(sameConcreteState(impl, runner.state, same.state), 'runner keeps actual state after refusal; no resynchronization');

    // Reachable interference changes both balance and round. The isolated field
    // controls below are explicitly synthetic, not claimed reachable histories.
    const interference = new ReplayRunner(impl, model, fundedState, variant);
    check((await interference.invoke(deposit)).conforms, 'reachable competing deposit invocation');
    await requireAdmission(await interference.admit(frozen), false, 'deposit-interference-reachable');
    const pre = projectState(impl, restoreState(impl, fundedState));
    const changedRound = mutateConcreteCell(impl, fundedState, 'round', pre.round + 1n);
    check(projectState(impl, restoreState(impl, changedRound)).round === pre.round + 1n, 'synthetic round fixture actually changes supplied concrete state');
    await requireAdmission(await new ReplayRunner(impl, model, changedRound, variant).admit(frozen), false, 'deposit-round-synthetic');
    const changedBalance = mutateConcreteBalance(impl, fundedState, color, 99n);
    check(projectState(impl, restoreState(impl, changedBalance)).balances.find(([c]) => c === color)?.[1] === 99n, 'synthetic balance fixture actually changes supplied concrete state');
    await requireAdmission(await new ReplayRunner(impl, model, changedBalance, variant).admit(frozen), false, 'deposit-balance-synthetic');
    const changedKey = mutateConcreteCell(impl, fundedState, 'encKey', hex(prng.bytes(32)));
    await requireAdmission(await new ReplayRunner(impl, model, changedKey, variant).admit(frozen), true, 'deposit-unrelated-key-synthetic');

    // Wrong observations are false, distinct from malformed transport/backend errors.
    const observation = same.observation;
    check(!(await model.check({ ...observation, final: { ...observation.final, round: observation.final.round + 1n } })), 'wrong accepted poststate is false');
    check(!(await model.check({ ...observation, transition: { ...observation.transition, outcome: { kind: 'rejected' } } })), 'wrong outcome is false');
    check(!(await model.check({ ...observation, transition: { ...observation.transition, outcome: { kind: 'aborted', code: 'overflow' } } })), 'admission cannot build-abort');
    check(!(await model.check({ ...repeated.observation, final: same.observation.initial })), 'wrong rejected poststate is false');
    const invalidCandidate = structuredClone(frozen.candidate);
    const readRound = invalidCandidate.journal.find((e) => e.kind === 'op' && e.name === 'readRound');
    assert.ok(readRound?.kind === 'op' && readRound.result.kind === 'count');
    readRound.result.value += 1n;
    const invalidRejected: Observation = { ...observation, final: observation.initial,
      transition: { kind: 'admission', context: observation.transition.context, candidate: invalidCandidate, outcome: { kind: 'rejected' } } };
    check(await model.check(invalidRejected), 'external candidate validation rejects invalid claimed journal');
    check(!(await model.check({ ...invalidRejected, transition: { ...invalidRejected.transition, outcome: { kind: 'accepted' } } })), 'invalid candidate cannot become a certified core transaction');
    check(!(await model.check({ ...invalidRejected, final: observation.final })), 'external validation rejection preserves the initial state');
    const abortedCandidate: Observation = { ...invalidRejected, transition: { kind: 'admission',
      context: observation.transition.context, candidate: { ...frozen.candidate, call: { kind: 'finalise' } }, outcome: { kind: 'rejected' } } };
    check(await model.check(abortedCandidate), 'aborting candidate execution is external admission rejection');
    check(!(await model.check({ ...abortedCandidate, transition: { ...abortedCandidate.transition,
      outcome: { kind: 'aborted', code: 'noPending' } } })), 'candidate validation failure is not an invocation build-abort');
    const accountMismatch: Observation = { ...invalidRejected, transition: { kind: 'admission',
      context: { ...observation.transition.context, account: 1n }, candidate: frozen.candidate, outcome: { kind: 'rejected' } } };
    check(await model.check(accountMismatch), 'frozen transaction account mismatch rejects');
    const nonzeroCandidate = { ...frozen.candidate, account: 7n };
    const nonzeroAdmission: Observation = { ...observation, transition: { kind: 'admission',
      context: { ...observation.transition.context, account: 7n }, candidate: nonzeroCandidate, outcome: { kind: 'accepted' } } };
    check(await model.check(nonzeroAdmission), 'certified target admits at the matching nonzero contract instance');
    check(!(await model.check({ ...nonzeroAdmission, transition: { ...nonzeroAdmission.transition,
      context: { ...nonzeroAdmission.transition.context, account: 0n } } })), 'certified target cannot admit at another contract instance');
    // Structural event fixtures cover ALL operations/result kinds, publication
    // and both time bounds. This synthetic journal is not reachable interference.
    const eventCases: Event[] = [];
    for (const name of ['readNonce', 'readRound', 'readEpoch', 'readDeviceCount', 'readVetoWindow', 'readNotBefore'] as const)
      eventCases.push({ kind: 'op', name, args: [], result: { kind: 'count', value: 2n } });
    eventCases.push({ kind: 'op', name: 'readBalance', args: [color], result: { kind: 'count', value: 5n } },
      { kind: 'op', name: 'readPending', args: [], result: { kind: 'flag', value: false } });
    for (const name of ['deviceMember', 'balanceMember'] as const)
      eventCases.push({ kind: 'op', name, args: [color], result: { kind: 'flag', value: true } });
    for (const name of ['readRecoveryPk', 'readPendingRecoveryPk'] as const)
      eventCases.push({ kind: 'op', name, args: [], result: { kind: 'point', value: recovery.pk } });
    for (const name of ['readSession', 'readPendingEntry'] as const)
      eventCases.push({ kind: 'op', name, args: [], result: { kind: 'bytes', value: color } });
    eventCases.push({ kind: 'op', name: 'writeBalance', args: [color, 6n], result: { kind: 'unit' } },
      { kind: 'op', name: 'resetDevices', args: [], result: { kind: 'unit' } });
    for (const name of ['insertDevice', 'removeDevice', 'setEncKey', 'writeSession', 'writePendingEntry'] as const)
      eventCases.push({ kind: 'op', name, args: [color], result: { kind: 'unit' } });
    for (const name of ['writeNonce', 'writeRound', 'writeEpoch', 'writeDeviceCount', 'writeNotBefore', 'writePhiLen', 'insertPhi1', 'insertPhi2', 'insertPhi3', 'insertPhi4'] as const)
      eventCases.push({ kind: 'op', name, args: [2n], result: { kind: 'unit' } });
    for (const name of ['writeRecoveryPk', 'writePendingRecoveryPk'] as const)
      eventCases.push({ kind: 'op', name, args: [recovery.pk], result: { kind: 'unit' } });
    eventCases.push({ kind: 'op', name: 'writePending', args: [false], result: { kind: 'unit' } },
      { kind: 'op', name: 'writeWrap', args: ['ab'.repeat(64)], result: { kind: 'unit' } },
      { kind: 'publish', value: 9n }, { kind: 'require', bound: 'min', time: 3n }, { kind: 'require', bound: 'max', time: 4n });
    const allEvents: Observation = { ...invalidRejected, transition: { kind: 'admission', context: observation.transition.context,
      candidate: { ...frozen.candidate, journal: eventCases }, outcome: { kind: 'rejected' } } };
    check(encodeObservation(await model.normalize(allEvents)) === encodeObservation(allEvents), 'every typed event form survives Agda/TS normalization');
    check(await model.check(allEvents), 'synthetic nonmatching full journal is rejected, not turned into a certificate');
    const encoded = encodeObservation(observation);
    check(encodeObservation(decodeObservation(encoded)) === encoded, 'observation typed codec roundtrip');
    check(encodeObservation(await model.normalize(observation)) === encoded, 'Agda canonical observation roundtrip');
    const alteredExpected = decodeFixture(encodeFixture(signedFixture));
    alteredExpected.observation.final.round += 1n;
    const mismatch = await consumeFixture(impl, model, alteredExpected);
    check(mismatch.conforms && !mismatch.expectedMatches, 'fixture retains wrong supplied expected result rather than repairing it');
    const wrongInitial = decodeFixture(encodeFixture(signedFixture));
    wrongInitial.observation.initial.round += 1n;
    await expectError(() => consumeFixture(impl, model, wrongInitial), 'supplied initial projection mismatch is an error, not redeployment');

    // Exercise every raw-call family through typed serialization, independent of
    // whether that input succeeds (withdraw/add/remove/publish/cancel are signed).
    const rawPlans = [rotated, submitPlan, client.finalise('finalise'), client.deposit('deposit', Buffer.from(color, 'hex'), 1n),
      client.gated('withdraw', { kind: 'withdraw', color: Buffer.from(color, 'hex'), amount: 1n, recipient: prng.bytes(32) }, acct.owner),
      client.gated('add', { kind: 'add', entry: prng.bytes(32) }, acct.owner),
      client.gated('remove', { kind: 'remove', entry: prng.bytes(32) }, acct.owner),
      client.gated('cancel', { kind: 'cancel' }, acct.owner),
      client.gated('publish', { kind: 'publish', p: { newRecoveryPk: newRecovery.pk, session: prng.bytes(32),
        phi: [1n, 2n, 3n, 0n], phiLen: 3n, wrap: prng.bytes(64) } }, acct.owner)];
    for (const plan of rawPlans) check(encodeCall(decodeCall(plan.call)) === plan.call, `raw call ${plan.label} roundtrip`);
    const aborted = await new ReplayRunner(impl, model, initial, variant).invoke({ kind: 'finalise' });
    check(aborted.conforms && aborted.observation.transition.outcome.kind === 'aborted', 'actual build-aborted invocation checks');
    check(sameConcreteState(impl, initial, aborted.state), 'actual build-aborted full state atomicity');
    await roundtrip('no-pending-build-abort', aborted.fixture);

    // Freeze the actual signed recovery transcript and replay its time dependency.
    const recoveryCall = recoveryFixture.observation.transition;
    assert.ok(recoveryCall.kind === 'invocation' && recoveryCall.call.kind === 'submit');
    const recoveryRunner = new ReplayRunner(impl, model, initial, variant);
    const recoveryFrozen = await recoveryRunner.freeze(recoveryCall.call);
    await requireAdmission(await recoveryRunner.admit(recoveryFrozen), true, 'signed-recovery-sameview');
    const late = { ...initial, time: Number(recoveryCall.call.nowUpper) + 1 };
    await requireAdmission(await new ReplayRunner(impl, model, late, variant).admit(recoveryFrozen), false, 'signed-recovery-time-conflict');
    const submitted = recoveryRunner.state;
    const pending = projectState(impl, restoreState(impl, submitted));
    const atDeadline = { ...submitted, time: Number(pending.pendingNotBefore) };
    const finaliser = new ReplayRunner(impl, model, atDeadline, variant);
    const finaliseFrozen = await finaliser.freeze({ kind: 'finalise' });
    await requireAdmission(await finaliser.admit(finaliseFrozen), true, 'recovery-finalise-deadline');
    await requireAdmission(await new ReplayRunner(impl, model, { ...submitted, time: atDeadline.time - 1 }, variant).admit(finaliseFrozen), false, 'recovery-finalise-too-early');

    // The runtime verifies VM reads (including time) but this negative control
    // demonstrates that supplied Effects are NOT authenticated by runTranscript.
    // This is not proof/coin/private-witness/full-ledger validation.
    const effectsData = decodeRuntimeValue(frozen.concrete.transcript);
    assert.ok(effectsData !== null && typeof effectsData === 'object' && 'effects' in effectsData);
    const effects = effectsData.effects;
    assert.ok(effects !== null && typeof effects === 'object' && 'unshieldedInputs' in effects && effects.unshieldedInputs instanceof Map);
    const input = effects.unshieldedInputs.entries().next().value;
    assert.ok(input && typeof input[1] === 'bigint');
    effects.unshieldedInputs.set(input[0], input[1] + 1n);
    const badEffects: FrozenCase = { ...frozen, concrete: { ...frozen.concrete, transcript: encodeRuntimeValue(effectsData) } };
    check(replayConcrete(impl, fundedState, badEffects.concrete).verdict.ok, 'coverage limit: runtime replay accepts changed declared effects');

    const malformed = [
      `${encoded} trailing`, encoded.replace('monitor-v1', 'monitor-v9'), encoded.replace(` ${observation.self} `, ' ff '),
      encoded.replace(` ${observation.initial.round} `, ' -1 '), encoded.replace(' J ', ' NOJ '),
      encoded.replace(' admit 0 ', ` admit ${initial.address} `),
    ];
    for (let i = 0; i < malformed.length; i++) {
      await expectError(() => model.request(`check ${malformed[i]}`), `malformed observation ${i} errors rather than false`);
      await expectError(() => decodeObservation(malformed[i]), `typed malformed observation ${i} rejected`);
    }
    const duplicate = structuredClone(observation);
    duplicate.initial.devices.push(duplicate.initial.devices[0]);
    await expectError(() => encodeObservation(duplicate), 'duplicate state device rejected');
    const backendThrow: Impl = { ...impl, rt: { ...impl.rt, ecMulGenerator: () => { throw new Error('injected backend failure'); } } };
    const backendMalformed: Impl = { ...impl, rt: { ...impl.rt, ecMulGenerator: () => ({ x: -1n, y: 0n }) } };
    for (const [label, backend] of [['exception', backendThrow], ['malformed', backendMalformed]] as const) {
      const broken = new Model(backend);
      try { await expectError(() => broken.check(signedFixture.observation), `primitive backend ${label} is error, not conformance false`); }
      finally { broken.close(); }
    }
    await expectError(() => answerPrimitive(impl, ['mulg', '-1']), 'oracle command rejects malformed natural');
    await expectError(() => answerPrimitive(impl, ['entry', 'ff', '1', '2', '3', '4']), 'oracle command rejects malformed bytes');
    await expectError(() => answerPrimitive(impl, ['mulg', '1', '2']), 'oracle command rejects trailing arguments');
    if (fixtures) {
      await mkdir(fixtures, { recursive: true });
      for (const [name, fixture] of saved) {
        await writeFile(join(fixtures, `${name}.json`), `${encodeFixture(fixture)}\n`, { flag: 'wx' });
        await writeFile(join(fixtures, `${name}.observation`), `${encodeObservation(fixture.observation)}\n`, { flag: 'wx' });
      }
    }
    console.log(`MONITOR_CHECKS PASS implementation=${REPAIRED ? 'repaired' : 'source'} variant=${variant} checks=${passed.length} rpc=${model.rpcCount}`);
    console.log('Coverage: concrete VM reads and changed time context. Negative control: changed declared Effects accepted, so no effects-authentication claim. No ZK verification, coin availability, private witness, full ledger, or Compact-to-Agda journal decoder/refinement claim. Synthetic controls are labelled; reachable interference executes real calls.');
  }
} finally { model.close(); }

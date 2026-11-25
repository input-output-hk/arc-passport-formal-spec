import assert from 'node:assert/strict';
import test from 'node:test';
import { FullAccount, invoke, loadFullImplementation, record } from './full-impl.ts';
import { decodeInstruction, replayAccountTranscript } from './vm-account.ts';
import { FormalVM } from './vm-formal.ts';
import { FullModel } from './full-model.ts';
import { compareNativeEffects } from './full-effects.ts';

test('formal and native replay reject a changed concrete membership read', async () => {
  const impl = await loadFullImplementation();
  const coinKey = { bytes: new Uint8Array(32).fill(7) };
  const deployed = await impl.contract.initialState(
    invoke(impl.runtime, 'createConstructorContext', invoke(impl.witnesses, 'emptyCoinStore'), coinKey),
    new Uint8Array(32).fill(1), new Uint8Array(32).fill(2),
    invoke(impl.runtime, 'ecMulGenerator', 1n), new Uint8Array(64).fill(3), 60n,
  );
  const context = invoke(impl.runtime, 'createCircuitContext', {
    circuitId: 'deposit_unshielded', contractAddress: Buffer.alloc(32, 6).toString('hex'),
    coinPublicKeyOrZswapState: coinKey, contractState: deployed.currentContractState.data,
    privateState: deployed.currentPrivateState, time: 1_800_000_000,
  });
  const result = await impl.contract.impureCircuits.deposit_unshielded(context, new Uint8Array(32).fill(4), 1000n);
  assert.equal(result.context.callProofDataTrace.length, 1);
  const trace = result.context.callProofDataTrace[0];
  const changed = structuredClone(trace.publicTranscript);
  const index = changed.findIndex(raw => {
    const op = decodeInstruction(raw);
    if (op.opcode !== 'popeq' || op.result.alignment.length !== 1) return false;
    const segment = record(op.result.alignment[0]);
    return segment.tag === 'atom' && record(segment.value).tag === 'bytes' && record(segment.value).length === 1;
  });
  assert(index >= 0, 'generated deposit must expose its membership result');
  const observed = record(record(changed[index]).popeq);
  const payload = record(observed.result).value;
  assert(Array.isArray(payload) && payload.length === 1 && payload[0] instanceof Uint8Array);
  assert(payload[0].length === 0 || (payload[0].length === 1 && payload[0][0] <= 1));
  payload[0] = payload[0].length === 0 || payload[0][0] === 0 ? Uint8Array.of(1) : new Uint8Array();
  decodeInstruction(changed[index]);

  const vm = new FormalVM();
  try {
    assert.equal((await vm.compare(trace.initialQueryContext, trace.publicTranscript, trace.finalQueryContext)).finalStackMatches, true);
    assert.equal((await vm.compare(trace.initialQueryContext, trace.publicTranscript, trace.initialQueryContext)).finalStackMatches, false);
    await assert.rejects(vm.compare(trace.initialQueryContext, changed, trace.finalQueryContext));
    assert.throws(() => replayAccountTranscript(trace.initialQueryContext, {
      gas: result.context.callContext.currentGasCost, effects: trace.finalQueryContext.effects, program: changed,
    }, result.context.costModel));
  } finally {
    vm.close();
  }
});

test('native output-index registration remains checked outside VM replay', async () => {
  const impl = await loadFullImplementation();
  const vm = new FormalVM(), model = new FullModel(impl);
  try {
    const account = new FullAccount(impl, vm);
    account.address.fill(6);
    account.coinKey.fill(7);
    const deployed = await account.call('deterministic deployment', 'constructor', [
      new Uint8Array(32).fill(1), new Uint8Array(32).fill(2),
      invoke(impl.runtime, 'ecMulGenerator', 1n), new Uint8Array(64).fill(3), 60n,
    ]);
    assert.equal(deployed.outcome.tag, 'accepted');
    const observation = await account.call('shielded output', 'deposit_shielded', [
      { nonce: new Uint8Array(32).fill(8), color: new Uint8Array(32).fill(4), value: 1000n },
      new Uint8Array(192).fill(9),
    ]);
    assert(observation.outcome.tag === 'accepted');
    const answer = await model.step(observation.request);
    assert(answer.tag === 'accepted');
    assert(observation.outcome.formalVM.every(result => result.finalStackMatches));
    assert.equal(compareNativeEffects(observation, answer.effects).matches, true);
    const altered = {
      ...observation,
      outcome: {
        ...observation.outcome,
        nativeCommitments: observation.outcome.nativeCommitments.map(context => ({
          ...context,
          after: context.after.map(([key, index]): [string, string] => [key, String(BigInt(index) + 1n)]),
        })),
      },
    };
    assert.equal(compareNativeEffects(altered, answer.effects).matches, false);
  } finally {
    model.close();
    vm.close();
  }
});

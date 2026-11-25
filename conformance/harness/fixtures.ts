import { canonical, projectState, settled, unhex, type Impl, type Verdict } from './impl.ts';
import { buildConcrete, replayConcrete, restoreState, type ConcreteExecution, type ConcreteSnapshot, type FrozenTranscript } from './concrete.ts';
import { Model } from './model.ts';
import { decodeObservation, decodeOutcome, encodeObservation, type Observation, type RawCall } from './wire.ts';

export interface ImplementationCall { circuit: string; args: unknown[] }
/** Calls are already signed. This adapter never invokes a wallet or draws randomness. */
export function implementationCall(c: RawCall): ImplementationCall {
  switch (c.kind) {
    case 'deposit': return { circuit: 'deposit_unshielded', args: [unhex(c.color), c.amount] };
    case 'finalise': return { circuit: 'recover_finalise', args: [] };
    case 'submit': return { circuit: 'recover_submit', args: [c.successor, c.recoveryPk, c.epoch, c.nonce, c.nowUpper,
      c.recoveryR, c.recoveryS, c.successorR, c.successorS, c.grind] };
    case 'gated': {
      const g = c.gate;
      let circuit: string, payload: unknown[];
      switch (g.kind) {
        case 'withdraw': circuit = 'withdraw_unshielded_with_jubjub'; payload = [unhex(g.color), g.amount, { bytes: unhex(g.recipient) }]; break;
        case 'add': circuit = 'add_device_with_jubjub'; payload = [unhex(g.entry)]; break;
        case 'remove': circuit = 'remove_device_with_jubjub'; payload = [unhex(g.entry)]; break;
        case 'rotate': circuit = 'rotate_enc_key_with_jubjub'; payload = [unhex(g.key)]; break;
        case 'publish': circuit = 'publish_recovery_session_with_jubjub'; payload = [g.recoveryPk, unhex(g.session), ...g.phi, g.phiLen, unhex(g.wrap)]; break;
        case 'cancel': circuit = 'recover_cancel_with_jubjub'; payload = []; break;
      }
      return { circuit, args: [...payload, c.auth.pk, c.auth.useCounter, c.auth.r, c.auth.s, c.auth.grind] };
    }
  }
}
export interface ImplementationFixture {
  schema: 'monitor-fixture-v1';
  observation: Observation;
  /** Complete supplied simulator state, not an instruction to redeploy. */
  initial: ConcreteSnapshot;
  /** Required for admission. Independent of observation.transition.candidate. */
  frozen?: FrozenTranscript;
}
export interface FixtureResult {
  observation: Observation;
  verdict: Verdict;
  post: ConcreteSnapshot;
  /** True when the actual observation conforms, including an accurate rejection or abort. */
  conforms: boolean;
  /** Supplied outcome/poststate are not replaced or silently corrected. */
  expectedMatches: boolean;
}
export function encodeFixture(fixture: ImplementationFixture): string {
  return JSON.stringify({ schema: fixture.schema, observation: encodeObservation(fixture.observation),
    initial: fixture.initial, frozen: fixture.frozen });
}
function snapshot(value: unknown): ConcreteSnapshot {
  if (value === null || typeof value !== 'object' || !('schema' in value) || value.schema !== 'compact-state-v1'
    || !('environment' in value) || value.environment !== 'default-simulator-v1'
    || !('address' in value) || typeof value.address !== 'string' || !/^[a-f0-9]{64}$/.test(value.address)
    || !('account' in value) || typeof value.account !== 'string' || !/^[0-9]+$/.test(value.account)
    || !('coinPublicKey' in value) || typeof value.coinPublicKey !== 'string' || !/^[a-f0-9]{64}$/.test(value.coinPublicKey)
    || !('time' in value) || typeof value.time !== 'number' || !Number.isSafeInteger(value.time) || value.time < 0
    || !('state' in value) || typeof value.state !== 'string') throw new Error('invalid supplied full-state fixture');
  return { schema: value.schema, environment: value.environment, address: value.address, account: value.account, coinPublicKey: value.coinPublicKey, time: value.time, state: value.state };
}
export function decodeFixture(text: string): ImplementationFixture {
  const data: unknown = JSON.parse(text);
  if (data === null || typeof data !== 'object' || !('schema' in data) || data.schema !== 'monitor-fixture-v1'
    || !('observation' in data) || typeof data.observation !== 'string' || !('initial' in data)) throw new Error('invalid monitor fixture');
  const observation = decodeObservation(data.observation), initial = snapshot(data.initial);
  let frozen: FrozenTranscript | undefined;
  if ('frozen' in data && data.frozen !== undefined) {
    const f = data.frozen;
    if (f === null || typeof f !== 'object' || !('schema' in f) || f.schema !== 'compact-transcript-v1'
      || !('circuit' in f) || typeof f.circuit !== 'string' || !('costModel' in f) || f.costModel !== 'initial'
      || !('build' in f) || !('builtPost' in f) || !('transcript' in f) || typeof f.transcript !== 'string') throw new Error('invalid frozen implementation transcript');
    frozen = { schema: f.schema, circuit: f.circuit, costModel: f.costModel, build: snapshot(f.build), builtPost: snapshot(f.builtPost), transcript: f.transcript };
  }
  if ((observation.transition.kind === 'admission') !== (frozen !== undefined)) throw new Error('admission requires frozen concrete transcript; invocation must not have one');
  return { schema: 'monitor-fixture-v1', observation, initial, frozen };
}

/** Executes exactly the supplied initial state, context, raw signatures and transcript. */
export async function consumeFixture(impl: Impl, model: Model, fixture: ImplementationFixture): Promise<FixtureResult> {
  const { observation: expected, initial } = fixture;
  const t = expected.transition;
  if (expected.self !== initial.address) throw new Error('fixture crypto domain disagrees with supplied concrete address');
  if (canonical(projectState(impl, restoreState(impl, initial))) !== canonical(expected.initial)) throw new Error('fixture full state disagrees with supplied model initial state');
  if (BigInt(initial.account) !== t.context.account || BigInt(initial.time) !== t.context.time) throw new Error('fixture context disagrees with supplied concrete context');
  let execution: ConcreteExecution;
  if (t.kind === 'admission') {
    if (!fixture.frozen) throw new Error('missing frozen concrete transcript');
    execution = replayConcrete(impl, initial, fixture.frozen);
  } else {
    const call = implementationCall(t.call);
    execution = await buildConcrete(impl, initial, call.circuit, call.args);
  }
  const actual: Observation = { ...expected, transition: { ...t, outcome: decodeOutcome(settled(execution.verdict)) },
    final: projectState(impl, restoreState(impl, execution.post)) };
  return {
    observation: actual, verdict: execution.verdict, post: execution.post,
    conforms: await model.check(actual),
    expectedMatches: canonical(actual.final) === canonical(expected.final)
      && JSON.stringify(actual.transition.outcome) === JSON.stringify(expected.transition.outcome),
  };
}

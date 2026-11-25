import { projectState, settled, type Impl } from './impl.ts';
import { buildConcrete, replayConcrete, restoreState, type ConcreteSnapshot, type FrozenTranscript } from './concrete.ts';
import { implementationCall, type ImplementationFixture } from './fixtures.ts';
import { Model } from './model.ts';
import { decodeOutcome, type Candidate, type Observation, type RawCall, type Variant } from './wire.ts';

export interface FrozenCase { candidate: Candidate; concrete: FrozenTranscript }
export interface ReplayResult { observation: Observation; conforms: boolean; state: ConcreteSnapshot; fixture: ImplementationFixture }
/** Separate from Runner's historical local-comparison/resynchronization behavior.
 * Each instance advances ONLY with concrete results. Admission consumes both frozen
 * artifacts as supplied; it does not call prepare, sign, or execute a circuit.
 */
export class ReplayRunner {
  private current: ConcreteSnapshot;
  constructor(readonly impl: Impl, readonly model: Model, initial: ConcreteSnapshot, readonly variant: Variant) {
    restoreState(impl, initial);
    this.current = { ...initial };
  }
  get state(): ConcreteSnapshot { return { ...this.current }; }
  async freeze(call: RawCall): Promise<FrozenCase> {
    const initial = this.current;
    const prepared = await this.model.prepare(this.variant, initial.address, BigInt(initial.account),
      projectState(this.impl, restoreState(this.impl, initial)), call);
    if (prepared.kind !== 'candidate') throw new Error(`model preparation aborted: ${prepared.code}`);
    const implementation = implementationCall(call);
    const built = await buildConcrete(this.impl, initial, implementation.circuit, implementation.args);
    if (!built.frozen) throw new Error(`concrete build aborted: ${settled(built.verdict)}`);
    return { candidate: prepared.candidate, concrete: built.frozen };
  }
  async invoke(call: RawCall): Promise<ReplayResult> {
    const initial = this.current, implementation = implementationCall(call);
    const execution = await buildConcrete(this.impl, initial, implementation.circuit, implementation.args);
    const observation: Observation = {
      variant: this.variant, self: initial.address, initial: projectState(this.impl, restoreState(this.impl, initial)),
      transition: { kind: 'invocation', context: { account: BigInt(initial.account), time: BigInt(initial.time) }, call, outcome: decodeOutcome(settled(execution.verdict)) },
      final: projectState(this.impl, restoreState(this.impl, execution.post)),
    };
    this.current = execution.post;
    const conforms = await this.model.check(observation);
    return { observation, conforms, state: this.state, fixture: { schema: 'monitor-fixture-v1', observation, initial } };
  }
  async admit(frozen: FrozenCase): Promise<ReplayResult> {
    const initial = this.current;
    const execution = replayConcrete(this.impl, initial, frozen.concrete);
    const observation: Observation = {
      variant: this.variant, self: initial.address, initial: projectState(this.impl, restoreState(this.impl, initial)),
      transition: { kind: 'admission', context: { account: BigInt(initial.account), time: BigInt(initial.time) }, candidate: frozen.candidate, outcome: decodeOutcome(settled(execution.verdict)) },
      final: projectState(this.impl, restoreState(this.impl, execution.post)),
    };
    this.current = execution.post;
    const conforms = await this.model.check(observation);
    return { observation, conforms, state: this.state,
      fixture: { schema: 'monitor-fixture-v1', observation, initial, frozen: frozen.concrete } };
  }
}

/** Comparing state contents ignores the fixture's block time, not any state field. */
export function sameConcreteState(impl: Impl, a: ConcreteSnapshot, b: ConcreteSnapshot): boolean {
  return restoreState(impl, a).toString() === restoreState(impl, b).toString();
}

// Run with the target package's tsx and FULL_IMPL_DIR / FULL_MODEL_BIN set.
// The report is executable correspondence evidence, never a proof of the
// compiler, runtime, cryptography, transaction validity, or coin ownership.
import { writeFileSync } from 'node:fs';
import { loadFullImplementation } from './full-impl.ts';
import type { ConcreteError } from './full-impl.ts';
import { FullModel } from './full-model.ts';
import type { ModelError, ModelOutcome } from './full-model.ts';
import { fullScenarios } from './full-scenarios.ts';
import { canonicalState } from './full-wire.ts';
import { assertMainPins } from './full-pins.ts';
import { compareAccountEffects } from './vm-observe.ts';
import { compareNativeEffects } from './full-effects.ts';
import { FormalVM } from './vm-formal.ts';

function equivalentError(concrete: ConcreteError, model: ModelError): boolean {
  if (concrete.kind === 'assertion') return model.kind === 'assertion' && concrete.message === model.message;
  if (/^type error:/.test(concrete.original)) return model.kind === 'decoding' && model.message === 'circuit arguments';
  const uint = /cast from Field or Uint value to smaller Uint value failed: [0-9]+ is greater than ([0-9]+)/.exec(concrete.original);
  if (uint) {
    const upper = BigInt(uint[1]) + 1n;
    let bits = 0n, n = upper;
    while (n > 1n && n % 2n === 0n) { bits++; n /= 2n; }
    return n === 1n && model.kind === 'bounds' && model.bits === String(bits);
  }
  const field = /exceeds maximum value ([0-9]+) of Field type/.exec(concrete.original);
  if (field) return model.kind === 'bounds' && model.bits === '255' && model.message === 'Bytes<32> as Field'
    && BigInt(field[1]) === 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000n;
  const byteWidth = /does not fit into ([0-9]+) bytes/.exec(concrete.original);
  if (byteWidth) return model.kind === 'bounds' && model.bits === String(BigInt(byteWidth[1]) * 8n);
  if (concrete.kind === 'decoding') return model.kind === 'decoding' && concrete.original.includes(model.message);
  if (concrete.kind === 'primitive') return model.kind === 'primitive' && concrete.message === model.message;
  return false;
}
const implementation = await loadFullImplementation();
const formalVM = new FormalVM();
const scenarios = await fullScenarios(implementation, formalVM).finally(() => formalVM.close());
const captureOnly = process.env.FULL_CAPTURE_ONLY === '1';
const model = captureOnly ? undefined : new FullModel(implementation);
const judged: { label: string; model?: ModelOutcome; reasons: string[]; compared: string[] }[] = [];
const coverage = new Map<string, { accepted: number; rejected: number }>();
try {
  for (const [index, observation] of scenarios.observations.entries()) {
    const name = observation.request.call.name;
    const count = coverage.get(name) ?? { accepted: 0, rejected: 0 };
    count[observation.outcome.tag]++;
    coverage.set(name, count);
    const reasons: string[] = [];
    const compared: string[] = [];
    const expected = scenarios.expectations[index];
    if (expected.expected !== observation.outcome.tag) reasons.push(`scenario expected ${expected.expected}, got ${observation.outcome.tag}`);
    if (expected.boundsBits) {
      const maximum = String((1n << BigInt(expected.boundsBits)) - 1n);
      if (observation.outcome.tag !== 'rejected' || !observation.outcome.error.original.endsWith(` is greater than ${maximum}`))
        reasons.push(`represented fixture did not reach the exact Uint${expected.boundsBits} cast bound`);
    }
    if (observation.outcome.tag === 'accepted') {
      compared.push('independent Agda VM execution and all native VM stack roots');
      if (observation.outcome.formalVM.length !== observation.outcome.transcripts.length)
        reasons.push('missing independent formal VM execution');
      if (observation.outcome.formalVM.some(result => !result.finalStackMatches))
        reasons.push('formal/native VM final stack mismatch');
      if (observation.outcome.nativeCommitments.length !== observation.outcome.transcripts.length
        || observation.outcome.nativeCommitments.some(context => !context.unchangedContextFields))
        reasons.push('native helper changed context outside commitment-index registration');
    }
    const answer = model ? await model.step(observation.request) : undefined;
    if (answer) {
      compared.push('accept/refuse');
      if (answer.tag !== observation.outcome.tag) reasons.push('accept/refuse mismatch');
      else if (answer.tag === 'rejected' && observation.outcome.tag === 'rejected') {
        compared.push(observation.outcome.error.kind === 'decoding' ? 'native ABI refusal category (original type detail retained)' : 'exact assertion or bounded cast domain');
        if (!equivalentError(observation.outcome.error, answer.error)) reasons.push('failure reason/domain mismatch');
        if (JSON.stringify(observation.outcome.state) !== JSON.stringify(observation.request.state)) reasons.push('refusal changed installed state');
      } else if (answer.tag === 'accepted' && observation.outcome.tag === 'accepted') {
        compared.push('entire ledger', 'exact output');
        if (JSON.stringify(canonicalState(implementation.info, answer.state)) !== JSON.stringify(canonicalState(implementation.info, observation.outcome.state))) reasons.push('full ledger mismatch');
        if (JSON.stringify(answer.output) !== JSON.stringify(observation.outcome.output)) reasons.push('circuit output mismatch');
        compared.push('exact original VM admission', 'public VM effects', 'declared native assets', 'actual production witnesses', 'Zswap descriptions');
        if (!observation.outcome.runtimeReplay) reasons.push('missing exact runtime VM replay');
        if (observation.outcome.vmObservations.length !== 1) reasons.push('unexpected multi-call trace');
        if (name === 'constructor' && !observation.outcome.constructorAllocation) reasons.push('missing separately checked constructor allocation');
        for (const concrete of observation.outcome.vmObservations) {
          const effects = compareAccountEffects(concrete, answer.effects);
          if (!effects.ledgerMatches) reasons.push('ordered concrete ledger effects mismatch');
          if (!effects.publicMatches) reasons.push('ordered concrete public/context effects mismatch');
        }
        reasons.push(...compareNativeEffects(observation, answer.effects).reasons);
      }
    }
    judged.push({ label: observation.label, ...(answer ? { model: answer } : {}), reasons, compared });
    console.log(`${String(index + 1).padStart(3)} ${name} ${observation.outcome.tag} ${reasons.length ? `DIVERGE: ${reasons.join('; ')}` : captureOnly ? 'captured' : 'agree'} — ${observation.label}`);
  }
} finally { model?.close(); }
const missing = implementation.pins.surface.filter(name => {
  const counts = coverage.get(name);
  return !counts || counts.accepted === 0 || counts.rejected === 0;
});
const failedScenarios = judged.filter(j => j.reasons.length > 0);
assertMainPins(implementation.root, implementation.info, Object.keys(implementation.contract.impureCircuits));
const report = {
  schema: 'passport-full-account-conformance-v1', target: implementation.pins.sourceRevision,
  identity: implementation.pins,
  mode: captureOnly ? 'implementation-capture-only' : 'executable-model-correspondence',
  evidenceBoundary: {
    environment: 'compact-runtime simulator', independentConcreteTranscripts: true,
    independentHashAndAtomEncoding: true, sharedCurveAndPoseidonRuntime: true,
    authenticatedTransactionAssets: false, zkProofsGenerated: false, onChainInclusion: false,
    constructorVmTranscript: true, constructorDeclarationAllocationSeparatelyChecked: true,
    independentFormalVMExecution: true, universalNativeVMRefinement: false,
    unavailableOnChainPrerequisite: 'Proof-server/key generation requires the Midnight SRS at srs.midnight.network:443; sandbox policy denied that connection during provisioning. Simulator execution does not use the SRS.',
  },
  coverage: Object.fromEntries([...coverage].sort(([a], [b]) => a.localeCompare(b))),
  missingSuccessfulOrRefusedCircuits: missing,
  modelPrimitiveCalls: model?.rpcCount ?? 0, modelPrimitiveFailures: model?.primitiveFailures ?? [],
  verdict: missing.length === 0 && failedScenarios.length === 0 ? captureOnly ? 'CAPTURED' : 'AGREE' : 'DIVERGE',
  observations: scenarios.observations.map((concrete, i) => ({ concrete, ...judged[i] })),
};
const reportPath = process.env.FULL_REPORT ?? 'full-account-report.json';
writeFileSync(reportPath, `${JSON.stringify(report)}\n`);
console.log(JSON.stringify({ verdict: report.verdict, target: report.target, circuits: coverage.size, observations: scenarios.observations.length,
  divergent: failedScenarios.length, missing, primitiveCalls: report.modelPrimitiveCalls, report: reportPath }));
process.exitCode = missing.length === 0 && failedScenarios.length === 0 ? 0 : 1;

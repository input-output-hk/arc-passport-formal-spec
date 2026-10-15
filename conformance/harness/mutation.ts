// Compile each mutant in an isolated copy: the user's model sources are never edited.
// Detection requires the intended verdict difference on both oracles, not an unrelated
// driver crash or a historical, annotated recovery divergence.

import { spawnSync } from 'node:child_process';
import { cpSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { join } from 'node:path';

import { IMPL_DIR } from './impl.ts';

interface Mutation { source: string; guard: string; mutant: string; driver: string; args: string[]; observation: RegExp }

const MUTATIONS: Record<string, Mutation> = {
  debit: {
    source: 'src/Conformance/Custody.agda',
    guard: 'assert (a ≤ᵇ bal) insufficientBalance',
    mutant: 'assert (a <ᵇ bal) insufficientBalance',
    driver: 'main.ts', args: ['--seed', '1', '--steps', '30'],
    observation: /withdraw .*full balance.*impl=ok.*O1=DIVERGE \(verdict model=fail insufficientBalance.*O2=REJECT/,
  },
  deadline: {
    source: 'src/Conformance/Recovery.agda',
    guard: 'perform (atChain (timeAtLeast notBefore))',
    mutant: 'pure tt',
    driver: 'recovery.ts', args: ['--implementation', 'source', '--variant', 'source', '--only', 'scenarios'],
    observation: /finalise at deadline - 1.*impl=refused.*model=ok.*O1=DIVERGE.*O2=REJECT/,
  },
};

const name = process.argv[2];
const m = MUTATIONS[name];
if (!m) throw new Error(`usage: mutation.ts <${Object.keys(MUTATIONS).join('|')}> [driver args]`);
const SPEC = fileURLToPath(new URL('../..', import.meta.url)).replace(/\/$/, '');
if (process.env.RECOVERY_IMPLEMENTATION === 'repaired') throw new Error('mutations run against the pinned source implementation');
const original = readFileSync(`${SPEC}/${m.source}`, 'utf8');
if (original.split(m.guard).length !== 2) throw new Error(`guard not found exactly once in ${m.source}`);
mkdirSync(`${SPEC}/.worktrees`, { recursive: true });
const workspace = mkdtempSync(`${SPEC}/.worktrees/conformance-mutation-`);
try {
  for (const entry of ['src', 'flake.nix', 'flake.lock', 'pagda.nix', 'arc-passport.agda-lib', '.pagda'])
    cpSync(join(SPEC, entry), join(workspace, entry), { recursive: true });
  writeFileSync(join(workspace, m.source), original.replace(m.guard, m.mutant));
  // Nix otherwise treats this nested copy as untracked files of the user's repository.
  for (const args of [
    ['init', '--quiet', '--initial-branch=recovery-mutation'],
    ['add', 'src', 'flake.nix', 'flake.lock', 'pagda.nix', 'arc-passport.agda-lib'],
  ]) {
    const setup = spawnSync('git', args, { cwd: workspace, encoding: 'utf8' });
    if (setup.error || setup.status !== 0) throw new Error(`isolated mutation repository setup failed: ${setup.error ?? setup.stderr}`);
  }
  console.log(`mutation ${name}: ${m.guard} → ${m.mutant} (${m.source}; isolated copy)`);
  const build = spawnSync(process.env.PAGDA_BIN ?? 'pagda', [
    '--useUntracked', 'false', 'check', 'src/Conformance/Main.agda', '--',
    '--compile', '--compile-dir=_build/conformance-mutant', '--ghc-flag=-O0', '+RTS', '-M3G', '-H1G', '-RTS',
  ], { cwd: workspace, env: { ...process.env, LC_ALL: 'C.UTF-8' }, encoding: 'utf8', timeout: 1_800_000, maxBuffer: 1 << 28 });
  const buildOutput = `${build.stdout ?? ''}${build.stderr ?? ''}`;
  if (build.error || build.status !== 0 || /ModuleDoesntExport|UselessPublic|UselessPrivate|DuplicateUsing/.test(buildOutput))
    throw new Error(`mutant build failed (${build.status}): ${build.error ?? ''}\n${buildOutput}`);
  const extra = process.argv.slice(3);
  const run = spawnSync(`${IMPL_DIR}/node_modules/.bin/tsx`, [
    fileURLToPath(new URL(`./${m.driver}`, import.meta.url)), ...(extra.length > 0 ? extra : m.args),
  ], {
    env: { ...process.env, MODEL_BIN: `${workspace}/_build/conformance-mutant/Main`, RECOVERY_IMPLEMENTATION: 'source' },
    encoding: 'utf8', maxBuffer: 1 << 28, timeout: 1_800_000,
  });
  process.stdout.write(run.stdout ?? '');
  process.stderr.write(run.stderr ?? '');
  if (run.error || run.signal) throw new Error(`mutation driver failed: ${run.error ?? run.signal}`);
  const intended = (run.stdout ?? '').split('\n').filter((l) => m.observation.test(l));
  const detected = run.status === 1 && intended.length > 0;
  console.log(detected
    ? `MUTATION DETECTED ${name}: ${intended.length} intended step(s) diverge on both oracles`
    : `MUTATION MISSED ${name} (driver exit ${run.status}, ${intended.length} intended observations)`);
  process.exitCode = detected ? 0 : 1;
} finally {
  rmSync(workspace, { recursive: true, force: true });
  console.log('isolated mutation workspace removed; original model untouched');
}

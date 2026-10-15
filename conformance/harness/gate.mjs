#!/usr/bin/env node
// Recovery conformance gate; all implementation/model/tool paths are explicit.
// `pin` is trusted enrollment of a reviewed snapshot constrained by recovery-pins.json,
// not authorization to bless arbitrary source or dependencies. `run` revalidates the
// lock, recompiles pinned contracts, then executes source/repaired attack histories
// and isolated deadline/debit mutations. Simulator evidence is not deployment proof.
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { accessSync, constants, mkdirSync, mkdtempSync, readFileSync, readdirSync, realpathSync, rmSync, statSync, writeFileSync } from 'node:fs';
import { dirname, join, relative, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const HARNESS = dirname(fileURLToPath(import.meta.url));
const SPEC = resolve(HARNESS, '../..');
const BASE = JSON.parse(readFileSync(join(HARNESS, 'recovery-pins.json'), 'utf8'));
const HELP = 'gate.mjs <pin|run> --source CONTRACT_DIR --repaired CONTRACT_DIR --model MODEL_BIN --compiler COMPACTC --pagda PAGDA '
  + '(pin: --repair-sha256 SHA256 --output LOCK.json; run: --pins LOCK.json)';
const [mode, ...args] = process.argv.slice(2);
if (!['pin', 'run'].includes(mode)) throw new Error(HELP);
const options = {};
const allowed = ['source', 'repaired', 'model', 'compiler', 'pagda', ...(mode === 'pin' ? ['repair-sha256', 'output'] : ['pins'])];
for (let i = 0; i < args.length; i += 2) {
  const key = args[i]?.replace(/^--/, '');
  if (!args[i]?.startsWith('--') || !allowed.includes(key) || !args[i + 1] || args[i + 1].startsWith('--') || options[key])
    throw new Error(HELP);
  options[key] = args[i + 1];
}
for (const key of allowed) if (!options[key]) throw new Error(`missing --${key}; ${HELP}`);
if (process.env.IMPL_DIR || process.env.MODEL_BIN || process.env.RECOVERY_IMPLEMENTATION)
  throw new Error('unset IMPL_DIR, MODEL_BIN and RECOVERY_IMPLEMENTATION; gate inputs must be explicit');
const paths = Object.fromEntries(['source', 'repaired', 'model', 'compiler', 'pagda'].map((key) => [key, realpathSync(resolve(options[key]))]));
for (const key of ['model', 'compiler', 'pagda']) accessSync(paths[key], constants.X_OK);
if (paths.source === paths.repaired) throw new Error('source and repaired implementations must be distinct');

const sha = (bytes) => createHash('sha256').update(bytes).digest('hex');
const fileHash = (path) => sha(readFileSync(path));
const treeCache = new Map();
function treeHash(root, sourceOnly = false) {
  root = realpathSync(root);
  const cacheKey = `${root}:${sourceOnly}`;
  if (treeCache.has(cacheKey)) return treeCache.get(cacheKey);
  const rows = [];
  function walk(path) {
    for (const entry of readdirSync(path, { withFileTypes: true }).sort((a, b) => a.name < b.name ? -1 : a.name > b.name ? 1 : 0)) {
      const child = join(path, entry.name);
      if (sourceOnly) {
        if (entry.isDirectory()) walk(child);
        else if (/\.(agda|lagda(?:\.md|\.rst|\.tex)?)$/.test(entry.name))
          rows.push([relative(root, child).split('\\').join('/'), fileHash(child)]);
      } else if (statSync(child).isDirectory()) walk(child);
      else rows.push([relative(root, child).split('\\').join('/'), fileHash(child)]);
    }
  }
  walk(root);
  if (!rows.length) throw new Error(`empty fingerprint input ${root}`);
  rows.sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0);
  const result = sha(rows.map(([name, digest]) => `${name}\0${digest}\n`).join(''));
  treeCache.set(cacheKey, result);
  return result;
}
function command(bin, args, cwd, env = process.env, capture = false) {
  const result = spawnSync(bin, args, { cwd, env, encoding: 'utf8', stdio: capture ? 'pipe' : 'inherit', timeout: 1_800_000, maxBuffer: 1 << 28 });
  if (result.error || result.status !== 0)
    throw new Error(`${bin} ${args.join(' ')} failed (${result.status}): ${result.error ?? result.signal ?? ''}\n${capture ? `${result.stdout ?? ''}${result.stderr ?? ''}` : ''}`);
  return result.stdout?.trim();
}
function equal(label, actual, expected) {
  if (JSON.stringify(actual) !== JSON.stringify(expected))
    throw new Error(`pin mismatch: ${label}\nexpected ${JSON.stringify(expected)}\nactual   ${JSON.stringify(actual)}`);
}
function implementation(root, role) {
  const revision = command('git', ['-C', root, 'rev-parse', 'HEAD'], SPEC, process.env, true);
  command('git', ['-C', root, 'merge-base', '--is-ancestor', BASE.sourceRevision, revision], SPEC);
  const source = Object.fromEntries(Object.keys(BASE.source).map((name) => [name, fileHash(join(root, name))]));
  const signing = treeHash(join(root, 'src/wallet'));
  const dependencies = treeHash(join(root, 'node_modules'));
  const managed = Object.fromEntries(['account', 'control', 'faucet'].map((name) => [name, treeHash(join(root, 'contracts/managed', name))]));
  const runtimeVersion = JSON.parse(readFileSync(join(root, 'node_modules/@midnight-ntwrk/compact-runtime/package.json'), 'utf8')).version;
  equal('runtime version', runtimeVersion, BASE.runtimeVersion);
  equal(`${role} installed dependency tree (runtime/signing/tsx and transitives)`,
    dependencies, role === 'source' ? BASE.dependencies : BASE.repairedDependencies);
  accessSync(join(root, 'node_modules/.bin/tsx'), constants.X_OK);
  return { revision, source, signing, dependencies, runtimeVersion, managed };
}
function snapshot() {
  const source = implementation(paths.source, 'source');
  equal('historical source revision', source.revision, BASE.sourceRevision);
  equal('historical source files', source.source, BASE.source);
  equal('historical signing sources', source.signing, BASE.signing);
  const repaired = implementation(paths.repaired, 'repaired');
  equal('repaired account source', repaired.source['contracts/account.compact'], BASE.repairedAccount);
  equal('repaired signing/wallet sources', repaired.signing, BASE.repairedSigning);
  for (const name of Object.keys(BASE.source).filter((name) => name !== 'contracts/account.compact'))
    equal(`repaired unchanged ${name}`, repaired.source[name], BASE.source[name]);
  const compiler = treeHash(dirname(paths.compiler));
  equal('Compact compiler installation', compiler, BASE.compiler);
  equal('Node version', process.version, BASE.nodeVersion);
  equal('Node executable', fileHash(process.execPath), BASE.node);
  const harness = Object.fromEntries(['gate.mjs', 'recovery-pins.json', 'recovery.ts', 'mutation.ts', 'package.json', 'driver.ts', 'impl.ts', 'model.ts', 'main.ts', 'prng.ts']
    .map((name) => [name, fileHash(join(HARNESS, name))]));
  const model = {
    binary: fileHash(paths.model), sources: treeHash(join(SPEC, 'src'), true),
    buildInputs: Object.fromEntries(['flake.nix', 'flake.lock', 'pagda.nix', 'arc-passport.agda-lib'].map((name) => [name, fileHash(join(SPEC, name))])),
    pagda: fileHash(paths.pagda), agda: treeHash(join(SPEC, '.pagda/agda')), checkEnv: fileHash(join(SPEC, '.pagda/check-env')),
  };
  return { schema: 1, source, repaired, compiler, node: { version: process.version, binary: fileHash(process.execPath) }, model, harness, settings: BASE.settings };
}

const actual = snapshot();
if (mode === 'pin') {
  if (!/^[a-f0-9]{64}$/.test(options['repair-sha256'])) throw new Error('--repair-sha256 must be a lowercase SHA256');
  equal('explicit repaired account fingerprint', actual.repaired.source['contracts/account.compact'], options['repair-sha256']);
  const output = resolve(options.output);
  mkdirSync(dirname(output), { recursive: true });
  writeFileSync(output, `${JSON.stringify({ ...actual, locations: paths }, null, 2)}\n`, { flag: 'wx' });
  console.log(`PINNED ${output} sha256=${fileHash(output)}`);
  console.log('Enrollment records a working-tree source digest as well as HEAD; it does not claim a committed repair revision.');
} else {
  const pinPath = resolve(options.pins);
  const { locations, ...expected } = JSON.parse(readFileSync(pinPath, 'utf8'));
  equal('complete recovery input snapshot', actual, expected);
  console.log(`GATE_INPUTS ${JSON.stringify({ lock: pinPath, lockSha256: fileHash(pinPath), paths, snapshot: actual })}`);
  mkdirSync(join(SPEC, '.worktrees'), { recursive: true });
  const compiled = mkdtempSync(join(SPEC, '.worktrees/recovery-gate-'));
  try {
    // Recompilation prevents a pin from pairing repaired source with stale generated JS.
    for (const role of ['source', 'repaired']) {
      for (const name of ['account', 'control', 'faucet']) {
        const output = join(compiled, role, name);
        mkdirSync(output, { recursive: true });
        command(paths.compiler, [...BASE.settings.compileArgs, `contracts/${name}.compact`, output], paths[role]);
        for (const artifact of ['index.js', 'index.d.ts'])
          equal(`${role}/${name} freshly compiled ${artifact}`, fileHash(join(output, 'contract', artifact)),
            fileHash(join(paths[role], 'contracts/managed', name, 'contract', artifact)));
      }
    }
    for (const role of ['source', 'repaired']) {
      const env = { ...process.env, IMPL_DIR: paths[role], MODEL_BIN: paths.model, PAGDA_BIN: paths.pagda, RECOVERY_IMPLEMENTATION: role, LC_ALL: 'C.UTF-8' };
      command(join(paths[role], 'node_modules/.bin/tsx'), [join(HARNESS, 'recovery.ts'), '--implementation', role,
        '--variant', role === 'source' ? 'both' : 'corrected', '--only', 'all', '--seeds', BASE.settings.seeds.join(','), '--steps', String(BASE.settings.randomSteps)], HARNESS, env);
    }
    for (const name of BASE.settings.mutations) {
      const env = { ...process.env, IMPL_DIR: paths.source, MODEL_BIN: paths.model, PAGDA_BIN: paths.pagda, RECOVERY_IMPLEMENTATION: 'source', LC_ALL: 'C.UTF-8' };
      command(join(paths.source, 'node_modules/.bin/tsx'), [join(HARNESS, 'mutation.ts'), name], HARNESS, env);
    }
    console.log(`RECOVERY_GATE PASS lockSha256=${fileHash(pinPath)} seeds=${BASE.settings.seeds.join(',')} randomSteps=${BASE.settings.randomSteps}`);
  } finally {
    rmSync(compiled, { recursive: true, force: true });
  }
}

import { createHash } from 'node:crypto';
import { readFileSync, readdirSync } from 'node:fs';
import { join, relative } from 'node:path';
import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import type { AccountInfo } from './full-wire.ts';

export const FULL_IMPL_DIR = process.env.FULL_IMPL_DIR ?? process.env.IMPL_DIR
  ?? fileURLToPath(new URL('../../../../../arc-passport/.worktrees/formal-correspondence-main/contract', import.meta.url));
export const sha256 = (data: Uint8Array | string): string => createHash('sha256').update(data).digest('hex');
export interface MainPins {
  schema: number; sourceRevision: string; source: Record<string, string>;
  compiler: { version: string; commit: string; release: string; archiveSha256: string; executables: Record<string, string>; executableDirectory: string };
  runtimeVersion: string; surface: string[];
  node: { version: string; executableSha256: string };
  artifacts?: Record<string, string>;
  dependencies?: Record<string, string>;
}
function object(x: unknown): Record<string, unknown> {
  if (x === null || typeof x !== 'object' || Array.isArray(x)) throw new Error('invalid provenance object');
  return x as Record<string, unknown>;
}
function strings(x: unknown): Record<string, string> {
  return Object.fromEntries(Object.entries(object(x)).map(([k, v]) => {
    if (typeof v !== 'string') throw new Error('invalid provenance digest');
    return [k, v];
  }));
}
export function readMainPins(): MainPins {
  const x = object(JSON.parse(readFileSync(new URL('./passport-main-pins.json', import.meta.url), 'utf8')));
  const c = object(x.compiler);
  const node = strings(x.node);
  if (x.schema !== 1 || typeof x.sourceRevision !== 'string' || typeof x.runtimeVersion !== 'string'
    || !Array.isArray(x.surface) || x.surface.some(v => typeof v !== 'string')
    || typeof c.version !== 'string' || typeof c.commit !== 'string' || typeof c.release !== 'string'
    || typeof c.archiveSha256 !== 'string' || typeof c.executableDirectory !== 'string'
    || !node.version || !node.executableSha256) throw new Error('invalid main pins');
  return {
    schema: x.schema, sourceRevision: x.sourceRevision, runtimeVersion: x.runtimeVersion,
    source: strings(x.source), compiler: { version: c.version, commit: c.commit, release: c.release, archiveSha256: c.archiveSha256,
      executables: strings(c.executables), executableDirectory: c.executableDirectory },
    surface: x.surface as string[],
    node: { version: node.version, executableSha256: node.executableSha256 },
    ...(x.artifacts === undefined ? {} : { artifacts: strings(x.artifacts) }),
    ...(x.dependencies === undefined ? {} : { dependencies: strings(x.dependencies) }),
  };
}
/** Digest the bytes actually loaded, not just npm's declared semver range. */
export function treeDigest(root: string): string {
  const entries: string[] = [];
  function visit(dir: string): void {
    for (const e of readdirSync(dir, { withFileTypes: true }).sort((a, b) => a.name.localeCompare(b.name))) {
      const path = join(dir, e.name);
      if (e.isDirectory()) visit(path);
      else if (e.isFile()) entries.push(`${relative(root, path)}\0${sha256(readFileSync(path))}\n`);
      else throw new Error(`unsupported dependency filesystem entry: ${path}`);
    }
  }
  visit(root);
  return sha256(entries.join(''));
}
export function assertMainPins(root: string, info: AccountInfo, runtimeNames: string[]): MainPins {
  const pins = readMainPins();
  const revision = execFileSync('git', ['rev-parse', 'HEAD'], { cwd: root, encoding: 'utf8' }).trim();
  if (revision !== pins.sourceRevision) throw new Error(`main revision drift: ${revision}`);
  for (const [path, expected] of Object.entries({ ...pins.source, ...pins.artifacts })) {
    if (sha256(readFileSync(join(root, path))) !== expected) throw new Error(`main bytes drift: ${path}`);
  }
  if (!pins.artifacts || !pins.dependencies) throw new Error('main artifact/dependency identity is not recorded');
  for (const [path, expected] of Object.entries(pins.dependencies)) {
    if (treeDigest(join(root, path)) !== expected) throw new Error(`main dependency bytes drift: ${path}`);
  }
  if (process.version !== pins.node.version || sha256(readFileSync(process.execPath)) !== pins.node.executableSha256) throw new Error('main Node runtime identity drift');
  const compilerDirectory = process.env.FULL_COMPACT_DIR ?? pins.compiler.executableDirectory;
  for (const [name, expected] of Object.entries(pins.compiler.executables)) {
    if (sha256(readFileSync(join(compilerDirectory, name))) !== expected) throw new Error(`main compiler executable drift: ${name}`);
  }
  if (info['compiler-version'] !== pins.compiler.version || info['compiler-commit'] !== pins.compiler.commit
    || info['runtime-version'] !== pins.runtimeVersion) throw new Error('main compiler/runtime identity drift');
  const expected = JSON.stringify([...pins.surface].sort());
  const metadata = ['constructor', ...info.circuits.filter(c => !c.pure).map(c => c.name)].sort();
  const runtime = ['constructor', ...runtimeNames].sort();
  if (JSON.stringify(metadata) !== expected || JSON.stringify(runtime) !== expected) throw new Error('full account circuit surface drift');
  return pins;
}

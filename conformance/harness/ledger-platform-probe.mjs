// Opt-in isolated infrastructure discovery. Never touches existing containers,
// volumes, wallet seeds or implementation artifacts; never pulls images.
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { FULL_IMPL_DIR } from './full-pins.ts';

assert(process.argv.includes('--isolated-stack'), 'Explicit --isolated-stack opt-in required');
const output = process.argv.find(x => x.startsWith('--output='))?.slice(9);
assert(output, '--output=PATH required');
const commands = [], endpoints = [], started = [];
const run = (program, args, timeout = 30_000) => {
  const r = spawnSync(program, args, { encoding: 'utf8', timeout, maxBuffer: 4 * 1024 * 1024 });
  const observation = { program, args, status: r.status, signal: r.signal,
    stdout: r.stdout ?? '', stderr: r.stderr ?? '', error: r.error?.message };
  commands.push(observation);
  return observation;
};
const request = async (url, body) => {
  try {
    const r = await fetch(url, { ...(body ? { method: 'POST', headers: { 'content-type': 'application/json' }, body: JSON.stringify(body) } : {}),
      signal: AbortSignal.timeout(3000) });
    const record = { url, request: body, status: r.status, body: await r.text() };
    endpoints.push(record);
    return record;
  } catch (e) { const record = { url, request: body, error: String(e), cause: String(e.cause) }; endpoints.push(record); return record; }
};
const work = mkdtempSync(join(tmpdir(), 'passport-ledger-platform-'));
const suffix = `${process.pid}`;
const nodeName = `passport-ledger-probe-node-${suffix}`, proverName = `passport-ledger-probe-prover-${suffix}`;
const nodeImage = 'midnightntwrk/midnight-node@sha256:9040c346c27f569b72dfbbad9420cf38fc7cc6a13b38adf814a925bbe9311678';
const proverImage = 'midnightntwrk/proof-server@sha256:2666c7bd7b4517f8ad135565387f98d14347a9ac715c6c466d4a8a852b545ecf';
const report = { schema: 1, startedAt: new Date().toISOString(), node: process.version,
  boundary: 'Infrastructure availability only; no Passport deployment, transaction or finality claim', commands, endpoints };
try {
  run('docker', ['ps', '-a', '--format', '{{.Names}} {{.Image}} {{.Status}}']);
  run('docker', ['image', 'ls', '--digests', '--format', '{{.Repository}}:{{.Tag}} {{.Digest}}']);
  for (const port of [9944, 8088, 6300]) await request(`http://127.0.0.1:${port}/`);
  // Abort if our isolated ports are already occupied, rather than reusing a
  // user's service and mistaking its state for this run's fresh chain.
  for (const port of [19945, 16301]) {
    const response = await request(`http://127.0.0.1:${port}/`);
    assert(response.error && response.cause.includes('ECONNREFUSED'), `port ${port} is not available`);
  }
  for (const [name, image, args] of [
    [nodeName, nodeImage, ['--env', 'CFG_PRESET=dev', '--env', 'SIDECHAIN_BLOCK_BENEFICIARY=04bcf7ad3be7a5c790460be82a713af570f22e0f801f6659ab8e84a52be6969e',
      '--cap-add', 'CHOWN', '--cap-add', 'DAC_OVERRIDE', '--cap-add', 'FOWNER']],
    [proverName, proverImage, ['--env', 'PORT=16301']],
  ]) {
    const r = run('docker', ['run', '--detach', '--pull', 'never', '--name', name, '--network', 'host',
      '--cap-drop', 'ALL', '--security-opt', 'no-new-privileges:true', ...args, image,
      ...(name === nodeName ? ['--dev', '--rpc-port', '19945', '--port', '30340', '--no-prometheus', '--no-telemetry', '--base-path', '/tmp/passport-ledger-probe'] : [])]);
    if (r.status === 0) started.push(name);
  }
  await new Promise(resolve => setTimeout(resolve, 15_000));
  for (const method of ['system_version', 'system_health', 'chain_getHeader', 'chain_getFinalizedHead', 'state_getRuntimeVersion'])
    await request('http://127.0.0.1:19945', { jsonrpc: '2.0', id: 1, method, params: [] });
  await request('http://127.0.0.1:16301/version');
  for (const name of started) run('docker', ['logs', name]);
  run('curl', ['--max-time', '15', '--silent', '--show-error', '--include', '--range', '0-31', 'https://srs.midnight.network/bls_midnight_2p10']);
  run('sbx', ['policy', 'approval', 'ls']);
  const compiler = '/tmp/passport-compact-0.35.0/zkir-v3';
  report.compilerSha256 = createHash('sha256').update(readFileSync(compiler)).digest('hex');
  run(compiler, ['compile', `${FULL_IMPL_DIR}/contracts/managed/account/zkir/activate_initial_device_with_jubjub.zkir`,
    join(work, 'activation.prover'), join(work, 'activation.verifier')], 120_000);
  report.result = 'INVESTIGATED';
} catch (e) { report.result = 'FAIL'; report.failure = e.stack ?? String(e); process.exitCode = 1; }
finally {
  for (const name of started) run('docker', ['rm', '--force', name]);
  rmSync(work, { recursive: true, force: true });
  report.completedAt = new Date().toISOString();
  report.runnerSha256 = createHash('sha256').update(readFileSync(new URL(import.meta.url))).digest('hex');
  writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify({ result: report.result, output, failure: report.failure }));
}

// Custody conformance run (docs/conformance-spike.md): one seeded deposit/withdraw sequence
// driven through the implementation and the source-shaped model, judged per step by both
// oracles (see driver.ts).
//
// Usage: tsx main.ts [--seed N] [--steps N]; env MODEL_BIN, IMPL_DIR. Exit 1 on divergence.

import { Client, option, Runner, type Planned } from './driver.ts';
import { hex, IMPL_DIR, loadImpl, openAccount, type LedgerView } from './impl.ts';
import { Model, MODEL_BIN } from './model.ts';
import { Prng } from './prng.ts';

const KINDS = ['deposit', 'overflow', 'valid', 'replay', 'staleCounter', 'wrongKey', 'unregistered', 'insufficient', 'unknownColor'] as const;
type Kind = (typeof KINDS)[number];

const seed = Number(option('seed', '1'));
const steps = Number(option('steps', '30'));
const prng = new Prng(seed);
const impl = await loadImpl();
const { signer } = impl;
const recovery = new signer.JubjubDevice(signer.randomJubjubScalar(() => prng.bytes(32)));
const acct = await openAccount(impl, prng, { recoveryPk: recovery.pk, vetoWindow: 3600n, time: 1_800_000_000 });
const client = new Client(impl, acct, prng);
const stranger = client.device();
const colorA = prng.bytes(32);
const colorB = prng.bytes(32);
const colorUnknown = prng.bytes(32);
const model = new Model(impl);
const runner = new Runner(model, client, 'source');

// Every category at least once; the first two steps fund the account; the rest weighted.
const base: Kind[] = ['valid', 'replay', 'staleCounter', 'wrongKey', 'unregistered', 'insufficient', 'unknownColor', 'overflow', 'valid'];
const weighted: Kind[] = ['deposit', 'deposit', 'deposit', 'valid', 'valid', 'valid', ...KINDS];
const rest: Kind[] = [...base];
while (rest.length < steps - 2) rest.push(weighted[prng.below(weighted.length)]);
for (let i = rest.length - 1; i > 0; i--) {
  const j = prng.below(i + 1);
  [rest[i], rest[j]] = [rest[j], rest[i]];
}
const schedule: Kind[] = ['deposit', 'deposit', ...rest];

let validCount = 0;
let lastValid: Planned | undefined;

const balanceOf = (v: LedgerView, c: Uint8Array) => v.balances.find(([k]) => k === hex(c))?.[1] ?? 0n;

function plan(kind: Kind): [Kind, Planned] {
  const v = acct.view();
  const funded = [colorA, colorB].filter((c) => balanceOf(v, c) > 0n);
  const someFunded = funded.length > 0 ? funded[prng.below(funded.length)] : colorA;
  const owner = acct.owner;
  const useCounter = client.counters.get(owner) ?? 0n;
  const withdraw = (label: string, color: Uint8Array, amount: bigint, by = owner, opts = {}) =>
    client.gated(label, { kind: 'withdraw', color, amount, recipient: prng.bytes(32) }, by, opts);
  switch (kind) {
    case 'deposit': {
      const amount = prng.between(1n, 1000n);
      return [kind, client.deposit(`deposit ${amount}`, prng.below(2) === 0 ? colorA : colorB, amount)];
    }
    case 'overflow':
      if (funded.length === 0) return plan('deposit');
      return [kind, client.deposit('deposit 2^128-1 (overflow)', someFunded, 2n ** 128n - 1n)];
    case 'valid': {
      if (funded.length === 0) return plan('deposit');
      const bal = balanceOf(v, someFunded);
      const full = validCount++ % 3 === 0;
      const amount = full ? bal : prng.between(1n, bal);
      return [kind, withdraw(`withdraw ${amount}${full ? ' (full balance)' : ''}`, someFunded, amount)];
    }
    case 'replay':
      return lastValid ? [kind, { ...lastValid, label: 'replay of last valid withdraw', signer: undefined }] : plan('valid');
    case 'staleCounter':
      if (useCounter === 0n) return plan('valid');
      return [kind, withdraw(`stale use_counter ${useCounter - 1n}`, someFunded, 1n, owner, { uc: useCounter - 1n })];
    case 'wrongKey':
      return [kind, withdraw('owner pk, stranger signs', someFunded, 1n, stranger, { pk: owner.pk, uc: useCounter })];
    case 'unregistered':
      return [kind, withdraw('unregistered pk', someFunded, 1n, stranger, { uc: 0n })];
    case 'insufficient':
      return [kind, withdraw(`withdraw > balance`, someFunded, balanceOf(v, someFunded) + prng.between(1n, 100n))];
    case 'unknownColor':
      return [kind, withdraw('never-deposited colour', colorUnknown, prng.between(1n, 100n))];
  }
}

console.log(`conformance harness (custody)  seed=${seed} steps=${schedule.length}`);
console.log(`  model  ${MODEL_BIN}`);
console.log(`  impl   ${IMPL_DIR}`);
console.log(`  account ${acct.addressHex.slice(0, 16)}…  r_J(signer) == JUBJUB_SCALAR_MODULUS(runtime): ${signer.JUBJUB_R === impl.rt.JUBJUB_SCALAR_MODULUS}`);
console.log('');

let divergences = 0;
const covered = new Map<Kind, number>();
const started = Date.now();
let coins = 0;

for (const [i, scheduled] of schedule.entries()) {
  const [kind, p] = plan(scheduled);
  covered.set(kind, (covered.get(kind) ?? 0) + 1);
  const r = await runner.run(p);
  if (r.impl === 'ok' && p.signer === acct.owner) lastValid = p;
  coins += r.coins;
  if (r.diverged) divergences++;
  const o1 = r.reasons.length === 0 ? 'agree' : `DIVERGE (${r.reasons.join('; ')})`;
  console.log(
    `#${String(i + 1).padStart(2, '0')} ${kind.padEnd(12)} ${p.label.padEnd(30)} impl=${r.impl.padEnd(26)}`
    + ` coins=${String(r.coins).padStart(5)} rpc=${String(r.rpc).padStart(3)}  O1=${o1}  O2=${r.decided ? 'accept' : 'REJECT'}`,
  );
}

model.close();
const elapsed = ((Date.now() - started) / 1000).toFixed(1);
console.log('');
console.log(`coverage: ${KINDS.map((k) => `${k}=${covered.get(k) ?? 0}`).join(' ')}`);
console.log(`coin bits consumed: ${coins}; primitive round trips: ${model.rpcCount}; wall: ${elapsed}s`);
console.log(divergences === 0 ? `RESULT: ${schedule.length}/${schedule.length} steps agree on both oracles` : `RESULT: ${divergences} divergent step(s)`);
process.exit(divergences === 0 ? 0 : 1);

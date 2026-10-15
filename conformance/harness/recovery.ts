// Recovery scenarios, planted-credential histories and random interleavings.
// `gate.mjs` pins the implementation, model, compiler and signing/runtime inputs.
// A planted use has an exact verdict/oracle annotation, derived from the credential's
// epoch and the successful finalisation rather than from a static random schedule.

import { asRaw, Client, option, Runner, type Planned, type Publication, type StepResult, type SubmitOptions } from './driver.ts';
import { hex, IMPL_DIR, loadImpl, openAccount, type Account, type Device, type Impl, type Point } from './impl.ts';
import { Model, MODEL_BIN, type Variant } from './model.ts';
import { Prng } from './prng.ts';

const T0 = 1_800_000_000;
/** The scenarios' veto window; random runs draw theirs per seed. */
const WINDOW = 86_400n;
const implementation = option('implementation', process.env.RECOVERY_IMPLEMENTATION ?? 'source');
if (!['source', 'repaired'].includes(implementation)) throw new Error('implementation must be source or repaired');
if (process.env.RECOVERY_IMPLEMENTATION && process.env.RECOVERY_IMPLEMENTATION !== implementation)
  throw new Error('implementation option and RECOVERY_IMPLEMENTATION disagree');
process.env.RECOVERY_IMPLEMENTATION = implementation;
const selected = option('variant', implementation === 'repaired' ? 'corrected' : 'both');
if (!['source', 'corrected', 'both'].includes(selected)) throw new Error('variant must be source, corrected or both');
if (implementation === 'repaired' && selected !== 'corrected') throw new Error('repaired implementation requires corrected model');
const variants: Variant[] = selected === 'both' ? ['source', 'corrected'] : [selected as Variant];
const only = option('only', 'all');
if (!['all', 'scenarios', 'generated', 'random'].includes(only)) throw new Error('only must be all, scenarios, generated or random');
const seeds = option('seeds', '1,2,3,4,5').split(',').map(Number);
const steps = Number(option('steps', '60'));
if (!seeds.length || seeds.some((s) => !Number.isSafeInteger(s) || s < 1 || s > 0xffffffff))
  throw new Error('seeds must be positive Uint32 integers');
if (!Number.isSafeInteger(steps) || steps < 20) throw new Error('steps must be an integer >= 20');
const impl = await loadImpl();
const { signer } = impl;
const model = new Model(impl);
const IDENTITY: Point = impl.rt.ecMulGenerator(0n);

interface Key { sk: bigint; pk: Point }

/** One account under test, with the honest parties' secrets. */
class World {
  readonly client: Client;
  readonly runner: Runner;
  recoverySk: bigint;
  failures: string[] = [];
  divergent = 0;
  log: string[] = [];
  private n = 0;

  private constructor(readonly prng: Prng, readonly acct: Account, recoverySk: bigint, readonly variant: Variant) {
    this.recoverySk = recoverySk;
    this.client = new Client(impl, acct, prng);
    this.runner = new Runner(model, this.client, variant);
  }

  static async open(seed: number, variant: Variant, window = WINDOW): Promise<World> {
    const prng = new Prng(seed);
    const recoverySk = signer.randomJubjubScalar(() => prng.bytes(32));
    const acct = await openAccount(impl, prng, { recoveryPk: new signer.JubjubDevice(recoverySk).pk, vetoWindow: window, time: T0 });
    return new World(prng, acct, recoverySk, variant);
  }

  get owner(): Device { return this.acct.owner; }
  get view() { return this.acct.view(); }
  device(): Device { return this.client.device(); }
  key(): Key {
    const d = this.device();
    return { sk: d.sk, pk: d.pk };
  }

  submit(label: string, successor: Device, successorRecovery: Key, extra: Partial<SubmitOptions> = {}): Planned {
    return this.client.submit(label, {
      recoverySk: this.recoverySk, successor, successorRecoveryPk: successorRecovery.pk,
      nowUpper: BigInt(this.acct.now) + 600n, ...extra,
    });
  }

  publication(newRecovery: Key, over: Partial<Publication> = {}): Publication {
    const phi = [this.prng.between(1n, 1n << 200n), this.prng.between(1n, 1n << 200n), this.prng.between(1n, 1n << 200n), 0n] as const;
    return { newRecoveryPk: newRecovery.pk, session: this.prng.bytes(32), phi, phiLen: 3n, wrap: this.prng.bytes(64), ...over };
  }

  /** The successor becomes the live device at counter 0 and the recovery secret rotates. */
  adopt(successor: Device, successorRecovery: Key): void {
    this.client.counters.clear();
    this.client.counters.set(successor, 0n);
    this.recoverySk = successorRecovery.sk;
  }

  async step(p: Planned & { exclusion?: boolean }): Promise<StepResult> {
    const r = await this.runner.run(p);
    this.n++;
    const annotated = p.diverges?.includes(this.variant) ?? false;
    const notes: string[] = [];
    if (p.expect !== undefined && !p.expect.includes(r.impl)) {
      this.failures.push(`#${this.n} ${p.label}: implementation ${r.impl}, scenario requires ${p.expect.join(' | ')}`);
      notes.push(`OBSERVATION ≠ ${p.expect.join(' | ')}`);
    }
    if (r.diverged) this.divergent++;
    if (annotated && !r.diverged) this.failures.push(`#${this.n} ${p.label}: annotated divergence did not occur`);
    if (!annotated && r.diverged) this.failures.push(`#${this.n} ${p.label}: unannotated divergence`);
    if (annotated) notes.push(r.diverged ? 'expected divergence ✓' : 'EXPECTED DIVERGENCE MISSING');
    if (p.exclusion) {
      const excluded = implementation === 'repaired' || this.variant === 'corrected';
      const wanted = excluded ? 'fail unknownDevice' : p.expect![0];
      if (r.model !== wanted) this.failures.push(`#${this.n} ${p.label}: model ${r.model}, exclusion requires ${wanted}`);
      if (annotated && (r.reasons.length === 0 || r.decided))
        this.failures.push(`#${this.n} ${p.label}: planted use must disagree on BOTH oracles`);
      if (!annotated && (r.reasons.length !== 0 || !r.decided))
        this.failures.push(`#${this.n} ${p.label}: planted use must agree on BOTH oracles`);
    }
    if (p.exclusion) notes.push(`planted-use expected model=${implementation === 'repaired' || this.variant === 'corrected' ? 'fail unknownDevice' : p.expect![0]}, both oracles=${annotated ? 'disagree' : 'agree'}`);
    if (r.impl === 'ok') notes.push(r.transcriptVerified ? 'VM transcript checked; tampered read rejected' : 'VM TRANSCRIPT CHECK FAILED');
    const o1 = r.reasons.length === 0 ? 'agree' : `DIVERGE (${r.reasons.join('; ')})`;
    const line = `  #${String(this.n).padStart(2, '0')} t=T0+${String(this.acct.now - T0).padEnd(7)} ${p.label.padEnd(58)} impl=${r.impl.padEnd(30)} model=${r.model.padEnd(30)}`
      + ` O1=${o1}  O2=${r.decided ? 'accept' : 'REJECT'}${notes.length > 0 ? `  [${notes.join('; ')}]` : ''}`;
    this.log.push(line);
    console.log(line);
    return r;
  }

  deadline(): number { return Number(this.view.pendingNotBefore); }
}

// ── The acceptance scenarios (recovery-specification.md:349-364) ───────────────────────

type Scenario = { name: string; row: string; run: (w: World) => Promise<void> };

const ok = (p: Planned): Planned => ({ ...p, expect: ['ok'] });
const fails = (codes: string | string[], p: Planned): Planned =>
  ({ ...p, expect: [codes].flat().map((c) => (c === 'refused' ? 'refused' : `fail ${c}`)) });
const rotate = (w: World, label: string, by: Device, opts = {}) => w.client.gated(label, { kind: 'rotate', key: w.prng.bytes(32) }, by, opts);
const cancel = (w: World, label: string, by: Device, opts = {}) => w.client.gated(label, { kind: 'cancel' }, by, opts);

function plantedUse(p: Planned, sourceVerdict = 'ok'): Planned & { exclusion: boolean } {
  return {
    ...p, exclusion: true,
    expect: [implementation === 'source' ? sourceVerdict : 'fail unknownDevice'],
    diverges: implementation === 'source' ? ['corrected'] : [],
  };
}

/** A seam-passing replacement of submit argument `i` (0-based, recoverSubmitArgs order). */
function tamper(args: unknown[], i: number, value: unknown): unknown[] {
  return args.map((a, j) => (j === i ? value : a));
}

const scenarios: Scenario[] = [
  {
    name: 'valid-recovery', row: 'Valid submission, eligible finalisation, successor use',
    run: async (w) => {
      const S = w.device(), R1 = w.key();
      await w.step(ok(w.submit('submit (recovery key + successor S)', S, R1)));
      w.acct.now = w.deadline();
      await w.step(ok(w.client.finalise('finalise at deadline (permissionless, no signer)')));
      w.adopt(S, R1);
      await w.step(ok(rotate(w, 'S rotates enc key (epoch 1, counter 0)', S)));
      await w.step(fails('unknownDevice', rotate(w, 'old owner rotates enc key', w.owner, { uc: 0n })));
      await w.step(ok(w.client.gated('S enrols a fresh device', { kind: 'add', entry: w.client.entryOf(w.device()) }, S)));
    },
  },
  {
    name: 'finalise-deadline', row: 'Finalise before, at, and after deadline',
    run: async (w) => {
      const S = w.device(), R1 = w.key();
      await w.step(ok(w.submit('submit', S, R1)));
      w.acct.now = w.deadline() - 1;
      await w.step(fails('refused', w.client.finalise('finalise at deadline - 1')));
      w.acct.now = w.deadline();
      await w.step(ok(w.client.finalise('finalise at deadline')));
      w.adopt(S, R1);
      const S2 = w.device(), R2 = w.key();
      await w.step(ok(w.submit('second submission (recovery key R1, successor S2)', S2, R2)));
      w.acct.now = w.deadline() + 3600;
      await w.step(ok(w.client.finalise('finalise at deadline + 3600')));
    },
  },
  {
    name: 'cancel-before-finalise', row: 'Cancel before finalise',
    run: async (w) => {
      const S = w.device(), R1 = w.key();
      await w.step(ok(w.submit('submit', S, R1)));
      const deadline = w.deadline();
      w.acct.now += 60;
      await w.step(ok(cancel(w, 'owner cancels inside the window', w.owner)));
      w.acct.now = deadline + 1;
      await w.step(fails('noPending', w.client.finalise('finalise after the old deadline')));
      await w.step(ok(rotate(w, 'owner still authorises', w.owner)));
    },
  },
  {
    name: 'cancel-after-deadline', row: 'Cancel after deadline but before finalise',
    run: async (w) => {
      const S = w.device(), R1 = w.key();
      await w.step(ok(w.submit('submit', S, R1)));
      w.acct.now = w.deadline() + 10;
      await w.step(ok(cancel(w, 'owner cancels after the deadline (no deadline check)', w.owner)));
      await w.step(fails('noPending', w.client.finalise('finalise')));
    },
  },
  {
    name: 'finalise-then-old-cancel', row: 'Finalise before old-device cancellation',
    run: async (w) => {
      const A = w.device();
      await w.step(ok(w.client.gated('owner enrols device A (epoch 0)', { kind: 'add', entry: w.client.entryOf(A) }, w.owner)));
      w.client.counters.set(A, 0n);
      await w.step(ok(w.client.gated('A plants A@epoch 1, counter 0', { kind: 'add', entry: w.client.entryOf(A, 1n) }, A)));
      const S = w.device(), R1 = w.key();
      await w.step(ok(w.submit('submit (successor S)', S, R1)));
      w.acct.now = w.deadline();
      await w.step(ok(w.client.finalise('finalise')));
      await w.step(fails('unknownDevice', cancel(w, 'old owner cancels', w.owner)));
      await w.step(plantedUse(cancel(w, 'old device A cancels via its planted entry', A, { uc: 0n }), 'fail noPending'));
    },
  },
  {
    name: 'cancel-then-replay', row: 'Cancel then replay old submission',
    run: async (w) => {
      const S = w.device(), R1 = w.key();
      const original = w.submit('submit', S, R1);
      await w.step(ok(original));
      await w.step(ok(cancel(w, 'owner cancels', w.owner)));
      await w.step(fails('staleNonce', w.client.rawSubmit('replay the cancelled submission verbatim', original.args)));
      await w.step(ok(w.submit('fresh submission against the current nonce', S, R1)));
    },
  },
  {
    name: 'use-while-pending', row: 'Ordinary device use while pending',
    run: async (w) => {
      const color = w.prng.bytes(32);
      await w.step(ok(w.client.deposit('deposit 1000', color, 1000n)));
      const S = w.device(), R1 = w.key();
      await w.step(ok(w.submit('submit', S, R1)));
      await w.step(ok(rotate(w, 'owner rotates enc key while pending', w.owner)));
      await w.step(ok(w.client.gated('owner withdraws 100 while pending', { kind: 'withdraw', color, amount: 100n, recipient: w.prng.bytes(32) }, w.owner)));
      await w.step(ok(w.client.gated('owner enrols D2 while pending', { kind: 'add', entry: w.client.entryOf(w.device()) }, w.owner)));
      if (!w.view.pending) w.failures.push('pending record lost after ordinary use');
      w.acct.now = w.deadline();
      await w.step(ok(w.client.finalise('finalise (nonce moved since submission)')));
    },
  },
  {
    name: 'publish-while-pending', row: 'Publish session while pending',
    run: async (w) => {
      const S = w.device(), R1 = w.key();
      await w.step(ok(w.submit('submit', S, R1)));
      const fresh = w.key();
      await w.step(fails('recoveryPending', w.client.gated('owner publishes a session while pending', { kind: 'publish', p: w.publication(fresh) }, w.owner)));
      await w.step(ok(cancel(w, 'owner cancels', w.owner)));
      await w.step(ok(w.client.gated('owner publishes the session', { kind: 'publish', p: w.publication(fresh) }, w.owner)));
    },
  },
  {
    name: 'wrong-binding', row: 'Wrong account, key, epoch, nonce, or time bound',
    run: async (w) => {
      await w.step(ok(rotate(w, 'owner rotates (auth_nonce 0 → 1)', w.owner)));
      const S = w.device(), R1 = w.key(), other = w.device();
      const foreign = w.prng.bytes(32);
      // A challenge recomputed over different arguments is no longer ground below r_J, so the
      // `as Field` cast may abort before the signature check: either is the binding rejecting.
      const rebound = (code: string) => [code, 'challengeRange'];
      await w.step(fails(rebound('invalidRecoverySignature'), asRaw(w.submit('submit signed for another account', S, R1, { address: foreign }))));
      await w.step(fails(rebound('invalidSignature'), asRaw(cancel(w, 'cancel signed for another account', w.owner, { address: foreign }))));
      await w.step(fails('invalidRecoverySignature', w.submit('submit signed by a stranger as recovery key', S, R1, { recoverySk: other.sk })));
      const signed = w.submit('-', S, R1);
      await w.step(fails(rebound('invalidRecoverySignature'), w.client.rawSubmit('successor pk swapped after signing', tamper(signed.args, 0, other.pk))));
      await w.step(fails('invalidSuccessorSignature', w.client.rawSubmit('successor response s altered', tamper(signed.args, 8, (signed.args[8] as bigint) + 1n))));
      await w.step(fails(rebound('invalidRecoverySignature'), w.client.rawSubmit('now_upper raised after signing', tamper(signed.args, 4, (signed.args[4] as bigint) + 1000n))));
      await w.step(fails('staleEpoch', w.submit('submit against epoch 1', S, R1, { epoch: 1n })));
      await w.step(fails('staleNonce', w.submit('submit against auth_nonce 0', S, R1, { nonce: 0n })));
      await w.step(fails('refused', w.submit('now_upper already past', S, R1, { nowUpper: BigInt(w.acct.now) - 1n })));
      await w.step(fails('commitmentReused', w.submit('successor recovery key = current key', S, { sk: w.recoverySk, pk: w.view.recoveryPk })));
      await w.step(fails('identityKey', w.submit('successor recovery key = identity', S, { sk: 0n, pk: IDENTITY })));
      await w.step(fails('identityKey', w.submit('successor key = identity', new signer.JubjubDevice(0n), R1)));
      await w.step(fails('overflow', w.submit('now_upper + veto_window ≥ 2^64', S, R1, { nowUpper: 2n ** 64n - 10n })));
      await w.step(ok(w.submit('correctly bound submission', S, R1)));
    },
  },
  {
    name: 'failed-after-roll', row: 'Failed operation after tentative credential roll',
    run: async (w) => {
      const color = w.prng.bytes(32);
      await w.step(ok(w.client.deposit('deposit 50', color, 50n)));
      const owner = w.owner;
      const rolled = (k = 1n) => owner.entryAt(w.acct.address, w.view.deviceEpoch, (w.client.counters.get(owner) ?? 0n) + k);
      await w.step(fails('noPending', cancel(w, 'cancel with nothing pending', owner)));
      await w.step(fails('lastDevice', w.client.gated('remove a device with device_count 1', { kind: 'remove', entry: rolled() }, owner)));
      const D2 = w.device();
      await w.step(ok(w.client.gated('owner enrols D2', { kind: 'add', entry: w.client.entryOf(D2) }, owner)));
      await w.step(fails('entryPresent', w.client.gated('enrol D2 again', { kind: 'add', entry: w.client.entryOf(D2) }, owner)));
      await w.step(fails('authorisingDevice', w.client.gated('owner removes its own rolled entry', { kind: 'remove', entry: rolled() }, owner)));
      await w.step(fails('unknownDevice', w.client.gated('remove an absent entry', { kind: 'remove', entry: w.prng.bytes(32) }, owner)));
      await w.step(fails('insufficientBalance', w.client.gated('withdraw 51 of 50', { kind: 'withdraw', color, amount: 51n, recipient: w.prng.bytes(32) }, owner)));
      const pub = (label: string, over: Partial<Publication>, k = w.key()) =>
        w.client.gated(label, { kind: 'publish', p: w.publication(k, over) }, owner);
      await w.step(fails('phiEmpty', pub('publish with phi_len 0', { phiLen: 0n })));
      await w.step(fails('phiLength', pub('publish with phi_len 5', { phiLen: 5n })));
      await w.step(fails('phiSlot3', pub('publish phi_len 2 with slot 3 set', { phiLen: 2n })));
      await w.step(fails('sessionZero', pub('publish with a zero session id', { session: new Uint8Array(32) })));
      await w.step(fails('commitmentReused', pub('publish the current recovery key', { newRecoveryPk: w.view.recoveryPk })));
      await w.step(fails('identityKey', pub('publish the identity as recovery key', { newRecoveryPk: IDENTITY })));
      const k = w.key();
      const session = w.prng.bytes(32);
      await w.step(ok(pub('publish a session', { session }, k)));
      w.recoverySk = k.sk;
      await w.step(fails('sessionReused', pub('publish reusing the session id', { session })));
    },
  },
  {
    name: 'future-epoch-attack', row: 'Future-epoch enrolment followed by recovery',
    run: async (w) => {
      const color = w.prng.bytes(32);
      await w.step(ok(w.client.deposit('deposit 1000', color, 1000n)));
      const A = w.device();
      await w.step(ok(w.client.gated('owner enrols adversary device A (epoch 0, counter 0)', { kind: 'add', entry: w.client.entryOf(A) }, w.owner)));
      w.client.counters.set(A, 0n);
      await w.step(ok(w.client.gated('A enrols the dormant entry A@epoch 1, counter 0', { kind: 'add', entry: w.client.entryOf(A, 1n) }, A)));
      const S = w.device(), R1 = w.key();
      await w.step(ok(w.submit('recover_submit: recovery key + successor S co-sign', S, R1)));
      w.acct.now = w.deadline();
      await w.step(ok(w.client.finalise('recover_finalise at the deadline')));
      w.adopt(S, R1);
      await w.step(plantedUse(w.client.gated('A signs withdraw 1000 at the current nonce (epoch 1, counter 0)',
        { kind: 'withdraw', color, amount: 1000n, recipient: w.prng.bytes(32) }, A, { uc: 0n })));
    },
  },
  {
    name: 'enc-key-rotation', row: 'Ordinary encryption-key rotation',
    run: async (w) => {
      await w.step(ok(rotate(w, 'owner rotates enc key (no recovery)', w.owner)));
      const S = w.device(), R1 = w.key();
      await w.step(ok(w.submit('submit', S, R1)));
      await w.step(ok(rotate(w, 'owner rotates enc key while pending', w.owner)));
      w.acct.now = w.deadline();
      await w.step(ok(w.client.finalise('finalise')));
      w.adopt(S, R1);
      await w.step(ok(rotate(w, 'successor rotates enc key', S)));
    },
  },
];

// Every generated history plants all attack credentials before recovery, then uses each
// only after its target epoch is finalised. Fresh signatures bind the *current* nonce.
async function generatedRun(seed: number, variant: Variant): Promise<World> {
  const settings = new Prng(seed);
  const window = settings.between(60n, 7n * 86_400n);
  const epochs = 1 + settings.below(3);
  const w = await World.open(2000 + seed, variant, window);
  const { client, prng } = w;
  const color = prng.bytes(32);
  const amount = prng.between(100n, 1000n);
  const A = w.device();
  const credentials: { epoch: bigint; uc: bigint }[] = [];
  console.log(`\n── generated seed ${seed}, account seed ${2000 + seed}, epochs ${epochs}, veto_window ${window}s, variant ${variant}`);
  await w.step(ok(client.deposit('fund generated history', color, amount * BigInt(epochs + 1))));
  await w.step(ok(client.gated('owner enrols generated adversary', { kind: 'add', entry: client.entryOf(A) }, w.owner)));
  client.counters.set(A, 0n);
  for (let e = 1; e <= epochs; e++) {
    const epoch = BigInt(e), uc = settings.between(0n, 4n);
    credentials.push({ epoch, uc });
    await w.step(ok(client.gated(`plant adversary epoch ${epoch}, counter ${uc}`,
      { kind: 'add', entry: A.entryAt(w.acct.address, epoch, uc) }, A)));
  }
  let live = w.owner;
  for (const { epoch, uc } of credentials) {
    const S = w.device(), R = w.key();
    const before = 1 + settings.below(3);
    for (let i = 0; i < before; i++) await w.step(ok(rotate(w, `ordinary pre-submit operation ${i + 1}`, live)));
    await w.step(ok(w.submit(`submit recovery to epoch ${epoch}`, S, R)));
    await w.step(ok(rotate(w, 'ordinary operation while pending', live)));
    w.acct.now = w.deadline() - 1;
    await w.step(fails('refused', client.finalise('generated deadline - 1')));
    w.acct.now = w.deadline() + settings.below(3601);
    await w.step(ok(client.finalise(`finalise generated epoch ${epoch}`)));
    w.adopt(S, R);
    await w.step(ok(rotate(w, 'successor proves live authority before planted use', S)));
    const nonce = w.view.authNonce;
    await w.step(plantedUse(client.gated(`fresh planted withdraw epoch ${epoch}, counter ${uc}, nonce ${nonce}`,
      { kind: 'withdraw', color, amount, recipient: prng.bytes(32) }, A, { uc })));
    await w.step(ok(client.gated('successor withdraws after the planted-use observation',
      { kind: 'withdraw', color, amount: 1n, recipient: prng.bytes(32) }, S)));
    live = S;
  }
  return w;
}

// ── Seeded random interleavings ─────────────────────────────────────────────────────────

const KINDS = [
  'deposit', 'withdraw', 'insufficient', 'enrol', 'plant', 'remove', 'rotate', 'staleCounter', 'stranger',
  'publish', 'publishBad', 'submit', 'submitStale', 'submitWrongKey', 'submitPast', 'replay',
  'cancel', 'finaliseEarly', 'finalise', 'advance',
] as const;
type Kind = (typeof KINDS)[number];

async function randomRun(seed: number, variant: Variant): Promise<World> {
  const window = new Prng(seed).between(60n, 7n * 86_400n);
  const w = await World.open(1000 + seed, variant, window);
  const { prng, client } = w;
  const roster: Device[] = [w.owner];
  const colors = [prng.bytes(32), prng.bytes(32)];
  const stranger = w.device();
  let pending: { successor: Device; recovery: Key } | undefined;
  let lastSubmit: Planned | undefined;
  const planted = new Map<string, { device: Device; epoch: bigint; uc: bigint }>();
  const covered = new Map<Kind, number>();
  const pick = <T>(xs: readonly T[]): T => xs[prng.below(xs.length)];
  const balance = (c: Uint8Array) => w.view.balances.find(([k]) => k === hex(c))?.[1] ?? 0n;

  // Every kind once, then weighted towards the stateful ones.
  const schedule: Kind[] = [...KINDS];
  const weighted: Kind[] = [...KINDS, 'deposit', 'withdraw', 'enrol', 'rotate', 'submit', 'submit', 'cancel', 'finalise', 'finalise', 'advance'];
  while (schedule.length < steps) schedule.push(pick(weighted));
  for (let i = schedule.length - 1; i > 1; i--) {
    const j = 1 + prng.below(i);
    [schedule[i], schedule[j]] = [schedule[j], schedule[i]];
  }
  schedule[0] = 'deposit';

  console.log(`\n── random seed ${seed} (account seed ${1000 + seed}), ${schedule.length} steps, veto_window ${window}s, variant ${variant}`);
  for (const kind of schedule) {
    covered.set(kind, (covered.get(kind) ?? 0) + 1);
    const by = pick(roster);
    const color = pick(colors);
    const submitFresh = (label: string, extra = {}) => {
      const S = w.device(), R = w.key();
      return { S, R, p: w.submit(label, S, R, { nowUpper: BigInt(w.acct.now) + BigInt(prng.below(3600)), ...extra }) };
    };
    switch (kind) {
      case 'deposit':
        await w.step(client.deposit('deposit', color, prng.between(1n, 1000n)));
        break;
      case 'withdraw': {
        const bal = balance(color);
        await w.step(client.gated(`withdraw ${bal > 0n ? 'within' : 'from empty'} balance`,
          { kind: 'withdraw', color, amount: bal > 0n ? prng.between(1n, bal) : 1n, recipient: prng.bytes(32) }, by));
        break;
      }
      case 'insufficient':
        await w.step(client.gated('withdraw more than the balance', { kind: 'withdraw', color, amount: balance(color) + 1n, recipient: prng.bytes(32) }, by));
        break;
      case 'enrol': {
        const d = w.device();
        const r = await w.step(client.gated('enrol a fresh device', { kind: 'add', entry: client.entryOf(d) }, by));
        if (r.impl === 'ok') {
          roster.push(d);
          client.counters.set(d, 0n);
        }
        break;
      }
      case 'plant': {
        const epoch = w.view.deviceEpoch + 1n;
        const entry = client.entryOf(by, epoch);
        const r = await w.step(client.gated('a live device enrols its own key at epoch + 1', { kind: 'add', entry }, by));
        if (r.impl === 'ok') planted.set(hex(entry), { device: by, epoch, uc: 0n });
        break;
      }
      case 'remove': {
        const target = pick(roster);
        const entry = target.entryAt(w.acct.address, w.view.deviceEpoch, client.counters.get(target) ?? 0n);
        const r = await w.step(client.gated(target === by ? 'remove own current entry' : 'remove another live device', { kind: 'remove', entry }, by));
        if (r.impl === 'ok') roster.splice(roster.indexOf(target), 1);
        break;
      }
      case 'rotate':
        await w.step(rotate(w, 'rotate enc key', by));
        break;
      case 'staleCounter': {
        const uc = client.counters.get(by) ?? 0n;
        await w.step(rotate(w, `rotate with stale use_counter`, by, { uc: uc === 0n ? 1n : uc - 1n }));
        break;
      }
      case 'stranger':
        await w.step(rotate(w, 'live pk presented, stranger signs', stranger, { pk: by.pk, uc: client.counters.get(by) ?? 0n }));
        break;
      case 'publish': {
        const k = w.key();
        const r = await w.step(client.gated('publish a recovery session', { kind: 'publish', p: w.publication(k) }, by));
        if (r.impl === 'ok') w.recoverySk = k.sk;
        break;
      }
      case 'publishBad':
        await w.step(client.gated('publish with phi_len 1 and slot 2 set', { kind: 'publish', p: w.publication(w.key(), { phiLen: 1n }) }, by));
        break;
      case 'submit': {
        const { S, R, p } = submitFresh('recover_submit');
        const r = await w.step(p);
        if (r.impl === 'ok') {
          pending = { successor: S, recovery: R };
          lastSubmit = p;
        }
        break;
      }
      case 'submitStale':
        await w.step(submitFresh('recover_submit against a stale nonce', { nonce: w.view.authNonce + 1n }).p);
        break;
      case 'submitWrongKey':
        await w.step(submitFresh('recover_submit signed by a stranger', { recoverySk: stranger.sk }).p);
        break;
      case 'submitPast':
        await w.step(submitFresh('recover_submit with now_upper in the past', { nowUpper: BigInt(w.acct.now) - BigInt(1 + prng.below(100)) }).p);
        break;
      case 'replay':
        if (lastSubmit) await w.step(client.rawSubmit('replay the last accepted submission', lastSubmit.args));
        else await w.step(rotate(w, 'rotate enc key', by));
        break;
      case 'cancel': {
        const r = await w.step(cancel(w, 'cancel', by));
        if (r.impl === 'ok') pending = undefined;
        break;
      }
      case 'finaliseEarly':
      case 'finalise': {
        if (w.view.pending) {
          w.acct.now = kind === 'finalise'
            ? Math.max(w.acct.now, w.deadline() + pick([0, 0, 1, 7200]))
            : Math.max(w.acct.now, w.deadline() - 1 - prng.below(100));
        }
        const r = await w.step(client.finalise(kind === 'finalise' ? 'finalise at/after the deadline' : 'finalise just before the deadline'));
        if (r.impl === 'ok' && pending) {
          const successor = pending.successor;
          w.adopt(successor, pending.recovery);
          roster.splice(0, roster.length, successor);
          pending = undefined;
          await w.step(ok(rotate(w, 'random successor operates after finalisation', successor)));
          for (const [entry, credential] of planted) {
            if (credential.epoch !== w.view.deviceEpoch) continue;
            const nonce = w.view.authNonce;
            await w.step(plantedUse(rotate(w,
              `random fresh planted use epoch ${credential.epoch}, counter ${credential.uc}, nonce ${nonce}`,
              credential.device, { uc: credential.uc })));
            planted.delete(entry);
          }
        }
        break;
      }
      case 'advance':
        w.acct.now += prng.below(Number(window / 2n));
        await w.step(client.deposit('deposit after advancing time', color, 1n));
        break;
    }
  }
  console.log(`  coverage: ${KINDS.map((k) => `${k}=${covered.get(k) ?? 0}`).join(' ')}`);
  return w;
}

// ── Main ─────────────────────────────────────────────────────────────────────────────────

console.log('recovery conformance harness');
console.log(`  model  ${MODEL_BIN}`);
console.log(`  impl   ${IMPL_DIR}`);
console.log(`  implementation ${implementation}`);
console.log(`  scenarios: veto_window ${WINDOW}s, T0 ${T0}`);

let failed = false;
const summaries: string[] = [];
for (const variant of variants) {
  const started = Date.now();
  const rpc0 = model.rpcCount;
  let scenariosOk = 0, steps0 = 0, divergent0 = 0, expected = 0;
  if (only === 'all' || only === 'scenarios') {
    for (const [i, s] of scenarios.entries()) {
      console.log(`\n── scenario ${i + 1}/${scenarios.length} ${s.name} [${variant}]: ${s.row}`);
      const w = await World.open(i + 1, variant);
      await s.run(w);
      steps0 += w.log.length;
      divergent0 += w.divergent;
      expected += w.log.filter((l) => l.includes('expected divergence ✓')).length;
      if (w.failures.length === 0) scenariosOk++;
      for (const f of w.failures) console.log(`  FAIL ${f}`);
      console.log(`  ${w.failures.length === 0 ? 'PASS' : 'FAIL'} ${s.name}`);
    }
  }
  let generatedSteps = 0, generatedDivergent = 0, generatedFailures = 0;
  if (only === 'all' || only === 'generated') {
    for (const seed of seeds) {
      const w = await generatedRun(seed, variant);
      generatedSteps += w.log.length;
      generatedDivergent += w.divergent;
      generatedFailures += w.failures.length;
      for (const f of w.failures) console.log(`  FAIL ${f}`);
    }
  }
  let randomSteps = 0, randomDivergent = 0, randomFailures = 0;
  if (only === 'all' || only === 'random') {
    for (const seed of seeds) {
      const w = await randomRun(seed, variant);
      randomSteps += w.log.length;
      randomDivergent += w.divergent;
      randomFailures += w.failures.length;
      for (const f of w.failures) console.log(`  FAIL ${f}`);
    }
  }
  const scenariosPass = !['all', 'scenarios'].includes(only) || scenariosOk === scenarios.length;
  const pass = scenariosPass && generatedFailures === 0 && randomFailures === 0;
  failed ||= !pass;
  const wall = ((Date.now() - started) / 1000).toFixed(1);
  summaries.push(`RESULT [${implementation}/${variant}]: ${pass ? 'PASS' : 'FAIL'} — scenarios ${!['all', 'scenarios'].includes(only) ? '-' : `${scenariosOk}/${scenarios.length} as annotated (${steps0} steps, ${divergent0} divergent, ${expected} of them annotated)`};`
    + ` generated seeds ${!['all', 'generated'].includes(only) ? '-' : `${seeds.join(',')}: ${generatedSteps} steps, ${generatedDivergent} exact planted-use divergences`};`
    + ` random seeds ${!['all', 'random'].includes(only) ? '-' : `${seeds.join(',')}: ${randomSteps} steps, ${randomDivergent} annotated divergences`};`
    + ` ${model.rpcCount - rpc0} primitive round trips; wall ${wall}s`);
}
model.close();
console.log('');
for (const s of summaries) console.log(s);
process.exit(failed ? 1 : 0);

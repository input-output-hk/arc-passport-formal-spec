// Shared driver: an honest client that signs exactly as the implementation's wallet code
// does (with its nonce draws recorded as coin bits), and a runner that executes one call
// on the implementation and judges it with both model oracles.
//
//   Oracle 1 (execute & compare): the model runs its own wallet → client → bridge →
//     admission system on the same coin bits the implementation's signers consumed;
//     settlement, signature, post-state and coin consumption must match.
//   Oracle 2 (decide): the model judges the implementation's observed
//     (pre-state, call incl. signatures, post-state, verdict) at the same block time.
//     Its certificate still uses the model journal. Successful calls separately
//     require implementation VM replay agreement and altered-read rejection.
//
// Historical source/corrected comparison hides pre-finalisation `retained` entries;
// source/source never hides them. RECOVERY_IMPLEMENTATION=repaired instead observes
// current-stamp membership in impl.ts, with no retained-entry masking, and supports
// only corrected-model comparison. Both projections are executable observations,
// not verified refinements of the concrete contract.

import {
  canonical, encodeState, hex, observed, REPAIRED, settled, showPoint, stateDiff,
  type Account, type CallContext, type ChallengeBuilder, type Device, type Impl, type LedgerView, type Point,
} from './impl.ts';
import type { Model, Variant } from './model.ts';
import { Prng, toBits } from './prng.ts';

export interface Planned {
  label: string;
  circuit: string;
  args: unknown[];
  /** Model wallet request (Oracle 1). */
  request: string;
  /** Observed call with the implementation's signatures (Oracle 2). */
  call: string;
  bits: string;
  sig?: string;
  /** The device whose use counter a success advances. */
  signer?: Device;
  /** Admissible implementation verdicts (`ok`, `refused`, `fail CODE`): the scenario's observation. */
  expect?: string[];
  /** Variants for which this step is an annotated divergence. */
  diverges?: Variant[];
}

export interface Publication {
  newRecoveryPk: Point;
  session: Uint8Array;
  phi: readonly [bigint, bigint, bigint, bigint];
  phiLen: bigint;
  wrap: Uint8Array;
}

export type Gate =
  | { kind: 'withdraw'; color: Uint8Array; amount: bigint; recipient: Uint8Array }
  | { kind: 'add' | 'remove'; entry: Uint8Array }
  | { kind: 'rotate'; key: Uint8Array }
  | { kind: 'publish'; p: Publication }
  | { kind: 'cancel' };

const CIRCUIT: Record<Gate['kind'], string> = {
  withdraw: 'withdraw_unshielded_with_jubjub',
  add: 'add_device_with_jubjub',
  remove: 'remove_device_with_jubjub',
  rotate: 'rotate_enc_key_with_jubjub',
  publish: 'publish_recovery_session_with_jubjub',
  cancel: 'recover_cancel_with_jubjub',
};

export interface SubmitOptions {
  recoverySk: bigint;
  successor: Device;
  successorRecoveryPk: Point;
  nowUpper: bigint;
  /** Values the client signs against; default: this account and the current ledger. */
  address?: Uint8Array;
  epoch?: bigint;
  nonce?: bigint;
  recoveryPk?: Point;
}

export class Client {
  /** Each device's next use counter at the live epoch. */
  readonly counters = new Map<Device, bigint>();

  constructor(readonly impl: Impl, readonly acct: Account, readonly prng: Prng) {
    this.counters.set(acct.owner, 0n);
  }

  device(): Device {
    return new this.impl.signer.JubjubDevice(this.impl.signer.randomJubjubScalar(() => this.prng.bytes(32)));
  }

  /** The entry a device enrols under: `epoch` (default the live one), counter 0. */
  entryOf(d: Device, epoch = this.acct.view().deviceEpoch): Uint8Array {
    return d.entryAt(this.acct.address, epoch, 0n);
  }

  private recorder(): { draw: () => bigint; bits: () => string } {
    const draws: string[] = [];
    return {
      draw: () => this.impl.signer.randomJubjubScalar(() => {
        const b = this.prng.bytes(32);
        draws.push(toBits(b));
        return b;
      }),
      bits: () => draws.join(''),
    };
  }

  /** A seam-gated call: `pk` presented, `by` signs at use counter `uc` (default: `by`'s)
   *  for account `address` (default: this one). */
  gated(label: string, g: Gate, by: Device, opts: { pk?: Point; uc?: bigint; address?: Uint8Array } = {}): Planned {
    const pk = opts.pk ?? by.pk;
    const uc = opts.uc ?? this.counters.get(by) ?? 0n;
    const ctx: CallContext = { contractAddress: opts.address ?? this.acct.address, authNonce: this.acct.view().authNonce };
    const c = this.impl.signer.jubjubChallenges;
    const [builder, payload, tokens] = ((): [ChallengeBuilder, unknown[], string] => {
      switch (g.kind) {
        case 'withdraw':
          return [c.withdrawUnshielded(ctx, pk, g.color, g.amount, g.recipient), [g.color, g.amount, { bytes: g.recipient }],
            `W ${hex(g.color)} ${g.amount} ${hex(g.recipient)}`];
        case 'add':
          return [c.addDevice(ctx, pk, g.entry), [g.entry], `A ${hex(g.entry)}`];
        case 'remove':
          return [c.removeDevice(ctx, pk, g.entry), [g.entry], `R ${hex(g.entry)}`];
        case 'rotate':
          return [c.rotateEncKey(ctx, pk, g.key), [g.key], `K ${hex(g.key)}`];
        case 'publish': {
          const p = g.p;
          return [c.publishRecoverySession(ctx, pk, p.newRecoveryPk, p.session, p.phi, p.phiLen, p.wrap),
            [p.newRecoveryPk, p.session, ...p.phi, p.phiLen, p.wrap],
            `P ${showPoint(p.newRecoveryPk)} ${hex(p.session)} ${p.phi.join(' ')} ${p.phiLen} ${hex(p.wrap)}`];
        }
        case 'cancel':
          return [c.recoverCancel(ctx, pk), [], 'C'];
      }
    })();
    const rec = this.recorder();
    const auth = by.sign(builder, uc, rec.draw);
    const sig = `${showPoint(auth.sig_r)} ${auth.sig_s} ${auth.grind_nonce}`;
    return {
      label, circuit: CIRCUIT[g.kind], args: [...payload, pk, uc, auth.sig_r, auth.sig_s, auth.grind_nonce],
      request: `S ${tokens} ${showPoint(pk)} ${uc} ${by.sk} ${ctx.authNonce}`,
      call: `J ${tokens} ${showPoint(pk)} ${uc} ${sig}`, bits: rec.bits(), sig,
      signer: pk === by.pk ? by : undefined,
    };
  }

  /** `recover_submit` signed by the recovery key and co-signed by the successor. */
  submit(label: string, o: SubmitOptions): Planned {
    const v = this.acct.view();
    const epoch = o.epoch ?? v.deviceEpoch;
    const nonce = o.nonce ?? v.authNonce;
    const recoveryPk = o.recoveryPk ?? v.recoveryPk;
    const { signer, gate } = this.impl;
    const recovery = new signer.JubjubDevice(o.recoverySk);
    const rec = this.recorder();
    const auth = gate.signRecoverSubmit(recovery, o.successor,
      gate.recoverSubmitChallenge({ contractAddress: o.address ?? this.acct.address, authNonce: nonce }, recoveryPk, o.successor.pk,
        o.successorRecoveryPk, epoch + 1n, o.nowUpper),
      { successorRecoveryPk: o.successorRecoveryPk, expectedEpoch: epoch, expectedNonce: nonce, nowUpper: o.nowUpper }, rec.draw);
    const sig = `${showPoint(auth.sig_r_recovery)} ${auth.sig_s_recovery} ${showPoint(auth.sig_r_successor)} ${auth.sig_s_successor} ${auth.grind_nonce}`;
    return {
      label, circuit: 'recover_submit', args: gate.recoverSubmitArgs(auth),
      request: `U ${o.recoverySk} ${o.successor.sk} ${showPoint(o.successorRecoveryPk)} ${showPoint(recoveryPk)} ${epoch} ${nonce} ${o.nowUpper}`,
      call: submitCall(auth.successor_pk, auth.successor_recovery_pk, auth.expected_epoch, auth.expected_nonce, auth.now_upper,
        auth.sig_r_recovery, auth.sig_s_recovery, auth.sig_r_successor, auth.sig_s_successor, auth.grind_nonce),
      bits: rec.bits(), sig,
    };
  }

  /** `recover_submit` with arguments taken verbatim, e.g. a replay or a tampered copy. */
  rawSubmit(label: string, args: unknown[]): Planned {
    const [q, q2, e, n, u, rr, sr, rs, ss, g] = args as [Point, Point, bigint, bigint, bigint, Point, bigint, Point, bigint, bigint];
    const call = submitCall(q, q2, e, n, u, rr, sr, rs, ss, g);
    return { label, circuit: 'recover_submit', args, request: `X ${call}`, call, bits: '' };
  }

  finalise(label: string): Planned {
    return { label, circuit: 'recover_finalise', args: [], request: 'X F', call: 'F', bits: '' };
  }

  deposit(label: string, color: Uint8Array, amount: bigint): Planned {
    const call = `D ${hex(color)} ${amount}`;
    return { label, circuit: 'deposit_unshielded', args: [color, amount], request: `X ${call}`, call, bits: '' };
  }
}

/** The same call presented as built outside the wallet (no model-side signing). */
export function asRaw(p: Planned, label = p.label): Planned {
  return { ...p, label, request: `X ${p.call}`, bits: '', sig: undefined, signer: undefined };
}

function submitCall(q: Point, q2: Point, e: bigint, n: bigint, u: bigint, rr: Point, sr: bigint, rs: Point, ss: bigint, g: bigint): string {
  return `U ${showPoint(q)} ${showPoint(q2)} ${e} ${n} ${u} ${showPoint(rr)} ${sr} ${showPoint(rs)} ${ss} ${g}`;
}

export interface StepResult {
  impl: string;
  model: string;
  reasons: string[];
  decided: boolean;
  diverged: boolean;
  coins: number;
  /** Successful calls additionally verify the implementation's public VM transcript. */
  transcriptVerified: boolean;
  rpc: number;
}

export class Runner {
  private modelState: LedgerView;
  /** Entries the corrected finalisation removed but the implementation kept. */
  private readonly retained = new Set<string>();

  constructor(readonly model: Model, readonly client: Client, readonly variant: Variant) {
    this.modelState = this.project(client.acct.view());
  }

  private project(v: LedgerView): LedgerView {
    return { ...v, devices: v.devices.filter((d) => !this.retained.has(d)) };
  }

  async run(p: Planned): Promise<StepResult> {
    const { acct, counters } = this.client;
    const time = acct.now;
    const rawPre = acct.view();
    const verdict = await acct.call(p.circuit, ...p.args);
    const rawPost = acct.view();
    if (verdict.ok && p.signer) counters.set(p.signer, (counters.get(p.signer) ?? 0n) + 1n);
    if (verdict.ok && p.circuit === 'recover_finalise' && this.variant === 'corrected' && !REPAIRED) {
      for (const d of rawPre.devices) if (d !== rawPre.pendingEntry) this.retained.add(d);
    }
    const pre = this.project(rawPre);
    const post = this.project(rawPost);
    const impl = settled(verdict);
    const rpcBefore = this.model.rpcCount;

    const reasons: string[] = [];
    const answer = await this.model.step(this.variant, acct.addressHex, time, this.modelState, p.request, p.bits);
    let model = impl;
    let next = post;
    if (answer.kind !== 'answer') {
      reasons.push(answer.text);
      model = answer.kind;
    } else {
      model = answer.settled;
      next = answer.post;
      if (answer.settled !== impl) reasons.push(`verdict model=${answer.settled}`);
      if (answer.sig !== p.sig) reasons.push(`signature model=${answer.sig ?? '-'} impl=${p.sig ?? '-'}`);
      if (canonical(answer.post) !== canonical(post)) reasons.push(`state ${stateDiff(answer.post, post)}`);
      if (answer.restBits !== 0) reasons.push(`${answer.restBits} unread coin bits`);
    }
    // A divergent model state is re-synchronised so later steps are judged locally.
    this.modelState = reasons.length === 0 ? next : post;

    const transcriptVerified = !verdict.ok || (verdict.transcript?.verified === true && verdict.transcript.tamperRejected);
    const decided = transcriptVerified && await this.model.decide(
      this.variant, acct.addressHex, time, encodeState(pre), p.call, encodeState(post), observed(verdict),
    );
    return {
      impl, model, reasons, decided, diverged: reasons.length > 0 || !decided, transcriptVerified,
      coins: p.bits.length, rpc: this.model.rpcCount - rpcBefore,
    };
  }
}

export function option(name: string, fallback: string): string {
  const at = process.argv.indexOf(`--${name}`);
  return at < 0 ? fallback : process.argv[at + 1];
}

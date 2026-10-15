// The model side: the MAlonzo-compiled Conformance.Main as a line-protocol subprocess.
// It sends `? <primitive> <args>` lines while evaluating and finishes each request with
// `= <answer>`; the primitives are answered here by the implementation's own pure
// circuits and compact-runtime (the accepted shared-oracle caveat).
//
// Requests (see src/Conformance/Main.agda):
//   step   VARIANT SELF TIME <state> <request> B <bits|->
//   decide VARIANT SELF TIME <state> <call> <state> <ok | fail CODE>
// where VARIANT = source | corrected and
//   <gated>   = W color amount recipient | A entry | R entry | K key
//             | P qx qy session phi1 phi2 phi3 phi4 phiLen wrap | C
//   <request> = S <gated> pkx pky useCounter sk nonce
//             | U recoverySk successorSk q'x q'y rpkx rpky epoch nonce nowUpper
//             | X <call>
//   <call>    = D color amount | F
//             | U qx qy q'x q'y epoch nonce nowUpper Rrx Rry sr Rsx Rsy ss grind
//             | J <gated> pkx pky useCounter rx ry s grind

import { spawn, type ChildProcessWithoutNullStreams } from 'node:child_process';
import { createInterface } from 'node:readline';
import { fileURLToPath } from 'node:url';

import { decodeState, encodeState, hex, showPoint, unhex, type Impl, type LedgerView, type Point } from './impl.ts';

export const MODEL_BIN =
  process.env.MODEL_BIN ?? fileURLToPath(new URL('../../_build/conformance/Main', import.meta.url));

export type Variant = 'source' | 'corrected';

/** Oracle 1's answer: settlement (`ok`, `refused`, `fail CODE`), signature tokens, post-state. */
export type StepAnswer =
  | { kind: 'answer'; settled: string; sig?: string; post: LedgerView; restBits: number }
  | { kind: 'stuck' | 'error'; text: string };

export class Model {
  private readonly child: ChildProcessWithoutNullStreams;
  private readonly lines: AsyncIterator<string>;
  /** Primitive round trips answered since construction. */
  rpcCount = 0;
  private stderr = '';

  constructor(private readonly impl: Impl, bin = MODEL_BIN) {
    this.child = spawn(bin, [], { stdio: ['pipe', 'pipe', 'pipe'] });
    this.child.stderr.on('data', (chunk: Buffer) => { this.stderr += chunk.toString(); });
    this.lines = createInterface({ input: this.child.stdout })[Symbol.asyncIterator]();
  }

  async request(line: string): Promise<string> {
    this.child.stdin.write(`${line}\n`);
    for (;;) {
      const { value, done } = await this.lines.next();
      if (done) throw new Error(`model exited on: ${line.slice(0, 400)}\n${this.stderr}`);
      if (value.startsWith('= ')) return value.slice(2);
      if (!value.startsWith('? ')) throw new Error(`unexpected model output: ${value}`);
      this.rpcCount++;
      this.child.stdin.write(`${this.primitive(value.slice(2).split(' '))}\n`);
    }
  }

  async step(variant: Variant, self: string, time: number, pre: LedgerView, request: string, bits: string): Promise<StepAnswer> {
    const answer = (await this.request(`step ${variant} ${self} ${time} ${encodeState(pre)} ${request} B ${bits || '-'}`)).split(/\s+/);
    if (answer[0] === 'stuck' || answer[0] === 'error') return { kind: answer[0], text: answer.join(' ') };
    let k = answer[0] === 'fail' ? 2 : 1;
    const settled = answer.slice(0, k).join(' ');
    const sigStart = k + 1; // after "sig"
    const stateAt = answer.indexOf('state', sigStart);
    const sig = answer[sigStart] === '-' ? undefined : answer.slice(sigStart, stateAt).join(' ');
    k = stateAt + 1;
    const [post, after] = decodeState(answer, k);
    return { kind: 'answer', settled, sig, post, restBits: Number(answer[after + 1]) };
  }

  async decide(variant: Variant, self: string, time: number, pre: string, call: string, post: string, verdict: string): Promise<boolean> {
    return (await this.request(`decide ${variant} ${self} ${time} ${pre} ${call} ${post} ${verdict}`)) === 'true';
  }

  close(): void {
    this.child.stdin.end();
  }

  private primitive([op, ...a]: string[]): string {
    const { rt, pureCircuits: pc } = this.impl;
    const n = (i: number) => BigInt(a[i]);
    const pt = (i: number): Point => ({ x: n(i), y: n(i + 1) });
    const self = () => ({ bytes: unhex(a[0]) });
    switch (op) {
      case 'entry':
        return hex(pc.derive_device_entry_with_jubjub(self(), pt(1), n(3), n(4)));
      case 'chal-w':
        return hex(pc.challenge_withdraw_unshielded_with_jubjub(self(), pt(1), pt(3), unhex(a[5]), n(6), { bytes: unhex(a[7]) }, n(8), n(9)));
      case 'chal-add':
        return hex(pc.challenge_add_device_with_jubjub(self(), pt(1), pt(3), unhex(a[5]), n(6), n(7)));
      case 'chal-rm':
        return hex(pc.challenge_remove_device_with_jubjub(self(), pt(1), pt(3), unhex(a[5]), n(6), n(7)));
      case 'chal-rot':
        return hex(pc.challenge_rotate_enc_key_with_jubjub(self(), pt(1), pt(3), unhex(a[5]), n(6), n(7)));
      case 'chal-pub':
        return hex(pc.challenge_publish_recovery_session_with_jubjub(self(), pt(1), pt(3), pt(5), unhex(a[7]),
          n(8), n(9), n(10), n(11), n(12), unhex(a[13]), n(14), n(15)));
      case 'chal-cancel':
        return hex(pc.challenge_recover_cancel_with_jubjub(self(), pt(1), pt(3), n(5), n(6)));
      case 'chal-submit':
        return hex(pc.challenge_recover_submit(self(), pt(1), pt(3), pt(5), pt(7), pt(9), n(11), n(12), n(13), n(14)));
      // Scalars are reduced mod r_J exactly as the generated circuit code does before ecMul.
      case 'mulg':
        return showPoint(rt.ecMulGenerator(rt.convertNumericToJubjubScalar(n(0))));
      case 'mul':
        return showPoint(rt.ecMul(pt(0), rt.convertNumericToJubjubScalar(n(2))));
      case 'add':
        return showPoint(rt.ecAdd(pt(0), pt(2)));
      default:
        throw new Error(`unknown primitive ${op}`);
    }
  }
}

// Seeded byte stream (sfc32 seeded through splitmix32). Every random choice of a run —
// keys, salts, colours, amounts, schedule, and the signer's nonce draws — comes from
// one stream, so a seed reproduces the run exactly.

function splitmix32(seed: number): () => number {
  let s = seed >>> 0;
  return () => {
    s = (s + 0x9e3779b9) >>> 0;
    let z = s;
    z = Math.imul(z ^ (z >>> 16), 0x85ebca6b) >>> 0;
    z = Math.imul(z ^ (z >>> 13), 0xc2b2ae35) >>> 0;
    return (z ^ (z >>> 16)) >>> 0;
  };
}

export class Prng {
  private a: number;
  private b: number;
  private c: number;
  private d: number;

  constructor(seed: number) {
    const init = splitmix32(seed);
    this.a = init();
    this.b = init();
    this.c = init();
    this.d = init();
    for (let i = 0; i < 16; i++) this.next();
  }

  next(): number {
    const t = (((this.a + this.b) >>> 0) + this.d) >>> 0;
    this.d = (this.d + 1) >>> 0;
    this.a = this.b ^ (this.b >>> 9);
    this.b = (this.c + (this.c << 3)) >>> 0;
    this.c = ((this.c << 21) | (this.c >>> 11)) >>> 0;
    this.c = (this.c + t) >>> 0;
    return t;
  }

  bytes(n: number): Uint8Array {
    const out = new Uint8Array(n);
    for (let i = 0; i < n; i += 4) {
      const w = this.next();
      for (let j = 0; j < 4 && i + j < n; j++) out[i + j] = (w >>> (8 * j)) & 0xff;
    }
    return out;
  }

  /** Uniform integer in [0, n) for small n. */
  below(n: number): number {
    return this.next() % n;
  }

  /** Uniform bigint in [lo, hi] for small ranges. */
  between(lo: bigint, hi: bigint): bigint {
    return lo + (BigInt(this.next()) * 0x100000000n + BigInt(this.next())) % (hi - lo + 1n);
  }
}

/** Bits of a byte string, most significant bit of each byte first (the order in which
 *  `BigInt('0x' + hex)` reads them, i.e. the model's `fromBitsBE`). */
export function toBits(bytes: Uint8Array): string {
  let s = '';
  for (const b of bytes) s += b.toString(2).padStart(8, '0');
  return s;
}

// SHA-256 over fixed-width Compact atoms, independent of the runtime codec.
// Encoding reference: pinned Passport signer-rs/src/main.rs, Element encoders
// and the by-hand device-entry vectors. No compiler/runtime hash helper is used.
import { createHash } from 'node:crypto';
import type { Value } from './full-wire.ts';

const FIELD_ORDER = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001n;

function unsigned(value: Value, width: number, limit = 1n << BigInt(width * 8)): Uint8Array {
  if (value.tag !== 'nat' || !/^(0|[1-9][0-9]*)$/.test(value.value)) throw new Error('noncanonical hash integer');
  let n = BigInt(value.value);
  if (n >= limit) throw new Error(`hash integer exceeds ${width}-byte domain`);
  const encoded = new Uint8Array(width);
  for (let i = 0; i < width; i++, n >>= 8n) encoded[i] = Number(n & 255n);
  return encoded;
}

function octets(value: Value, width: number): Uint8Array {
  if (value.tag !== 'bytes' || value.value.length !== width
    || value.value.some(x => !Number.isInteger(x) || x < 0 || x > 255)) throw new Error(`invalid Bytes<${width}> hash atom`);
  return Uint8Array.from(value.value);
}

function tuple(value: Value, length: number): Value[] {
  if (value.tag !== 'tuple' || value.value.length !== length) throw new Error('hash struct arity mismatch');
  return value.value;
}

function encode(type: string, value: Value): Uint8Array[] {
  const bytes = /^Bytes<([0-9]+)>$/.exec(type);
  if (bytes) {
    const width = Number(bytes[1]);
    if (!Number.isSafeInteger(width) || width < 0) throw new Error('invalid hash byte width');
    return [octets(value, width)];
  }
  const uint = /^Uint<(8|32|64|128)>$/.exec(type);
  if (uint) return [unsigned(value, Number(uint[1]) / 8)];
  switch (type) {
    case 'Boolean':
      if (value.tag !== 'bool') throw new Error('invalid Boolean hash atom');
      return [Uint8Array.of(value.value ? 1 : 0)];
    case 'Field': return [unsigned(value, 32, FIELD_ORDER)];
    case 'ContractAddress': case 'UserAddress': case 'ZswapCoinPublicKey':
      return [octets(value, 32)];
    case 'JubjubPoint': {
      const [x, y] = tuple(value, 2);
      return [unsigned(x, 32, FIELD_ORDER), unsigned(y, 32, FIELD_ORDER)];
    }
    case 'ShieldedCoinInfo': {
      const [nonce, color, amount] = tuple(value, 3);
      return [octets(nonce, 32), octets(color, 32), unsigned(amount, 16)];
    }
    case 'QualifiedShieldedCoinInfo': {
      const [nonce, color, amount, index] = tuple(value, 4);
      return [octets(nonce, 32), octets(color, 32), unsigned(amount, 16), unsigned(index, 8)];
    }
    default: throw new Error(`unsupported independent hash atom: ${type}`);
  }
}

export function independentPersistentHash(atoms: readonly (readonly [string, Value])[]): Uint8Array {
  const hash = createHash('sha256');
  for (const [type, value] of atoms) for (const encoded of encode(type, value)) hash.update(encoded);
  return hash.digest();
}

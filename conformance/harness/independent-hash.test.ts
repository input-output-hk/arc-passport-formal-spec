import assert from 'node:assert/strict';
import test from 'node:test';
import { independentPersistentHash } from './independent-hash.ts';
import { bytes, nat } from './full-wire.ts';

test('matches the independently published k256 device-entry encoding vector', () => {
  const tag = new Uint8Array(32);
  tag.set(new TextEncoder().encode('midnight:account:device:k1:v2'));
  const digest = independentPersistentHash([
    ['Bytes<32>', bytes(tag)],
    ['ContractAddress', bytes(new Uint8Array(32).fill(0x11))],
    ['Bytes<32>', bytes(Buffer.from('79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798', 'hex').reverse())],
    ['Bytes<32>', bytes(Buffer.from('483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8', 'hex').reverse())],
    ['Uint<8>', nat(0n)], ['Uint<32>', nat(0n)], ['Uint<64>', nat(0n)],
  ]);
  assert.equal(Buffer.from(digest).toString('hex'), 'f88e6a3085478879ae9e3859c59493a60b2d443c1608f6bcedbdb7ee1a8f5d66');
});

test('rejects overflowing integers instead of truncating hash preimages', () => {
  assert.throws(() => independentPersistentHash([['Uint<64>', nat(1n << 64n)]]));
});

test('requires canonical field elements rather than reducing the preimage', () => {
  const modulus = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001n;
  assert.throws(() => independentPersistentHash([['Field', nat(modulus)]]));
});

test('does not pad malformed byte atoms into otherwise valid hash preimages', () => {
  assert.throws(() => independentPersistentHash([['Bytes<32>', bytes(new Uint8Array(31))]]));
});

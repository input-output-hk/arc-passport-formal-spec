import { decodeRuntimeValue } from './concrete.ts';
import { independentPersistentHash } from './independent-hash.ts';
import { record } from './full-impl.ts';
import type { FullObservation } from './full-impl.ts';
import type { FullEffect } from './full-model.ts';
import { bytes, qualifiedCoinType, toValue, tuple } from './full-wire.ts';
import type { TypeInfo, Value } from './full-wire.ts';

const coinType: TypeInfo = { 'type-name': 'Struct', name: 'ShieldedCoinInfo', elements: qualifiedCoinType.elements!.slice(0, 3) };
const same = (a: unknown, b: unknown): boolean => JSON.stringify(a) === JSON.stringify(b);
function octets(v: Value): string {
  if (v.tag !== 'bytes') throw new Error('expected effect bytes');
  return Buffer.from(v.value).toString('hex');
}
function count(v: Value): bigint {
  if (v.tag !== 'nat') throw new Error('expected effect amount');
  return BigInt(v.value);
}
function entries(v: unknown): [unknown, unknown][] {
  if (!(v instanceof Map)) throw new Error('expected declared native effect map');
  return [...v];
}
function ordered<T>(values: T[]): T[] {
  return values.sort((a, b) => JSON.stringify(a).localeCompare(JSON.stringify(b)));
}
function strings(v: unknown): string[] {
  if (!Array.isArray(v) || v.some(x => typeof x !== 'string')) throw new Error('invalid native commitment/nullifier list');
  return ordered(v as string[]);
}
function token(v: unknown): string {
  const t = record(v, 'native token type');
  if (t.tag !== 'unshielded' || typeof t.raw !== 'string') throw new Error('unexpected non-unshielded native effect token');
  return t.raw;
}
function amount(v: unknown): string {
  if (typeof v !== 'bigint' || v < 0n) throw new Error('invalid native effect amount');
  return String(v);
}
function commitment(coin: Value, self: Value): string {
  return Buffer.from(independentPersistentHash([
    ['Bytes<21>', bytes(Buffer.from('midnight:zswap-cc[v1]'))], ['ShieldedCoinInfo', coin],
    ['Boolean', { tag: 'bool', value: false }], ['Bytes<32>', self],
  ])).toString('hex');
}
function aggregate(effects: FullEffect[], tag: string): [string, string][] {
  const amounts = new Map<string, bigint>();
  for (const effect of effects.filter(e => e.tag === tag)) {
    const key = octets(effect.arguments[0]);
    amounts.set(key, (amounts.get(key) ?? 0n) + count(effect.arguments[1]));
  }
  return ordered([...amounts].map(([k, n]) => [k, String(n)] as [string, string]));
}
/** Compare declarations to declarations, not authenticated transaction assets.
 * Both sides remain in the report, including actual Zswap witness I/O. */
export function compareNativeEffects(observation: FullObservation, model: FullEffect[]): { matches: boolean; reasons: string[]; authenticatedAssets: false } {
  const outcome = observation.outcome;
  if (outcome.tag !== 'accepted') throw new Error('effect comparison requires accepted concrete execution');
  const actual = record(decodeRuntimeValue(outcome.nativeEffects), 'native effects');
  const reasons: string[] = [];
  const compare = (label: string, a: unknown, b: unknown): void => { if (!same(a, b)) reasons.push(label); };
  compare('unshielded input declarations', ordered(entries(actual.unshieldedInputs).map(([k, v]) => [token(k), amount(v)])), aggregate(model, 'receiveUnshielded'));
  compare('unshielded output declarations', ordered(entries(actual.unshieldedOutputs).map(([k, v]) => [token(k), amount(v)])), aggregate(model, 'sendUnshielded'));
  const expectedClaimed = model.filter(e => e.tag === 'sendUnshielded').map(e => {
    const [color, n, recipient] = e.arguments;
    if (recipient.tag !== 'tuple' || recipient.value.length !== 2 || recipient.value[0].tag !== 'bool') throw new Error('invalid model public recipient');
    return [octets(color), String(count(n)), recipient.value[0].value ? 'contract' : 'user', octets(recipient.value[1])];
  });
  const actualClaimed = entries(actual.claimedUnshieldedSpends).map(([key, n]) => {
    if (!Array.isArray(key) || key.length !== 2) throw new Error('invalid native unshielded claim key');
    const recipient = record(key[1]);
    if ((recipient.tag !== 'user' && recipient.tag !== 'contract') || typeof recipient.address !== 'string') throw new Error('invalid native public recipient');
    return [token(key[0]), amount(n), recipient.tag, recipient.address];
  });
  compare('unshielded recipient claims', ordered(actualClaimed), ordered(expectedClaimed));
  const consume = model.filter(e => e.tag === 'consumeShielded');
  const create = model.filter(e => e.tag === 'createShielded');
  const receive = model.filter(e => e.tag === 'receiveShielded');
  compare('shielded nullifier declarations', strings(actual.claimedNullifiers), ordered(consume.map(e => octets(e.arguments[1]))));
  compare('shielded receive declarations', strings(actual.claimedShieldedReceives), ordered(receive.map(e => commitment(e.arguments[0], observation.request.context.self))));
  compare('shielded spend declarations', strings(actual.claimedShieldedSpends), consume.length === 0 ? [] : ordered(create.map(e => octets(e.arguments[2]))));
  if (!Array.isArray(actual.claimedContractCalls) || actual.claimedContractCalls.length !== 0
    || entries(actual.shieldedMints).length !== 0 || entries(actual.unshieldedMints).length !== 0) reasons.push('unexpected calls or mint declarations');
  const zswap = record(decodeRuntimeValue(outcome.zswap), 'Zswap local state');
  if (!Array.isArray(zswap.inputs) || !Array.isArray(zswap.outputs)) throw new Error('invalid native Zswap state');
  compare('shielded input witness descriptions', zswap.inputs.map(c => toValue(qualifiedCoinType, c)), consume.map(e => e.arguments[0]));
  const zoutputs = zswap.outputs.map(o => {
    const output = record(o), recipient = record(output.recipient);
    if (typeof recipient.is_left !== 'boolean') throw new Error('invalid native shielded recipient');
    const address = record(recipient.is_left ? recipient.left : recipient.right).bytes;
    if (!(address instanceof Uint8Array)) throw new Error('invalid native shielded recipient address');
    return [toValue(coinType, output.coinInfo), tuple([{ tag: 'bool', value: recipient.is_left }, bytes(address)])];
  });
  compare('shielded output descriptions and recipients', zoutputs, create.map(e => [e.arguments[0], e.arguments[1]]));
  compare('shielded output index', typeof zswap.currentIndex === 'bigint' ? String(zswap.currentIndex) : null, String(create.length));
  if (outcome.nativeCommitments.length !== 1) reasons.push('unexpected native context count');
  for (const context of outcome.nativeCommitments) {
    const expected = new Map(context.before);
    create.forEach((effect, index) => expected.set(octets(effect.arguments[2]), String(index)));
    compare('native output commitment-index registrations', ordered(context.after), ordered([...expected]));
  }
  const witnesses = model.filter(e => e.tag === 'witness').map(e => ({
    name: Buffer.from(e.arguments[0].tag === 'bytes' ? e.arguments[0].value : []).toString('utf8'), color: e.arguments[1], coin: e.arguments[2],
  }));
  compare('production held_coin witness observations', observation.witnesses, witnesses);
  return { matches: reasons.length === 0, reasons, authenticatedAssets: false };
}

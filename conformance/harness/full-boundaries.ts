// Explicit represented states, not claimed reachable histories. Changes are
// made to the native StateValue encoding and decoded by the pinned runtime.
import { record, stateEncoding } from './full-impl.ts';
import type { AccountState, FullAccount } from './full-impl.ts';

export function installRepresentedFixture(account: FullAccount, update: { deviceEpoch?: bigint; deviceEntries?: Uint8Array[] }): AccountState {
  if (!account.state) throw new Error('boundary fixture requires a constructed account');
  const previous = account.state;
  const root = record(stateEncoding(previous));
  if (root.tag !== 'array' || !Array.isArray(root.content) || root.content.length !== 2) throw new Error('account root schema drift');
  const group = record(root.content[0]);
  if (group.tag !== 'array' || !Array.isArray(group.content) || group.content.length !== 10) throw new Error('account base schema drift');
  if (update.deviceEpoch !== undefined) {
    if (update.deviceEpoch < 0n || update.deviceEpoch >= 1n << 32n) throw new Error('invalid represented epoch');
    const cell = record(group.content[7]);
    const aligned = record(cell.content);
    if (cell.tag !== 'cell' || !Array.isArray(aligned.value) || aligned.value.length !== 1) throw new Error('epoch cell schema drift');
    const encoded: number[] = [];
    for (let n = update.deviceEpoch; n > 0n; n >>= 8n) encoded.push(Number(n & 255n));
    aligned.value[0] = Uint8Array.from(encoded);
  }
  if (update.deviceEntries !== undefined) {
    const devices = record(group.content[6]);
    if (devices.tag !== 'map' || !(devices.content instanceof Map)) throw new Error('device Set schema drift');
    const entries = new Map<unknown, unknown>();
    for (const entry of update.deviceEntries) {
      if (entry.length !== 32) throw new Error('invalid represented device entry');
      entries.set({ value: [entry], alignment: [{ tag: 'atom', value: { tag: 'bytes', length: 32 } }] }, { tag: 'null' });
    }
    devices.content = entries;
  }
  const Type = account.impl.runtime.StateValue;
  if (typeof Type !== 'function' || !('decode' in Type) || typeof Type.decode !== 'function') throw new Error('missing native StateValue.decode');
  const state = Reflect.apply(Type.decode, Type, [root]);
  if (state === null || typeof state !== 'object' || !('encode' in state) || typeof state.encode !== 'function') throw new Error('invalid decoded boundary fixture');
  // The value was decoded by the pinned native StateValue constructor above.
  account.state = state as AccountState;
  account.origin = 'synthetic-represented-state';
  return previous;
}

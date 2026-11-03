// Every counted item invokes the generated runtime circuit (including negative
// items); source signer helpers provide actual signatures and held_coin uses the
// production private coin store. No circuit is credited for merely existing.
import { FullAccount, invoke, record, rnd } from './full-impl.ts';
import type { FullImplementation, FullObservation, Module } from './full-impl.ts';
import { installRepresentedFixture } from './full-boundaries.ts';
import type { FormalVM } from './vm-formal.ts';

type Arm = 'jubjub' | 'k256' | 'p256';
interface Actor { arm: Arm; device: Module; grantee: Module; counter: bigint }
interface Coin { nonce: Uint8Array; color: Uint8Array; value: bigint; mt_index: bigint }
export interface ScenarioResult { observations: FullObservation[]; expectations: { label: string; expected: 'accepted' | 'rejected'; actual: string; boundsBits?: string }[] }
function array(x: unknown): unknown[] {
  if (!Array.isArray(x)) throw new Error('expected signer argument array');
  return x;
}
function generate(module: Module, name: string): Module {
  const ctor = module[name];
  if (typeof ctor !== 'function' || !('generate' in ctor) || typeof ctor.generate !== 'function') throw new Error(`missing signer ${name}.generate`);
  return record(Reflect.apply(ctor.generate, ctor, []), name);
}
function actor(impl: FullImplementation, arm: Arm): Actor {
  if (arm === 'p256') {
    const f = record(invoke(impl.fixtures, 'softwarePasskey'));
    return { arm, device: record(f.device), grantee: record(f.grantee), counter: 0n };
  }
  return { arm, device: generate(impl.signer, arm === 'jubjub' ? 'JubjubDevice' : 'K256Device'),
    grantee: generate(impl.signer, arm === 'jubjub' ? 'JubjubGrantee' : 'K256Grantee'), counter: 0n };
}
const deviceBuilders = (impl: FullImplementation, arm: Arm): Module => record(arm === 'p256' ? impl.p256.p256Challenges
  : arm === 'jubjub' ? impl.signer.jubjubChallenges : impl.signer.k256Challenges);
const grantBuilders = (impl: FullImplementation, arm: Arm): Module => record(arm === 'p256' ? impl.p256.p256GrantChallenges
  : arm === 'jubjub' ? impl.signer.jubjubGrantChallenges : impl.signer.k256GrantChallenges);
export async function fullScenarios(impl: FullImplementation, formalVM: FormalVM): Promise<ScenarioResult> {
  const observations: FullObservation[] = [];
  const expectations: ScenarioResult['expectations'] = [];
  const run = async (account: FullAccount, label: string, name: string, args: unknown[], expected: 'accepted' | 'rejected', boundsBits?: string) => {
    const o = await account.call(label, name, args);
    observations.push(o);
    expectations.push({ label, expected, actual: o.outcome.tag, ...(boundsBits ? { boundsBits } : {}) });
    return o;
  };
  for (const arm of ['jubjub', 'k256', 'p256'] as const) {
    const owner = actor(impl, arm), stranger = actor(impl, arm);
    const recovery = generate(impl.signer, 'JubjubDevice');
    const account = new FullAccount(impl, formalVM);
    const prefix = (s: string) => `${arm}: ${s}`;
    const salt = rnd(), enc = rnd(), wrap = rnd(64);
    const boot = invoke(owner.device, 'bootCommitment', salt);
    const constructorArgs = [boot, enc, recovery.pk, wrap, 60n];
    await run(account, prefix('constructor rejects Uint64 overflow'), 'constructor', [...constructorArgs.slice(0, 4), 1n << 64n], 'rejected');
    await run(account, prefix('constructor'), 'constructor', constructorArgs, 'accepted');
    const activation = (s: Uint8Array): unknown[] => arm === 'p256' ? [owner.device.pk, s, owner.device.policy]
      : arm === 'k256' ? [owner.device.pk, s, owner.device.envelope] : [owner.device.pk, s];
    await run(account, prefix('activation boot mismatch'), `activate_initial_device_with_${arm}`, activation(rnd()), 'rejected');
    await run(account, prefix('activation'), `activate_initial_device_with_${arm}`, activation(salt), 'accepted');
    await run(account, prefix('activation replay'), `activate_initial_device_with_${arm}`, activation(salt), 'rejected');
    const callContext = () => ({ contractAddress: account.address, authNonce: account.ledger().auth_nonce });
    const signed = async (builder: string, fields: unknown[], by = owner) => {
      const challenge = invoke(deviceBuilders(impl, by.arm), builder, callContext(), by.device.pk, ...fields);
      const auth = await invoke(by.device, 'sign', challenge, by.counter);
      return array(invoke(impl.signer, 'authArgs', auth));
    };
    const gated = async (label: string, operation: string, builder: string, fields: unknown[], args: unknown[], expected: 'accepted' | 'rejected' = 'accepted', by = owner, boundsBits?: string) => {
      const auth = await signed(builder, fields, by);
      const result = await run(account, prefix(label), `${operation}_with_${by.arm}`, [...args, ...auth], expected, boundsBits);
      if (result.outcome.tag === 'accepted') by.counter++;
      return { result, args: [...args, ...auth] };
    };
    const color = rnd(), unknown = rnd(), recipient = rnd();
    await run(account, prefix('fund unshielded'), 'deposit_unshielded', [color, 1_000n], 'accepted');
    await run(account, prefix('deposit overflow'), 'deposit_unshielded', [color, (1n << 128n) - 1n], 'rejected');
    const inbox = rnd(192);
    const appended = await gated('append inbox', 'append_inbox', 'appendInbox', [inbox], [inbox]);
    await run(account, prefix('append inbox replay'), `append_inbox_with_${arm}`, appended.args, 'rejected');
    const key = rnd();
    const rotated = await gated('rotate encryption key', 'rotate_enc_key', 'rotateEncKey', [key], [key]);
    await run(account, prefix('rotate key replay'), `rotate_enc_key_with_${arm}`, rotated.args, 'rejected');
    await gated('unregistered device', 'rotate_enc_key', 'rotateEncKey', [rnd()], [rnd()], 'rejected', stranger);
    const entry = invoke(stranger.device, 'entryAt', account.address, account.ledger().device_epoch, 0n);
    await gated('enrol device', 'add_device', 'addDevice', [entry], [entry]);
    await gated('duplicate device', 'add_device', 'addDevice', [entry], [entry], 'rejected');
    await gated('remove device', 'remove_device', 'removeDevice', [entry], [entry]);
    await gated('remove missing device', 'remove_device', 'removeDevice', [entry], [entry], 'rejected');
    const nextEntry = invoke(owner.device, 'entryAt', account.address, account.ledger().device_epoch, owner.counter + 1n);
    await gated('last device removal', 'remove_device', 'removeDevice', [nextEntry], [nextEntry], 'rejected');
    const withdrawal = await gated('withdraw unshielded', 'withdraw_unshielded', 'withdrawUnshielded', [color, 5n, recipient], [color, 5n, { bytes: recipient }]);
    await run(account, prefix('withdraw unshielded replay'), `withdraw_unshielded_with_${arm}`, withdrawal.args, 'rejected');
    await gated('withdraw insufficient', 'withdraw_unshielded', 'withdrawUnshielded', [color, 10_000n, recipient], [color, 10_000n, { bytes: recipient }], 'rejected');
    await gated('withdraw absent color', 'withdraw_unshielded', 'withdrawUnshielded', [unknown, 1n, recipient], [unknown, 1n, { bytes: recipient }], 'rejected');
    const depositCoin = async (label: string, amount = 10n): Promise<Coin> => {
      const coin: Coin = { nonce: rnd(), color, value: amount, mt_index: 0n };
      // The runtime emits a real contract-owned Zswap output. The local
      // simulator's per-call output index starts at zero; a chain proof's
      // global Merkle qualification is deliberately not asserted here.
      await run(account, prefix(label), 'deposit_shielded', [{ nonce: coin.nonce, color, value: amount }, rnd(192)], 'accepted');
      account.setCoin(coin);
      return coin;
    };
    await run(account, prefix('shielded input value overflow'), 'deposit_shielded', [{ nonce: rnd(), color, value: 1n << 128n }, rnd(192)], 'rejected');
    for (const [operation, builder] of [['withdraw_shielded', 'withdrawShielded'], ['withdraw_shielded_to_contract', 'withdrawShieldedToContract']] as const) {
      const coin = await depositCoin(`fund ${operation}`);
      await gated(`${operation} change`, operation, builder, [recipient, color, 4n, coin], [{ bytes: recipient }, color, 4n]);
      const oversized = await depositCoin(`fund ${operation} overspend`);
      await gated(`${operation} overspend`, operation, builder, [recipient, color, 11n, oversized], [{ bytes: recipient }, color, 11n], 'rejected');
      const full = await depositCoin(`fund ${operation} exact`);
      await gated(`${operation} exact`, operation, builder, [recipient, color, 10n, full], [{ bytes: recipient }, color, 10n]);
    }
    const origin = invoke(impl.signer, 'originHash', 'http://localhost:8973');
    const grantee = stranger.grantee;
    const grantId = invoke(grantee, 'grantId', account.address, origin, 0n), grantSalt = rnd();
    const scope = record(invoke(impl.signer, 'spendScope', {
      withdrawUnshielded: true, withdrawShielded: true, withdrawShieldedToContract: true,
      color, cap: 100n, perCallCap: 20n, maxCoinValue: 20n, readPkHash: rnd(),
      ...(arm === 'p256' ? { rpIdHash: record(grantee.policy).rp_id_hash } : {}),
    }));
    const scopeFields = array(invoke(impl.signer, 'scopeArgs', scope));
    const digest = invoke(impl.signer, 'scopeDigest', grantSalt, scope);
    await gated('issue grant', 'issue_grant', 'issueGrant', [grantId, digest], [grantId, ...scopeFields, grantSalt]);
    await gated('duplicate active grant', 'issue_grant', 'issueGrant', [grantId, digest], [grantId, ...scopeFields, grantSalt], 'rejected');
    let opening = record(invoke(impl.signer, 'openingOf', scope, grantSalt, origin, 0n));
    const grantRecord = (): Module => {
      const grants = record(account.ledger().grants);
      return record(invoke(grants, 'lookup', grantId));
    };
    const grantAuth = async (builder: string, fields: unknown[]) => {
      const g = grantRecord();
      const ctx = { contractAddress: account.address, grantId, issuedAt: g.issued_at, grantNonce: g.nonce };
      const challenge = invoke(grantBuilders(impl, arm), builder, ctx, grantee.pk, ...fields);
      const auth = await invoke(grantee, 'sign', challenge);
      return array(invoke(impl.signer, 'grantAuthArgs', opening, auth));
    };
    const spendGrant = async (label: string, operation: string, builder: string, fields: unknown[], args: unknown[], amount: bigint,
      expected: 'accepted' | 'rejected' = 'accepted') => {
      const auth = await grantAuth(builder, fields);
      const result = await run(account, prefix(label), `${operation}_with_grant_${arm}`, [...args, ...auth], expected);
      if (result.outcome.tag === 'accepted') opening = { ...opening, spentPrev: BigInt(String(opening.spentPrev)) + amount };
      return [...args, ...auth];
    };
    const firstSpend = await spendGrant('grant unshielded spend', 'withdraw_unshielded', 'withdrawUnshielded', [color, 3n, recipient], [color, 3n, { bytes: recipient }], 3n);
    await run(account, prefix('grant spent-opening replay'), `withdraw_unshielded_with_grant_${arm}`, firstSpend, 'rejected');
    await spendGrant('grant per-call cap refusal', 'withdraw_unshielded', 'withdrawUnshielded', [color, 21n, recipient], [color, 21n, { bytes: recipient }], 21n, 'rejected');
    for (const [operation, builder] of [['withdraw_shielded', 'withdrawShielded'], ['withdraw_shielded_to_contract', 'withdrawShieldedToContract']] as const) {
      const changeEntry = rnd(192), encKey = account.ledger().enc_key;
      const coin = await depositCoin(`fund grant ${operation}`);
      await spendGrant(`grant ${operation} change`, operation, builder, [recipient, color, 4n, changeEntry, encKey, coin],
        [{ bytes: recipient }, color, 4n, changeEntry, encKey], 4n);
      const stale = await depositCoin(`fund grant ${operation} refusal`), wrongKey = rnd();
      await spendGrant(`grant ${operation} stale encryption key`, operation, builder, [recipient, color, 4n, changeEntry, wrongKey, stale],
        [{ bytes: recipient }, color, 4n, changeEntry, wrongKey], 4n, 'rejected');
      const full = await depositCoin(`fund grant ${operation} exact`);
      await spendGrant(`grant ${operation} exact`, operation, builder, [recipient, color, 10n, changeEntry, encKey, full],
        [{ bytes: recipient }, color, 10n, changeEntry, encKey], 10n);
    }
    await gated('revoke grant', 'revoke_grant', 'revokeGrant', [grantId], [grantId]);
    await spendGrant('revoked grant refusal', 'withdraw_unshielded', 'withdrawUnshielded', [color, 1n, recipient], [color, 1n, { bytes: recipient }], 1n, 'rejected');
    await gated('revoke unknown grant', 'revoke_grant', 'revokeGrant', [unknown], [unknown], 'rejected');
    await gated('reissue tombstone', 'issue_grant', 'issueGrant', [grantId, digest], [grantId, ...scopeFields, grantSalt]);
    const revokedAll = await gated('revoke all grants', 'revoke_all_grants', 'revokeAllGrants', [], []);
    await run(account, prefix('revoke all replay'), `revoke_all_grants_with_${arm}`, revokedAll.args, 'rejected');
    await run(account, prefix('cleared grant after revoke all'), `withdraw_unshielded_with_grant_${arm}`, firstSpend, 'rejected');
    await gated('issue grant after generation reset', 'issue_grant', 'issueGrant', [grantId, digest], [grantId, ...scopeFields, grantSalt]);
    opening = record(invoke(impl.signer, 'openingOf', scope, grantSalt, origin, 0n));
    const expiringId = invoke(grantee, 'grantId', account.address, origin, 1n);
    const expiring = { ...scope, expiresAt: BigInt(account.time + 1) }, expiringSalt = rnd();
    const expiringDigest = invoke(impl.signer, 'scopeDigest', expiringSalt, expiring);
    await gated('issue expiring grant', 'issue_grant', 'issueGrant', [expiringId, expiringDigest],
      [expiringId, ...array(invoke(impl.signer, 'scopeArgs', expiring)), expiringSalt]);
    const expiringRecord = record(invoke(record(account.ledger().grants), 'lookup', expiringId));
    const expiringContext = { contractAddress: account.address, grantId: expiringId, issuedAt: expiringRecord.issued_at, grantNonce: expiringRecord.nonce };
    const expiringChallenge = invoke(grantBuilders(impl, arm), 'withdrawUnshielded', expiringContext, grantee.pk, color, 1n, recipient);
    const expiringAuth = await invoke(grantee, 'sign', expiringChallenge);
    const expiringOpening = invoke(impl.signer, 'openingOf', expiring, expiringSalt, origin, 1n);
    account.time++;
    await run(account, prefix('expiry exact boundary'), `withdraw_unshielded_with_grant_${arm}`,
      [color, 1n, { bytes: recipient }, ...array(invoke(impl.signer, 'grantAuthArgs', expiringOpening, expiringAuth))], 'rejected');
    const newRecovery = generate(impl.signer, 'JubjubDevice'), session = rnd(), phi = [1n, 2n, 0n, 0n], newWrap = rnd(64);
    const publishArgs = [newRecovery.pk, session, ...phi, 2n, newWrap];
    await gated('publish recovery', 'publish_recovery_session', 'publishRecoverySession', [newRecovery.pk, session, phi, 2n, newWrap], publishArgs);
    await gated('reused recovery session', 'publish_recovery_session', 'publishRecoverySession', [newRecovery.pk, session, phi, 2n, newWrap], publishArgs, 'rejected');
    const successor = generate(impl.signer, 'JubjubDevice'), nextRecovery = generate(impl.signer, 'JubjubDevice');
    const submit = async () => {
      const l = account.ledger();
      if (typeof l.device_epoch !== 'bigint' || typeof l.auth_nonce !== 'bigint') throw new Error('invalid recovery counters');
      const nowUpper = BigInt(account.time + 1);
      const challenge = invoke(impl.recovery, 'recoverSubmitChallenge', callContext(), l.recovery_pk, successor.pk, nextRecovery.pk, l.device_epoch + 1n, nowUpper);
      const auth = invoke(impl.recovery, 'signRecoverSubmit', newRecovery, successor, challenge,
        { successorRecoveryPk: nextRecovery.pk, expectedEpoch: l.device_epoch, expectedNonce: l.auth_nonce, nowUpper });
      return array(invoke(impl.recovery, 'recoverSubmitArgs', auth));
    };
    await gated('cancel without pending recovery', 'recover_cancel', 'recoverCancel', [], [], 'rejected');
    await run(account, prefix('finalise without pending'), 'recover_finalise', [], 'rejected');
    const submission = await submit();
    await run(account, prefix('recovery submit'), 'recover_submit', submission, 'accepted');
    await run(account, prefix('recovery submit replay'), 'recover_submit', submission, 'rejected');
    await gated('cancel recovery', 'recover_cancel', 'recoverCancel', [], []);
    await run(account, prefix('recovery submit again'), 'recover_submit', await submit(), 'accepted');
    await run(account, prefix('finalise before deadline'), 'recover_finalise', [], 'rejected');
    account.time += 62;
    await run(account, prefix('finalise at elapsed veto window'), 'recover_finalise', [], 'accepted');
    await gated('old device after recovery', 'rotate_enc_key', 'rotateEncKey', [key], [key], 'rejected');
    await spendGrant('old epoch grant after recovery', 'withdraw_unshielded', 'withdrawUnshielded', [color, 1n, recipient],
      [color, 1n, { bytes: recipient }], 1n, 'rejected');
    const reachable = installRepresentedFixture(account, { deviceEpoch: (1n << 32n) - 1n });
    const epochOverflow = [...submission];
    epochOverflow[1] = recovery.pk;
    epochOverflow[2] = (1n << 32n) - 1n;
    epochOverflow[3] = account.ledger().auth_nonce;
    epochOverflow[4] = BigInt(account.time + 1);
    await run(account, prefix('synthetic represented maximum epoch rejects recovery increment'), 'recover_submit', epochOverflow, 'rejected', '32');
    account.state = reachable;
    account.origin = 'reachable-history';
    const maxCounter = (1n << 64n) - 1n;
    const maxEntry = invoke(successor, 'entryAt', account.address, account.ledger().device_epoch, maxCounter);
    if (!(maxEntry instanceof Uint8Array)) throw new Error('invalid successor entry fixture');
    const beforeCounter = installRepresentedFixture(account, { deviceEntries: [maxEntry] });
    const atCounterMax: Actor = { arm: 'jubjub', device: successor, grantee: {}, counter: maxCounter };
    await gated('synthetic represented maximum use_counter rejects successor entry', 'rotate_enc_key', 'rotateEncKey', [key], [key], 'rejected', atCounterMax, '64');
    account.state = beforeCounter;
    account.origin = 'reachable-history';
  }
  return { observations, expectations };
}

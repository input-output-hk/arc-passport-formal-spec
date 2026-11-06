# Commitment binding and native typed encoding

## Decision and reading route

**Keep the current relevant-opening hypotheses explicit.** On canonical inputs,
each fixed application commitment layout below has an unambiguous byte encoding
of its *included* fields. An unequal included-field opening with the same digest
would therefore yield a SHA-256 collision (or a second preimage for a fixed
previous opening). This is a reduction obligation, **not a checked cryptographic
reduction, a global hash-injectivity axiom, or authenticated ledger adoption**.
Fields deliberately omitted, wildcard meanings, source guards and the origin of
context/state require different arguments. No semantic bug or Passport hash
collision was demonstrated by this audit.

Start with the [opening-premise inventory](#discharging-the-existing-premises),
then the [layout inventory](#application-layouts) and
[native evidence](#executed-native-evidence). The
[cryptographic assumptions audit](cryptographic-assumptions-audit.md) separately
covers signature/token realization: commitment binding does not repair the
native signature digest-uniqueness counterexamples documented there.

Scope is formal base `b87ccbeb556ace4b28265f49f0310c384f287451`, with native
[Passport `fc19e471536febb2133f20e817847251622dcdf5`][native]. Sources are
[`account.compact`][account], [`account-p256.compact`][p256],
[`webauthn.compact`][webauthn], and the installed runtime identified by
[`passport-main-pins.json`](../conformance/harness/passport-main-pins.json).
No cryptographic model, theorem, library classification, exception, or Passport
implementation is changed here.

## From typed atoms to hash input

The formal [`Atom`](../src/Conformance/FullAccountTypes.agda) is `String × Value`.
[`FullAccountCrypto`](../src/Conformance/FullAccountCrypto.agda) constructs typed
lists, but `P.persistentHash` remains a supplied primitive. Atom type names are
**instructions to an encoder, not bytes prefixed to the SHA input**.
[`independent-hash.ts`](../conformance/harness/independent-hash.ts) implements
SHA-256 over the following concatenation, without a native hash/codec call:

| Atom | Bytes entering SHA-256 | Canonical domain |
| --- | --- | --- |
| `Bytes<n>` | Exactly `n` octets, in their existing order | Exactly `n` integers in 0–255; no text, hex-case, or address-string normalization |
| `Uint<8/32/64/128>` | 1/4/8/16 bytes, unsigned little-endian | `0 ≤ x < 2^bits`; no wrap, sign extension or modular reduction |
| `Boolean` | One byte, `00` or `01` | Boolean, not an arbitrary integer/truthy object |
| `Field` | 32 bytes, unsigned little-endian | `0 ≤ x < F`, where `F = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001` |
| `ContractAddress`, `UserAddress`, `ZswapCoinPublicKey` | The contained 32 bytes | Address *kind* is not encoded by this atom; interpretation comes from layout or an explicit selector |
| `JubjubPoint` | `x:Field || y:Field` (64 bytes) | Canonical coordinate pair; serialization alone does not prove curve/subgroup membership or possession |
| k256/p256 key in application hashes | `x:Bytes<32> || y:Bytes<32>` (64 bytes), coordinates little-endian | Native affine coordinate extraction; not SEC1 big-endian/compressed encoding; identity extraction rejects |
| `ShieldedCoinInfo` | nonce32, color32, value16 (80 bytes) | Canonical component domains |
| `QualifiedShieldedCoinInfo` | preceding 80 bytes, then Merkle index8 (88 bytes) | Canonical component domains, index `Uint<64>` |
| `WebAuthnPolicy` | RP-id hash32, origin21 (53 bytes) | Fixed raw origin bytes; the verifier rejects bytes outside 33–126, quote and backslash |

The native path is runtime `persistentHash(type,value)` →
`onchain-runtime-v4.persistentHash(type.alignment(),type.toValue(value))`.
`toValue` uses minimal little-endian atoms and strips trailing zero bytes;
**alignment restores the declared width before hashing**. The independent
encoder constructs those full-width bytes directly. This explains why false's
native empty atom still hashes as one zero byte, not an empty string.

There is a material boundary distinction: native `CompactTypeBytes(32).toValue`
accepts a short array and the hash zero-extends it; its generated **public circuit
ABI rejects a short `Bytes<32>` argument**. The independent encoder likewise
rejects it. The formal dispatcher checks exact byte lengths, bounds and tuple
shapes before executing; raw `Value` and arbitrary `P` do not themselves impose
those checks. Numeric wire strings are canonical unsigned decimal; negative,
leading-zero and overflow forms are not alternate admissible openings.

`Maybe` also needs source normalization. Native `Maybe<ContractAddress>` includes
both a Boolean and an address payload. Absent caller with a nonzero payload is
rejected by the source. The formal body supports `none` and the explicit
`[false, zero32]` representation; both mean absent, not distinct caller policies.
The policy-opening lemmas compare present address values and numerical recipient
tags, rather than claiming injectivity of all raw `Value` representations.

### What injectivity means here

For a **fixed layout**, cut the concatenation at its known offsets. Equality of
bytes gives equality of every fixed-width byte slice; unsigned little-endian
encoding is injective on its bounded range, and canonical Boolean/field encoding
is likewise injective. For canonical affine nonidentity keys, the two coordinates
identify the key; the omitted identity flag is fixed false by successful
coordinate extraction. This is a mathematical argument about these recipes,
not an Agda proof of the native serializer or a universal native-refinement
result. The probes below support, but do not prove, that the implementations
follow the recipes for every admitted input.

There is **no injectivity over arbitrary typed Atom lists**: native and
independent encoders both hash `[Bytes<1>(01), Bytes<1>(02)]` exactly like
`[Bytes<2>(0102)]`; `Uint<32>(258)` hashes as `Bytes<4>(02010000)`. These are
identical SHA inputs, **not collisions of distinct byte strings and not Passport
exploits**. A theorem producing unequal formal typed preimages therefore needs
fixed-layout/canonical-encoding evidence before its result becomes a native
SHA-256 collision witness.

## Application layouts

Notation: `D(t)` is the ASCII literal `t` zero-padded to **32 bytes**; `H` is
SHA-256; `T(t) = H(pad64(t))`. Fields occur in the order shown. `B32` means 32 raw
bytes; `U8/U32/U64/U128` have the widths above; `J` is a 64-byte JubJub point;
`K` is the two 32-byte affine coordinates. All tags below are exact, including
versions. Fixed-layout injectivity concerns the listed fields, not the omitted
fields in the right column.

| Commitment and source | Exact preimage, including domain; byte length | Binding and intentional omissions |
| --- | --- | --- |
| Device, JubJub (`derive_device_entry_with_jubjub`) | `D(midnight:account:device:v1), account:B32, key:J, epoch:U32, counter:U64`; **140** | Binds account, key, epoch and presented use counter. Does not bind global `auth_nonce`, scope or signature. |
| Device, k256 | `D(midnight:account:device:k1:v2), account:B32, key:K, envelope:U8, epoch:U32, counter:U64`; **141** | Includes envelope; actual authorization permits only known envelopes. Derivation alone accepts the full U8 domain. |
| Device, p256 | `D(midnight:account:device:r1:v2), account:B32, key:K, rpHash:B32, origin:Bytes<21>, epoch:U32, counter:U64`; **193** | Includes full WebAuthn policy, not authenticator signCount/flags or an approval ceremony. |
| Bootstrap, JubJub/k256/p256 | Respectively `D(midnight:account:boot:v1), salt:B32, key:J`; `D(midnight:account:boot:k1:v2), salt:B32, key:K, envelope:U8`; `D(midnight:account:boot:r1:v2), salt:B32, key:K, rpHash:B32, origin:Bytes<21>`; **128/129/181** | No account, epoch or counter. Account is unavailable at construction; activation computes an account-specific entry at current epoch/counter 0 and burns boot. Copying a boot commitment across deployments is not a hash collision. Salt freshness/hiding is a client responsibility, not injectivity. |
| Grant id, JubJub/k256/p256 | `D(midnight:account:grant:id:v1), account:B32, key:J, originHash:B32, slot:U8`; k256 uses `D(midnight:account:grant:id:k1:v1), account:B32, key:K, envelope:U8, originHash:B32, slot:U8`; p256 uses `D(midnight:account:grant:id:r1:v1), account:B32, key:K, originHash:B32, slot:U8`; **161/162/161** | Stable identity, **not issuance identity**: omits epoch, generation, issued_at, grant nonce, scope and salt. Same id may intentionally be reissued. p256 RP hash is absent here, checked separately against stored RP commitment. k256 spend gate requires envelope 0. |
| Object (`derive_grant_object_commit`) | `D(midnight:account:grant:obj:v1), salt:B32, color:B32, recipientKind:U8, pin:B32, maximum:U128`; **145** | Includes every object-opening component. Kind 0 intentionally makes destination unrestricted; the pin bytes still remain hashed. Kind 1/2/3 denotes user/unshielded, shielded public key, contract/shielded. Other U8 kinds can be hashed/issued but cannot satisfy a spend's non-wildcard recipient guard. |
| Spent (`derive_grant_spent_commit`) | `D(midnight:account:grant:spent:v1), salt:B32, total:U128`; **80** | No id/account/nonce/issuance. Equal salt and total across grants intentionally give equal commitments. Historical episode selection supplies association with an issuance. |
| Caller, present (`derive_grant_caller_commit`) | `D(midnight:account:grant:caller:v1), salt:B32, contractAddress:B32`; **96** | Present output must be nonzero. The absence branch returns zero32 without hashing and ignores salt. Present zero *address* is distinct from absent caller. No account/id, origin, recipient, or call-stack ancestry is hashed. |
| RP (`derive_grant_rp_commit`) | `D(midnight:account:grant:rp:v1), salt:B32, rpIdHash:B32`; **96** | Binds the supplied RP hash, not a hostname's external authenticity. p256 spend checks it; other grant arms do not derive browser/RP authority from it. |
| p256 origin | `D(midnight:account:grant:origin:v1), origin:Bytes<21>`; **53** | Hashes exact fixed-width origin bytes, not URL equivalence. The source checks it against the grant-id opening and the signed WebAuthn JSON. JubJub/k256 originHash is an opaque client-chosen 32-byte value. |
| Scope digest (`derive_grant_scope_digest`) | `D(midnight:account:grant:scope:v2), salt:B32, withdrawUnshielded:Boolean, withdrawShielded:Boolean, withdrawToContract:Boolean, read:Boolean, color:B32, kind:U8, pin:B32, max:U128, perCallCap:U128, cap:U128, expiresAt:U64, rpIdHash:B32, readPkHash:B32, windowLen:U64, windowCap:U128, callerCommit:B32`; **309** | Outer layout injective in its fields, but it contains a *nested digest*, not the caller plaintext. Full present-caller binding also requires caller-commit binding; absent payload normalization is a guard. `grant_id` is outside, alongside this digest in the issue authorization challenge. |

For object/spent/RP/present-caller layouts, canonical serialization recovers all
opening components exactly. Bootstrap, device and grant-id serialization recovers
the listed curve-specific fields, conditional on canonical native key extraction.
Scope serialization recovers the caller *digest* only. Absent caller is expressly
not salt-injective. None of these facts grants hiding: fresh secret salts, entropy,
client handling and dictionary-attack resistance are separate obligations.

### Issuance, policy and historical guards are not hash binding

`do_issue_grant` accepts a literal id authorized by a device; it does not receive
and validate that id's grantee preimage. Likewise raw `add_device` accepts a
literal entry, without proving a usable key/current-epoch/counter-zero opening.
An intended-opening witness must come from the actual intended issuance/enrolment,
not be inferred from a stored digest alone.

Grant record identity retains `epoch:U32`, `gen:U32`, `issued_at:U64`, with
`nonce:U64` initially zero. Successful reissuance can reuse the same id but uses
the current global authorization counter for issued_at. Grant signature
challenges bind id, issued_at and current grant nonce; current epoch/generation
and active status are checked against ledger state. The
[`SameIssuance`](../src/Passport/GrantReplay.agda) condition (same map id, no
intervening accepted reissue) is a history condition, not a consequence of id
collision resistance.

A successful spend checks object/spent openings, operation flag, per-call cap,
wide `spentPrev + amount ≤ cap` **before** narrowing to U128, and the recipient
wildcard-or-exact-kind-and-pin rule. Shielded spending additionally checks the
*whole input coin value* against maximum and the change encryption key against
the current key. Neither maximum nor pin implies a stronger rule for unshielded
spending than its actual source guard. Zero amounts are permitted. Overflowing
counters/epoch/nonce fail bounded casts rather than wrapping.

Issuance requires nonempty scope, read permission for shielded spending, positive
cap for spending, perCallCap ≤ cap, max ≥ perCallCap, nonzero read key hash when
reading, zero reserved window fields, and canonical zero object fields on a
read-only grant. Read-only caller restriction is rejected. Expiry 0 intentionally
means no expiry. These are policy/normalization decisions, not omitted hashes to
be recovered by assuming stronger cryptography.

### Authorization and recovery preimages

The exact challenge-domain families are `T(midnight:account:auth:<arm>:<op>)`
for arms `v1`, `k1:v1`, `r1:v1` and operations
`withdraw_unshielded`, `withdraw_shielded`, `withdraw_shielded_to_contract`,
`append_inbox`, `rotate_enc_key`, `add_device`, `remove_device`, `issue_grant`,
`revoke_grant`, `revoke_all_grants`, `publish_recovery_session`, `recover_cancel`;
and `T(midnight:account:grant:auth:<arm>:<op>)` for the same three arms and three
withdrawal operations. Their typed construction is in
[`challengeAt`](../src/Conformance/FullAccountCrypto.agda),
[`operationAtoms`](../src/Conformance/FullAccountBody.agda) and
[`grantChallengeAtoms`](../src/Conformance/FullAccountGrantSecurity.agda).

JubJub challenges contain domain32, account32, signature R64, key64, operation
fields, authorization/grant nonce8, grindNonce8. k256/p256 omit R and grindNonce,
use affine key64, and retain nonce8. Grant operation fields start with id32 and
issued_at8. Unshielded payload is color32, amount16, user address32. Shielded
payload is recipient32, color32, amount16, change entry192, encryption key32,
qualified coin88; device shielded challenges omit the grant-specific change
entry/key fields. The coin includes its nonce, asset, entire value and index,
not merely the requested withdrawal amount. These fixed per-operation layouts
recover their included values; they do not identify requests differing only in
fields absent from the challenge.

Recovery submit uses
`T(midnight:account:recovery:submit:v1), account:B32, recoveryKey:J,
recoveryR:J, successorKey:J, successorR:J, successorRecoveryKey:J,
postEpoch:U32, authNonce:U64, nowUpper:U64, grindNonce:U64` (**412 bytes**).
It binds both public keys/R terms and the proposed next authority, epoch and time
bound. The pending entry is the ordinary JubJub device-entry digest for the
successor at postEpoch/counter 0. Delayed finalization needs the pending record,
epoch freshness, veto-time and authority-stamp source rules; hashing cannot
replace these history/state checks.

Recovery session operation fields are new recovery key64, session nonce32,
phi1–phi4 (four 32-byte Fields), phiLen1 and wrap64. Every slot is hashed, including
unused slots; source requires length 1–4, unused slots zero, a nonzero session
nonce different from the currently stored session identifier, and a changed live
recovery key. Historical non-reuse of all earlier identifiers is not enforced by
that comparison. The recovery “commitment” `recovery_pk = sG` is a group public key,
**not SHA-256 over s**; scalar canonicalization, admissible
keys, possession and discrete-log/signature assumptions are outside this hash
audit. Birth wrap, guardian data correctness, secret deletion and recovery-key
intent are not proved by a digest. Bootstrap only binds its own listed fields,
not the constructor's encryption/recovery parameters.

The final signing encodings add k256's `H(challenge32)` or
`H(pad27("midnight_signed_message:32:") || challenge32)` (27 bytes include the
padding), or p256's fixed WebAuthn JSON/authenticator hashing. Different
signatures may verify related digests; do not equate signature-byte reuse with
hash collision resistance. The linked signature audit owns that issue.

### Cross-layout separation

At this pin, **all 61 literal application domain prefixes are distinct**:
15 raw padded tags (all commitment rows above), plus 46 hashed challenge tags
(36 device, 9 grant, 1 recovery submit). The probe checks lengths before padding,
computes every hashed tag with both native and independent hash encoders, and
compares the resulting 32-byte prefixes across *both* families. Thus different
listed layouts start with different bytes, even when total lengths coincide.
This is exhaustive for those source literals, not sampling of domain constants.
A future tag/version must repeat that check; arbitrary strings must not inherit
it. The formal `pad` truncates long strings, so inventing new overlength tags
would invalidate this reasoning.

Consequently, equality of output across two distinct listed layouts would be a
collision of distinct SHA input strings; it is not explained by a boundary/type
alias. Within one layout, the slicing argument applies. No claim here says their
*digests* are mathematically disjoint. Wrapper hashes, raw user hashes and
platform hashes do not all begin with these application prefixes; a global
cross-purpose disjointness assertion would be unjustified.

Platform effect primitives are a separate edge: the formal adapter uses
`midnight:zswap-cc[v1]` / `midnight:zswap-cn[v1]` (21 raw bytes), then coin80,
recipient-kind Boolean and address32, for commitment/nullifier (**134 bytes**).
The contract nullifier uses the contract selector; the shielded coin commitment
selects a public key or contract. The canonical adapter deliberately retains only
the selected recipient, not both inactive native Either payloads. Coin nonce
evolution uses `transientHash` on two Fields: the little-endian ASCII integer of
`midnight:kernel:nonce_evolve` or `midnight:kernel:nonce_evolve/2`, and
`degradeToTransient(nonce)`, then `upgradeFromTransient`. Degradation is not
claimed injective and this is **not the audited independent SHA-256 encoder**.
Existing full conformance shares the curve/Poseidon runtime. The new probes do
not establish universal coin/nullifier or Poseidon binding. Asset authenticity,
coin ownership, conservation and ledger reconciliation remain platform obligations.

## Discharging the existing premises

| Current premise / result | Required independent justification; what it does not supply |
| --- | --- |
| [`ObjectOpeningsAgree`, `CallerOpeningsAgree`, `RelevantOpeningsAgree`](../src/Conformance/FullAccountGrantScope.agda) | Instantiate the real primitive and canonical encodings; relate both successful computations to the same stored digest. Unequal included fields give distinct fixed-layout bytes, hence a collision. For caller, use only present-address pairs; the source nonzero guard separates restricted from unrestricted, without an extra “hash never zero” axiom. |
| `IntendedGrant` / `PolicyCommitted` | Obtain the intended plaintext and actual id/record lookup/opening, from authenticated issuance and the chosen meaning of intent. Hash hardness cannot produce a missing preimage, approve policy, or identify the authentic ledger record. |
| [`SpentOpeningsAgree`](../src/Conformance/FullAccountGrantSecurity.agda), [`HistoryAgreement`](../src/Passport/GrantSpending.agda) | Carry the issuance's actual salt/zero opening forward through accepted settlements. At each accepted spend, compare that derived historical opening with the presented opening of the actual record. Outside the relevant collision event, both salt and numerical total agree. Initial accounting, historical sum and cap are then theorem conclusions, not premises to assume. Association with the current episode remains the source history/map argument. |
| Device old/rolled inequality; [`RelevantEntrySeparation`](../src/Passport/RevocationExclusion.agda) | For the same fixed device layout, changed bounded counter/epoch or another included field yields distinct byte inputs; cross-arm prefixes differ. Combine native binding with the actual non-reenrolment/separation policy. Literal raw enrolment of the protected digest, intentional successor-key reuse, or another live opening is not excluded by hash hardness. Ordinary removal is a literal-entry removal, not a permanent-key ban. |
| Source `challenge-collision` / `immediate-replay-collision` | Turn typed-list inequality into byte inequality only after fixing the operation/arm layout and canonical fields. The generic Atom-list counterexample above prevents skipping this step. |
| [`RelevantRequestBinding`, `IssuedAgreement`](cryptographic-assumptions-audit.md#assumption-inventory) | Included nonce/request views need the complete challenge and wrapper encoding argument, plus trace/ownership conditions where used. Nested scope/caller commitments need their own binding step. This does not imply `SignatureTokenInterpretation`, symbolic token availability or unforgeability. |

A collision-resistance argument permits an adversary to choose both distinct
openings; a second-preimage argument fixes the earlier one. Which experiment
fits an issuance/adaptive-history setting is a decision still to be made.
Computational hardness bounds the probability of a bad event; it does not make
finite-output SHA-256 globally injective or directly prove an unconditional Agda
equality. A future realization must establish native correspondence and
canonicality, exhibit the distinct-byte witness on premise failure, and account
for the actual queried pairs/history. Conditional theorems can then be applied
on executions outside that bad event. No new axiom or mock proof is added here.

### Authentication is a separate obligation

A bound account address is useful only if `kernel.self()` refers to the adopted
contract. A caller commitment binds the *observed immediate contract caller*;
it cannot authenticate a caller value chosen by a simulator, prove an outer
user's identity, or authenticate an entire call stack. Likewise expiry and
recovery time bounds depend on ledger-authenticated time semantics; a qualified
coin opening does not prove the witness coin belongs to the adopted input set.

The companion `docs/ledger-adoption-boundary.md` specification separates
code/deployment identity, compiler/proof transcript correspondence, current-state replay/order,
authenticated self/caller/time, native asset/effect reconciliation and rollback,
and finality/read-provider authentication. These obligations do not discharge
opening premises, and opening premises do not discharge them. Local native
execution or digest equality must never be relabeled as authenticated adoption.

## Executed native evidence

Retained review artifacts (outside the Git repository, not project dependencies):
`local://passport-commitment-boundaries.mts` and
`local://passport-commitment-boundary-evidence.json`. They preserve the exact probe
and output executed at the corresponding `/tmp/` paths. The final run exited **0** with
**66 report rows**: 36 native/independent digest-agreement rows, 25 expected
rejections, and 5 normalization/ambiguity/domain-inventory observations. It used
real generated **public pure circuits** and the actual runtime's native/WASM
hash path, not an emulated hash or patched generated contract.

| Coverage | Observed result / precise limit |
| --- | --- |
| U8 recipient kind, U32 device epoch, U64 device counter, U128 spent total | Each exercised zero, non-palindromic endian sample, high-bit/signed midpoint, and maximum (16 agreement rows). Native public ABI and independent encoder rejected −1 and `2^bits` (16 rejection rows). This covers representation widths, not every impure field-update overflow path. |
| Field and Boolean | Fields 0, 258, F−1 matched native, independent and direct fixed-width SHA; −1 and F rejected on both paths. False/true hashed exactly as 00/01. |
| Exact byte lengths and normalization | Public spent-commit salt of 31/33 bytes rejected, as did independent encoding. Low-level descriptor accepted `[01]` as the same normalized bytes as `[01,00×31]`. |
| Key and commitment recipes | All three device, bootstrap and grant-id arms matched (real key `5G`; k256 envelope 1; p256 policy53; id slot 255; device epoch 258/counter `2^63`). Object maximum, RP, present caller and nested scope-v2 matched independently. Key generation/coordinate extraction is native, not an independent curve implementation. |
| Caller sentinel | Absent canonical caller returned zero for two distinct salts. Present all-zero address returned nonzero. Absent nonzero payload rejected with `noncanonical absent caller`. **No real SHA-256 zero preimage was found or manufactured**; reserved-zero-output rejection is inspected source/proved source-guard evidence, not an exercised native hash-to-zero branch. |
| Recovery / issuance / coin | Real public recovery challenge matched at postEpoch `2^32−1`, nonce `2^64−1`, nowUpper 258; grant shielded challenge matched at issued_at/index `2^64−1`, coin value `2^128−1`, nonce 258. These are derivation calls, not accepted signed recoveries/spends. |
| Generic encoding ambiguity | Both encoders reproduced split-byte versus joined-byte equality, and U32 versus Bytes4 equality. No distinct-byte SHA collision. |
| Domain constants | All 61 application prefixes distinct; all 46 hashed-domain computations matched native/independent encoders. Separate from the 36 digest-vector rows. |

Runtime was **0.20.0**, Compact compiler metadata **0.35.0**,
`debb05f9414b9d1e176741c2be289bb32233f0fc`, Node **v22.22.1**, Linux arm64.
`loadFullImplementation` checked the exact source/generated artifact, dependency
tree, Node binary and compiler-executable pins plus exported impure surface
before probes. This identifies the loaded artifacts; it is not a new compilation
or proof-generation run. Evidence retains the complete pin maps, typed preimages,
digests, rejection messages and all domain prefixes.

Probe SHA-256:
`ab802cb017339529af118cb8dc69a5f33c2d798c9f2b2afb3c821903ecd6b69d`.
Evidence JSON SHA-256:
`33956b58161a40b81cee9bf738a1cfb15266d9fd6f6e1e32bc4d4417c0aa6713`.
Pin-file SHA-256:
`3541b7e16f372465cb043fb7420ece4b7248a2155b752183d570ab9c72245474`.
The source hashes are `ef1e3d6eb873e91e205c12e07f33cda744d228470dd43a4794cb3784447fd6ae`
(account) and `50aca789d611fab99292725a64a8231e0a6509ca726fdb1e23babf96e0ad9fd4`
(p256); generated account JS is
`afdc3aaa5bb426329122427ed65876bd820fc5bb452c02cb4eb48a7b97ed5697`.

Reproduce while the retained artifacts and pinned installation are available:
first copy the retained probe to `/tmp/passport-commitment-boundaries.mts`
(the temporary executable is removed after handoff), then run:

```sh
FORMAL_AUDIT_ROOT=/path/to/formal-checkout \
FULL_IMPL_DIR=/path/to/pinned/passport/contract \
/path/to/pinned/passport/contract/node_modules/.bin/tsx \
  /tmp/passport-commitment-boundaries.mts /tmp/passport-commitment-boundary-evidence.json
```

The compiler executable directory defaults to the pin-file path; if relocated,
set `FULL_COMPACT_DIR` to the matching binaries. The external probe imports the
formal checkout's existing harness/independent encoder and selects its loaded
implementation via the existing environment controls. Preserve both external
files with the review package: this documentation-only commit intentionally does
not install an audit-only harness. If those files are lost, the exact executable
run cannot be reproduced from this commit alone; the tables and pinned recipes
remain an explicit test specification, not replacement execution evidence.

Existing [`independent-hash.test.ts`](../conformance/harness/independent-hash.test.ts)
has one published k256 device vector plus U64-overflow, field-modulus and short
byte rejection cases. Existing full conformance compares typed primitive results
and runtime transcripts but shares curve/Poseidon primitives and does not prove
universal serialization correctness. The additional run above targets the
previously untested native-width, normalization and ambiguity boundaries; it does
not rerun the full suite. No Agda source changed or Agda check ran for this audit.
No ZK proof, admitted ledger transaction, finality event, browser ceremony, or
hardware-signing evidence is claimed, and none is declared impossible.

## Decisions still needed and safe current position

1. Retain pair/history-local opening premises and native-correspondence boundaries;
   do not replace them with universal typed-hash or global SHA injectivity.
2. Decide the canonical native interpretation and how it is carried into intended
   policy/history witnesses. Short low-level byte arrays and omitted Maybe payloads
   must not be treated as distinct canonical policies. Preserve the source's
   wildcard, expiry-zero, absent-caller and same-id reissuance meanings unless a
   separately approved policy change says otherwise.
3. Decide the adversarial experiment and reduction interface for commitment
   binding, including adaptive issuance, nested hashes and cross-purpose uses.
   This audit selects neither a crypto model nor a generic encoding lemma: no
   independently useful checked abstraction was necessary for this deliverable.
4. Supply authenticated deployment/state/context and platform-effect evidence
   separately before promoting local conditional properties to ledger-adopted
   properties. A finite passing native corpus and exact pin identity are evidence
   for the tested implementation boundary, not proofs of this platform bridge.

[native]: https://github.com/midnightntwrk/passport/tree/fc19e471536febb2133f20e817847251622dcdf5/contract
[account]: https://github.com/midnightntwrk/passport/blob/fc19e471536febb2133f20e817847251622dcdf5/contract/contracts/account.compact
[p256]: https://github.com/midnightntwrk/passport/blob/fc19e471536febb2133f20e817847251622dcdf5/contract/contracts/account-p256.compact
[webauthn]: https://github.com/midnightntwrk/passport/blob/fc19e471536febb2133f20e817847251622dcdf5/contract/contracts/webauthn.compact

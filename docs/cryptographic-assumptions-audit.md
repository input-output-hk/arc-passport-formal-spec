# Cryptographic assumptions audit

## Verdict and scope

**The current results are conditional symbolic/local-source results, not a
cryptographic realization of Passport authorization or replay security.** The
relevant-pair and trace premises can hold on restricted executions; they are not
universal cryptographic axioms. This audit supplies no combined native model
witness and therefore does not certify that every premise is jointly realized.

A universal claim that the same key and signature material can verify only one
exact digest is **false for all three native signature arms**. The executable
witnesses below demonstrate this at the digest/arithmetic boundary. They do
**not** demonstrate two accepted Passport calls, a source-hash collision, or a
Passport replay exploit. Finding source-generated requests whose digests have
the required relation is a separate problem, potentially computationally hard;
no reduction establishing that hardness is present in these proofs.

Formal scope: `0b0e72c6995c21f997c86adfc9e9a3477fedf1e4`, the signing,
account-security, grant-scope/spending/replay and device-replay modules linked
below. Native scope: [Passport `fc19e471536febb2133f20e817847251622dcdf5`][native],
Compact runtime 0.20.0. No theorem, implementation, cryptographic model,
classification, or exception is changed by this audit.

## Assumption inventory

Here **source evidence** means a proposition extracted from the modeled evaluator
for arbitrary primitive backend `P`. It is not an assertion that `P` implements
secure native cryptography. **Hypothesis** means evidence a caller must supply;
**interpretation** means a restriction of the symbolic history language.

### Verification and symbolic authorization

| Assumption or boundary | Quantifier scope and actual use | Status |
| --- | --- | --- |
| `P : Primitives`, and native correspondence | Each theorem is parameterized by one deterministic primitive backend. Hash, point and ECDSA answers are inputs, not security axioms. The [crypto evaluator](../src/Conformance/FullAccountCrypto.agda) constructs typed preimages and calls those primitives. | Source-model boundary. Native typed serialization, admissible keys, primitive implementation and proof/ledger correspondence require separate evidence. |
| `Verified`, `SchnorrAccepts`, `Encodes` | One successful source check/request. [Binding properties](../src/Conformance/FullAccountSignatureBindingProperties.agda), `verification-evidence`, `authorisation-message`, `recovery-message`, derive the checked arithmetic/digest and exact request encoding. | Source evidence, **not** digest uniqueness, ownership, unforgeability, or consent. Recovery's two keys encode the same submission digest, but have separate tokens. |
| `ownership`, `Permitted`, empty `initial` | One fixed key-ownership map; every signing event in an initial-rooted [symbolic trace](../src/Midnight/ContractDSL/SymbolicSigning.agda) obeys its constructor rule. `approve` is an honest-party input; `honestSign` needs prior approval; `attackerSign` needs initial attacker ownership or compromise. | Interpretation. Valid/non-adversarial key generation, authentic approval events and an honest signer are not established by native verification. Compromise is permanent; approvals and tokens persist. |
| `Available` / joint invocation token requirement | Each request retained by the verification gates of [AccountSecurity.requiredTokens](../src/Passport/AccountSecurity.agda) must already have its exact `(key, encode request)` token available at that invocation. [Joint.invocation](../src/Midnight/ContractDSL/AdversarialLifecycle.agda) enforces this for attempts, including refusals. | Interpretation, not extracted from signature bytes. Invalid checks require no token. An accepted call alone does not supply availability. |
| `IssuedAgreement view trace k d r` | For **every actual `honestSign k r′` occurrence** in this trace whose encoding equals `just d`, `view r′ = view r`. It does not quantify over all possible colliding requests. [Binding.request-provenance](../src/Conformance/FullAccountSignatureBindingProof.agda) applies it to the issuance furnished by symbolic provenance. | Explicit hypothesis. Identity view gives whole-request agreement; nonce view gives only nonce agreement. `encode` is not assumed injective. |
| `TraceAgreement`, `AgreesIn`, and their `All` packages | [AccountSecurity](../src/Passport/AccountSecurity.agda) specializes issued agreement to each target signed request and its successful encoding, on the joint history's signing projection. [request-views](../src/Passport/AccountSecurityProperties.agda) consumes agreement, availability and encoding evidence. | Same hypothesis repackaged, not an independent law or a consequence of successful verification. |
| Honest, uncompromised key | For the target key, honest initial ownership and absence from the **final** compromise list in [honest-signature-provenance](../src/Midnight/ContractDSL/SymbolicSigningProperties.agda). | Additional hypothesis only when eliminating the attacker-control disjunct. General provenance retains that disjunct. |

`SymbolicSigningExecution` adds decidable equalities only to implement its event
checker; [certify](../src/Midnight/ContractDSL/SymbolicSigningExecution.agda)
connects successful checking to `Permitted`. These equalities are not extra
cryptographic assumptions of the declarative theorems. The
[provenance proof](../src/Midnight/ContractDSL/SymbolicSigningProof.agda) is a trace
induction, not an unforgeability reduction.

### Grant policy and cumulative spending

| Assumption | Quantifier scope and use | Status |
| --- | --- | --- |
| `IntendedGrant` / `PolicyCommitted` | For one call and chosen `IntendedPolicy`, witnesses run the actual grant-id computation and lookup, then open that stored record's object/caller commitments. [Scope.evidence-scope](../src/Conformance/FullAccountGrantScopeProof.agda) identifies records by evaluator determinism. | Supplied witness of an opening, not proof of human intent or approval of that policy. |
| `ObjectOpeningsAgree` | For the **fixed presented/intended opening pair**, any states and common successful output imply equality of salt, asset, numeric recipient tag, recipient and maximum. Used by `scope-enforced`. | Pair-local binding hypothesis; not global hash injectivity. Native ABI normalization/typed encoding matters. |
| `CallerOpeningsAgree` / `CallerAgreement` | Fixed salt/address opening pair; common successful output implies equal openings. `CallerAgreement` requires it only for an address actually observed as contract caller; unrestricted policy requires `⊤`. Used by `caller-enforced`. | Pair-local hypothesis. The pinned-opening hash being nonzero is instead a source guard, proved by `caller-commit-nonzero`; no extra sentinel-separation axiom is needed. |
| `RelevantOpeningsAgree` | Packages the preceding object/caller premises for the actual operation, context and grant opening. [runtime-grant-scope](../src/Conformance/FullAccountGrantScopeProperties.agda) combines them with source scope, recipient and whole-shielded-coin guards. | Explicit hypothesis; unrelated to signature-byte uniqueness. |
| `SpentOpeningsAgree` | Fixed `(callSalt, spentPrev)` and `(historicalSalt, total)` pair; for any states/common successful commitment output, both components agree. [GrantSecurity](../src/Conformance/FullAccountGrantSecurity.agda) defines it; `GrantSpendingProof.spend-opens` uses it through `cumulative-spend`. | Pair-local hypothesis. The source guard checks an opening and a numerical cap; it cannot alone identify `spentPrev` with the historical sum. |
| `CallAgreement`, `AttemptAgreement`, `HistoryAgreement` | [GrantSpending](../src/Passport/GrantSpending.agda) quantifies over current book episodes whose key is the call's computed grant id; asks for spent-opening agreement only at accepted grant attempts. It accumulates over the actual deployment-rooted trace. Refusals/non-grant calls add no such premise. | History-local binding hypotheses. Initial empty accounting, retained issuance identity, nonce count, historical sum and cap preservation are [conclusions](../src/Passport/GrantSpendingProperties.agda), not assumed invariants. A new accepted spend needs the new attempt's agreement as well as the prior history's. |

These opening hypotheses are locally satisfiable, for example when both openings
are equal: their conclusions follow by reflexivity regardless of the hash.
For distinct openings with distinct computed outputs they also hold, since the
common-output antecedent is impossible. Equal-output witnesses for *different*
openings instead refute the relevant premise. None of these observations is a
universal SHA-256 binding proof or a joint native execution witness. Object,
caller and spent commitments have different layouts/domains; binding for one
pair does not establish binding for the others.

### Device and grant replay

| Assumption | Quantifier scope and use | Status |
| --- | --- | --- |
| Actual old/rolled device-entry inequality, and body frame | [consumed-credentials-refused](../src/Conformance/FullAccountDeviceSecurityProperties.agda) takes `equal current rolled = false`, a successful device call, and absence of `devices` from its body's writes. The subsequent authorization has the same account and decoded credentials, immediately at that final state. | Concrete separation hypothesis plus source structural evidence; no signature law. Different counters alone do not prove different hashes. It does not cover arbitrary intervening calls. |
| Equal challenge and different account/nonce | The same module's `challenge-collision` / `immediate-replay-collision` produce a pair of distinct **typed preimages** with equal primitive outputs. | Conditional source conclusion, not assumed collision resistance, not necessarily a collision of different native serialized byte strings, and not byte-signature replay exclusion. |
| `SameIssuance` | [GrantReplay](../src/Passport/GrantReplay.agda): same actual map identifier and no accepted reissuance of that identifier in the intervening trace. | History fact. [same-issuance-nonce](../src/Passport/GrantReplayProof.agda) derives retained issuance and strict nonce growth; rejected attempts remain in scope. |
| `RelevantRequestBinding k r k′ r′` | For these **two fixed source requests**, key equality and exact encoding equality imply nonce-view equality. Used by `historical-token-replay-excluded`. | Pair-local hypothesis; covers the final hash/envelope/WebAuthn encoding. It neither follows from nonce growth nor establishes a native crypto reduction. |
| `SignatureTokenInterpretation old next` | For these **two successful spends**, `SameSignature` implies exact encoding equality. `SameSignature` is equal curve/key plus `(R,S)` for Schnorr or `(r,s)` for ECDSA. It omits Schnorr grind nonce and ECDSA envelope/WebAuthn inputs. Used only by `historical-signature-replay-excluded`. | Additional pair-local hypothesis. Universal primitive generalizations are false; symbolic tokens do not prove it. |
| Later-token `IssuedAgreement nonceView` and `Available` | [later-token-provenance](../src/Passport/GrantReplayProperties.agda) applies the existing signing provenance rules to the later successful request. | Independent provenance hypotheses, not token consumption. An old token can remain available while a freshly authorized different token is issued. |

## Implications and realization gap

For a same-issuance successful spend pair, source history proves `nonce₁ < nonce₂`.
Consequently:

1. `RelevantRequestBinding` implies distinct exact tokens. Conversely, distinct
   exact tokens suffice for that pair's binding implication, since its
   equal-key/equal-encoding antecedent would equate the tokens. Thus on this
   already nonce-separated pair, the premise is logically equivalent to the
   required token separation; its independent cryptographic justification is
   still necessary.
2. Adding `SignatureTokenInterpretation` immediately excludes `SameSignature`:
   same material → same exact encoding → same nonce → contradiction. This is the
   whole [proof](../src/Passport/GrantReplayProof.agda), not a hidden reduction.
   Conversely, absence of `SameSignature` makes the interpretation implication
   vacuous. Proving it by assuming replay impossible would be circular.
3. Neither pair law gives `Available`, `IssuedAgreement`, semantic policy
   openings, or historical spent-opening agreement. Issued agreement constrains
   actual honest-signing occurrences, not all requests or arbitrary byte reuse.
   Identity-view agreement implies agreement under every projection, but
   nonce-view agreement does not imply whole-request approval.

Satisfiable special cases (equal openings, agreeing issuance traces, distinct
signature pairs) do not establish a common native realization for all histories.
Conversely, a failed premise on a concrete pair does not make a conditional Agda
theorem inconsistent. No unconditional axiom asserting these premises is added
by the audited modules.

## Native scheme analysis

**JubJub Schnorr.** [Source authorization][schnorr] casts the little-endian
32-byte hash to `Field` and then to `JubjubScalar`; the latter reduces modulo
subgroup order `q`. The [signer][signer] grinds honest challenges below `q`, but
the verifier only requires them below the larger field modulus `F`.
For a prime-order nonidentity key, fixed `(R,S)` determines the challenge
*modulo q*, not its exact bytes: `h` and `h+q < F` satisfy the same equation.
The same arithmetic issue applies to recovery co-signatures. Restricting both
hash integers below `q` would remove this alias for valid subgroup keys; honest
signer grinding alone does not restrict all verifying adversarial requests.

**k256 and p256 ECDSA.** The native verifier reduces the big-endian digest modulo
curve order `n`. Thus digests `1` and `1+n` share one verification equation.
There is also a distinct-reduced-digest obstruction: with key `Q=xG` and fixed
signature `(r,s)`, if `z` verifies with point
`R=s⁻¹(zG+rQ)`, then `z′=−z−2rx (mod n)` yields `−R` and the same x-coordinate,
hence the same `r`. The witnesses below have `z′≠z` modulo `n`. Their
construction uses the known secret `x`; it is **not** an attack extracting an
unknown honest key. Even canonical digests below `n` therefore do not establish
universal exact-digest uniqueness. This is not signature malleability:
`(r,s)` is unchanged, rather than replacing `s` by `n−s`.

**Wrappers and WebAuthn.** [k256 envelope_digest][envelope] hashes the challenge
again, with either no prefix or the source's 27-byte padded connector prefix.
[WebAuthn][webauthn] hashes canonical client JSON containing base64url(challenge)
and the fixed-width origin, then hashes the 37-byte authenticator data with that
client hash. RP/UP/UV checks and origin-byte restrictions are source evidence;
flags do not prove a human consent ceremony. The signed authenticator signCount
is deliberately not Passport's freshness counter. Finding requests yielding
ECDSA-related final digests must pass these wrappers and all source guards;
arbitrary chosen digest examples do not do that. Wrapper binding must therefore
be included in any realization argument, not assumed from raw-hash binding or
from the signature primitive alone.

## Executed evidence

The external probe `/tmp/passport-crypto-audit.mts` ran with pinned implementation
imports via its installed `node_modules/.bin/tsx`, Node v22.22.1, runtime 0.20.0;
exit 0. Full keys, signatures, digest bytes, source hashes and observations are
retained in `/tmp/passport-crypto-audit-evidence.json`, outside the repository.
These paths are handoff artifacts, not dependencies of the formal project.

| Probe | Exact observation | Boundary |
| --- | --- | --- |
| Schnorr, real `JubjubDevice(5)` signer on `rotateEncKey`, fixed address bytes `03`, replacement bytes `09`, nonce 0 | Original little-endian digest integer `4671055731839077190486374239236050233127827665969380522790498288284225952637` and that integer plus `q=6554484396890773809930967563523245729705921265872317281365359162392183254199` both passed the native cast/arithmetic equation with identical key, `R`, `S`. Both are below `F=52435875175126190479447740508185965837690552500527637822603658699938581184513`. | First digest comes from the real source challenge builder and signer; the alias has **no demonstrated source preimage**. Equation evaluated with real runtime operations matching source, not a second account call. |
| k256, `x=5`, signing nonce `k=7`, `r=x-coordinate(7G) mod n`, `s=7⁻¹(1+5r) mod n` | Generated `_secp256k1EcdsaVerify_0` returned `true` on all three digest integers: `1`, `1+n`, and `43684604032820585642181848099363077879105330917735696607237712702842006356907`. | Same nonidentity key and nonzero signature; all are 32-byte big-endian digests, third strictly below `n` and different modulo `n`. Arbitrary digest inputs only. |
| p256, same `x=5`, `k=7` construction on P-256 | Generated `_p256_verify_digest_0` returned `true` on `1`, `1+n`, and `50997705084960379089835785678507077880317251709708075238276742252921633498503`. | Same bounds and limitations; zero-scalar guards also exercised. Not WebAuthn preimage construction. |
| Wrapper controls | Real `K256Device(5)` source-request signature verified; plain and connector digests differed and each matched Node SHA-256 of its exact source preimage. A real Node/OpenSSL software-passkey assertion passed generated WebAuthn verification and final-digest verification; flipping one challenge byte returned `false`. | One positive/negative vector, not universal wrapper binding or a browser/hardware ceremony. |
| Actual source-call smoke | Real `AccountSim` constructor/activation and signer: `rotate_enc_key_with_jubjub` accepted, `auth_nonce` 0→1. Verbatim repeat failed with `CompactError: failed assert: unknown device entry`; nonce stayed 1. | Actual pinned generated contract/runtime/signers, not mocks. No node admission, proof generation, or replay exploit. |

ECDSA curve orders are `n_k =
115792089237316195423570985008687907852837564279074904382605163141518161494337`
and `n_p =
115792089210356248762697446949407573529996955224135760342422259061068512044369`.
The fixed-secret/fixed-nonce construction above reproduces the two ECDSA
witnesses without relying on random signer output. The generated account JS
SHA-256 was `afdc3aaa5bb426329122427ed65876bd820fc5bb452c02cb4eb48a7b97ed5697`;
`account.compact` was
`ef1e3d6eb873e91e205c12e07f33cda744d228470dd43a4794cb3784447fd6ae`.
The probe called existing generated private digest-verifier helpers to isolate
primitive claims; it did not modify generated code. No Agda source changed and
no Agda check was run for this documentation-only audit.

## Safe current position and decisions needed

- Retain explicit symbolic availability, ownership/compromise, trace-view
  agreement and relevant opening premises. Advertise source-extracted guards,
  conditional semantic scope/caps, immediate consumed-device exclusion and
  conditional exact-token separation at those boundaries only.
- Do not advertise `SignatureTokenInterpretation` as a proved native law or infer
  it from nonce growth. No theorem repair is required merely to retain the
  existing **conditional** statement. Reports that say “same bytes imply same
  digest” without the relevant-pair qualification need that precise correction.
- Before any unconditional byte-replay or honest-authorization claim, choose and
  justify a realization covering admissible keys, honest signing interfaces,
  source-computable requests, wrappers, adversarial search and compromise. This
  audit does **not** choose that model. Restricting to finite observed request
  sets could discharge pair obligations by checking those sets, but would not
  prove security for all adversarial executions.
- If a future realization cannot supply exact-message token interpretation,
  the precise interface needing reconsideration is
  `Symbolic.Message`/`encode` together with `requiredTokens`, `IssuedAgreement`
  and the two replay laws—not the nonce-growth proof. An effective-message or
  verifier-relation alternative would require a coherent provenance interface
  and new justification; replacing ECDSA messages merely by `digest mod n`
  is insufficient, as the third-digest witnesses show.
- Native serialization binding and each object/caller/spent opening obligation
  remain separate from signature realization. A composition must carry all
  applicable hypotheses; combining proven conditional components does not
  discharge them or establish ledger adoption.

[native]: https://github.com/midnightntwrk/passport/tree/fc19e471536febb2133f20e817847251622dcdf5/contract
[schnorr]: https://github.com/midnightntwrk/passport/blob/fc19e471536febb2133f20e817847251622dcdf5/contract/contracts/account.compact#L850-L878
[signer]: https://github.com/midnightntwrk/passport/blob/fc19e471536febb2133f20e817847251622dcdf5/contract/src/wallet/signer.ts#L133-L152
[envelope]: https://github.com/midnightntwrk/passport/blob/fc19e471536febb2133f20e817847251622dcdf5/contract/contracts/account.compact#L541-L548
[webauthn]: https://github.com/midnightntwrk/passport/blob/fc19e471536febb2133f20e817847251622dcdf5/contract/contracts/webauthn.compact#L69-L109

# Passport proof status report

Scope: Passport [`fc19e471536febb2133f20e817847251622dcdf5`](https://github.com/midnightntwrk/passport/tree/fc19e471536febb2133f20e817847251622dcdf5).

## Current state

The proof inventory below is covered by the integrated Agda entrypoint check. Change-description durability and encryption binding are not established, and the pinned implementation admits concrete counterexamples. The checked results are local source-execution proofs, not end-to-end proofs of the top-level security promises.

## Proof inventory

### Composed local transaction safety

The [transaction-safety theorem](../src/Passport/TransactionSafetyProperties.agda) classifies actual accepted runtime withdrawals into device/grant authorization, retains the exact source request and enforces intended grant scope plus the issuance cap including the current spend under explicit opening-agreement premises. It composes immediate device and historical symbolic-grant replay guarantees at their distinct boundaries, with exact-request provenance conditional on same-history token availability and trace agreement; cryptographic realization and ledger-adoption P11 remain open.

### Symbolic signature provenance

The generic [symbolic signing](../src/Midnight/ContractDSL/SymbolicSigningProperties.agda) and [adversarial-history](../src/Midnight/ContractDSL/AdversarialLifecycleProperties.agda) proofs trace available tokens to attacker-controlled keys or approved honest issuance, with request-level provenance conditional on relevant encoding agreement. The [source binding](../src/Conformance/FullAccountSignatureBindingProperties.agda) and [account dispatcher bridge](../src/Passport/AccountRequestDispatchProperties.agda) connect this model to actual request extraction, but do not prove concrete cryptographic security or human consent.

### Device authorization and bootstrap

[Device proofs](../src/Conformance/FullAccountDeviceSecurityProperties.agda) derive live entry membership, signature verification, entry rolling and bounded nonce/round advancement from successful source executions. Bootstrap instead requires the unconsumed boot commitment, and the immediate replay result identifies a necessary challenge collision rather than proving universal signature non-replay.

### Immediate device replay refusal

The [device replay proofs](../src/Conformance/FullAccountDeviceSecurityProperties.agda) show that a successful device call whose body preserves the device set cannot be repeated verbatim from its final state, provided its current and rolled entries differ. At that state the same account identity and decoded authentication arguments cannot authorize even a different challenge; this does not cover intervening histories or establish hash separation or ledger-adoption safety.

### Ordinary device removal

The [removal proofs](../src/Passport/DeviceRemovalProperties.agda) extract the source guards and exact removal/count effects, then show that the removed literal entry stays absent until an actual subsequent introduction and cannot authorize a call through that opening before then. Reintroduction includes activation, rolling, enrolment and recovery successors; other openings for the same key may remain live, so this is not a permanent-key ban or ledger-adoption theorem.

### Grant authorization and settlement

[Grant proofs](../src/Conformance/FullAccountGrantSecurityProperties.agda) derive current/active/unexpired record checks, scope and recipient restrictions, numerical caps, verification, and the nonce/spent commitment stored after execution. Commitment equality is not automatically equality of intended keys, assets or recipients; those interpretations require relevant-opening agreement.

### Semantic grant scope

The [semantic scope proofs](../src/Conformance/FullAccountGrantScopeProperties.agda) connect accepted typed runtime withdrawals to an explicitly witnessed intended asset, caller policy, recipient policy and whole-held-coin maximum under relevant-pair object/caller opening agreement. Unrestricted sentinels and pinned policies are distinguished; the result does not establish native hash binding, authenticated coin ownership or ledger adoption.

### Grant authority confinement

The [confinement proofs](../src/Passport/GrantConfinementProperties.agda) show that grant withdrawals preserve account authority, including devices, recovery records and encryption keys, through finite withdrawal/refusal histories. Each accepted withdrawal also preserves other grants under identifier separation and its own issuance/scope while settling nonce/spending; structural preservation does not establish change recoverability or availability.

### Historical grant replay exclusion

The [grant replay proofs](../src/Passport/GrantReplayProperties.agda) derive strictly increasing nonces between accepted spends without intervening reissuance, including zero-value spends, and exclude reuse of the old symbolic token under relevant request-binding agreement. Exclusion of repeated concrete signature material additionally requires an external signature-token interpretation law; concrete cryptographic realization and ledger adoption remain open.

### Grants-map mutation effects

[Source mutation proofs](../src/Passport/GrantEffectsProperties.agda) extract issuance, revocation and settlement updates, together with a classification of grants-map effects for runtime entrypoints. These local execution facts support spending and exclusion histories; they are distinct from the accumulated-spend invariant itself.

### Recovery submission and finalisation

[Recovery guard proofs](../src/Conformance/FullAccountRecoverySecurityProperties.agda) establish source verification, installation, cancellation and deadline/replacement facts. [Occurrence proofs](../src/Passport/AccountRecoveryOccurrenceProperties.agda) connect finalisation to an actual accepted submission in the deployment-rooted history, with no intervening accepted submission, cancellation or finalisation.

### Accumulated spending per grant issuance

[Whole-history spending proofs](../src/Passport/GrantSpendingProperties.agda) bound every current or archived issuance episode by its original cap and relate stored commitments/nonces to accumulated accepted spends. The sole additional cryptographic premise is agreement of the relevant spent-opening pairs; reissue, revocation/reset, recovery and refused calls are handled by the source-derived history accounting.

### Grant revocation and stale-record exclusion

[Revocation proofs](../src/Passport/RevocationExclusionProperties.agda) keep a revoked identifier absent or inactive until an actual matching device-authorized issuance, and exclude the corresponding source grant call before that boundary. They also show that old-epoch and old-generation records remain excluded after recovery or revoke-all.

### Post-recovery device exclusion

[Device-origin proofs](../src/Passport/RevocationExclusionProperties.agda) identify every later live entry as the installed recovery successor or an actual subsequent insertion occurrence. Excluding a queried device opening requires separation from that successor and those insertions, explicitly allowing re-enrolment and rejecting an unconditional permanent-key-ban interpretation.

### Counters and issuance ordering

[Counter proofs](../src/Passport/RevocationExclusionProperties.agda) derive nondecreasing authorization nonce, device epoch and grant generation from actual source executions rather than assuming monotonicity. Ordered issuance occurrences have strictly increasing issuance stamps, including across revocation, resets and recovery.

### Unshielded accounting

[Accounting proofs](../src/Passport/UnshieldedAccountingProperties.agda) establish, for every color and deployment-rooted history, that stored balance plus cumulative declared sends equals cumulative declared receives. They derive funding, arithmetic bounds and preservation from actual executions, but do not identify those declared effects with authenticated or adopted ledger assets.

### Restricted outsider preservation

[Outsider-history proofs](../src/Passport/OutsiderPreservationProperties.agda) show that accepted permissionless deposits and refused attempts preserve stored authority/recovery resources and enrolled device membership. They account exactly for deposit round consumption and explicitly exclude successful bootstrap and finalisation, so they are not availability or liveness proofs.

## Remaining assurance obligations

### Concrete cryptographic realization

The [assumption audit](cryptographic-assumptions-audit.md) inventories symbolic availability, trace-view agreement, relevant-opening binding and signature-token interpretation without establishing a joint native realization. Native verifier digest ambiguities must be addressed by a source-request-aware realization argument; composing conditional proofs does not discharge these premises.

### Commitment serialization and binding

The [commitment audit](commitment-binding-audit.md) gives canonical fixed-layout encoding arguments and native boundary evidence for the relevant opening premises, including all 61 application domain prefixes. Universal native serializer correspondence and collision/second-preimage reductions remain unproved; omitted fields, wildcard semantics and context authenticity need separate arguments.

### Ledger adoption and transaction safety

The [ledger-adoption boundary](ledger-adoption-boundary.md) specifies complete source-call projection, authenticated context/assets, ordering, partial effects and finality, with six candidate platform obligations that are neither approved nor discharged. A deployment-rooted projection cannot omit state-changing partial prefixes; native VM replay/ordering evidence does not establish that projection or top-level P11.

### Snapshot-aware reporting

The accounting invariant is a P12 precursor, not `SnapshotSound` or `SnapshotProgress`. Those require snapshot/completeness-aware report semantics, authenticated movement and fee accounting, and a synchronization model with explicit progress assumptions.

### Crash-safe recoverability

P13 needs an enforced relation between change descriptions, ciphertext recipients and actual remaining holdings, plus atomic recording or a durable restart/reconciliation protocol. Recovery after viewing-key rotation also needs access to the appropriate historical viewing material, without assuming a surviving private coin store.

### Availability and liveness

Resource preservation does not establish that authorized operations can eventually execute. Chain/client scheduling, data and proving access, fees, trustworthy time and finite contract counters need an explicit model and sufficient assumptions.

### Privacy and outsourced proving

No confidentiality or leakage theorem is established by these execution and authorization proofs. The adversary's observations, secret-bearing witness flows and proving-service boundary still need to be specified and related to the implementation.

### Guardian protocol security

The contract checks recovery authority, not the off-chain guardian exchange or the owner's consent. Quorum trust, share handling and recovery-protocol correctness remain separate obligations.

### Upgrade safety

The checked source target is fixed; these proofs do not cover code upgrades or preservation of their assumptions across versions. Upgrade authority, allowed changes and migration/refinement obligations still need a model.

## Other findings

### Signed ciphertext need not describe the change

Native execution demonstrates that authorized grant withdrawals accept supplied ciphertext describing the wrong change or encrypted to another real key, despite a matching separately supplied `enc_pk`. Signature coverage and atomic append therefore do not establish description/encryption binding against an authorized delegate.

### Device change recording has a transaction gap

The examined device path returns change before a separate inbox-backfill submission. Crash-safe recording is not established for that path at the pinned source; this is not an impossibility claim about a different recovery protocol.

### Structural preservation has a finite cost

Permissionless deposits preserve authority records but consume the finite round budget. This makes the distinction between non-corruption and non-griefability concrete: the former result cannot simply be relabeled as availability.

### Reauthorization is an explicit exception

The checked results permit explicit old-key re-enrolment and same-id grant reissue. An unconditional permanent-ban formulation would exclude supported authorization paths, so the theorems track those actual occurrences.

### Signature material does not identify one raw digest

The [native cryptographic audit](cryptographic-assumptions-audit.md#executed-evidence) demonstrates identical key/signature material verifying multiple raw digests in all three schemes, including distinct reduced ECDSA digests. These primitive-boundary witnesses refute universal exact-digest uniqueness, not source-request binding or Passport replay security: no matching source-request preimages or accepted replay were constructed.

### Typed preimages need a canonical layout

The [commitment probes](commitment-binding-audit.md#executed-native-evidence) show that different generic typed-atom lists can encode the same bytes and that low-level byte descriptors accept padding which the public circuit ABI rejects. These are encoding-boundary observations, not SHA-256 collisions or Passport exploits; binding arguments must restrict inputs to the validated layout.

### Execution evidence is broader than a proof of refinement

Current native/model correspondence evidence covers all 53 entrypoints with 243 observations and no mismatches, including all 18 withdrawal branches and zero-spend, cumulative-cap and reissuance boundaries. These are exercised correspondence checks, not a universal compiler-refinement theorem, ZK proof or on-chain inclusion result.

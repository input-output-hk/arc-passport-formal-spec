# Passport proof status report

Target: Passport [`fc19e471536febb2133f20e817847251622dcdf5`](https://github.com/midnightntwrk/passport/tree/fc19e471536febb2133f20e817847251622dcdf5), the latest fetched `main` when this work began. Formalization branch: `feat/passport-main-correspondence`.

## Current state

All packages in the proof inventory below have passed the integrated Agda entrypoint check after the focused readability refactoring, including accumulated grant spending. Revocation/recovery exclusion is still under verification, and change-durability/binding has concrete counterexamples. Overall readability acceptance, integration of any successful revocation result and remaining cleanup are pending.

## Proof inventory

### Symbolic signature provenance

The generic [symbolic signing](../src/Midnight/ContractDSL/SymbolicSigningProperties.agda) and [adversarial-history](../src/Midnight/ContractDSL/AdversarialLifecycleProperties.agda) proofs trace available tokens to attacker-controlled keys or approved honest issuance, with request-level provenance conditional on relevant encoding agreement. The [source binding](../src/Conformance/FullAccountSignatureBindingProperties.agda) and [account dispatcher bridge](../src/Passport/AccountRequestDispatchProperties.agda) connect this model to actual request extraction, but do not prove concrete cryptographic security or human consent.

### Device authorization and bootstrap

[Device proofs](../src/Conformance/FullAccountDeviceSecurityProperties.agda) derive live entry membership, signature verification, entry rolling and bounded nonce/round advancement from successful source executions. Bootstrap instead requires the unconsumed boot commitment, and the immediate replay result identifies a necessary challenge collision rather than proving universal signature non-replay.

### Grant authorization and settlement

[Grant proofs](../src/Conformance/FullAccountGrantSecurityProperties.agda) derive current/active/unexpired record checks, scope and recipient restrictions, numerical caps, verification, and the nonce/spent commitment stored after execution. Commitment equality is not automatically equality of intended keys, assets or recipients; those interpretations require relevant-opening agreement.

### Grants-map mutation effects

[Source mutation proofs](../src/Passport/GrantEffectsProperties.agda) extract issuance, revocation and settlement updates, together with a classification of grants-map effects for runtime entrypoints. These local execution facts support spending and exclusion histories; they are distinct from the accumulated-spend invariant itself.

### Recovery submission and finalisation

[Recovery guard proofs](../src/Conformance/FullAccountRecoverySecurityProperties.agda) establish source verification, installation, cancellation and deadline/replacement facts. [Occurrence proofs](../src/Passport/AccountRecoveryOccurrenceProperties.agda) connect finalisation to an actual accepted submission in the deployment-rooted history, with no intervening accepted submission, cancellation or finalisation.

### Accumulated spending per grant issuance

[Whole-history spending proofs](../src/Passport/GrantSpendingProperties.agda) bound every current or archived issuance episode by its original cap and relate stored commitments/nonces to accumulated accepted spends. The sole additional cryptographic premise is agreement of the relevant spent-opening pairs; reissue, revocation/reset, recovery and refused calls are handled by the source-derived history accounting.

### Unshielded accounting

[Accounting proofs](../src/Passport/UnshieldedAccountingProperties.agda) establish, for every color and deployment-rooted history, that stored balance plus cumulative declared sends equals cumulative declared receives. They derive funding, arithmetic bounds and preservation from actual executions, but do not identify those declared effects with authenticated or adopted ledger assets.

### Restricted outsider preservation

[Outsider-history proofs](../src/Passport/OutsiderPreservationProperties.agda) show that accepted permissionless deposits and refused attempts preserve stored authority/recovery resources and enrolled device membership. They account exactly for deposit round consumption and explicitly exclude successful bootstrap and finalisation, so they are not availability or liveness proofs.

## Missing or unfinished obligations

### Whole-history revocation and recovery exclusion

History-wide exclusion of revoked/stale grants and pre-recovery devices is still under formal verification, with explicit exceptions for actual reissue or re-enrolment. The same unfinished package seeks to prove that relevant source counters never decrease, preventing earlier epoch/generation values from becoming current again.

### Concrete cryptographic realization

We still need assumptions and realization arguments connecting real signature/hash operations to the ideal signing model and relevant-opening agreements. Effective-digest equivalences, including signature-scheme reductions, must be addressed rather than assuming raw digest or signature-byte uniqueness.

### Ledger adoption and transaction safety

Local source acceptance is not proof that an authenticated ledger adopts exactly the modeled effects under its actual context and asset rules. Completing top-level P11 needs that bridge, including the relevant authority, binding and replay guarantees at adoption.

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

Native probes accepted authorized grant withdrawals whose supplied ciphertext described the wrong change or was encrypted to another real key, despite a matching separately supplied `enc_pk`. Signature coverage and atomic append therefore do not establish description/encryption binding against an authorized delegate.

### Device change recording has a transaction gap

The examined device path returns change before a separate inbox-backfill submission. No crash-safe protocol was found in that examined path at the pinned source; this is not an impossibility proof for a different recovery protocol.

### Structural preservation has a finite cost

Permissionless deposits preserve authority records but consume the finite round budget. This makes the distinction between non-corruption and non-griefability concrete: the former result cannot simply be relabeled as availability.

### Execution evidence is broader than a proof of refinement

The full native/model comparison covered all 53 entrypoints with 225 observations and no mismatches, alongside focused property probes. These are exercised correspondence checks, not a universal compiler-refinement theorem, ZK proof or on-chain inclusion result.

### Unsuccessful work is retained

The failed durability/binding candidate remains on `feat/passport-properties-change-durability` in `.worktrees/passport-properties-change-durability`, with a runnable probe and 123 captured observations. No weaker append-only result is substituted for the requested property.

{-# OPTIONS --safe --without-K #-}

module Passport where

-- Reader entry point. Full-account correspondence scope and execution evidence:
-- docs/conformance-testing-plan.md#pinned-main-full-account-execution.
-- The older recovery theorem route is described in docs/conformance-recovery.md.
-- Cryptographic premise inventory and native realization limits:
-- docs/cryptographic-assumptions-audit.md.
-- Native commitment encoding and candidate ledger-adoption obligations:
-- docs/commitment-binding-audit.md; docs/ledger-adoption-boundary.md.

-- A. Full pinned-main account: transition wrapper, then its semantic definitions.
-- This is local source execution, not certified delayed ledger admission.
import Passport.Account
-- Values, state, execution/effects and primitive interface; named ABI projections.
import Conformance.FullAccountTypes
import Conformance.FullAccountLayouts
-- Accepted source-execution witnesses used in the security statements.
import Conformance.FullAccountExecution
-- Typed cryptographic preimages/authentication, source bodies, then grant twins.
import Conformance.FullAccountCrypto
import Conformance.FullAccountBody
import Conformance.FullAccountGrant
-- Entrypoint dispatch, argument validation and full ledger schema.
import Conformance.FullAccount
import Conformance.FullAccountProperties
-- Deployment-rooted labelled histories: generic relations and conditional
-- induction rules, then the account instance with a runtime-only call boundary.
-- Finite local histories with no environment/security policy chosen; scope:
-- docs/conformance-testing-plan.md#deployment-rooted-local-histories.
import Midnight.ContractDSL.Lifecycle
import Midnight.ContractDSL.LifecycleProperties
import Passport.AccountLifecycle

-- Symbolic signing knowledge and its interleaving with contract execution.
-- Approval is an abstract trusted input; message provenance is not a proof of
-- request binding, live authority or Passport transaction safety.
-- Scope: docs/conformance-testing-plan.md#symbolic-signing-and-adversarial-histories.
import Midnight.ContractDSL.SymbolicSigning
import Midnight.ContractDSL.SymbolicSigningProperties
import Midnight.ContractDSL.AdversarialLifecycle
import Midnight.ContractDSL.AdversarialLifecycleProperties

-- Concrete source requests, authorization guards and their account-level
-- composition. Ideal signing interpretation remains distinct from a native
-- cryptographic realization or a ledger-adoption theorem. Scope:
-- docs/conformance-testing-plan.md#contract-level-authorization-evidence.
-- Canonical fixed-layout bytes, distinct from hash binding/native refinement.
import Conformance.CommitmentEncoding
import Conformance.CommitmentLayouts
import Passport.CommitmentEncodingProperties
import Conformance.FullAccountSignatureBinding
import Conformance.FullAccountSignatureBindingProperties
import Conformance.FullAccountDeviceSecurity
import Conformance.FullAccountDeviceSecurityProperties
import Conformance.FullAccountGrantSecurity
import Conformance.FullAccountGrantSecurityProperties
-- Intended grant policy enforcement under relevant-opening agreement.
import Conformance.FullAccountGrantScope
import Conformance.FullAccountGrantScopeProperties
-- Grant withdrawals preserve account authority and other grants.
import Passport.GrantConfinement
import Passport.GrantConfinementProperties
-- Pinned recovery: device-authorized session publication/cancellation,
-- recovery and successor signatures at submission, and deadline-based
-- finalisation tied to an actual source-history occurrence. Architecture and
-- off-chain boundary: docs/conformance-recovery.md#pinned-recovery-architecture.
import Conformance.FullAccountRecoverySecurity
import Conformance.FullAccountRecoverySecurityProperties
import Passport.AccountSecurity
import Passport.AccountRequestDispatchProperties
import Passport.AccountSecurityProperties
import Passport.AccountRecoveryOccurrence
import Passport.AccountRecoveryOccurrenceProperties

-- Actual issuance, revocation and settlement mutations of the grants map.
import Passport.GrantEffects
import Passport.GrantEffectsProperties
-- Accumulated caps per actual issuance, with relevant spent-opening agreement.
import Passport.GrantSpending
import Passport.GrantSpendingProperties
-- Same-issuance historical replay exclusion under explicit binding premises.
import Passport.GrantReplay
import Passport.GrantReplayProperties
-- Composed local withdrawal safety, with distinct device/grant replay bounds.
import Passport.TransactionSafety
import Passport.TransactionSafetyProperties
-- Actual revocation/recovery boundaries and reauthorization occurrences.
-- Device exclusion additionally requires relevant-entry separation.
import Passport.RevocationExclusion
import Passport.RevocationExclusionProperties
-- Ordinary removal: literal-entry exclusion until a subsequent introduction.
import Passport.DeviceRemoval
import Passport.DeviceRemovalProperties

-- Per-color balance conservation against declared contract effects, not adopted
-- ledger balances, fees or snapshot reports.
import Passport.UnshieldedAccounting
import Passport.UnshieldedAccountingProperties

-- Restricted outsider histories preserve stored authority/recovery resources,
-- not execution availability: deposits consume finite round/inbox capacity.
import Passport.OutsiderPreservation
import Passport.OutsiderPreservationProperties

-- B. Local VM properties and their statement definitions, not compiler refinement.
-- Interpreter/DSL replay, opcode codec, then typed map/set representation.
import Conformance.VM
import Conformance.VMEncoding
import Conformance.VMAccount
import Conformance.VMProperties

-- C. Earlier recovery slice.
-- C.1. Intended contract and its post-bootstrap boundary.
import Passport.AccountRecovery

-- C.2. Generic Contract.Admissions; AccountRecovery.Chain instantiates it.
-- Traces include arbitrary ordering, build views and rejection, without policy.
import Midnight.ContractDSL.Contract
-- Protocol adapter: submission receipts and reachability of those admission traces.
import Midnight.ContractDSL.Protocol

-- C.3. Advertised properties with required companion guard/assumption definitions:
-- execution/provenance/deadline obligations, then compromised-device exclusion
-- under the separate TracePolicy hypothesis.
import Conformance.RecoveryExecutionDefinitions
import Conformance.RecoveryExecution
import Conformance.RecoveryAuthorityDefinitions
import Conformance.RecoveryAuthority

-- Appendix: model data, authorisation seam, and circuit bodies.
import Conformance.Primitives
import Conformance.AccountLedger
import Conformance.Custody
import Conformance.Recovery

-- Appendix: wallet/signing clients and reusable raw transition monitor.
-- Runtime API, build and examples:
-- docs/conformance-recovery.md#runtime-transition-monitor
import Conformance.Account
import Conformance.Monitor
-- External candidate-journal validation before certified core admission.
import Conformance.CertificateDecision
-- Pure serialization/dispatch and the trusted primitive backend boundary.
import Conformance.Wire
import Conformance.Oracle

-- Appendix: checked proof implementations.
import Conformance.RecoveryExecutionProof
import Conformance.RecoveryAuthorityProof
import Conformance.FullAccountProof
import Conformance.FullAccountSignatureBindingProof
import Conformance.CommitmentEncodingProof
import Conformance.FullAccountDeviceSecurityProof
import Conformance.FullAccountGrantSecurityProof
import Conformance.FullAccountGrantScopeProof
import Passport.GrantConfinementProof
import Conformance.FullAccountRecoverySecurityProof
import Conformance.FullAccountRecoverySecurityHelpers
import Conformance.FullAccountRecoverySecurityStages
import Conformance.FullAccountRecoverySecurityPendingProof
import Passport.AccountSecurityProof
import Passport.AccountRecoveryOccurrenceProof
import Passport.GrantEffectsProof
import Passport.GrantSpendingProof
import Passport.GrantReplayProof
import Passport.TransactionSafetyProof
import Passport.RevocationExclusionProof
import Passport.DeviceRemovalProof
import Passport.UnshieldedAccountingProof
import Passport.UnshieldedAccountingNeutral
import Passport.OutsiderPreservationProof
import Conformance.VMProof
import Conformance.VMEncodingProof
import Conformance.VMAccountProof
import Midnight.ContractDSL.LifecycleProof
import Midnight.ContractDSL.SymbolicSigningProof
import Midnight.ContractDSL.AdversarialLifecycleProof

-- Appendix: local evaluation, journals and replay.
-- Optional executable signing decisions and certification of model transitions.
import Midnight.ContractDSL.SymbolicSigningExecution
import Midnight.ContractDSL.Program
import Midnight.ContractDSL.Ledger
import Midnight.ContractDSL.Properties
import Midnight.ContractDSL.Hoare
import Midnight.ContractDSL.AdmissionProperties

-- Appendix: schema-derived storage and lens laws.
import Midnight.ContractDSL.Storage
import Midnight.ContractDSL.Storage.Properties

-- Appendix: full-account wire codec and concrete VM instantiation/transports.
import Conformance.FullAccountWire
import Conformance.VMConcrete
import Conformance.VMWire

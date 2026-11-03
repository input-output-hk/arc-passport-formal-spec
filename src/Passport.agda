{-# OPTIONS --safe --without-K #-}

module Passport where

-- Reader entry point. Full-account correspondence scope and execution evidence:
-- docs/conformance-testing-plan.md#pinned-main-full-account-execution.
-- The older recovery theorem route is described in docs/conformance-recovery.md.

-- A. Full pinned-main account: transition wrapper, then its semantic definitions.
-- This is local source execution, not certified delayed ledger admission.
import Passport.Account
-- Values, state, execution/effects and primitive interface; named ABI projections.
import Conformance.FullAccountTypes
import Conformance.FullAccountLayouts
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
import Conformance.VMProof
import Conformance.VMEncodingProof
import Conformance.VMAccountProof
import Midnight.ContractDSL.LifecycleProof

-- Appendix: local evaluation, journals and replay.
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

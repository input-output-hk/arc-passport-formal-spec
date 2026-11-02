{-# OPTIONS --safe --without-K #-}

module Passport where

-- Reader entry point. Assumptions and concrete-correspondence limits are in the
-- theorem modules; supporting prose is docs/conformance-recovery.md.

-- 1. Intended shared account-recovery contract and its post-bootstrap boundary.
import Passport.AccountRecovery

-- 2. Generic Contract.Admissions; AccountRecovery.Chain instantiates it.
-- Traces include arbitrary ordering, build views and rejection, without policy.
import Midnight.ContractDSL.Contract
-- Protocol adapter: submission receipts and reachability of those admission traces.
import Midnight.ContractDSL.Protocol

-- 3. Advertised properties with required companion guard/assumption definitions:
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

-- Appendix: local evaluation, journals and replay.
import Midnight.ContractDSL.Program
import Midnight.ContractDSL.Ledger
import Midnight.ContractDSL.Properties
import Midnight.ContractDSL.Hoare
import Midnight.ContractDSL.AdmissionProperties

-- Appendix: schema-derived storage and lens laws.
import Midnight.ContractDSL.Storage
import Midnight.ContractDSL.Storage.Properties

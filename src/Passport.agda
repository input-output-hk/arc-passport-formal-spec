{-# OPTIONS --safe --without-K #-}

module Passport where

import Midnight.ContractDSL.Ledger
import Midnight.ContractDSL.Properties
import Midnight.ContractDSL.Hoare
import Midnight.ContractDSL.Contract
import Midnight.ContractDSL.AdmissionProperties
import Midnight.ContractDSL.Storage
import Midnight.ContractDSL.Storage.Properties

-- Reader entry point. Assumptions and concrete-correspondence limits are in the
-- theorem modules; supporting prose is docs/conformance-recovery.md.


-- 1. Intended shared account-recovery contract and its post-bootstrap boundary.
import Passport.AccountRecovery

-- 2. Generic Interpreter.Admissions; AccountRecovery.Chain instantiates it.
-- Traces include arbitrary ordering, build views and rejection, without policy.
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

-- Appendix: wallet/signing protocols and historical conformance comparator.
import Conformance.Account

-- Appendix: checked proof implementations.
import Conformance.RecoveryExecutionProof
import Conformance.RecoveryAuthorityProof

-- Appendix: local evaluation, journals and replay.
import Midnight.ContractDSL.Program

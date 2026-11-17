{-# OPTIONS --safe --without-K #-}

module Passport where

-- Finalized ledger: structured state transitions, then accounting and replay laws.
-- Scope and executable examples: ../docs/finalized-ledger.md
import Passport.FinalizedLedger
import Passport.FinalizedLedgerProperties

-- Contract DSL
import Midnight.ContractDSL.Ledger
import Midnight.ContractDSL.Program
import Midnight.ContractDSL.Properties
import Midnight.ContractDSL.Hoare

-- Contracts and current-state admission
import Midnight.ContractDSL.Contract
import Midnight.ContractDSL.AdmissionProperties
import Midnight.ContractDSL.Protocol

-- Schema-derived storage
import Midnight.ContractDSL.Storage
import Midnight.ContractDSL.Storage.Properties

------------------------------------------------------------------------
-- Appendix: concrete finalized-ledger accounting and rejection examples
------------------------------------------------------------------------
import Passport.FinalizedLedgerExamples

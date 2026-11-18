{-# OPTIONS --safe #-}

module Passport where

-- Finalized ledger: structured state transitions, then accounting and replay laws.
-- Scope and executable examples: ../docs/finalized-ledger.md
import Passport.FinalizedLedger
import Passport.FinalizedLedgerProperties

-- Account/asset custody queries and whole-architecture preservation of value.
-- Scope and reading route: ../docs/account-custody.md
import Passport.AccountCustody
import Passport.AccountCustodyProperties
import Passport.AccountCustodyArchitecture
import Passport.AccountCustodyArchitectureProperties

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
-- Appendix: concrete ledger and custody accounting/rejection examples
------------------------------------------------------------------------
import Passport.FinalizedLedgerExamples
import Passport.AccountCustodyExamples

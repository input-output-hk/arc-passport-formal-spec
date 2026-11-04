{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

-- All three actual grant-withdrawal entrypoints, for Jubjub, K256 and P256.
-- Runtime acceptance, not an assumed neutral action, supplies the frame.
-- Read GrantConfinement for the protected cells and the own/other-grant record
-- guarantees. Refused attempts may be interspersed in finite histories.
-- Grants, balances, inbox and round are intentionally not blanket-preserved.
-- No cryptographic binding premise is needed: these are source-runtime write
-- restrictions, not change recoverability or global non-griefability claims.
module Passport.GrantConfinementProperties (P : Primitives) (address : Value) where

open import Conformance.FullAccountExecution using (Run)
open import Conformance.FullAccountGrant P
open import Conformance.FullAccountGrantSecurity P using (Withdrawal)
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (_×_)
import Passport.Account as Account
open import Passport.GrantConfinement P address
import Passport.GrantConfinementProof P address as Proof
open import Relation.Binary.PropositionalEquality using (_≡_)

source-confinement : ∀ c op ctx ga xs → Withdrawal op → ∀ {s v t} →
  Run (grantCall c op ctx ga xs) s v t → Confinement c op ctx ga xs s t
source-confinement = Proof.source-confinement

runtime-confinement : ∀ {s t} (step : Runs.Step s t) c op → Withdrawal op → ∀ {v es} →
  Runs.Step.outcome step ≡ Account.committed v es →
  resolve (Runs.Step.call step) ≡ just (Semantics.grant c op) → RuntimeConfinement step c op
runtime-confinement = Proof.runtime-confinement

trace-frame : ∀ {s t} → GrantTrace s t → Frame s t
trace-frame = Proof.trace-frame

trace-authority : ∀ {s t} → GrantTrace s t → AuthorityPreserved s t
trace-authority = Proof.trace-authority

trace-enrolled : ∀ {s t} → GrantTrace s t → ∀ entry → Enrolled entry s → Enrolled entry t
trace-enrolled = Proof.trace-enrolled

history-confinement : ∀ {s t} → Runs.History s → GrantTrace s t →
  Runs.History t × Frame s t × AuthorityPreserved s t × (∀ entry → Enrolled entry s → Enrolled entry t)
history-confinement = Proof.history-confinement

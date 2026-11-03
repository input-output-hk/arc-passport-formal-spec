{-# OPTIONS --safe --without-K #-}

open import Conformance.FullAccountTypes

-- Whole-history local contract accounting, not ledger adoption or a proof of
-- SHA-256 binding. HistoryAgreement concerns only the two spent openings at
-- an accepted grant spend. It assumes neither a cumulative cap nor that the
-- caller's spentPrev already equals a historical sum.
--
-- historyBook records every accepted grant amount under the most recent
-- actual issuance at that id. Reissue archives the old episode, revoke-all
-- archives the current map, and refusals do not change the book. Revocation
-- and recovery preserve its accounting. Issuance retains stored id, epoch,
-- generation and issuedAt; amounts are newest first.
module Passport.GrantSpendingProperties (P : Primitives) (address : Value) where

open import Data.List.Base using (_++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat.Base using (_≤_)
open import Passport.GrantSpending P
open Histories address
import Passport.GrantSpendingProof P as Proof

whole-history-spend-cap : ∀ {s} (history : Runs.History s) → HistoryAgreement history →
  ∀ ep → ep ∈ (Book.current (historyBook history) ++ Book.completed (historyBook history)) →
  total ep ≤ Episode.capValue ep
whole-history-spend-cap = Proof.Rooted.rooted-episode-cap address

-- At every retained map entry, the stored commitment opens to the sum of
-- accepted amounts for that issuance and the nonce counts those spends.
whole-history-stored-openings : ∀ {s} (history : Runs.History s) → HistoryAgreement history →
  Accounted (historyBook history) s
whole-history-stored-openings = Proof.Rooted.rooted-accounted address

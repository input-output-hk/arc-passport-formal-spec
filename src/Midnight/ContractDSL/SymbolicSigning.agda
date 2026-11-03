{-# OPTIONS --safe --without-K #-}

-- Symbolic approval and message-level signing against a key-compromising
-- adversary. Tokens represent message-level signature knowledge, not signature
-- bytes. Constructing `signature k m` alone does not establish Available;
-- issuance is justified for histories rooted in initial.
--
-- Approve events are trusted abstract honest-party inputs, not attacker actions.
-- This is an interpretation assumption: the model does not authenticate the
-- actor supplying an event, wallet UI, human consent or an authenticator ceremony.
--
-- Attacker-owned keys are valid keys controlled from the outset. Honest keys
-- become attacker-controlled permanently once compromised. Issued tokens are
-- never consumed, so the attacker may retain, replay, reorder and delay them.
--
-- encode is supplied by the instantiation and is NOT assumed injective.
-- Provenance is therefore message-level: a token traces back to some request that
-- was actually approved and signed, not necessarily the request a later call
-- intends. No key-material, curve or unforgeability claim is made here.
-- Statements: SymbolicSigningProperties; proofs: SymbolicSigningProof.
-- Scope: docs/conformance-testing-plan.md#symbolic-signing-and-adversarial-histories.
module Midnight.ContractDSL.SymbolicSigning where

open import Data.List.Base using (List; _∷_; [])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_)
open import Level
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.PropositionalEquality

-- Initial ownership, not current live contract authority.
data Ownership : Set where
  honest attacker : Ownership

record Interface (ℓ : Level) : Set (suc ℓ) where
  field Key Request Message : Set ℓ
        ownership : Key → Ownership
        encode : Key → Request → Message

module Model {ℓ} (S : Interface ℓ) where
  open Interface S

  record Token : Set ℓ where
    constructor signature
    field key : Key
          message : Message

  -- Resources only grow; duplicates are harmless under membership semantics.
  record State : Set ℓ where
    constructor state
    field compromised : List Key
          approvals : List (Key × Request)
          signatures : List Token

  open State

  initial : State
  initial = state [] [] []

  data Event : Set ℓ where
    approve honestSign : Key → Request → Event
    attackerSign : Key → Message → Event
    compromise : Key → Event

  Controlled : State → Key → Set ℓ
  Controlled s k = ownership k ≡ attacker ⊎ k ∈ compromised s

  Approved : State → Key → Request → Set ℓ
  Approved s k r = (k , r) ∈ approvals s

  Available : State → Token → Set ℓ
  Available s τ = τ ∈ signatures s

  -- An honest key may still sign approved requests after compromise; any
  -- conclusion about such a key then already exposes attacker control.
  data Permitted (s : State) : Event → Set ℓ where
    honestApproval : ∀ {k r} → ownership k ≡ honest → Permitted s (approve k r)
    approvedSigning : ∀ {k r} → ownership k ≡ honest → Approved s k r → Permitted s (honestSign k r)
    controlledSigning : ∀ {k m} → Controlled s k → Permitted s (attackerSign k m)
    anyCompromise : ∀ {k} → Permitted s (compromise k)

  apply : Event → State → State
  apply (approve k r) s = record s { approvals = (k , r) ∷ approvals s }
  apply (honestSign k r) s = record s { signatures = signature k (encode k r) ∷ signatures s }
  apply (attackerSign k m) s = record s { signatures = signature k m ∷ signatures s }
  apply (compromise k) s = record s { compromised = k ∷ compromised s }

  record Transition (before after : State) : Set ℓ where
    constructor transition
    field event : Event
          permitted : Permitted before event
          executed : apply event before ≡ after

  Trace : State → State → Set ℓ
  Trace = Star Transition

  -- `Occurs e before trace`: some transition of trace executes e from before.
  data Occurs (e : Event) (before : State) : ∀ {s t} → Trace s t → Set ℓ where
    now : ∀ {m t} (permitted : Permitted before e) (executed : apply e before ≡ m)
      (rest : Trace m t) → Occurs e before (transition e permitted executed ◅ rest)
    later : ∀ {s m t} (x : Transition s m) {rest : Trace m t} →
      Occurs e before rest → Occurs e before (x ◅ rest)

  -- Message-level honest provenance of τ within trace: an honestSign of an
  -- approved request whose encoding is τ's message. With a colliding encode,
  -- request need not be the request a later consumer of τ has in mind.
  record HonestlyIssued {s t} (trace : Trace s t) (τ : Token) : Set ℓ where
    constructor issued
    field request : Request
          before : State
          honestKey : ownership (Token.key τ) ≡ honest
          approved : Approved before (Token.key τ) request
          encodes : encode (Token.key τ) request ≡ Token.message τ
          occurs : Occurs (honestSign (Token.key τ) request) before trace

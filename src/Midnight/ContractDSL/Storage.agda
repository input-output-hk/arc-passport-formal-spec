{-# OPTIONS --safe --without-K #-}

-- Schema-derived state, defaults, lenses and whole-field read/write semantics.
-- Collections are lists: duplicates are possible and equality observes order.
-- Reads record whole fields, so unrelated map-key changes can invalidate replay.
module Midnight.ContractDSL.Storage where

open import Class.DecEq
open import Data.Bool using (Bool; false)
open import Data.Empty
open import Data.List
open import Data.Maybe
open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties using (_<?_; m^n>0)
open import Data.Product
open import Data.Sum
open import Data.Unit hiding (_≟_)
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Midnight.ContractDSL.Ledger

record Lens (V State : Set) : Set where
  field get : State → V
        put : V → State → State

record Atoms : Set₁ where
  field Atom         : Set
        Meaning      : Atom → Set
        defaultAtom  : (a : Atom) → Meaning a
        equalityAtom : (a : Atom) → DecEq (Meaning a)

-- Store the natural directly; an inductive Fin would allocate up to 2^width nodes.
record Uint (width : ℕ) : Set where
  constructor uintValue
  field toℕ : ℕ
        .inRange : toℕ < 2 ^ width
open Uint public

uintEquality : {width : ℕ} → DecEq (Uint width)
uintEquality .DecEq._≟_ (uintValue x _) (uintValue y _) with x ≟ y
... | yes refl = yes refl
... | no neq = no (λ { refl → neq refl })

module Types (A : Atoms) where
  data ValueCode : Set where
    boolean : ValueCode
    uint    : ℕ → ValueCode
    atom    : Atoms.Atom A → ValueCode

  Value : ValueCode → Set
  Value boolean      = Bool
  Value (uint width) = Uint width
  Value (atom a)     = Atoms.Meaning A a

  valueDefault : (c : ValueCode) → Value c
  valueDefault boolean      = false
  valueDefault (uint width) = uintValue 0 (m^n>0 2 width)
  valueDefault (atom a)     = Atoms.defaultAtom A a

  valueEquality : (c : ValueCode) → DecEq (Value c)
  valueEquality boolean      = DecEq-Bool
  valueEquality (uint width) = uintEquality
  valueEquality (atom a)     = Atoms.equalityAtom A a

  uintFromNat : (width n : ℕ) → Maybe (Value (uint width))
  uintFromNat width n = case n <? 2 ^ width of λ where
    (yes bounded) → just (uintValue n bounded)
    (no  _)       → nothing

  data Code : Set where
    cell setOf : ValueCode → Code
    mapOf      : ValueCode → ValueCode → Code

  El : Code → Set
  El (cell c)    = Value c
  El (setOf c)   = List (Value c)
  El (mapOf k v) = List (Value k × Value v)

  default : (c : Code) → El c
  default (cell c)    = valueDefault c
  default (setOf c)   = []
  default (mapOf k v) = []

  equality : (c : Code) → DecEq (El c)
  equality (cell c)  = valueEquality c
  equality (setOf c) = DecEq-List ⦃ valueEquality c ⦄
  equality (mapOf k v) =
    DecEq-List ⦃ DecEq-× ⦃ valueEquality k ⦄ ⦃ valueEquality v ⦄ ⦄

  record Schema : Set₁ where
    field Field             : Set
          ⦃ fieldEquality ⦄ : DecEq Field
          code              : Field → Code

    State : Set
    State = (f : Field) → El (code f)

    initial : State
    initial f = default (code f)

    update : (f : Field) → El (code f) → State → State
    update f v s f′ = case f ≟ f′ of λ where
      (yes refl) → v
      (no  _)    → s f′

    lens : (f : Field) → Lens (El (code f)) State
    lens f = record { get = λ s → s f ; put = update f }

    module Sem where
      data Kind : Set where
        reading : Field → Kind
        writing : Kind

      Res : Kind → Set
      Res (reading f) = El (code f)
      Res writing     = ⊤

      data Op : Kind → Set where
        read  : (f : Field) → Op (reading f)
        write : (f : Field) → El (code f) → Op writing

      Failure : Kind → Set
      Failure _ = ⊥

      prepare : {k : Kind} → Op k → State → Failure k ⊎ (Res k × State)
      prepare (read f)    s = inj₂ (s f , s)
      prepare (write f v) s = inj₂ (tt , update f v s)

      resultEquality : (k : Kind) → DecEq (Res k)
      resultEquality (reading f) = equality (code f)
      resultEquality writing     = DecEq-⊤

    semantics : Semantics
    semantics = record { Sem ; DecEq-Res = λ {k} → Sem.resultEquality k }

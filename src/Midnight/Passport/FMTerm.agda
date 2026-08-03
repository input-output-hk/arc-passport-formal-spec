{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Midnight.Passport.FMTerm
--
-- The free strict monoidal category over named channel generators,
-- backed by categorical-crypto's Categories.FreeStrictMonoidal.
--
-- Objects are List String (channel names); tensoring (_⊗₀_) is list
-- concatenation, so parallel layers glue definitionally.
--
-- Public interface
-- ────────────────
--   ObjTerm, _⊗₀_, unit, Var   — object language (wire lists)
--   Label                       — generator record { name : String }
--   HomTerm                     — morphism type (the library's WTerm)
--   var, id, _∘_, _⊗₁_         — renamed library constructors
--   gen, idm, _>>_, _⊗_        — convenience constructors
------------------------------------------------------------------------

module Midnight.Passport.FMTerm where

open import Categories.FreeStrictMonoidal using (module FreeStrictMonoidalHelper)
open import Data.String using (String)
open import Data.List using (List; []; _++_; [_])

------------------------------------------------------------------------
-- Object language: wire lists over channel names

ObjTerm : Set
ObjTerm = List String

infixr 10 _⊗₀_
_⊗₀_ : ObjTerm → ObjTerm → ObjTerm
_⊗₀_ = _++_

unit : ObjTerm
unit = []

Var : String → ObjTerm
Var = [_]

------------------------------------------------------------------------
-- Generator type
--
-- A named morphism generator.  The domain A and codomain B are carried
-- entirely as type indices; only the human-readable name is stored.

record Label (A B : ObjTerm) : Set where
  constructor mkLabel
  field name : String

------------------------------------------------------------------------
-- HomTerm and its constructors, instantiated at the Label generators

module H = FreeStrictMonoidalHelper Label

open H public using ()
  renaming ( WTerm to HomTerm; boxʷ to var; idʷ to id
           ; _∘ʷ_ to infixr 9 _∘_; _⊗ʷ_ to infixr 10 _⊗₁_ )

------------------------------------------------------------------------
-- Convenience aliases preserving the old FMTerm calling conventions

-- Left-to-right sequential composition.
-- The library uses right-to-left order (_∘_), so _>>_ = flip _∘_.
infixr 9 _>>_
_>>_ : ∀ {A B C : ObjTerm} → HomTerm A B → HomTerm B C → HomTerm A C
f >> g = g ∘ f

-- Tensor product (alias for _⊗₁_).
infixr 8 _⊗_
_⊗_ : ∀ {A B C D : ObjTerm}
    → HomTerm A B → HomTerm C D → HomTerm (A ⊗₀ C) (B ⊗₀ D)
_⊗_ = _⊗₁_

-- Identity on an explicit object.
idm : (a : ObjTerm) → HomTerm a a
idm _ = id

------------------------------------------------------------------------
-- gen — lift a named component into a morphism
--
-- ins and outs are ObjTerm values; callers build them with Var / _⊗₀_.

gen : (n : String) (ins outs : ObjTerm) → HomTerm ins outs
gen n ins outs = var (mkLabel n)

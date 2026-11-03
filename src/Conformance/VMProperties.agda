{-# OPTIONS --safe --without-K #-}

-- These claims concern the explicit interpreter and typed collection leaves.
-- They do not identify the pinned WASM/compiler with this interpreter, account
-- for native gas/cache charging, or authenticate external asset effects.
module Conformance.VMProperties where

open import Data.Bool.Base using (false)
open import Data.List.Base using ([]; _∷_; map)
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (_×_)
open import Relation.Binary.PropositionalEquality
open import Conformance.VM using (Atoms; module Machine)
import Conformance.FullAccountTypes as Account
import Conformance.VMEncoding as Encoding
import Conformance.VMAccount as Representation
import Conformance.VMProof as ExecutionProof
import Conformance.VMEncodingProof as EncodingProof
import Conformance.VMAccountProof as RepresentationProof

module Execution (A : Atoms) where
  open Machine A
  module P = ExecutionProof.Proofs A

  -- Every relational instruction journal succeeds under DSL-backed replay.
  journal-admission : ∀ {s ops t} → Journal s ops t → replay ops s ≡ just t
  journal-admission = P.journal-admission

  -- A fuel-bounded relational program run is accepted by the interpreter.
  program-admission : ∀ {program fuel s t} → ProgramRun program fuel s t → run fuel program s ≡ just t
  program-admission = P.program-admission

  -- Every successful interpreter run has a matching relational derivation.
  run-sound : ∀ {fuel program s t} → run fuel program s ≡ just t → ProgramRun program fuel s t
  run-sound = P.run-sound

module Codec (A : Atoms) where
  open Encoding.Encoding A
  module P = EncodingProof.Proofs A

  -- Encoding a typed instruction sequence and decoding it recovers that sequence.
  trace-roundtrip : ∀ ops → decodeAll (map encode ops) ≡ just ops
  trace-roundtrip = P.trace-roundtrip

  -- A decoded relational run is accepted by the concrete-code admission function.
  decoded-admission : ∀ {encoded fuel s t} → DecodedRun encoded fuel s t → admit fuel encoded s ≡ just t
  decoded-admission = P.decoded-admission

  -- Successful concrete-code admission yields a decoded relational run.
  admission-sound : ∀ {encoded fuel s t} → admit fuel encoded s ≡ just t → DecodedRun encoded fuel s t
  admission-sound = P.admission-sound

module AccountRepresentation (A : Atoms) where
  module M = Machine A
  module R = Representation.Representation A
  module P = RepresentationProof.Proofs A

  -- E assumes equality-preserving encoding within one declared key type.
  -- Cross-type injectivity is neither assumed nor claimed.
  module Typed (E : R.AtomEncoding) where
    module Key = R.AtomEncoding E
    module Entries = R.Encoded E
    module Q = P.Encoded E

    -- Pure map insertion preserves the typed leaf relation; not a lowering of ins.
    insert-correspondence : ∀ {xs ys} → Entries.MapEntries xs ys → ∀ k v →
      Entries.MapEntries (Account.insertMap (Key.keyValue k) v xs)
        (M.insert (Key.encodeKey k) (M.cell (Key.encodeValue v)) ys)
    insert-correspondence = Q.insert-correspondence

    -- Pure set removal preserves the typed leaf relation; not a whole-circuit claim.
    remove-correspondence : ∀ {xs ys} → Entries.SetEntries xs ys → ∀ k →
      Entries.SetEntries (Account.removeSet (Key.keyValue k) xs) (M.remove (Key.encodeKey k) ys)
    remove-correspondence = Q.remove-correspondence

    -- A successful source map lookup agrees with idx followed by popeq checking
    -- its observed value. Two non-branching instructions advance nextPC twice.
    typed-map-read : ∀ label s xs ys k v → Account.cell label s ≡ Account.tuple xs →
      Entries.MapEntries xs ys → Account.lookupMap (Key.keyValue k) xs ≡ just v →
      ∀ cached strength pc rest →
      (Account.lookup label (Key.keyValue k) s ≡
        Account.accepted v s (Account.mapLookup label (Key.keyValue k) v ∷ [])) ×
      M.Journal (M.machine pc (M.item strength (M.table ys) ∷ rest))
        (M.idx cached false (M.literal (Key.encodeKey k) ∷ []) ∷
          M.popeq cached (Key.encodeValue v) ∷ [])
        (M.machine (Entries.nextPC (Entries.nextPC pc)) rest)
    typed-map-read = Q.typed-map-read

    -- Source set membership agrees with the single member opcode and one PC step.
    typed-set-member : ∀ label s xs ys k → Account.cell label s ≡ Account.tuple xs →
      Entries.SetEntries xs ys → ∀ strength keyStrength pc rest →
      (Account.has label (Key.keyValue k) s ≡
        Account.accepted (Account.member (Key.keyValue k) xs) s
          (Account.setMember label (Key.keyValue k) (Account.member (Key.keyValue k) xs) ∷ [])) ×
      M.Step M.member
        (M.machine pc (M.item keyStrength (M.cell (Key.encodeKey k)) ∷ M.item strength (M.table ys) ∷ rest))
        (M.machine (Entries.nextPC pc) (M.boolItem (Account.member (Key.keyValue k) xs) ∷ rest))
    typed-set-member = Q.typed-set-member

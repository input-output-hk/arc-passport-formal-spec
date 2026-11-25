{-# OPTIONS --safe --without-K #-}

module Conformance.VMEncodingProof where

open import Data.List.Base using ([]; _∷_; map)
open import Data.Maybe.Base using (nothing; just)
open import Relation.Binary.PropositionalEquality
open import Conformance.VM using (Atoms)
import Conformance.VMEncoding as Codec
import Conformance.VMProof as ExecutionProof

module Proofs (A : Atoms) where
  open Codec.Encoding A
  module P = ExecutionProof.Proofs A

  roundtrip : ∀ op → decode (encode op) ≡ just op
  roundtrip (M.noop n) = refl
  roundtrip (M.dup n) = refl
  roundtrip (M.swap n) = refl
  roundtrip M.lt = refl
  roundtrip M.eq = refl
  roundtrip M.type = refl
  roundtrip M.size = refl
  roundtrip M.new = refl
  roundtrip M.and = refl
  roundtrip M.or = refl
  roundtrip M.neg = refl
  roundtrip M.pop = refl
  roundtrip M.add = refl
  roundtrip M.sub = refl
  roundtrip M.member = refl
  roundtrip M.ckpt = refl
  roundtrip (M.popeq cached r) = refl
  roundtrip (M.addi n) = refl
  roundtrip (M.subi n) = refl
  roundtrip (M.push storage v) = refl
  roundtrip (M.branch n) = refl
  roundtrip (M.jmp n) = refl
  roundtrip (M.concat cached n) = refl
  roundtrip (M.ins cached n) = refl
  roundtrip (M.rem cached) = refl
  roundtrip (M.idx cached pushPath keys) = refl
  roundtrip M.unsupported = refl

  trace-roundtrip : ∀ ops → decodeAll (map encode ops) ≡ just ops
  trace-roundtrip [] = refl
  trace-roundtrip (op ∷ ops) rewrite roundtrip op | trace-roundtrip ops = refl

  decoded-admission : ∀ {encoded fuel s t} → DecodedRun encoded fuel s t → admit fuel encoded s ≡ just t
  decoded-admission (decodedRun program decoded execution) rewrite decoded = P.program-admission execution

  encoded-program-admission : ∀ {program fuel s t} → M.ProgramRun program fuel s t →
    admit fuel (map encode program) s ≡ just t
  encoded-program-admission {program} execution rewrite trace-roundtrip program = P.program-admission execution

  admission-sound : ∀ {encoded fuel s t} → admit fuel encoded s ≡ just t → DecodedRun encoded fuel s t
  admission-sound {encoded} accepted with decodeAll encoded in decoded
  ... | nothing with accepted
  ...   | ()
  admission-sound {encoded} accepted | just program = decodedRun program decoded (P.run-sound accepted)

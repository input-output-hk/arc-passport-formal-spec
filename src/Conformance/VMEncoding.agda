{-# OPTIONS --safe --without-K #-}

-- The JSON parser/field canonicalizer is outside Agda. Its boundary is a tagged
-- opcode with an ordered, typed argument vector. No read result or update value
-- is recovered by re-running an account model.
module Conformance.VMEncoding where

open import Data.Bool.Base
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base
open import Data.String.Base using (String)
open import Relation.Binary.PropositionalEquality

open import Conformance.VM

module Encoding (A : Atoms) where
  open Atoms A
  module M = Machine A

  data Argument : Set where
    number : ℕ → Argument
    flag : Bool → Argument
    result : Aligned → Argument
    state : M.Value → Argument
    path : List M.Key → Argument

  record Raw : Set where
    constructor raw
    field opcode : String
          arguments : List Argument

  encode : M.Instruction → Raw
  encode (M.noop n) = raw "noop" (number n ∷ [])
  encode (M.dup n) = raw "dup" (number n ∷ [])
  encode (M.swap n) = raw "swap" (number n ∷ [])
  encode M.lt = raw "lt" []
  encode M.eq = raw "eq" []
  encode M.type = raw "type" []
  encode M.size = raw "size" []
  encode M.new = raw "new" []
  encode M.and = raw "and" []
  encode M.or = raw "or" []
  encode M.neg = raw "neg" []
  encode M.pop = raw "pop" []
  encode M.add = raw "add" []
  encode M.sub = raw "sub" []
  encode M.member = raw "member" []
  encode M.ckpt = raw "ckpt" []
  encode (M.popeq cached r) = raw "popeq" (flag cached ∷ result r ∷ [])
  encode (M.addi n) = raw "addi" (number n ∷ [])
  encode (M.subi n) = raw "subi" (number n ∷ [])
  encode (M.push storage v) = raw "push" (flag storage ∷ state v ∷ [])
  encode (M.branch n) = raw "branch" (number n ∷ [])
  encode (M.jmp n) = raw "jmp" (number n ∷ [])
  encode (M.concat cached n) = raw "concat" (flag cached ∷ number n ∷ [])
  encode (M.ins cached n) = raw "ins" (flag cached ∷ number n ∷ [])
  encode (M.rem cached) = raw "rem" (flag cached ∷ [])
  encode (M.idx cached pushPath keys) = raw "idx" (flag cached ∷ flag pushPath ∷ path keys ∷ [])
  encode M.unsupported = raw "!unsupported" []

  decode : Raw → Maybe M.Instruction
  decode (raw "noop" (number n ∷ [])) = just (M.noop n)
  decode (raw "dup" (number n ∷ [])) = just (M.dup n)
  decode (raw "swap" (number n ∷ [])) = just (M.swap n)
  decode (raw "lt" []) = just M.lt
  decode (raw "eq" []) = just M.eq
  decode (raw "type" []) = just M.type
  decode (raw "size" []) = just M.size
  decode (raw "new" []) = just M.new
  decode (raw "and" []) = just M.and
  decode (raw "or" []) = just M.or
  decode (raw "neg" []) = just M.neg
  decode (raw "pop" []) = just M.pop
  decode (raw "add" []) = just M.add
  decode (raw "sub" []) = just M.sub
  decode (raw "member" []) = just M.member
  decode (raw "ckpt" []) = just M.ckpt
  decode (raw "popeq" (flag cached ∷ result r ∷ [])) = just (M.popeq cached r)
  decode (raw "addi" (number n ∷ [])) = just (M.addi n)
  decode (raw "subi" (number n ∷ [])) = just (M.subi n)
  decode (raw "push" (flag storage ∷ state v ∷ [])) = just (M.push storage v)
  decode (raw "branch" (number n ∷ [])) = just (M.branch n)
  decode (raw "jmp" (number n ∷ [])) = just (M.jmp n)
  decode (raw "concat" (flag cached ∷ number n ∷ [])) = just (M.concat cached n)
  decode (raw "ins" (flag cached ∷ number n ∷ [])) = just (M.ins cached n)
  decode (raw "rem" (flag cached ∷ [])) = just (M.rem cached)
  decode (raw "idx" (flag cached ∷ flag pushPath ∷ path keys ∷ [])) = just (M.idx cached pushPath keys)
  decode (raw "!unsupported" []) = just M.unsupported
  decode _ = nothing

  decodeAll : List Raw → Maybe (List M.Instruction)
  decodeAll [] = just []
  decodeAll (r ∷ rs) with decode r | decodeAll rs
  ... | just op | just ops = just (op ∷ ops)
  ... | _ | _ = nothing

  admit : ℕ → List Raw → M.State → Maybe M.State
  admit fuel encoded s with decodeAll encoded
  ... | nothing = nothing
  ... | just program = M.run fuel program s

  record DecodedRun (encoded : List Raw) (fuel : ℕ) (s t : M.State) : Set where
    constructor decodedRun
    field program : List M.Instruction
          decoded : decodeAll encoded ≡ just program
          execution : M.ProgramRun program fuel s t


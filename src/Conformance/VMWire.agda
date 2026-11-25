{-# OPTIONS --safe --without-K #-}

module Conformance.VMWire where

open import Data.Bool.Base
open import Data.List.Base using (List; []; _∷_; length; map)
open import Data.Maybe.Base using (Maybe; nothing; just; _>>=_)
open import Data.Nat.Base
open import Data.Nat.Show using (show)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String; words; _++_)
open import Relation.Nullary using (does)

import Conformance.FullAccountTypes as F
import Conformance.FullAccountWire as W
import Conformance.VMConcrete as C
import Conformance.VMEncoding as Codec

module VM = C.VM
module E = Codec.Encoding C.atoms

numbers : List F.Value → Maybe (List ℕ)
numbers [] = just []
numbers (F.nat n ∷ xs) = numbers xs >>= λ ns → just (n ∷ ns)
numbers _ = nothing

fits : List ℕ → List ℕ → Bool
fits [] [] = true
fits (n ∷ ns) (0 ∷ als) = (n <ᵇ F.fieldOrder) ∧ fits ns als
fits (n ∷ ns) (suc (suc width) ∷ als) = (width <ᵇ 524288) ∧ (n <ᵇ 256 ^ width) ∧ fits ns als
fits _ _ = false

aligned : F.Value → Maybe C.Aligned
aligned (F.tuple (F.tuple ns ∷ F.tuple als ∷ [])) = do
  words ← numbers ns
  alignments ← numbers als
  if fits words alignments then just (words , alignments) else nothing
aligned _ = nothing

mutual
  stateValue : ℕ → F.Value → Maybe VM.Value
  stateValue zero v = nothing
  stateValue (suc fuel) (F.tuple (F.nat 0 ∷ [])) = just VM.null
  stateValue (suc fuel) (F.tuple (F.nat 1 ∷ a ∷ [])) = do
    v ← aligned a
    if C.byteSize v ≤ᵇ 32768 then just (VM.cell v) else nothing
  stateValue (suc fuel) (F.tuple (F.nat 2 ∷ F.tuple xs ∷ [])) = do
    vs ← stateValues fuel xs
    if length vs <ᵇ 17 then just (VM.array vs) else nothing
  stateValue (suc fuel) (F.tuple (F.nat 3 ∷ F.tuple xs ∷ [])) = entries fuel xs >>= λ es → just (VM.table es)
  stateValue (suc fuel) _ = nothing

  stateValues : ℕ → List F.Value → Maybe (List VM.Value)
  stateValues fuel [] = just []
  stateValues zero (_ ∷ _) = nothing
  stateValues (suc fuel) (x ∷ xs) = do
    v ← stateValue fuel x
    vs ← stateValues fuel xs
    just (v ∷ vs)

  entries : ℕ → List F.Value → Maybe (List (C.Aligned × VM.Value))
  entries fuel [] = just []
  entries zero (_ ∷ _) = nothing
  entries (suc fuel) (F.tuple (k ∷ v ∷ []) ∷ xs) = do
    key ← aligned k
    value ← stateValue fuel v
    rest ← entries fuel xs
    if VM.contains key rest then nothing else just ((key , value) ∷ rest)
  entries (suc fuel) _ = nothing

keys : List F.Value → Maybe (List VM.Key)
keys [] = just []
keys (F.none ∷ xs) = keys xs >>= λ ks → just (VM.stack ∷ ks)
keys (x ∷ xs) = do
  a ← aligned x
  ks ← keys xs
  just (VM.literal a ∷ ks)

instruction : ℕ → F.Value → Maybe VM.Instruction
instruction fuel (F.tuple (F.nat 0 ∷ F.nat n ∷ [])) = E.decode (E.raw "noop" (E.number n ∷ []))
instruction fuel (F.tuple (F.nat 1 ∷ F.nat n ∷ [])) = if n <ᵇ 256 then E.decode (E.raw "dup" (E.number n ∷ [])) else nothing
instruction fuel (F.tuple (F.nat 2 ∷ F.nat n ∷ [])) = if n <ᵇ 256 then E.decode (E.raw "swap" (E.number n ∷ [])) else nothing
instruction fuel (F.tuple (F.nat 3 ∷ [])) = E.decode (E.raw "lt" [])
instruction fuel (F.tuple (F.nat 4 ∷ [])) = E.decode (E.raw "eq" [])
instruction fuel (F.tuple (F.nat 5 ∷ [])) = E.decode (E.raw "type" [])
instruction fuel (F.tuple (F.nat 6 ∷ [])) = E.decode (E.raw "size" [])
instruction fuel (F.tuple (F.nat 7 ∷ [])) = E.decode (E.raw "new" [])
instruction fuel (F.tuple (F.nat 8 ∷ [])) = E.decode (E.raw "and" [])
instruction fuel (F.tuple (F.nat 9 ∷ [])) = E.decode (E.raw "or" [])
instruction fuel (F.tuple (F.nat 10 ∷ [])) = E.decode (E.raw "neg" [])
instruction fuel (F.tuple (F.nat 11 ∷ [])) = E.decode (E.raw "pop" [])
instruction fuel (F.tuple (F.nat 12 ∷ [])) = E.decode (E.raw "add" [])
instruction fuel (F.tuple (F.nat 13 ∷ [])) = E.decode (E.raw "sub" [])
instruction fuel (F.tuple (F.nat 14 ∷ [])) = E.decode (E.raw "member" [])
instruction fuel (F.tuple (F.nat 15 ∷ [])) = E.decode (E.raw "ckpt" [])
instruction fuel (F.tuple (F.nat 16 ∷ F.bool cached ∷ a ∷ [])) = do
  r ← aligned a
  E.decode (E.raw "popeq" (E.flag cached ∷ E.result r ∷ []))
instruction fuel (F.tuple (F.nat 17 ∷ F.nat n ∷ [])) = E.decode (E.raw "addi" (E.number n ∷ []))
instruction fuel (F.tuple (F.nat 18 ∷ F.nat n ∷ [])) = E.decode (E.raw "subi" (E.number n ∷ []))
instruction fuel (F.tuple (F.nat 19 ∷ F.bool storage ∷ v ∷ [])) = do
  value ← stateValue fuel v
  E.decode (E.raw "push" (E.flag storage ∷ E.state value ∷ []))
instruction fuel (F.tuple (F.nat 20 ∷ F.nat n ∷ [])) = E.decode (E.raw "branch" (E.number n ∷ []))
instruction fuel (F.tuple (F.nat (suc 20) ∷ F.nat n ∷ [])) = E.decode (E.raw "jmp" (E.number n ∷ []))
instruction fuel (F.tuple (F.nat (suc (suc 20)) ∷ F.bool cached ∷ F.nat n ∷ [])) = E.decode (E.raw "concat" (E.flag cached ∷ E.number n ∷ []))
instruction fuel (F.tuple (F.nat (suc (suc (suc 20))) ∷ F.bool cached ∷ F.nat n ∷ [])) = if (0 <ᵇ n) ∧ (n <ᵇ 256) then E.decode (E.raw "ins" (E.flag cached ∷ E.number n ∷ [])) else nothing
instruction fuel (F.tuple (F.nat (suc (suc (suc (suc 20)))) ∷ F.bool cached ∷ [])) = E.decode (E.raw "rem" (E.flag cached ∷ []))
instruction fuel (F.tuple (F.nat (suc (suc (suc (suc (suc 20))))) ∷ F.bool cached ∷ F.bool pushPath ∷ F.tuple ks ∷ [])) = do
  path ← keys ks
  E.decode (E.raw "idx" (E.flag cached ∷ E.flag pushPath ∷ E.path path ∷ []))
instruction fuel _ = nothing

instructions : ℕ → List F.Value → Maybe (List VM.Instruction)
instructions fuel [] = just []
instructions zero (_ ∷ _) = nothing
instructions (suc fuel) (x ∷ xs) = do
  op ← instruction fuel x
  ops ← instructions fuel xs
  just (op ∷ ops)

stack : ℕ → List F.Value → Maybe VM.Stack
stack fuel [] = just []
stack zero (_ ∷ _) = nothing
stack (suc fuel) (F.tuple (F.bool strong ∷ x ∷ []) ∷ xs) = do
  v ← stateValue fuel x
  rest ← stack fuel xs
  just (VM.item strong v ∷ rest)
stack (suc fuel) _ = nothing

showAligned : C.Aligned → F.Value
showAligned (ns , als) = F.tuple (F.tuple (map F.nat ns) ∷ F.tuple (map F.nat als) ∷ [])

mutual
  showStateValue : VM.Value → F.Value
  showStateValue VM.null = F.tuple (F.nat 0 ∷ [])
  showStateValue (VM.cell a) = F.tuple (F.nat 1 ∷ showAligned a ∷ [])
  showStateValue (VM.array xs) = F.tuple (F.nat 2 ∷ F.tuple (showStateValues xs) ∷ [])
  showStateValue (VM.table xs) = F.tuple (F.nat 3 ∷ F.tuple (showEntries xs) ∷ [])

  showStateValues : List VM.Value → List F.Value
  showStateValues [] = []
  showStateValues (x ∷ xs) = showStateValue x ∷ showStateValues xs

  showEntries : List (C.Aligned × VM.Value) → List F.Value
  showEntries [] = []
  showEntries ((k , v) ∷ xs) = F.tuple (showAligned k ∷ showStateValue v ∷ []) ∷ showEntries xs

showStack : VM.Stack → F.Value
showStack xs = F.tuple (map (λ x → F.tuple (F.bool (VM.strong x) ∷ showStateValue (VM.value x) ∷ [])) xs)

request : List String → Maybe (ℕ × List VM.Instruction × VM.State)
request ("vm-v1" ∷ ts) = do
  let fuel = suc (length ts)
  (steps , ts) ← W.natural ts
  (F.tuple rawStack , ts) ← W.value fuel ts where _ → nothing
  (F.tuple rawProgram , []) ← W.value fuel ts where _ → nothing
  initial ← stack fuel rawStack
  program ← instructions fuel rawProgram
  just (steps , program , VM.machine 0 initial)
request _ = nothing

respond : String → String
respond line with request (words line)
... | nothing = "{\"tag\":\"decoding-error\"}"
... | just (fuel , program , initial) with VM.run fuel program initial
...   | nothing = "{\"tag\":\"refused\"}"
...   | just final = "{\"tag\":\"accepted\",\"pc\":" ++ W.jsonString (show (VM.pc final))
  ++ ",\"stack\":" ++ W.showValue (showStack (VM.stackValues final)) ++ "}"

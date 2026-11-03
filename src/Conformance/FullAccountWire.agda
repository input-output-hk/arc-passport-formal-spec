{-# OPTIONS --safe --without-K #-}

-- Token framing is independent of JSON escaping and preserves arbitrary-width
-- integers. The only interpretation parameter is the explicit primitive RPC.
module Conformance.FullAccountWire where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_)
import Data.Char.Base as Char
open import Data.List.Base using (List; []; _∷_; length; map; intersperse)
open import Data.Maybe.Base using (Maybe; just; nothing; _>>=_)
open import Data.Nat.DivMod using (_/_; _%_)
open import Data.Nat.Base hiding (equal)
open import Data.Nat.Show using (show; readMaybe)
open import Data.Product.Base hiding (map)
open import Data.String.Base using (String; words; toList; fromList; concat; _++_)
open import Conformance.FullAccountTypes hiding (_>>=_; _>>_; return)
import Conformance.FullAccount as Account

Tokens = List String
Parse : Set → Set
Parse A = Tokens → Maybe (A × Tokens)

allDigits : List Char.Char → Bool
allDigits [] = true
allDigits (c ∷ cs) = (48 ≤ᵇ Char.toℕ c) ∧ (Char.toℕ c ≤ᵇ 57) ∧ allDigits cs

natural : Parse ℕ
natural [] = nothing
natural (x ∷ xs) with toList x
... | [] = nothing
... | c ∷ cs = if allDigits (c ∷ cs) then (do
  n ← readMaybe 10 x
  just (n , xs)) else nothing

byteList : ℕ → Parse (List ℕ)
byteList zero ts = just ([] , ts)
byteList (suc n) ts = do
  (x , ts) ← natural ts
  if x <ᵇ 256 then (do
    (xs , ts) ← byteList n ts
    just (x ∷ xs , ts)) else nothing

mutual
  value : ℕ → Parse Value
  value zero ts = nothing
  value (suc fuel) ("n" ∷ ts) = do
    (n , ts) ← natural ts
    just (nat n , ts)
  value (suc fuel) ("b" ∷ "0" ∷ ts) = just (bool false , ts)
  value (suc fuel) ("b" ∷ "1" ∷ ts) = just (bool true , ts)
  value (suc fuel) ("y" ∷ ts) = do
    (n , ts) ← natural ts
    (bs , ts) ← byteList n ts
    just (bytes bs , ts)
  value (suc fuel) ("t" ∷ ts) = do
    (n , ts) ← natural ts
    (vs , ts) ← values fuel n ts
    just (tuple vs , ts)
  value (suc fuel) ("z" ∷ ts) = just (none , ts)
  value (suc fuel) ("s" ∷ ts) = do
    (v , ts) ← value fuel ts
    just (some v , ts)
  value (suc fuel) _ = nothing

  values : ℕ → ℕ → Parse (List Value)
  values fuel zero ts = just ([] , ts)
  values zero (suc n) ts = nothing
  values (suc fuel) (suc n) ts = do
    (v , ts) ← value fuel ts
    (vs , ts) ← values fuel n ts
    just (v ∷ vs , ts)

fieldsP : ℕ → ℕ → Parse (List (String × Value))
fieldsP fuel zero ts = just ([] , ts)
fieldsP fuel (suc n) [] = nothing
fieldsP fuel (suc n) (k ∷ ts) = do
  (v , ts) ← value fuel ts
  (vs , ts) ← fieldsP fuel n ts
  just ((k , v) ∷ vs , ts)

request : Tokens → Maybe (RawCall × Context × State)
request ("full-v1" ∷ name ∷ ts) = do
  let fuel = suc (length ts)
  (tuple args , ts) ← value fuel ts where _ → nothing
  (self , ts) ← value fuel ts
  (time , ts) ← natural ts
  (caller , ts) ← value fuel ts
  (coin , ts) ← value fuel ts
  (n , ts) ← natural ts
  (cells , []) ← fieldsP fuel n ts where _ → nothing
  just (rawCall name args , context self time caller coin , state cells)
request _ = nothing

hexDigit : ℕ → String
hexDigit n = fromList (Char.fromℕ (if n <ᵇ 10 then 48 + n else 87 + n) ∷ [])

escape : Char.Char → String
escape '"' = "\\\""
escape '\\' = "\\\\"
escape c = if Char.toℕ c <ᵇ 32
  then "\\u00" ++ hexDigit (Char.toℕ c / 16) ++ hexDigit (Char.toℕ c % 16)
  else fromList (c ∷ [])

jsonString : String → String
jsonString s = "\"" ++ concat (map escape (toList s)) ++ "\""

array : List String → String
array xs = "[" ++ concat (intersperse "," xs) ++ "]"

mutual
  showValue : Value → String
  showValue (nat n) = "{\"tag\":\"nat\",\"value\":" ++ jsonString (show n) ++ "}"
  showValue (bool b) = "{\"tag\":\"bool\",\"value\":" ++ (if b then "true" else "false") ++ "}"
  showValue (bytes bs) = "{\"tag\":\"bytes\",\"value\":" ++ array (map show bs) ++ "}"
  showValue (tuple vs) = "{\"tag\":\"tuple\",\"value\":" ++ showValues vs ++ "}"
  showValue none = "{\"tag\":\"none\"}"
  showValue (some v) = "{\"tag\":\"some\",\"value\":" ++ showValue v ++ "}"

  showValues : List Value → String
  showValues vs = array (valueStrings vs)

  valueStrings : List Value → List String
  valueStrings [] = []
  valueStrings (v ∷ vs) = showValue v ∷ valueStrings vs

showState : State → String
showState s = "{\"ledger\":" ++ array (map (λ (k , v) → array (jsonString k ∷ showValue v ∷ [])) (ledger s)) ++ "}"

showError : Error → String
showError (assertion message) = "{\"kind\":\"assertion\",\"message\":" ++ jsonString message ++ "}"
showError (bounds label bits) = "{\"kind\":\"bounds\",\"message\":" ++ jsonString label ++ ",\"bits\":" ++ jsonString (show bits) ++ "}"
showError (decoding message) = "{\"kind\":\"decoding\",\"message\":" ++ jsonString message ++ "}"
showError (primitiveFailure message) = "{\"kind\":\"primitive\",\"message\":" ++ jsonString message ++ "}"

effect : String → List Value → String
effect tag args = "{\"tag\":" ++ jsonString tag ++ ",\"arguments\":" ++ showValues args ++ "}"

showEffect : Effect → String
showEffect (readCell k v) = effect "readCell" (bytes (ascii k) ∷ v ∷ [])
showEffect (writeCell k v) = effect "writeCell" (bytes (ascii k) ∷ v ∷ [])
showEffect (mapMember k x b) = effect "mapMember" (bytes (ascii k) ∷ x ∷ bool b ∷ [])
showEffect (mapLookup k x v) = effect "mapLookup" (bytes (ascii k) ∷ x ∷ v ∷ [])
showEffect (mapInsert k x v) = effect "mapInsert" (bytes (ascii k) ∷ x ∷ v ∷ [])
showEffect (setMember k x b) = effect "setMember" (bytes (ascii k) ∷ x ∷ bool b ∷ [])
showEffect (setInsert k x) = effect "setInsert" (bytes (ascii k) ∷ x ∷ [])
showEffect (setRemove k x) = effect "setRemove" (bytes (ascii k) ∷ x ∷ [])
showEffect (reset k) = effect "reset" (bytes (ascii k) ∷ [])
showEffect (contextRead k v) = effect "contextRead" (bytes (ascii k) ∷ v ∷ [])
showEffect (witness k x v) = effect "witness" (bytes (ascii k) ∷ x ∷ v ∷ [])
showEffect (receiveUnshielded c a) = effect "receiveUnshielded" (c ∷ nat a ∷ [])
showEffect (sendUnshielded c a r) = effect "sendUnshielded" (c ∷ nat a ∷ r ∷ [])
showEffect (receiveShielded c) = effect "receiveShielded" (c ∷ [])
showEffect (consumeShielded c r) = effect "consumeShielded" (c ∷ r ∷ [])
showEffect (createShielded c r commitment) = effect "createShielded" (c ∷ r ∷ commitment ∷ [])

showOutcome : Execution Value → String
showOutcome (rejected e) = "{\"tag\":\"rejected\",\"error\":" ++ showError e ++ "}"
showOutcome (accepted v s es) = "{\"tag\":\"accepted\",\"output\":" ++ showValue v
  ++ ",\"state\":" ++ showState s ++ ",\"effects\":" ++ array (map showEffect es) ++ "}"

curveName : Curve → String
curveName jubjub = "jubjub"
curveName k256 = "k256"
curveName p256 = "p256"

module Backend (backend : String → String) where
  oracle : String → List Value → Result Value
  oracle name args with words (backend ("{\"oracle\":{\"name\":" ++ jsonString name ++ ",\"arguments\":" ++ showValues args ++ "}}"))
  ... | ts with value (suc (length ts)) ts
  ... | just (v , []) = success v
  ... | _ = failure (primitiveFailure name)

  naturalResult : String → Result Value → Result ℕ
  naturalResult name (success (nat n)) = success n
  naturalResult name (failure e) = failure e
  naturalResult name _ = failure (primitiveFailure name)

  boolResult : String → Result Value → Result Bool
  boolResult name (success (bool b)) = success b
  boolResult name (failure e) = failure e
  boolResult name _ = failure (primitiveFailure name)

  pairResult : String → Result Value → Result (Value × Value)
  pairResult name (success (tuple (x ∷ y ∷ []))) = success (x , y)
  pairResult name (failure e) = failure e
  pairResult name _ = failure (primitiveFailure name)

  primitives : Primitives
  primitives = record
    { persistentHash = λ atoms → oracle "persistentHash" (map (λ (t , v) → tuple (bytes (ascii t) ∷ v ∷ [])) atoms)
    ; transientHash = λ ns → naturalResult "transientHash" (oracle "transientHash" (map nat ns))
    ; degradeToTransient = λ v → naturalResult "degradeToTransient" (oracle "degradeToTransient" (v ∷ []))
    ; upgradeFromTransient = λ n → oracle "upgradeFromTransient" (nat n ∷ [])
    ; pointCoordinates = λ c v → pairResult "coordinates" (oracle (curveName c ++ "-coordinates") (v ∷ []))
    ; ecMulGenerator = λ c n → oracle (curveName c ++ "-mulg") (nat n ∷ [])
    ; ecMul = λ c p n → oracle (curveName c ++ "-mul") (p ∷ nat n ∷ [])
    ; ecAdd = λ c p q → oracle (curveName c ++ "-add") (p ∷ q ∷ [])
    ; ecdsaVerify = λ c d s p → boolResult "ecdsa" (oracle (curveName c ++ "-ecdsa") (d ∷ s ∷ p ∷ []))
    ; coinCommitment = λ c r → oracle "coinCommitment" (c ∷ r ∷ [])
    ; coinNullifier = λ c r → oracle "coinNullifier" (c ∷ r ∷ [])
    }

  respond : String → String
  respond line with request (words line)
  ... | nothing = showOutcome (rejected (decoding "invalid full-v1 request"))
  ... | just (call , ctx , initial) = showOutcome (Account.dispatch primitives ctx call initial)

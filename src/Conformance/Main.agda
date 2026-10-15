{-# OPTIONS --guardedness #-}

-- Executable model for conformance/harness (MAlonzo; see docs/conformance-spike.md for
-- why not the JS backend). Line protocol on stdin/stdout, one request per line:
--
--   step   VARIANT SELF TIME <state> <request> B <bits>      → = <settlement> sig <σ|-> state <state> rest <n>
--   decide VARIANT SELF TIME <state> <call> <state> <verdict> → = true | = false
--
-- VARIANT is `source` or `corrected` (the finalisation), TIME the block time. Crypto
-- primitives are answered by the harness on the same channel (`? …` lines), i.e. by the
-- implementation's own pure circuits / compact-runtime: a shared oracle. Token grammar
-- and encoder: conformance/harness/model.ts.
module Conformance.Main where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
import Data.Char.Base as Char
open import Data.List.Base using (List; []; _∷_; length; concatMap) renaming (_++_ to _++ˡ_)
open import Data.Maybe.Base using (Maybe; nothing; just; _>>=_; fromMaybe)
import Data.Maybe.Base as Maybe
open import Data.Nat.Base
open import Data.Nat.Properties using (_≟_)
open import Data.Nat.Show using (show; readMaybe)
open import Data.Product.Base
import Data.Product.Properties as ΣP
open import Data.String.Base using (String; _++_; words; unwords; toList)
import Data.String.Properties as String
open import Data.Unit.Base using (tt)
open import Function.Base using (_∘_)
import IO

open import Conformance.Primitives

------------------------------------------------------------------------
-- Primitive round trips

-- Total stand-in for type checking; the compiled form asks the harness. The stand-in must
-- use its argument, be no identity and stay out of line, or MAlonzo erases, drops or
-- inlines it past the binding.
rpc : String → String
rpc q = q ++ ""
{-# NOINLINE rpc #-}

{-# FOREIGN GHC
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Control.Exception (evaluate)
import System.IO (stdout, hFlush)
import System.IO.Unsafe (unsafePerformIO)

conformanceRpc :: T.Text -> T.Text
conformanceRpc q = unsafePerformIO $ do
  _ <- evaluate (T.length q)
  TIO.putStrLn (T.append (T.pack "? ") q)
  hFlush stdout
  TIO.getLine
{-# NOINLINE conformanceRpc #-}
#-}
{-# COMPILE GHC rpc = conformanceRpc #-}

nat : String → ℕ
nat = fromMaybe 0 ∘ readMaybe 10

point : String → ℕ × ℕ
point s with words s
... | x ∷ y ∷ _ = nat x , nat y
... | _ = 0 , 0

ask : List String → String
ask = rpc ∘ unwords

hexDigit : Char.Char → ℕ
hexDigit c = let n = Char.toℕ c in if n <ᵇ 58 then n ∸ 48 else n ∸ 87

leBytes : List Char.Char → ℕ
leBytes (h ∷ l ∷ rest) = 16 * hexDigit h + hexDigit l + 256 * leBytes rest
leBytes _ = 0

pt : ℕ × ℕ → List String
pt (x , y) = show x ∷ show y ∷ []

-- Byte strings travel as lowercase hex, points as decimal affine coordinates.
primitives : Primitives
primitives = record
  { Bytes32 = String ; Bytes64 = String ; Point = ℕ × ℕ
  ; _≟ᴮ_ = String._≟_ ; _≟ᵂ_ = String._≟_ ; _≟ᴾ_ = ΣP.≡-dec _≟_ _≟_
  ; zero32 = "0000000000000000000000000000000000000000000000000000000000000000"
  ; deviceEntry = λ self pk e c → ask ("entry" ∷ self ∷ pt pk ++ˡ show e ∷ show c ∷ [])
  ; challengeWithdraw = λ self R pk color a rcpt n g →
      ask ("chal-w" ∷ self ∷ pt R ++ˡ pt pk ++ˡ color ∷ show a ∷ rcpt ∷ show n ∷ show g ∷ [])
  ; challengeAddDevice = gated "chal-add"
  ; challengeRemoveDevice = gated "chal-rm"
  ; challengeRotateEncKey = gated "chal-rot"
  ; challengePublish = λ self R pk q sess φ₁ φ₂ φ₃ φ₄ len w n g →
      ask ("chal-pub" ∷ self ∷ pt R ++ˡ pt pk ++ˡ pt q ++ˡ sess ∷ show φ₁ ∷ show φ₂ ∷ show φ₃ ∷ show φ₄ ∷ show len ∷ w ∷ show n ∷ show g ∷ [])
  ; challengeCancel = λ self R pk n g → ask ("chal-cancel" ∷ self ∷ pt R ++ˡ pt pk ++ˡ show n ∷ show g ∷ [])
  ; challengeSubmit = λ self rpk Rᵣ q Rₛ q′ e n u g →
      ask ("chal-submit" ∷ self ∷ pt rpk ++ˡ pt Rᵣ ++ˡ pt q ++ˡ pt Rₛ ++ˡ pt q′ ++ˡ show e ∷ show n ∷ show u ∷ show g ∷ [])
  ; ecMulG = λ k → point (ask ("mulg" ∷ show k ∷ []))
  ; ecMul = λ p k → point (ask ("mul" ∷ pt p ++ˡ show k ∷ []))
  ; ecAdd = λ p q → point (ask ("add" ∷ pt p ++ˡ pt q))
  ; le = leBytes ∘ toList }
  where
  gated : String → String → ℕ × ℕ → ℕ × ℕ → String → ℕ → ℕ → String
  gated op self R pk x n g = ask (op ∷ self ∷ pt R ++ˡ pt pk ++ˡ x ∷ show n ∷ show g ∷ [])

open import Conformance.AccountLedger primitives

------------------------------------------------------------------------
-- Wire format

Tokens = List String
Parse : Set → Set
Parse A = Tokens → Maybe (A × Tokens)

tok : Parse String
tok [] = nothing
tok (t ∷ ts) = just (t , ts)

num : Parse ℕ
num ts = tok ts >>= λ (t , ts′) → Maybe.map (_, ts′) (readMaybe 10 t)

pointP : Parse (ℕ × ℕ)
pointP ts = do
  (x , ts) ← num ts
  (y , ts) ← num ts
  just ((x , y) , ts)

many : {A : Set} → ℕ → Parse A → Parse (List A)
many zero p ts = just ([] , ts)
many (suc n) p ts = do
  (x , ts) ← p ts
  (xs , ts) ← many n p ts
  just (x ∷ xs , ts)

phiP : Parse Phi
phiP ts = do
  (a , ts) ← num ts
  (b , ts) ← num ts
  (c , ts) ← num ts
  (d , ts) ← num ts
  just ((a , b , c , d) , ts)

stateP : Parse State
stateP ts = do
  (r , ts) ← num ts
  (n , ts) ← num ts
  (e , ts) ← num ts
  (c , ts) ← num ts
  (nd , ts) ← num ts
  (ds , ts) ← many nd tok ts
  (nb , ts) ← num ts
  (bs , ts) ← many nb entryP ts
  (k , ts) ← tok ts
  (rpk , ts) ← pointP ts
  (φ , ts) ← optional ts
  (len , ts) ← num ts
  (sess , ts) ← tok ts
  (w , ts) ← tok ts
  (pend , ts) ← num ts
  (pe , ts) ← tok ts
  (ppk , ts) ← pointP ts
  (t , ts) ← num ts
  (v , ts) ← num ts
  just (state r n e c ds bs k rpk φ len sess w (pend ≡ᵇ 1) pe ppk t v , ts)
  where
  entryP : Parse (String × ℕ)
  entryP ts = do
    (k , ts) ← tok ts
    (v , ts) ← num ts
    just ((k , v) , ts)
  optional : Parse (Maybe Phi)
  optional ("0" ∷ ts) = just (nothing , ts)
  optional ("4" ∷ ts) = Maybe.map (λ (φ , ts) → just φ , ts) (phiP ts)
  optional _ = nothing

showPoint : ℕ × ℕ → String
showPoint = unwords ∘ pt

showState : State → String
showState (state r n e c ds bs k rpk φ len sess w pend pe ppk t v) = unwords
  ( show r ∷ show n ∷ show e ∷ show c ∷ show (length ds) ∷ unwords ds ∷ show (length bs)
  ∷ unwords (concatMap (λ (k , v) → k ∷ show v ∷ []) bs) ∷ k ∷ showPoint rpk ∷ showPhi φ ∷ show len ∷ sess ∷ w
  ∷ (if pend then "1" else "0") ∷ pe ∷ showPoint ppk ∷ show t ∷ show v ∷ [])
  where
  showPhi : Maybe Phi → String
  showPhi nothing = "0"
  showPhi (just (a , b , c , d)) = unwords ("4" ∷ show a ∷ show b ∷ show c ∷ show d ∷ [])

bitsP : Parse (List Bool)
bitsP ("B" ∷ "-" ∷ ts) = just ([] , ts)
bitsP ("B" ∷ b ∷ ts) = just (decode (toList b) , ts)
  where decode : List Char.Char → List Bool
        decode [] = []
        decode (c ∷ cs) = (Char.toℕ c ≡ᵇ 49) ∷ decode cs
bitsP _ = nothing

module Line (self : String) (variant : Finalisation) where
  open import Conformance.Account primitives self variant
  open import Conformance.Custody primitives self
  open import Conformance.Recovery primitives self
  open import Passport.AccountRecovery primitives self

  gatedP : Parse (Σ Gated Payload)
  gatedP ("W" ∷ ts) = do
    (c , ts) ← tok ts
    (a , ts) ← num ts
    (r , ts) ← tok ts
    just ((withdrawUnshielded , c , a , r) , ts)
  gatedP ("A" ∷ e ∷ ts) = just ((addDevice , e) , ts)
  gatedP ("R" ∷ e ∷ ts) = just ((removeDevice , e) , ts)
  gatedP ("K" ∷ k ∷ ts) = just ((rotateEncKey , k) , ts)
  gatedP ("P" ∷ ts) = do
    (q , ts) ← pointP ts
    (sess , ts) ← tok ts
    (φ , ts) ← phiP ts
    (len , ts) ← num ts
    (w , ts) ← tok ts
    just ((publishRecoverySession , publishArgs q sess φ len w) , ts)
  gatedP ("C" ∷ ts) = just ((recoverCancel , tt) , ts)
  gatedP _ = nothing

  callP : Parse (Σ Name Input)
  callP ("D" ∷ ts) = do
    (c , ts) ← tok ts
    (a , ts) ← num ts
    just ((depositUnshielded , c , a) , ts)
  callP ("F" ∷ ts) = just ((recoverFinalise , tt) , ts)
  callP ("U" ∷ ts) = do
    (q , ts) ← pointP ts
    (q′ , ts) ← pointP ts
    (e , ts) ← num ts
    (n , ts) ← num ts
    (u , ts) ← num ts
    (Rᵣ , ts) ← pointP ts
    (sᵣ , ts) ← num ts
    (Rₛ , ts) ← pointP ts
    (sₛ , ts) ← num ts
    (g , ts) ← num ts
    just ((recoverSubmit , submitArgs q q′ e n u Rᵣ sᵣ Rₛ sₛ g) , ts)
  callP ("J" ∷ ts) = do
    ((g , p) , ts) ← gatedP ts
    (pk , ts) ← pointP ts
    (uc , ts) ← num ts
    (R , ts) ← pointP ts
    (s , ts) ← num ts
    (gr , ts) ← num ts
    just ((jubjub g , p , authorisation pk uc R s gr) , ts)
  callP _ = nothing

  requestP : Parse Request
  requestP ("S" ∷ ts) = do
    ((g , p) , ts) ← gatedP ts
    (pk , ts) ← pointP ts
    (uc , ts) ← num ts
    (sk , ts) ← num ts
    (n , ts) ← num ts
    just (signed g p pk uc sk n , ts)
  requestP ("U" ∷ ts) = do
    (skᵣ , ts) ← num ts
    (skₛ , ts) ← num ts
    (q′ , ts) ← pointP ts
    (rpk , ts) ← pointP ts
    (e , ts) ← num ts
    (n , ts) ← num ts
    (u , ts) ← num ts
    just (recover skᵣ skₛ q′ rpk e n u , ts)
  requestP ("X" ∷ ts) = Maybe.map (λ ((n , a) , ts) → raw n a , ts) (callP ts)
  requestP _ = nothing

  observedP : Parse Observed
  observedP ("ok" ∷ ts) = just (succeeded , ts)
  observedP ("fail" ∷ code ∷ ts) = just (failed code , ts)
  observedP _ = nothing

  showSettlement : Settlement → String
  showSettlement committed = "ok"
  showSettlement refused = "refused"
  showSettlement (aborted e) = "fail " ++ errorCode e

  showSigned : Maybe Signature → String
  showSigned nothing = "-"
  showSigned (just (signature rs g)) = unwords (concatMap (λ (R , s) → pt R ++ˡ show s ∷ []) rs) ++ " " ++ show g

  stepInput : Tokens → Maybe (ℕ × State × Request × List Bool)
  stepInput ts = do
    (t , ts) ← num ts
    (s , ts) ← stateP ts
    (q , ts) ← requestP ts
    (bs , _) ← bitsP ts
    just (t , s , q , bs)

  stepLine : Tokens → String
  stepLine ts with stepInput ts
  ... | nothing = "= error malformed step"
  ... | just (t , s , q , bs) with stepModel t s q bs
  ...   | nothing = "= stuck"
  ...   | just ((u , stepReport σ out) , rest) =
    "= " ++ showSettlement out ++ " sig " ++ showSigned σ ++ " state " ++ showState u ++ " rest " ++ show (length rest)

  decideInput : Tokens → Maybe (ℕ × State × Σ Name Input × State × Observed)
  decideInput ts = do
    (t , ts) ← num ts
    (s , ts) ← stateP ts
    (call , ts) ← callP ts
    (s′ , ts) ← stateP ts
    (v , _) ← observedP ts
    just (t , s , call , s′ , v)

  decideLine : Tokens → String
  decideLine ts with decideInput ts
  ... | nothing = "= error malformed decide"
  ... | just (t , s , (n , a) , s′ , v) = if decide t s n a s′ v then "= true" else "= false"

variantP : String → Maybe Finalisation
variantP "source" = just sourceShaped
variantP "corrected" = just corrected
variantP _ = nothing

respond : String → String
respond line with words line
... | "step" ∷ v ∷ self ∷ ts = Maybe.maybe (λ f → Line.stepLine self f ts) "= error unknown variant" (variantP v)
... | "decide" ∷ v ∷ self ∷ ts = Maybe.maybe (λ f → Line.decideLine self f ts) "= error unknown variant" (variantP v)
... | _ = "= error unknown request"

main : IO.Main
main = run (hSetBuffering stdout lineBuffering >> forever (getLine >>=ᴵ (putStrLn ∘ respond)))
  where open IO renaming (_>>=_ to _>>=ᴵ_)

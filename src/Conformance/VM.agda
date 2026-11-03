{-# OPTIONS --safe --without-K #-}

-- A value/stack semantics for the account's map/array instruction surface.
-- Cache charging, gas, the WASM interpreter and the compiler are not verified by
-- this module. Their interpretation is a separate trust boundary. In particular
-- a successful journal here is not authentication of external asset effects.
-- replay/run instantiate Midnight.ContractDSL.Ledger.Semantics and use its
-- Execution.apply; the generic ledger replay boundary is not duplicated here.
module Conformance.VM where

open import Class.DecEq using (DecEq)
open import Data.Bool.Base
open import Data.List.Base using (List; []; _∷_; _++_; length; map; replicate; drop)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no; does)

open import Midnight.ContractDSL.Ledger

record Atoms : Set₁ where
  field Aligned : Set
        _≟ᴬ_ : DecidableEquality Aligned
        natural : Aligned → Maybe ℕ
        boolean : Aligned → Maybe Bool
        truth : Aligned → Bool
        fromNat : ℕ → Aligned
        fromByte : ℕ → Aligned
        fromBool : Bool → Aligned
        empty : Aligned
        -- Byte-size and concatenation include alignment, not just raw payload.
        byteSize : Aligned → ℕ
        cellBound : ℕ
        concatenate : Aligned → Aligned → Maybe Aligned
        natural-roundtrip : ∀ n → natural (fromNat n) ≡ just n
        boolean-roundtrip : ∀ b → boolean (fromBool b) ≡ just b

module Machine (A : Atoms) where
  open Atoms A

  data Value : Set where
    null : Value
    cell : Aligned → Value
    array : List Value → Value
    table : List (Aligned × Value) → Value

  data Key : Set where
    literal : Aligned → Key
    stack : Key

  data Instruction : Set where
    noop dup swap : ℕ → Instruction
    lt eq type size new and or neg pop add sub member ckpt : Instruction
    popeq : Bool → Aligned → Instruction
    addi subi : ℕ → Instruction
    push : Bool → Value → Instruction
    branch jmp : ℕ → Instruction
    concat ins : Bool → ℕ → Instruction
    rem : Bool → Instruction
    idx : Bool → Bool → List Key → Instruction
    -- Bounded-Merkle-tree roots/logs are not emitted by this account's ledger
    -- interface. They have no permissive default interpretation.
    unsupported : Instruction

  record Item : Set where
    constructor item
    field strong : Bool
          value : Value
  open Item public

  Stack : Set
  Stack = List Item

  data Error : Set where
    underflow invalidType invalidArguments absent bounds unequal unsupportedOpcode : Error

  Result : Set → Set
  Result X = Error ⊎ X

  _>>=_ : ∀ {X Y : Set} → Result X → (X → Result Y) → Result Y
  inj₁ e >>= f = inj₁ e
  inj₂ x >>= f = f x

  atom : Item → Result Aligned
  atom (item _ (cell a)) = inj₂ a
  atom _ = inj₁ invalidType

  -- VM numeric operands are unsigned 64-bit values; arithmetic below checks
  -- this same exclusive 2^64 upper bound rather than wrapping on overflow.
  nat : Aligned → Result ℕ
  nat a with natural a
  ... | nothing = inj₁ invalidType
  ... | just n = if n <ᵇ 2 ^ 64 then inj₂ n else inj₁ bounds

  flag : Aligned → Result Bool
  flag a with boolean a
  ... | nothing = inj₁ invalidType
  ... | just b = inj₂ b

  at : ∀ {X : Set} → ℕ → List X → Result X
  at zero (x ∷ xs) = inj₂ x
  at (suc n) (x ∷ xs) = at n xs
  at _ [] = inj₁ bounds

  replace : ∀ {X : Set} → ℕ → X → List X → Result (List X)
  replace zero y (x ∷ xs) = inj₂ (y ∷ xs)
  replace (suc n) y (x ∷ xs) = replace n y xs >>= λ ys → inj₂ (x ∷ ys)
  replace _ _ [] = inj₁ bounds

  lookup : Aligned → List (Aligned × Value) → Value
  lookup k [] = null
  lookup k ((j , x) ∷ xs) = if does (k ≟ᴬ j) then x else lookup k xs

  contains : Aligned → List (Aligned × Value) → Bool
  contains k [] = false
  contains k ((j , x) ∷ xs) = does (k ≟ᴬ j) ∨ contains k xs

  insert : Aligned → Value → List (Aligned × Value) → List (Aligned × Value)
  insert k x [] = (k , x) ∷ []
  insert k x ((j , y) ∷ xs) = if does (k ≟ᴬ j) then (k , x) ∷ xs else (j , y) ∷ insert k x xs

  remove : Aligned → List (Aligned × Value) → List (Aligned × Value)
  remove k [] = []
  remove k ((j , x) ∷ xs) = if does (k ≟ᴬ j) then remove k xs else (j , x) ∷ remove k xs

  -- Array keys must fit the VM's unsigned-byte index domain (<256), then also
  -- pass the actual array length check in at/replace.
  get : Value → Aligned → Result Value
  get (array xs) k = nat k >>= λ n → if n <ᵇ 256 then at n xs else inj₁ bounds
  get (table xs) k = inj₂ (lookup k xs)
  get _ _ = inj₁ invalidType

  put : Value → Aligned → Value → Result Value
  put (array xs) k x = nat k >>= λ n →
    if n <ᵇ 256 then (replace n x xs >>= λ ys → inj₂ (array ys)) else inj₁ bounds
  put (table xs) k x = inj₂ (table (insert k x xs))
  put _ _ _ = inj₁ invalidType

  resolve : List Key → Stack → Result (List Item × Stack)
  resolve [] s = inj₂ ([] , s)
  resolve (literal a ∷ ks) s = resolve ks s >>= λ (keys , rest) → inj₂ (item false (cell a) ∷ keys , rest)
  resolve (stack ∷ ks) [] = inj₁ underflow
  resolve (stack ∷ ks) (x ∷ s) = resolve ks s >>= λ (keys , rest) → inj₂ (x ∷ keys , rest)

  index : Bool → List Item → Item → Stack → Result Stack
  index path [] current rest = inj₂ (current ∷ rest)
  index path (key ∷ keys) current rest = atom key >>= λ k → get (value current) k >>= λ v →
    index path keys (item (strong current) v)
      (if path then key ∷ current ∷ rest else rest)

  install : ℕ → Item → Stack → Result Stack
  install zero current rest = inj₂ (current ∷ rest)
  install (suc n) current (key ∷ container ∷ rest) = atom key >>= λ k →
    put (value container) k (value current) >>= λ v →
    install n (item (strong current ∧ strong container) v) rest
  install (suc n) current _ = inj₁ underflow

  natItem : ℕ → Item
  natItem n = item true (cell (fromNat n))

  byteItem : ℕ → Item
  byteItem n = item true (cell (fromByte n))

  boolItem : Bool → Item
  boolItem b = item true (cell (fromBool b))

  unaryNat : (ℕ → Result ℕ) → Stack → Result Stack
  unaryNat f (x ∷ xs) = atom x >>= λ a → nat a >>= λ n → f n >>= λ m → inj₂ (natItem m ∷ xs)
  unaryNat f [] = inj₁ underflow

  binaryNat : (ℕ → ℕ → Result Item) → Stack → Result Stack
  binaryNat f (b ∷ a ∷ xs) = atom a >>= λ aa → nat aa >>= λ an →
    atom b >>= λ ba → nat ba >>= λ bn → f an bn >>= λ c → inj₂ (c ∷ xs)
  binaryNat f _ = inj₁ underflow

  binaryBool : (Bool → Bool → Bool) → Stack → Result Stack
  binaryBool f (b ∷ a ∷ xs) = atom a >>= λ aa → flag aa >>= λ ab →
    atom b >>= λ ba → flag ba >>= λ bb → inj₂ (boolItem (f ab bb) ∷ xs)
  binaryBool f _ = inj₁ underflow

  -- VM type tags: cell=0, null=1, map=2, array(length)=3+8*length.
  -- new invokes this search with fuel=17 to admit lengths 0 through 16 only;
  -- type applies the same maximum length, independently of the byte index bound.
  newArray : ℕ → ℕ → ℕ → Result Value
  newArray zero code len = inj₁ invalidArguments
  newArray (suc fuel) code len =
    if code ≡ᵇ 3 + 8 * len then inj₂ (array (replicate len null))
    else newArray fuel code (suc len)

  execute : Instruction → Stack → Result (ℕ × Stack)
  execute (noop n) s = inj₂ (0 , s)
  execute ckpt s = inj₂ (0 , s)
  execute (push storage v) s = inj₂ (0 , item storage v ∷ s)
  execute pop (_ ∷ s) = inj₂ (0 , s)
  execute (popeq cached expected) (x ∷ s) = atom x >>= λ actual →
    if does (expected ≟ᴬ actual) then inj₂ (0 , s) else inj₁ unequal
  execute (dup n) s = at n s >>= λ x → inj₂ (0 , x ∷ s)
  execute (swap n) (x ∷ s) = do
    y ← at n s
    t ← replace n x s
    inj₂ (0 , y ∷ t)
  execute (idx cached path keys) s = resolve keys s >>= λ
    { (ks , []) → inj₁ underflow
    ; (ks , current ∷ rest) → index path ks current rest >>= λ t → inj₂ (0 , t)
    }
  execute (ins cached n) (x ∷ s) = install n x s >>= λ t → inj₂ (0 , t)
  execute member (key ∷ item strength (table xs) ∷ rest) = do
    k ← atom key
    inj₂ (0 , boolItem (contains k xs) ∷ rest)
  execute (rem cached) (key ∷ item strength (table xs) ∷ rest) = do
    k ← atom key
    inj₂ (0 , item strength (table (remove k xs)) ∷ rest)
  execute size (item _ (table xs) ∷ rest) = inj₂ (0 , natItem (length xs) ∷ rest)
  execute size (item _ (array xs) ∷ rest) = inj₂ (0 , natItem (length xs) ∷ rest)
  execute type (item _ null ∷ rest) = inj₂ (0 , byteItem 1 ∷ rest)
  execute type (item _ (cell a) ∷ rest) = inj₂ (0 , byteItem 0 ∷ rest)
  execute type (item _ (table xs) ∷ rest) = inj₂ (0 , byteItem 2 ∷ rest)
  execute type (item _ (array xs) ∷ rest) =
    if length xs <ᵇ 17 then inj₂ (0 , byteItem (3 + 8 * length xs) ∷ rest) else inj₁ bounds
  execute new (x ∷ rest) = do
    a ← atom x
    n ← nat a
    if n ≡ᵇ 0 then inj₂ (0 , item true (cell empty) ∷ rest)
      else if n ≡ᵇ 1 then inj₂ (0 , item true null ∷ rest)
      else if n ≡ᵇ 2 then inj₂ (0 , item true (table []) ∷ rest)
      else newArray 17 n 0 >>= λ v → inj₂ (0 , item true v ∷ rest)
  execute lt s = binaryNat (λ a b → inj₂ (boolItem (a <ᵇ b))) s >>= λ t → inj₂ (0 , t)
  execute add s = do
    t ← binaryNat (λ a b →
      if a + b <ᵇ 2 ^ 64 then inj₂ (natItem (a + b)) else inj₁ bounds) s
    inj₂ (0 , t)
  execute sub s = do
    t ← binaryNat (λ a b →
      if b ≤ᵇ a then inj₂ (natItem (a ∸ b)) else inj₁ bounds) s
    inj₂ (0 , t)
  execute (addi n) s = do
    t ← unaryNat (λ a → if a + n <ᵇ 2 ^ 64 then inj₂ (a + n) else inj₁ bounds) s
    inj₂ (0 , t)
  execute (subi n) s = do
    t ← unaryNat (λ a → if n ≤ᵇ a then inj₂ (a ∸ n) else inj₁ bounds) s
    inj₂ (0 , t)
  execute and s = binaryBool _∧_ s >>= λ t → inj₂ (0 , t)
  execute or s = binaryBool _∨_ s >>= λ t → inj₂ (0 , t)
  execute neg (x ∷ rest) = do
    a ← atom x
    b ← flag a
    inj₂ (0 , boolItem (not b) ∷ rest)
  execute eq (a ∷ b ∷ rest) = do
    aa ← atom a
    ba ← atom b
    if (64 <ᵇ byteSize aa) ∧ (64 <ᵇ byteSize ba) then inj₁ bounds
      else inj₂ (0 , boolItem (does (aa ≟ᴬ ba)) ∷ rest)
  execute (concat cached bound) (b ∷ a ∷ rest) = do
    aa ← atom a
    ba ← atom b
    if (bound ≤ᵇ cellBound) ∧ (byteSize aa + byteSize ba ≤ᵇ bound) then
      (case-concat (concatenate aa ba)) else inj₁ bounds
    where
    case-concat : Maybe Aligned → Result (ℕ × Stack)
    case-concat nothing = inj₁ invalidType
    case-concat (just a) = inj₂ (0 , item true (cell a) ∷ rest)
  execute (branch n) (x ∷ rest) = atom x >>= λ a → inj₂ ((if truth a then n else 0) , rest)
  execute (jmp n) s = inj₂ (n , s)
  execute unsupported s = inj₁ unsupportedOpcode
  execute _ [] = inj₁ underflow
  execute _ _ = inj₁ invalidType

  record State : Set where
    constructor machine
    field pc : ℕ
          stackValues : Stack
  open State public

  prepare : Instruction → State → Error ⊎ (⊤ × State)
  prepare op (machine pc s) = execute op s >>= λ (skip , t) → inj₂ (tt , machine (suc (pc + skip)) t)

  semantics : Semantics
  semantics = record
    { State = State ; Kind = ⊤ ; Res = λ _ → ⊤ ; Op = λ _ → Instruction
    ; Failure = λ _ → Error ; prepare = prepare
    ; DecEq-Res = record { _≟_ = λ { tt tt → yes refl } } }

  data Step (op : Instruction) (s : State) : State → Set where
    step : ∀ {skip t} → execute op (stackValues s) ≡ inj₂ (skip , t) →
      Step op s (machine (suc (pc s + skip)) t)

  data Journal : State → List Instruction → State → Set where
    done : ∀ {s} → Journal s [] s
    next : ∀ {s t u op ops} → Step op s t → Journal t ops u → Journal s (op ∷ ops) u

  replay : List Instruction → State → Maybe State
  replay [] s = just s
  replay (op ∷ ops) s with Execution.apply semantics {k = tt} op tt s
  ... | nothing = nothing
  ... | just t = replay ops t

  run : ℕ → List Instruction → State → Maybe State
  run fuel program s with pc s ≡ᵇ length program
  ... | true = just s
  ... | false with fuel
  ...   | zero = nothing
  ...   | suc fuel with at (pc s) program
  ...     | inj₁ _ = nothing
  ...     | inj₂ op with Execution.apply semantics {k = tt} op tt s
  ...       | nothing = nothing
  ...       | just t = run fuel program t

  data ProgramRun (program : List Instruction) : ℕ → State → State → Set where
    halt : ∀ {fuel s} → (pc s ≡ᵇ length program) ≡ true → ProgramRun program fuel s s
    advance : ∀ {fuel s t u op} →
      (pc s ≡ᵇ length program) ≡ false →
      at (pc s) program ≡ inj₂ op →
      Step op s t → ProgramRun program fuel t u → ProgramRun program (suc fuel) s u


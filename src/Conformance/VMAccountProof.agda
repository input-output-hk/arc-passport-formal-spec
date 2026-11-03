{-# OPTIONS --safe --without-K #-}

module Conformance.VMAccountProof where

open import Data.Bool.Base
open import Data.Empty using (⊥-elim)
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (inj₂)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (does; yes; no)
import Conformance.FullAccountTypes as Account
open import Conformance.VM
import Conformance.VMAccount as Representation

module Proofs (A : Atoms) where
  open Atoms A hiding (empty)
  module M = Machine A
  module R = Representation.Representation A

  module Encoded (E : R.AtomEncoding) where
    open R.AtomEncoding E
    open R.Encoded E

    encodeMaybe : Maybe Account.Value → M.Value
    encodeMaybe nothing = M.null
    encodeMaybe (just v) = M.cell (encodeValue v)

    lookup-correspondence : ∀ {xs ys} → MapEntries xs ys → ∀ k →
      M.lookup (encodeKey k) ys ≡ encodeMaybe (Account.lookupMap (keyValue k) xs)
    lookup-correspondence empty k = refl
    lookup-correspondence (entry {k = x} rest) k rewrite equality k x with Account.equal (keyValue k) (keyValue x)
    ... | true = refl
    ... | false = lookup-correspondence rest k

    present : Maybe Account.Value → Bool
    present nothing = false
    present (just _) = true

    map-member-correspondence : ∀ {xs ys} → MapEntries xs ys → ∀ k →
      M.contains (encodeKey k) ys ≡ present (Account.lookupMap (keyValue k) xs)
    map-member-correspondence empty k = refl
    map-member-correspondence (entry {k = x} rest) k rewrite equality k x with Account.equal (keyValue k) (keyValue x)
    ... | true = refl
    ... | false = map-member-correspondence rest k

    set-member-correspondence : ∀ {xs ys} → SetEntries xs ys → ∀ k →
      M.contains (encodeKey k) ys ≡ Account.member (keyValue k) xs
    set-member-correspondence empty k = refl
    set-member-correspondence (entry {k = x} rest) k rewrite equality k x =
      cong (Account.equal (keyValue k) (keyValue x) ∨_) (set-member-correspondence rest k)

    insert-correspondence : ∀ {xs ys} → MapEntries xs ys → ∀ k v →
      MapEntries (Account.insertMap (keyValue k) v xs) (M.insert (encodeKey k) (M.cell (encodeValue v)) ys)
    insert-correspondence empty k v = entry empty
    insert-correspondence (entry {k = x} rest) k v rewrite equality k x with Account.equal (keyValue k) (keyValue x)
    ... | true = entry rest
    ... | false = entry (insert-correspondence rest k v)

    remove-correspondence : ∀ {xs ys} → SetEntries xs ys → ∀ k →
      SetEntries (Account.removeSet (keyValue k) xs) (M.remove (encodeKey k) ys)
    remove-correspondence empty k = empty
    remove-correspondence (entry {k = x} rest) k rewrite equality k x with Account.equal (keyValue k) (keyValue x)
    ... | true = remove-correspondence rest k
    ... | false = entry (remove-correspondence rest k)

    map-read-argument-and-result : ∀ {xs ys k v} → MapEntries xs ys →
      Account.lookupMap (keyValue k) xs ≡ just v → M.get (M.table ys) (encodeKey k) ≡ inj₂ (M.cell (encodeValue v))
    map-read-argument-and-result {k = k} entries found rewrite lookup-correspondence entries k | found = refl

    map-write-argument-and-value : ∀ {xs ys} → MapEntries xs ys → ∀ k v →
      M.put (M.table ys) (encodeKey k) (M.cell (encodeValue v)) ≡
        inj₂ (M.table (M.insert (encodeKey k) (M.cell (encodeValue v)) ys))
    map-write-argument-and-value entries k v = refl

    same-atom : ∀ a → does (a ≟ᴬ a) ≡ true
    same-atom a with a ≟ᴬ a
    ... | yes p = refl
    ... | no p = ⊥-elim (p refl)

    map-lookup-execute : ∀ {xs ys k v} → MapEntries xs ys →
      Account.lookupMap (keyValue k) xs ≡ just v → ∀ cached strength rest →
      M.execute (M.idx cached false (M.literal (encodeKey k) ∷ []))
        (M.item strength (M.table ys) ∷ rest) ≡
      inj₂ (0 , M.item strength (M.cell (encodeValue v)) ∷ rest)
    map-lookup-execute {k = k} {v = v} entries found cached strength rest
      rewrite lookup-correspondence entries k | found = refl

    map-read-journal : ∀ {xs ys k v} → MapEntries xs ys →
      Account.lookupMap (keyValue k) xs ≡ just v → ∀ cached strength pc rest →
      M.Journal (M.machine pc (M.item strength (M.table ys) ∷ rest))
        (M.idx cached false (M.literal (encodeKey k) ∷ []) ∷ M.popeq cached (encodeValue v) ∷ [])
        (M.machine (nextPC (nextPC pc)) rest)
    map-read-journal {k = k} {v = v} entries found cached strength pc rest =
      M.next (M.step (map-lookup-execute {k = k} {v = v} entries found cached strength rest))
        (M.next (M.step pop-result) M.done)
      where
      pop-result : M.execute (M.popeq cached (encodeValue v))
        (M.item strength (M.cell (encodeValue v)) ∷ rest) ≡ inj₂ (0 , rest)
      pop-result rewrite same-atom (encodeValue v) = refl

    map-member-step : ∀ {xs ys} → MapEntries xs ys → ∀ k strength keyStrength pc rest →
      M.Step M.member
        (M.machine pc (M.item keyStrength (M.cell (encodeKey k)) ∷ M.item strength (M.table ys) ∷ rest))
        (M.machine (nextPC pc) (M.boolItem (present (Account.lookupMap (keyValue k) xs)) ∷ rest))
    map-member-step entries k strength keyStrength pc rest =
      M.step (cong (λ b → inj₂ (0 , M.boolItem b ∷ rest)) (map-member-correspondence entries k))

    set-member-step : ∀ {xs ys} → SetEntries xs ys → ∀ k strength keyStrength pc rest →
      M.Step M.member
        (M.machine pc (M.item keyStrength (M.cell (encodeKey k)) ∷ M.item strength (M.table ys) ∷ rest))
        (M.machine (nextPC pc) (M.boolItem (Account.member (keyValue k) xs) ∷ rest))
    set-member-step entries k strength keyStrength pc rest =
      M.step (cong (λ b → inj₂ (0 , M.boolItem b ∷ rest)) (set-member-correspondence entries k))

    map-insert-step : ∀ ys k v cached strength pc rest →
      M.Step (M.ins cached 1)
        (M.machine pc (M.item true (M.cell (encodeValue v)) ∷ M.item false (M.cell (encodeKey k)) ∷ M.item strength (M.table ys) ∷ rest))
        (M.machine (nextPC pc) (M.item strength (M.table (M.insert (encodeKey k) (M.cell (encodeValue v)) ys)) ∷ rest))
    map-insert-step ys k v cached strength pc rest = M.step refl

    typed-map-read : ∀ label s xs ys k v → Account.cell label s ≡ Account.tuple xs →
      MapEntries xs ys → Account.lookupMap (keyValue k) xs ≡ just v → ∀ cached strength pc rest →
      (Account.lookup label (keyValue k) s ≡ Account.accepted v s (Account.mapLookup label (keyValue k) v ∷ [])) ×
      M.Journal (M.machine pc (M.item strength (M.table ys) ∷ rest))
        (M.idx cached false (M.literal (encodeKey k) ∷ []) ∷ M.popeq cached (encodeValue v) ∷ [])
        (M.machine (nextPC (nextPC pc)) rest)
    typed-map-read label s xs ys k v cellValue entries found cached strength pc rest
      rewrite cellValue | found = refl , map-read-journal {k = k} {v = v} entries found cached strength pc rest

    typed-set-member : ∀ label s xs ys k → Account.cell label s ≡ Account.tuple xs →
      SetEntries xs ys → ∀ strength keyStrength pc rest →
      (Account.has label (keyValue k) s ≡ Account.accepted (Account.member (keyValue k) xs) s
        (Account.setMember label (keyValue k) (Account.member (keyValue k) xs) ∷ [])) ×
      M.Step M.member
        (M.machine pc (M.item keyStrength (M.cell (encodeKey k)) ∷ M.item strength (M.table ys) ∷ rest))
        (M.machine (nextPC pc) (M.boolItem (Account.member (keyValue k) xs) ∷ rest))
    typed-set-member label s xs ys k cellValue entries strength keyStrength pc rest
      rewrite cellValue = refl , set-member-step entries k strength keyStrength pc rest

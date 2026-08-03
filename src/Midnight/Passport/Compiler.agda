------------------------------------------------------------------------
-- Midnight.Passport.Compiler
--
-- Flattens a HomTerm to a wiring diagram and emits Graphviz DOT directly,
-- so the rendering pipeline is just `passport-compiler | dot -Tsvg` — no
-- Julia/Catlab/Python runtime, only the agda-compiled binary and graphviz
-- (both trivially packaged with Nix on every platform).
--
-- The flatten wires ports BY POSITION (compose connects output i to input
-- i; otimes concatenates), exactly mirroring the strict-SMC semantics. This
-- is correct even when channel names repeat across parallel lanes — the bug
-- the original name-keyed flattener had, and the reason we briefly detoured
-- through Catlab.
--
------------------------------------------------------------------------

module Midnight.Passport.Compiler where

open import Data.String as S using (String)
open import Data.List   as L using (List; []; _∷_; _++_; map; length; take; drop; reverse; foldr)
open import Data.Nat    as ℕ using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Function     using (case_of_)

open import Midnight.Passport.FMTerm

infixr 5 _⟨++⟩_
_⟨++⟩_ : String → String → String
_⟨++⟩_ = S._++_

------------------------------------------------------------------------
-- 0.  String / number utilities
------------------------------------------------------------------------

private
  digitChar : ℕ → String
  digitChar 0 = "0"
  digitChar 1 = "1"
  digitChar 2 = "2"
  digitChar 3 = "3"
  digitChar 4 = "4"
  digitChar 5 = "5"
  digitChar 6 = "6"
  digitChar 7 = "7"
  digitChar 8 = "8"
  digitChar _ = "9"

  {-# TERMINATING #-}
  digitsLSF : ℕ → List ℕ
  digitsLSF zero    = 0 ∷ []
  digitsLSF (suc m) =
    let n = suc m
        q = n ℕ./ 10
        r = n ℕ.% 10
    in  r ∷ (case q of λ { zero → [] ; _ → digitsLSF q })

  revJoin : List ℕ → String → String
  revJoin []       acc = acc
  revJoin (d ∷ ds) acc = revJoin ds (digitChar d ⟨++⟩ acc)

showNat : ℕ → String
showNat n = revJoin (digitsLSF n) ""

quoted : String → String
quoted s = "\"" ⟨++⟩ s ⟨++⟩ "\""

nodeId : ℕ → String
nodeId n = "n" ⟨++⟩ showNat n

------------------------------------------------------------------------
-- 1.  Wiring-diagram data
------------------------------------------------------------------------

data NodeKind : Set where
  boxN : String → NodeKind   -- a component box (label = its name)
  bndN : NodeKind            -- an outer-interface boundary (drawn invisibly)

-- A port: the id of the node producing it, paired with its channel name.
Port : Set
Port = ℕ × String

-- A wire: producing node id, consuming node id, channel name.
Wire : Set
Wire = ℕ × ℕ × String

record St : Set where
  constructor mkSt
  field
    nextId : ℕ
    nodes  : List (ℕ × NodeKind)
    wires  : List Wire

private
  freshNode : NodeKind → St → ℕ × St
  freshNode k (mkSt n ns ws) = n , mkSt (suc n) ((n , k) ∷ ns) ws

  addWire : ℕ → ℕ → String → St → St
  addWire src tgt ch (mkSt n ns ws) = mkSt n ns ((src , tgt , ch) ∷ ws)

  -- Wire each incoming port into a freshly-made box, positionally.
  wireInto : ℕ → List Port → St → St
  wireInto tgt ps st = foldr (λ { (src , ch) s → addWire src tgt ch s }) st ps

------------------------------------------------------------------------
-- 2.  Positional flatten (inside opaque unfolding)
------------------------------------------------------------------------

-- Thread state and the positional list of incoming ports; return the
-- updated state and the outgoing ports. |incoming| = |domain| always.
flatten : ∀ {A B} → HomTerm A B → St → List Port → St × List Port

flatten {_} {B} (var ℓ) st inc =
  let (bid , st₁) = freshNode (boxN (Label.name ℓ)) st
      st₂         = wireInto bid inc st₁
      outs        = map (λ ch → bid , ch) B
  in  st₂ , outs

flatten id s inc = s , inc

-- _∘_ is right-to-left: f runs first, feeding g.
flatten (g ∘ f) st inc =
  let (st₁ , mid) = flatten f st inc
      (st₂ , out) = flatten g st₁ mid
  in  st₂ , out

-- Split the incoming ports between the two factors by the left domain.
flatten (_⊗₁_ {A} f g) st inc =
  let (incF , incG) = take (length A) inc , drop (length A) inc
      (st₁ , outF)  = flatten f st  incF
      (st₂ , outG)  = flatten g st₁ incG
  in  st₂ , (outF ++ outG)

-- Outer input/output boundaries from the type indices.
outerInputs : ObjTerm → St → St × List Port
outerInputs A st = go A st []
  where
  go : List String → St → List Port → St × List Port
  go []       s acc = s , reverse acc
  go (c ∷ cs) s acc =
    let (i , s′) = freshNode bndN s in go cs s′ ((i , c) ∷ acc)

outerOutputs : List Port → St → St
outerOutputs []             st = st
outerOutputs ((src , ch) ∷ ps) st =
  let (o , st′) = freshNode bndN st in outerOutputs ps (addWire src o ch st′)

------------------------------------------------------------------------
-- 3.  DOT emission
------------------------------------------------------------------------

private
  renderNode : ℕ × NodeKind → String
  renderNode (i , boxN nm) =
    "  " ⟨++⟩ nodeId i ⟨++⟩ " [label=" ⟨++⟩ quoted nm ⟨++⟩ "];\n"
  renderNode (i , bndN) =
    "  " ⟨++⟩ nodeId i ⟨++⟩ " [shape=none, label=\"\", width=0, height=0];\n"

  renderWire : Wire → String
  renderWire (src , tgt , ch) =
    "  " ⟨++⟩ nodeId src ⟨++⟩ " -> " ⟨++⟩ nodeId tgt
          ⟨++⟩ " [label=" ⟨++⟩ quoted ch ⟨++⟩ "];\n"

  concatMapS : {A : Set} → (A → String) → List A → String
  concatMapS f = foldr (λ x acc → f x ⟨++⟩ acc) ""

------------------------------------------------------------------------
-- 4.  Public entry point
------------------------------------------------------------------------

-- Render a HomTerm to a complete Graphviz DOT document.
compileDot : ∀ {A B} → HomTerm A B → String
compileDot {A} {B} term =
  let (st₀ , inc)  = outerInputs A (mkSt 0 [] [])
      (st₁ , outs) = flatten term st₀ inc
      st           = outerOutputs outs st₁
  in  "digraph G {\n"
        ⟨++⟩ "  rankdir=\"BT\";\n"
        ⟨++⟩ "  node [shape=\"box\", style=\"rounded,filled\", fillcolor=\"white\", fontname=\"Times-Roman\"];\n"
        ⟨++⟩ "  edge [fontname=\"Times-Roman\", fontsize=\"10\", arrowsize=\"0.6\"];\n"
        ⟨++⟩ concatMapS renderNode (reverse (St.nodes st))
        ⟨++⟩ concatMapS renderWire (reverse (St.wires st))
        ⟨++⟩ "}\n"

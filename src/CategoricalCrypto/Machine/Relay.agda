{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

------------------------------------------------------------------------
-- CategoricalCrypto.Machine.Relay
--
-- A component relaying a query and an answer between a client port and a
-- server port. Generic in the query type `Q` and the answer type `V`, neither
-- of which carries any structure: nothing here needs to add, compare or order
-- queries or answers.
--
-- A `Port` is where an observer asks `qry q` and reads `ans q v` back, and
-- `Answers` says a machine can answer `v` to `q` there in one step; a `Server`
-- at that port answers every query, and every query-triggered transition
-- produces an answer to that query. A `Relay` adds the two positions the query
-- and the answer take on the way through. Its conditions
-- come in two modalities and both are needed: transferring an answer *down* to
-- the server rests on the permissions `ForwardsQuery` / `ForwardsAnswer` (IF
-- the component steps on this message, THEN it emits that one) together with
-- the `NoInvention` discipline, while transferring one *up* from the server
-- rests on the guarantee `Responsive` (the two forwarding steps are
-- available). Conflating the two would make the relay a deterministic function
-- of its input, which no useful component is.
--
-- `Routing S p₁ p₂` is the transfer itself, along a simulation `S`: the answers
-- at `p₁` and at `p₂` agree, in both directions. It composes (`_∙ʳ_`), so a
-- route from a whole system down to one component is a chain of links, one per
-- wiring combinator — the pattern `SimFlow` uses for flow. `Server` travels the
-- other way, from a component up to the system it sits in: `∘-server`,
-- `∘-serverʳ` and `⊗₁-serverˡ/ʳ` are the closure theorems, one per wiring
-- combinator. The links for a layer of pure rewiring (`modify-routes`,
-- `through-∘-routes`) are free: `Through` says such a layer relays everything,
-- and it is closed under `_⊗₁_` and `_∘_`, so nothing is left to assume but the
-- injectivity of the wiring itself.
------------------------------------------------------------------------

module CategoricalCrypto.Machine.Relay where

open import categorical-crypto.Prelude hiding (id; _∘_)
open import Data.Maybe renaming (map to mapₘ)
open import Data.Maybe.Properties

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Cascade
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Core.Ext
open import CategoricalCrypto.Machine.Simulation
open import CategoricalCrypto.Machine.Wiring

open Machine using (State; stepRel)

private variable
  A B C D E F : Channel
  Q V : Set

--------------------------------------------------------------------------------
-- Ports and the answers observable at them

-- where an observer asks `qry q` and reads `ans q v` back
record Port (M : Machine A B) (Q V : Set) : Set where
  field
    qry : Q → Msg M In
    ans : Q → V → Msg M Out

open Port public

-- The port at the single wire a machine's codomain consists of — `C ⊗₀ I`, the
-- shape a one-element wire list interprets to: the client asks on that wire and
-- reads the answer back on it.
codᵍ : ∀ {m C} → C [ m ]⇒[ ¬ₘ m ]ᵍ (A ⊗ᵀ (C ⊗₀ I))
codᵍ = L⊗ (ϵ ⊗R) ᵗ¹

wirePort : (C : Channel) (M : Machine A (C ⊗₀ I))
         → (Q → Channel.outType C) → (Q → V → Channel.inType C) → Port M Q V
wirePort _ _ q r = record { qry = λ x → codᵍ ↑ₒ q x ; ans = λ x v → codᵍ ↑ᵢ r x v }

-- in state s, one step at the port can answer v to q
Answers : {M : Machine A B} → Port M Q V → State M → Q → V → Set
Answers {M = M} p s q v = ∃[ s' ] stepRel M s (qry p q) (just (ans p q v)) s'

module _ {M : Machine A B} (p : Port M Q V) where

  -- permission: a step on the query answers it — no other reply, and no silent
  -- step (`Answers` alone leaves both open, since it only exhibits one step)
  AnswersOnly : Set
  AnswersOnly = ∀ {s q o s'} → stepRel M s (qry p q) o s' → ∃[ v ] o ≡ just (ans p q v)

  CanAnswer : Set
  CanAnswer = ∀ s q → ∃[ v ] Answers p s q v

  Server : Set
  Server = AnswersOnly × CanAnswer

  -- with the step relation functional at the port, the answer is a function of
  -- the state and the query
  answer-unique : (∀ {s q o o' s' s''} → stepRel M s (qry p q) o s'
                                       → stepRel M s (qry p q) o' s'' → o ≡ o')
                → (∀ {q v v'} → ans p q v ≡ ans p q v' → v ≡ v')
                → ∀ {s q v v'} → Answers p s q v → Answers p s q v' → v ≡ v'
  answer-unique det inj (_ , st) (_ , st') = inj (just-injective (det st st'))

--------------------------------------------------------------------------------
-- Relays

record Relay (M : Machine A B) (Q V : Set) : Set where
  field
    qryIn  : Q → Msg M In           -- the query, as it arrives from the client
    qryOut : Q → Msg M Out          -- … as it is forwarded to the server
    ansIn  : Q → V → Msg M In       -- the answer, as it arrives from the server
    ansOut : Q → V → Msg M Out      -- … as it is forwarded to the client

  clientPort : Port M Q V
  clientPort = record { qry = qryIn ; ans = ansOut }

module _ {M : Machine A B} (R : Relay M Q V) where
  open Relay R

  -- permissions: a step on the query (answer) forwards it, and does nothing else
  ForwardsQuery : Set
  ForwardsQuery = ∀ {s q o s'} → stepRel M s (qryIn q) o s' → o ≡ just (qryOut q)

  ForwardsAnswer : Set
  ForwardsAnswer = ∀ {s q v o s'} → stepRel M s (ansIn q v) o s' → o ≡ just (ansOut q v)

  -- discipline: an answer the client sees was answered by the server on that
  -- very step — the relay never makes one up (and, in particular, never caches)
  NoInvention : Set
  NoInvention = ∀ {s q v i s'} → stepRel M s i (just (ansOut q v)) s' → i ≡ ansIn q v

  -- guarantee: both forwarding steps are always available
  Responsive : Set
  Responsive = (∀ s q → ∃[ s' ] stepRel M s (qryIn q) (just (qryOut q)) s')
             × (∀ s q v → ∃[ s' ] stepRel M s (ansIn q v) (just (ansOut q v)) s')

--------------------------------------------------------------------------------
-- Answer transfer along a simulation

record Routing {G : Machine A B} {N : Machine C D} (S : Sim G N)
               (p₁ : Port G Q V) (p₂ : Port N Q V) : Set where
  field
    sound    : ∀ {s q v} → Answers p₁ s q v → Answers p₂ (Sim.π S s) q v
    complete : ∀ {s q v} → Answers p₂ (Sim.π S s) q v → Answers p₁ s q v

open Routing public

id-routes : {M : Machine A B} (p : Port M Q V) → Routing idSim p p
sound    (id-routes _) = λ a → a
complete (id-routes _) = λ a → a

infixr 9 _∙ʳ_
_∙ʳ_ : {G : Machine A B} {N : Machine C D} {P : Machine E F}
       {S : Sim G N} {T : Sim N P}
       {p₁ : Port G Q V} {p₂ : Port N Q V} {p₃ : Port P Q V}
     → Routing S p₁ p₂ → Routing T p₂ p₃ → Routing (S ∙ T) p₁ p₃
sound    (X ∙ʳ Y) a = sound Y (sound X a)
complete (X ∙ʳ Y) a = complete X (complete Y a)

--------------------------------------------------------------------------------
-- Tensor links
--
-- A factor's port, seen at the tensor's boundary. Nothing is assumed: a tensor
-- step *is* one factor's step, so a query at the left factor's port can only be
-- answered by the left factor.

module _ {M₁ : Machine A B} {M₂ : Machine C D} where

  ⊗₁-portˡ : Port M₁ Q V → Port (M₁ ⊗₁ M₂) Q V
  ⊗₁-portˡ p = record { qry = λ q → ⊗₁-inˡ {m = In} (qry p q)
                      ; ans = λ q v → ⊗₁-inˡ {m = Out} (ans p q v) }

  ⊗₁-portʳ : Port M₂ Q V → Port (M₁ ⊗₁ M₂) Q V
  ⊗₁-portʳ p = record { qry = λ q → ⊗₁-inʳ {m = In} (qry p q)
                      ; ans = λ q v → ⊗₁-inʳ {m = Out} (ans p q v) }

  ⊗₁-routesˡ : (p : Port M₁ Q V) → Routing (⊗₁-simˡ {M₁ = M₁} {M₂}) (⊗₁-portˡ p) p
  sound (⊗₁-routesˡ p) {s} {q} {v} (s' , st) =
    comp-atˡ-just {M₁ = M₁} {M₂}
      (⊗₁-compˡ {M₁ = M₁} {M₂} {i = qry p q} {o = just (ans p q v)} st)
      (λ st' _ → proj₁ s' , st')
  complete (⊗₁-routesˡ p) {s} {q} {v} (sₐ' , st) =
    (sₐ' , proj₂ s) , ⊗₁-mkˡ {M₁ = M₁} {M₂} {i = qry p q} {o = just (ans p q v)} (compL st)

  ⊗₁-routesʳ : (p : Port M₂ Q V) → Routing (⊗₁-simʳ {M₁ = M₁} {M₂}) (⊗₁-portʳ p) p
  sound (⊗₁-routesʳ p) {s} {q} {v} (s' , st) =
    comp-atʳ-just {M₁ = M₁} {M₂}
      (⊗₁-compʳ {M₁ = M₁} {M₂} {i = qry p q} {o = just (ans p q v)} st)
      (λ st' _ → proj₂ s' , st')
  complete (⊗₁-routesʳ p) {s} {q} {v} (sᵦ' , st) =
    (proj₁ s , sᵦ') , ⊗₁-mkʳ {M₁ = M₁} {M₂} {i = qry p q} {o = just (ans p q v)} (compR st)

  -- The server discipline is a factor's alone: a tensor step at the factor's
  -- port is that factor's step, whatever the other factor could do.

  ⊗₁-answers-onlyˡ : (p : Port M₁ Q V) → AnswersOnly p → AnswersOnly (⊗₁-portˡ p)
  ⊗₁-answers-onlyˡ p ao {s} {q} {nothing} {s'} st =
    comp-atˡ {M₁ = M₁} {M₂} (⊗₁-compˡ {M₁ = M₁} {M₂} {i = qry p q} {o = nothing} st) go
    where
      go : ∀ {mₒ} → nothing ≡ mapₘ (tagˡ {m = Out}) mₒ
         → stepRel M₁ (proj₁ s) (qry p q) mₒ (proj₁ s') → proj₂ s ≡ proj₂ s'
         → ∃[ v ] nothing ≡ just (ans (⊗₁-portˡ p) q v)
      go {just _}  ()
      go {nothing} _ st' _ with ao st'
      ... | _ , ()
  ⊗₁-answers-onlyˡ p ao {s} {q} {just x} {s'} st =
    go (⊗₁-in-split {M₁ = M₁} {M₂ = M₂} {m = Out} x)
    where
      at : ∀ {z} → x ≡ z → stepRel (M₁ ⊗₁ M₂) s (qry (⊗₁-portˡ p) q) (just z) s'
      at e = subst (λ z → stepRel (M₁ ⊗₁ M₂) s (qry (⊗₁-portˡ p) q) (just z) s') e st

      go : (∃[ y ] x ≡ ⊗₁-inˡ {m = Out} y) ⊎ (∃[ y ] x ≡ ⊗₁-inʳ {m = Out} y)
         → ∃[ v ] just x ≡ just (ans (⊗₁-portˡ p) q v)
      go (inj₁ (y , e)) =
        comp-atˡ-just {M₁ = M₁} {M₂}
          (⊗₁-compˡ {M₁ = M₁} {M₂} {i = qry p q} {o = just y} (at e))
          (λ st' _ → let v , e' = ao st'
                     in v , trans (cong just e) (cong (mapₘ (⊗₁-inˡ {m = Out})) e'))
      go (inj₂ (y , e)) =
        ⊥-elim (comp-atˡ-cross {M₁ = M₁} {M₂}
                  (⊗₁-compˡʳ {M₁ = M₁} {M₂} {i = qry p q} {o = just y} (at e)))

  ⊗₁-answers-onlyʳ : (p : Port M₂ Q V) → AnswersOnly p → AnswersOnly (⊗₁-portʳ p)
  ⊗₁-answers-onlyʳ p ao {s} {q} {nothing} {s'} st =
    comp-atʳ {M₁ = M₁} {M₂} (⊗₁-compʳ {M₁ = M₁} {M₂} {i = qry p q} {o = nothing} st) go
    where
      go : ∀ {mₒ} → nothing ≡ mapₘ (tagʳ {m = Out}) mₒ
         → stepRel M₂ (proj₂ s) (qry p q) mₒ (proj₂ s') → proj₁ s ≡ proj₁ s'
         → ∃[ v ] nothing ≡ just (ans (⊗₁-portʳ p) q v)
      go {just _}  ()
      go {nothing} _ st' _ with ao st'
      ... | _ , ()
  ⊗₁-answers-onlyʳ p ao {s} {q} {just x} {s'} st =
    go (⊗₁-in-split {M₁ = M₁} {M₂ = M₂} {m = Out} x)
    where
      at : ∀ {z} → x ≡ z → stepRel (M₁ ⊗₁ M₂) s (qry (⊗₁-portʳ p) q) (just z) s'
      at e = subst (λ z → stepRel (M₁ ⊗₁ M₂) s (qry (⊗₁-portʳ p) q) (just z) s') e st

      go : (∃[ y ] x ≡ ⊗₁-inˡ {m = Out} y) ⊎ (∃[ y ] x ≡ ⊗₁-inʳ {m = Out} y)
         → ∃[ v ] just x ≡ just (ans (⊗₁-portʳ p) q v)
      go (inj₁ (y , e)) =
        ⊥-elim (comp-atʳ-cross {M₁ = M₁} {M₂}
                  (⊗₁-compʳˡ {M₁ = M₁} {M₂} {i = qry p q} {o = just y} (at e)))
      go (inj₂ (y , e)) =
        comp-atʳ-just {M₁ = M₁} {M₂}
          (⊗₁-compʳ {M₁ = M₁} {M₂} {i = qry p q} {o = just y} (at e))
          (λ st' _ → let v , e' = ao st'
                     in v , trans (cong just e) (cong (mapₘ (⊗₁-inʳ {m = Out})) e'))

  ⊗₁-can-answerˡ : (p : Port M₁ Q V) → CanAnswer p → CanAnswer (⊗₁-portˡ p)
  ⊗₁-can-answerˡ p ca s q = let v , a = ca (proj₁ s) q in v , complete (⊗₁-routesˡ p) a

  ⊗₁-can-answerʳ : (p : Port M₂ Q V) → CanAnswer p → CanAnswer (⊗₁-portʳ p)
  ⊗₁-can-answerʳ p ca s q = let v , a = ca (proj₂ s) q in v , complete (⊗₁-routesʳ p) a

  ⊗₁-serverˡ : (p : Port M₁ Q V) → Server p → Server (⊗₁-portˡ p)
  ⊗₁-serverˡ p (ao , ca) = ⊗₁-answers-onlyˡ p ao , ⊗₁-can-answerˡ p ca

  ⊗₁-serverʳ : (p : Port M₂ Q V) → Server p → Server (⊗₁-portʳ p)
  ⊗₁-serverʳ p (ao , ca) = ⊗₁-answers-onlyʳ p ao , ⊗₁-can-answerʳ p ca

--------------------------------------------------------------------------------
-- The composition link: a relay in front of a server
--
-- `M₁ ∘ M₂` puts the relay `M₁` between the client (which talks on `C`) and the
-- server `M₂`, whose codomain `B` is the wire the two share. The client asks
-- `c q` and is answered `d q v`; on the wire the same exchange is `qʷ q`
-- answered `rʷ q v`. Everything is generic in those four messages, so the three
-- ports are *defined* from them rather than assumed to be related — the content
-- of the theorem is the cascade, not a coincidence of naming.

module _ {M₁ : Machine B C} {M₂ : Machine A B} {Q V : Set}
         (c : Q → Channel.outType C) (d : Q → V → Channel.inType C) where

  -- the composite's client port, and the same port on the front component
  -- (the two channels embed `C` alike, so the messages are the same)
  ∘-clientPort : Port (M₁ ∘ M₂) Q V
  ∘-clientPort = record { qry = λ q → L⊗ (ϵ ᵗ¹) ↑ₒ c q
                        ; ans = λ q v → L⊗ (ϵ ᵗ¹) ↑ᵢ d q v }

  ∘-frontPort : Port M₁ Q V
  ∘-frontPort = record { qry = λ q → L⊗ (ϵ ᵗ¹) ↑ₒ c q
                       ; ans = λ q v → L⊗ (ϵ ᵗ¹) ↑ᵢ d q v }


  private
    -- the machine `_∘_` traces over; naming it lets the cascade's nodes be
    -- spoken about (each is a `M₂ ⊗₁ M₁` step at translated messages)
    inner : Machine (A ⊗₀ B) (C ⊗₀ B)
    inner = modifyStepRel (∘-reshuffle {A} {B} {C}) (M₂ ⊗₁ M₁)

    -- A cascade node's output, as the tensor core sees it: the two translation
    -- layers a node's output crosses. This is the form an inversion hands an
    -- output *equation* back in, so a statement about an output that is still a
    -- variable has to be phrased here (a pinned output needs none of this — its
    -- translation computes).
    Φₒ : Maybe (Msg inner Out) → Maybe (modeType Out ((A ⊗ᵀ B) ⊗₀ (B ⊗ᵀ C)))
    Φₒ o = mapₘ (app {mᵢ = Out} (⊗₁-msg {A} {B} {B} {C}))
                (mapₘ (app {mᵢ = Out} (∘-reshuffle {A} {B} {C})) o)

    -- The cascade's message positions, named. Inside the `unfolding` block below
    -- a channel is a bare `⊎`, from which a DSL term's channel cannot be
    -- recovered — so every position gets a helper whose signature pins it.
    cQry : Channel.outType C → Msg inner In    -- the client's query, arriving
    cQry x = L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ x

    cAns : Channel.inType C → Msg inner Out    -- the client's answer, leaving
    cAns x = L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ x

    wQryₒ : Channel.outType B → Msg inner Out  -- the query, onto the wire
    wQryₒ x = (L⊗ ϵ) ⊗R ↑ₒ x

    wQryᵢ : Channel.outType B → Msg inner In   -- … and off it, at the server
    wQryᵢ x = L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹ ↑ᵢ x

    wAnsₒ : Channel.inType B → Msg inner Out   -- the answer, onto the wire
    wAnsₒ x = L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹ ↑ₒ x

    wAnsᵢ : Channel.inType B → Msg inner In    -- … and off it, at the relay
    wAnsᵢ x = (L⊗ ϵ) ⊗R ↑ᵢ x

    -- the tags of the tensor `_∘_` traces over: the server is its left factor,
    -- the relay its right one (both channel pairs pinned, as above)
    sTag : ∀ {m} → Msg M₂ m → modeType m ((A ⊗ᵀ B) ⊗₀ (B ⊗ᵀ C))
    sTag {m} = tagˡ {A} {B} {B} {C} {m}

    rTag : ∀ {m} → Msg M₁ m → modeType m ((A ⊗ᵀ B) ⊗₀ (B ⊗ᵀ C))
    rTag {m} = tagʳ {A} {B} {B} {C} {m}

  -- The wire-side positions, as functions: written bare, the tensor's other
  -- channel would stay a metavariable and nothing below would reduce.
  ansʷ : Channel.inType B → Msg M₁ In
  ansʷ x = ϵ ⊗R ↑ᵢ x

  qryʷ : Channel.outType B → Msg M₁ Out
  qryʷ x = ϵ ⊗R ↑ₒ x

  sansʷ : Channel.inType B → Msg M₂ Out
  sansʷ x = L⊗ (ϵ ᵗ¹) ↑ᵢ x

  -- Pass-through link: the front component answers the query by itself, so the
  -- answer transfers to *it* rather than to something behind it. `AnswersAlone`
  -- is what rules out the front component consulting the component behind:
  -- without it the cascade could continue and the answer would be assembled from
  -- a state the transfer does not speak about.
  AnswersAlone : Set
  AnswersAlone = ∀ {s q w s'} → stepRel M₁ s (qry ∘-frontPort q) (just (qryʷ w)) s' → ⊥

  opaque
    unfolding _⊗₀_ destruct-⊗ ⊗-right-intro ⊗-sym ⊗-combine ⊗-fusion ⊗-right-neutral

    ∘-completeʳ : ∀ {s q v} → Answers ∘-frontPort (proj₂ s) q v → Answers ∘-clientPort s q v
    ∘-completeʳ {s} (sᵦ' , st) = (proj₁ s , sᵦ') , Trace[ compR st ]

  module _ (aa : AnswersAlone) where
    opaque
      unfolding _⊗₀_ destruct-⊗ ⊗-right-intro ⊗-sym ⊗-combine ⊗-fusion ⊗-right-neutral

      private
        alone[] : ∀ {s s' q v} → stepRel inner s (cQry (c q)) (just (cAns (d q v))) s'
                → Answers ∘-frontPort (proj₂ s) q v
        alone[] {s' = s'} {q} {v} st₁ =
          comp-atʳ-just {M₁ = M₂} {M₂ = M₁}
            {mᵢ = qry ∘-frontPort q} {mₒ = ans ∘-frontPort q v} st₁
            (λ st₁' _ → proj₂ s' , st₁')

        aloneₒ : ∀ {s s' z w q v} → stepRel inner s (cQry (c q)) (just (wQryₒ w)) z
               → TraceRel inner z (wQryᵢ w) (just (cAns (d q v))) s'
               → Answers ∘-frontPort (proj₂ s) q v
        aloneₒ {w = w} {q} st₁ _ =
          comp-atʳ-just {M₁ = M₂} {M₂ = M₁} {mᵢ = qry ∘-frontPort q} {mₒ = qryʷ w} st₁
            (λ st₁' _ → ⊥-elim (aa st₁'))

        aloneᵢ : ∀ {s s' z w q v} → stepRel inner s (cQry (c q)) (just (wAnsₒ w)) z
               → TraceRel inner z (wAnsᵢ w) (just (cAns (d q v))) s'
               → Answers ∘-frontPort (proj₂ s) q v
        aloneᵢ {w = w} {q} st₁ _ =
          ⊥-elim (comp-atʳ-cross {M₁ = M₂} {M₂ = M₁}
                    {mᵢ = qry ∘-frontPort q} {mₒ = sansʷ w} st₁)

      ∘-soundʳ : ∀ {s q v} → Answers ∘-clientPort s q v → Answers ∘-frontPort (proj₂ s) q v
      ∘-soundʳ (_ , st) = trace-inv st alone[] aloneₒ aloneᵢ

    ∘-routesʳ : Routing (∘-simʳ {M₁ = M₁} {M₂}) ∘-clientPort ∘-frontPort
    sound    ∘-routesʳ = ∘-soundʳ
    complete ∘-routesʳ = ∘-completeʳ

  -- The front component's discipline, transferred up. It answers on the
  -- codomain, and the wire is not there, so the composite inherits the
  -- discipline and the front component provably never consults what is behind
  -- it — `AnswersAlone` comes for free rather than being assumed.
  module _ (ao : AnswersOnly ∘-frontPort) where
    opaque
      unfolding _⊗₀_ destruct-⊗ ⊗-right-intro ⊗-sym ⊗-combine ⊗-fusion ⊗-right-neutral

      private
        front-wire≢cod : ∀ {x q v} → qryʷ x ≡ ans ∘-frontPort q v → ⊥
        front-wire≢cod ()

        -- one node and stop: the front component's answer is the composite's
        -- output, and neither of the two wire-bound shapes can arise
        onlyʳ : ∀ {s y oᵗ q} → TraceRel inner s (cQry (c q)) oᵗ y
              → ∃[ v ] Φₒ oᵗ ≡ Φₒ (just (cAns (d q v)))
        onlyʳ {oᵗ = oᵗ} {q} t = trace-inv t single forwards crossed
          where
            single : ∀ {s y} → stepRel inner s (cQry (c q)) oᵗ y
                   → ∃[ v ] Φₒ oᵗ ≡ Φₒ (just (cAns (d q v)))
            single st₁ =
              comp-atʳ {M₁ = M₂} {M₂ = M₁} {mᵢ = qry ∘-frontPort q} st₁ λ e st₁' _ →
                let v , e' = ao st₁'
                in v , trans e (cong (mapₘ (rTag {m = Out})) e')

            forwards : ∀ {s y z w} → stepRel inner s (cQry (c q)) (just (wQryₒ w)) z
                     → TraceRel inner z (wQryᵢ w) oᵗ y
                     → ∃[ v ] Φₒ oᵗ ≡ Φₒ (just (cAns (d q v)))
            forwards {w = w} st₁ _ =
              comp-atʳ-just {M₁ = M₂} {M₂ = M₁} {mᵢ = qry ∘-frontPort q} {mₒ = qryʷ w} st₁
                (λ st₁' _ → ⊥-elim (front-wire≢cod (just-injective (proj₂ (ao st₁')))))

            crossed : ∀ {s y z w} → stepRel inner s (cQry (c q)) (just (wAnsₒ w)) z
                    → TraceRel inner z (wAnsᵢ w) oᵗ y
                    → ∃[ v ] Φₒ oᵗ ≡ Φₒ (just (cAns (d q v)))
            crossed {w = w} st₁ _ =
              ⊥-elim (comp-atʳ-cross {M₁ = M₂} {M₂ = M₁}
                        {mᵢ = qry ∘-frontPort q} {mₒ = sansʷ w} st₁)

      ∘-answers-onlyʳ : AnswersOnly ∘-clientPort
      ∘-answers-onlyʳ {o = nothing} st with onlyʳ st
      ... | _ , ()
      ∘-answers-onlyʳ {o = just (inj₁ _)} st with onlyʳ st
      ... | _ , ()
      ∘-answers-onlyʳ {o = just (inj₂ _)} st with onlyʳ st
      ... | v , refl = v , refl

    answers-only⇒alone : AnswersAlone
    answers-only⇒alone st = front-wire≢cod (just-injective (proj₂ (ao st)))

    ∘-serverʳ : CanAnswer ∘-frontPort → Server ∘-clientPort
    ∘-serverʳ ca = ∘-answers-onlyʳ
                 , λ s q → let v , a = ca (proj₂ s) q in v , ∘-completeʳ a

  -- The relay link proper: the query goes on to the server on the wire.
  module _ (qʷ : Q → Channel.outType B) (rʷ : Q → V → Channel.inType B) where

    -- the query leaves on the domain wire, the answer comes back on it
    ∘-relay : Relay M₁ Q V
    ∘-relay = record { qryIn  = λ q → L⊗ (ϵ ᵗ¹) ↑ₒ c q
                     ; qryOut = λ q → ϵ ⊗R ↑ₒ qʷ q
                     ; ansIn  = λ q v → ϵ ⊗R ↑ᵢ rʷ q v
                     ; ansOut = λ q v → L⊗ (ϵ ᵗ¹) ↑ᵢ d q v }

    ∘-serverPort : Port M₂ Q V
    ∘-serverPort = record { qry = λ q → L⊗ (ϵ ᵗ¹) ↑ₒ qʷ q
                          ; ans = λ q v → L⊗ (ϵ ᵗ¹) ↑ᵢ rʷ q v }


    private
      module R = Relay ∘-relay

    opaque
      unfolding _⊗₀_ destruct-⊗ ⊗-right-intro ⊗-sym ⊗-combine ⊗-fusion ⊗-right-neutral

      -- The exchange, built: the relay asks, the server answers, the relay passes
      -- the answer on. Three cascade nodes, so `Responsive` is all it takes.
      ∘-complete : Responsive ∘-relay
                 → ∀ {s q v} → Answers ∘-serverPort (proj₁ s) q v → Answers ∘-clientPort s q v
      ∘-complete (rq , ra) {s} {q} {v} (sₐ' , st) =
        let sᵦ' , n₁  = rq (proj₂ s) q
            sᵦ'' , n₃ = ra sᵦ' q v
        in (sₐ' , sᵦ'') , (compR n₁ Trace∷ₒ (compL st Trace∷ᵢ Trace[ compR n₃ ]))

      private
        -- positions are injective and pairwise distinct: `refl`/absurd once
        -- Channel.Core's tensor is unfolded
        ansʷ-inj : ∀ {x y} → ansʷ x ≡ ansʷ y → x ≡ y
        ansʷ-inj refl = refl

        qryʷ-inj : ∀ {x y} → qryʷ x ≡ qryʷ y → x ≡ y
        qryʷ-inj refl = refl

        sansʷ-inj : ∀ {x y} → sansʷ x ≡ sansʷ y → x ≡ y
        sansʷ-inj refl = refl

        -- what the relay sends to the server is never what it sends to the client
        wire≢cod : ∀ {x q y} → qryʷ x ≡ R.ansOut q y → ⊥
        wire≢cod ()

    -- Soundness. An answer the client saw must have come from the server, on a
    -- step taken from the state the query was asked in. The cascade of an
    -- answering composite step can only be relay/server/relay: every other shape
    -- contradicts one of the conditions or the wiring itself. One lemma per leg,
    -- each refuting the shapes that cannot arise there.
    --
    -- `AnswersOnly ∘-serverPort` is not implied by the relay's conditions, and
    -- soundness needs it: otherwise the relay could get something else back, ask
    -- again, and the answer the client finally sees would be one the server gave
    -- from a *later* state than the one the transfer speaks about.
    module _ (fq : ForwardsQuery ∘-relay) (fa : ForwardsAnswer ∘-relay)
             (ni : NoInvention ∘-relay) (sa : AnswersOnly ∘-serverPort) where
      opaque
        unfolding _⊗₀_ destruct-⊗ ⊗-right-intro ⊗-sym ⊗-combine ⊗-fusion ⊗-right-neutral

        -- Third leg: the relay is about to answer the client, so `NoInvention`
        -- says the wire carried the answer to *this* query.
        private
          three : ∀ {x y w q v v'} → w ≡ rʷ q v'
                → TraceRel inner x (wAnsᵢ w) (just (cAns (d q v))) y
                → w ≡ rʷ q v
          three {w = w} {q} {v} {v'} eq t = trace-inv t answers forwards crossed
            where
              answers : ∀ {x y} → stepRel inner x (wAnsᵢ w) (just (cAns (d q v))) y
                      → w ≡ rʷ q v
              answers st₃ =
                comp-atʳ-just {M₁ = M₂} {M₂ = M₁} {mᵢ = ansʷ w} {mₒ = R.ansOut q v} st₃
                  (λ st₃' _ → ansʷ-inj (ni st₃'))

              -- forwarding again instead of answering: `ForwardsAnswer` forbids it
              forwards : ∀ {x y z w'} → stepRel inner x (wAnsᵢ w) (just (wQryₒ w')) z
                       → TraceRel inner z (wQryᵢ w') (just (cAns (d q v))) y → w ≡ rʷ q v
              forwards {x} {w' = w'} st₃ _ =
                comp-atʳ-just {M₁ = M₂} {M₂ = M₁} {mᵢ = ansʷ w} {mₒ = qryʷ w'} st₃
                  (λ st₃' _ → ⊥-elim (wire≢cod (just-injective
                    (fa (subst (λ z → stepRel M₁ (proj₂ x) (ansʷ z) _ _) eq st₃')))))

              -- an answer to the client cannot come out of the server's own lane
              crossed : ∀ {x y z w'} → stepRel inner x (wAnsᵢ w) (just (wAnsₒ w')) z
                      → TraceRel inner z (wAnsᵢ w') (just (cAns (d q v))) y → w ≡ rʷ q v
              crossed {w' = w'} st₃ _ =
                ⊥-elim (comp-atʳ-cross {M₁ = M₂} {M₂ = M₁}
                          {mᵢ = ansʷ w} {mₒ = sansʷ w'} st₃)

          -- Second leg: the server answers on the wire, from the state the query
          -- was asked in (the relay's forward left the server alone).
          two : ∀ {z y sₐ q v} → proj₁ z ≡ sₐ
              → TraceRel inner z (wQryᵢ (qʷ q)) (just (cAns (d q v))) y
              → Answers ∘-serverPort sₐ q v
          two {z} {sₐ = sₐ} {q} {v} eqs t = trace-inv t straight forwards answers
            where
              straight : ∀ {y} → stepRel inner z (wQryᵢ (qʷ q)) (just (cAns (d q v))) y
                       → Answers ∘-serverPort sₐ q v
              straight st₂ =
                ⊥-elim (comp-atˡ-cross {M₁ = M₂} {M₂ = M₁}
                          {mᵢ = qry ∘-serverPort q} {mₒ = R.ansOut q v} st₂)

              -- the server cannot put a query on the relay's lane
              forwards : ∀ {y z' w'} → stepRel inner z (wQryᵢ (qʷ q)) (just (wQryₒ w')) z'
                       → TraceRel inner z' (wQryᵢ w') (just (cAns (d q v))) y
                       → Answers ∘-serverPort sₐ q v
              forwards {w' = w'} st₂ _ =
                ⊥-elim (comp-atˡ-cross {M₁ = M₂} {M₂ = M₁}
                          {mᵢ = qry ∘-serverPort q} {mₒ = qryʷ w'} st₂)

              -- the good shape: the server puts an answer on the wire
              answers : ∀ {y z' w'} → stepRel inner z (wQryᵢ (qʷ q)) (just (wAnsₒ w')) z'
                      → TraceRel inner z' (wAnsᵢ w') (just (cAns (d q v))) y
                      → Answers ∘-serverPort sₐ q v
              answers {z' = z'} {w'} st₂ rest =
                comp-atˡ-just {M₁ = M₂} {M₂ = M₁}
                  {mᵢ = qry ∘-serverPort q} {mₒ = sansʷ w'} st₂ λ st₂' _ →
                    let stₛ = subst (λ a → stepRel M₂ a (qry ∘-serverPort q)
                                             (just (sansʷ w')) (proj₁ z'))
                                    eqs st₂'
                        v' , e = sa stₛ
                    in proj₁ z'
                     , subst (λ x → stepRel M₂ sₐ (qry ∘-serverPort q) (just (sansʷ x))
                                      (proj₁ z'))
                             (three (sansʷ-inj (just-injective e)) rest) stₛ

          -- First leg: the relay forwards the query onto the wire. Any other shape
          -- contradicts `ForwardsQuery` or the wiring.
          one[] : ∀ {s s' q v} → stepRel inner s (cQry (c q)) (just (cAns (d q v))) s'
                → Answers ∘-serverPort (proj₁ s) q v
          one[] {q = q} {v} st₁ =
            comp-atʳ-just {M₁ = M₂} {M₂ = M₁} {mᵢ = R.qryIn q} {mₒ = R.ansOut q v} st₁
              (λ st₁' _ → ⊥-elim (wire≢cod (sym (just-injective (fq st₁')))))

          oneₒ : ∀ {s s' z w q v} → stepRel inner s (cQry (c q)) (just (wQryₒ w)) z
               → TraceRel inner z (wQryᵢ w) (just (cAns (d q v))) s'
               → Answers ∘-serverPort (proj₁ s) q v
          oneₒ {s' = s'} {z} {w} {q} {v} st₁ rest =
            comp-atʳ-just {M₁ = M₂} {M₂ = M₁} {mᵢ = R.qryIn q} {mₒ = qryʷ w} st₁
              λ st₁' eqs →
                two (sym eqs)
                    (subst (λ y → TraceRel inner z (wQryᵢ y) (just (cAns (d q v))) s')
                           (qryʷ-inj (just-injective (fq st₁'))) rest)

          oneᵢ : ∀ {s s' z w q v} → stepRel inner s (cQry (c q)) (just (wAnsₒ w)) z
               → TraceRel inner z (wAnsᵢ w) (just (cAns (d q v))) s'
               → Answers ∘-serverPort (proj₁ s) q v
          oneᵢ {w = w} {q} st₁ _ =
            ⊥-elim (comp-atʳ-cross {M₁ = M₂} {M₂ = M₁}
                      {mᵢ = R.qryIn q} {mₒ = sansʷ w} st₁)

        ∘-sound : ∀ {s q v} → Answers ∘-clientPort s q v → Answers ∘-serverPort (proj₁ s) q v
        ∘-sound (_ , st) = trace-inv st one[] oneₒ oneᵢ

      ∘-routes : Responsive ∘-relay
               → Routing (∘-simˡ {M₁ = M₁} {M₂}) ∘-clientPort ∘-serverPort
      sound    (∘-routes _)   = ∘-sound
      complete (∘-routes rsp) = ∘-complete rsp

    -- The server discipline, transferred up: a relay in front of a server is
    -- itself a server at the client's port. Soundness' `NoInvention` is not
    -- needed here — nothing has to be traced back to the server's step.
    module _ (fq : ForwardsQuery ∘-relay) (fa : ForwardsAnswer ∘-relay)
             (sa : AnswersOnly ∘-serverPort) where
      opaque
        unfolding _⊗₀_ destruct-⊗ ⊗-right-intro ⊗-sym ⊗-combine ⊗-fusion ⊗-right-neutral

        -- Each node's output is forced — the relay puts the query on the wire
        -- (`fq`), the server answers on it (`sa`), the relay forwards that answer
        -- to the client (`fa`) — so the cascade runs to the client's answer and
        -- stops there. The side conditions are what rules out stopping earlier:
        -- a cascade whose last node hands a message to the hidden wire is not a
        -- composite step, since the composite's own output is on `A ⊗ᵀ C`.
        private
          only₃ : ∀ {x y oᵗ w q v'} → w ≡ rʷ q v'
                → TraceRel inner x (wAnsᵢ w) oᵗ y
                → ∃[ v ] Φₒ oᵗ ≡ Φₒ (just (cAns (d q v)))
          only₃ {oᵗ = oᵗ} {w} {q} {v'} eq t = trace-inv t answers forwards crossed
            where
              answers : ∀ {x y} → stepRel inner x (wAnsᵢ w) oᵗ y
                      → ∃[ v ] Φₒ oᵗ ≡ Φₒ (just (cAns (d q v)))
              answers {x} st₃ =
                comp-atʳ {M₁ = M₂} {M₂ = M₁} {mᵢ = ansʷ w} st₃ λ e st₃' _ →
                  v' , trans e (cong (mapₘ (rTag {m = Out}))
                    (fa (subst (λ z → stepRel M₁ (proj₂ x) (ansʷ z) _ _) eq st₃')))

              -- forwarding again instead of answering: `ForwardsAnswer` forbids it
              forwards : ∀ {x y z w'} → stepRel inner x (wAnsᵢ w) (just (wQryₒ w')) z
                       → TraceRel inner z (wQryᵢ w') oᵗ y
                       → ∃[ v ] Φₒ oᵗ ≡ Φₒ (just (cAns (d q v)))
              forwards {x} {w' = w'} st₃ _ =
                comp-atʳ-just {M₁ = M₂} {M₂ = M₁} {mᵢ = ansʷ w} {mₒ = qryʷ w'} st₃
                  (λ st₃' _ → ⊥-elim (wire≢cod (just-injective
                    (fa (subst (λ z → stepRel M₁ (proj₂ x) (ansʷ z) _ _) eq st₃')))))

              crossed : ∀ {x y z w'} → stepRel inner x (wAnsᵢ w) (just (wAnsₒ w')) z
                      → TraceRel inner z (wAnsᵢ w') oᵗ y
                      → ∃[ v ] Φₒ oᵗ ≡ Φₒ (just (cAns (d q v)))
              crossed {w' = w'} st₃ _ =
                ⊥-elim (comp-atʳ-cross {M₁ = M₂} {M₂ = M₁}
                          {mᵢ = ansʷ w} {mₒ = sansʷ w'} st₃)

          only₂ : ∀ {z y oᵗ q} → TraceRel inner z (wQryᵢ (qʷ q)) oᵗ y
                → (∀ {w} → Φₒ oᵗ ≢ Φₒ (just (wAnsₒ w)))
                → ∃[ v ] Φₒ oᵗ ≡ Φₒ (just (cAns (d q v)))
          only₂ {oᵗ = oᵗ} {q} t nwa = trace-inv t straight forwards answers
            where
              straight : ∀ {z y} → stepRel inner z (wQryᵢ (qʷ q)) oᵗ y
                       → ∃[ v ] Φₒ oᵗ ≡ Φₒ (just (cAns (d q v)))
              straight st₂ =
                comp-atˡ {M₁ = M₂} {M₂ = M₁} {mᵢ = qry ∘-serverPort q} st₂ λ e st₂' _ →
                  ⊥-elim (nwa (trans e (cong (mapₘ (sTag {m = Out})) (proj₂ (sa st₂')))))

              -- the server cannot put a query on the relay's lane
              forwards : ∀ {z y z' w'} → stepRel inner z (wQryᵢ (qʷ q)) (just (wQryₒ w')) z'
                       → TraceRel inner z' (wQryᵢ w') oᵗ y
                       → ∃[ v ] Φₒ oᵗ ≡ Φₒ (just (cAns (d q v)))
              forwards {w' = w'} st₂ _ =
                ⊥-elim (comp-atˡ-cross {M₁ = M₂} {M₂ = M₁}
                          {mᵢ = qry ∘-serverPort q} {mₒ = qryʷ w'} st₂)

              answers : ∀ {z y z' w'} → stepRel inner z (wQryᵢ (qʷ q)) (just (wAnsₒ w')) z'
                      → TraceRel inner z' (wAnsᵢ w') oᵗ y
                      → ∃[ v ] Φₒ oᵗ ≡ Φₒ (just (cAns (d q v)))
              answers {w' = w'} st₂ rest =
                comp-atˡ-just {M₁ = M₂} {M₂ = M₁}
                  {mᵢ = qry ∘-serverPort q} {mₒ = sansʷ w'} st₂
                  (λ st₂' _ → only₃ (sansʷ-inj (just-injective (proj₂ (sa st₂')))) rest)

          only₁ : ∀ {s y oᵗ q} → TraceRel inner s (cQry (c q)) oᵗ y
                → (∀ {w} → Φₒ oᵗ ≢ Φₒ (just (wQryₒ w)))
                → (∀ {w} → Φₒ oᵗ ≢ Φₒ (just (wAnsₒ w)))
                → ∃[ v ] Φₒ oᵗ ≡ Φₒ (just (cAns (d q v)))
          only₁ {oᵗ = oᵗ} {q} t nwq nwa = trace-inv t single forwards crossed
            where
              single : ∀ {s y} → stepRel inner s (cQry (c q)) oᵗ y
                     → ∃[ v ] Φₒ oᵗ ≡ Φₒ (just (cAns (d q v)))
              single st₁ =
                comp-atʳ {M₁ = M₂} {M₂ = M₁} {mᵢ = R.qryIn q} st₁ λ e st₁' _ →
                  ⊥-elim (nwq (trans e (cong (mapₘ (rTag {m = Out})) (fq st₁'))))

              forwards : ∀ {s y z w} → stepRel inner s (cQry (c q)) (just (wQryₒ w)) z
                       → TraceRel inner z (wQryᵢ w) oᵗ y
                       → ∃[ v ] Φₒ oᵗ ≡ Φₒ (just (cAns (d q v)))
              forwards {y = y} {z} {w} st₁ rest =
                comp-atʳ-just {M₁ = M₂} {M₂ = M₁} {mᵢ = R.qryIn q} {mₒ = qryʷ w} st₁
                  (λ st₁' _ → only₂ (subst (λ x → TraceRel inner z (wQryᵢ x) oᵗ y)
                                           (qryʷ-inj (just-injective (fq st₁'))) rest) nwa)

              crossed : ∀ {s y z w} → stepRel inner s (cQry (c q)) (just (wAnsₒ w)) z
                      → TraceRel inner z (wAnsᵢ w) oᵗ y
                      → ∃[ v ] Φₒ oᵗ ≡ Φₒ (just (cAns (d q v)))
              crossed {w = w} st₁ _ =
                ⊥-elim (comp-atʳ-cross {M₁ = M₂} {M₂ = M₁}
                          {mᵢ = R.qryIn q} {mₒ = sansʷ w} st₁)

        -- Every position the composite can emit on: `nothing` and the two
        -- non-answer ones make `only₁`'s side conditions hold by `()`, and its
        -- verdict then contradicts them; at the answer position it pins the
        -- payload, since the translations are injections.
        ∘-answers-only : AnswersOnly ∘-clientPort
        ∘-answers-only {o = nothing} st with only₁ st (λ ()) (λ ())
        ... | _ , ()
        ∘-answers-only {o = just (inj₁ _)} st with only₁ st (λ ()) (λ ())
        ... | _ , ()
        ∘-answers-only {o = just (inj₂ _)} st with only₁ st (λ ()) (λ ())
        ... | v , refl = v , refl

      ∘-server : Responsive ∘-relay → CanAnswer ∘-serverPort → Server ∘-clientPort
      ∘-server rsp ca = ∘-answers-only
                      , λ s q → let v , a = ca (proj₁ s) q in v , ∘-complete rsp a

--------------------------------------------------------------------------------
-- Rewiring layers
--
-- A component sits behind pure rewiring: `modifyStepRel` translation layers, and
-- the stateless machines `TotalFunctionMachine'` builds (`id`, the unitors, the
-- associators). Both are crossed for free — the translation layer
-- definitionally, a rewiring machine because it forwards every message and
-- nothing else.
--
-- The translations are explicit arguments throughout: a machine's message type is
-- its channel's, so none of them is recoverable from the types below.

module _ (p : ∀ {m} → C ⊗₀ D ᵀ [ m ]⇒[ m ] A ⊗₀ B ᵀ) {N : Machine A B}
         (r : Port (modifyStepRel p N) Q V) where

  -- A port travels *down* the layer: the wrapper's step relation translates its
  -- own messages into the core's, so this direction needs no inverse of `app p`.
  modify-port : Port N Q V
  modify-port = record { qry = λ q → app {mᵢ = In} p (qry r q)
                       ; ans = λ q v → app {mᵢ = Out} p (ans r q v) }

  modify-routes : Routing (modify-sim {p = p} {N}) r modify-port
  sound    modify-routes (s' , st) = s' , unmodify {p = p} {N} st
  complete modify-routes (s' , st) = s' , remodify {p = p} {N} st

  -- The `AnswersOnly` transport needs the translation injective: the core's
  -- verdict is about `mapₘ (app p) o`, the discipline about the `o` the wrapper
  -- emitted.
  modify-answers-only : (∀ {x y} → app {mᵢ = Out} p x ≡ app {mᵢ = Out} p y → x ≡ y)
                      → AnswersOnly modify-port → AnswersOnly r
  modify-answers-only _   ao {o = nothing} st
    with ao {o = nothing} (unmodify {p = p} {N} {o = nothing} st)
  ... | _ , ()
  modify-answers-only inj ao {o = just x} st
    with ao {o = just (app {mᵢ = Out} p x)} (unmodify {p = p} {N} {o = just x} st)
  ... | v , e = v , cong just (inj (just-injective e))

  modify-can-answer : CanAnswer modify-port → CanAnswer r
  modify-can-answer ca s q = let v , a = ca s q in v , complete modify-routes a

  modify-server : (∀ {x y} → app {mᵢ = Out} p x ≡ app {mᵢ = Out} p y → x ≡ y)
                → Server modify-port → Server r
  modify-server inj (ao , ca) = modify-answers-only inj ao , modify-can-answer ca

--------------------------------------------------------------------------------
-- Machines that only forward
--
-- A wiring layer sends every domain message on to its codomain and every
-- codomain message back to its domain, and does nothing else: that is
-- `Through M fwd bwd`, at the very translation a `TotalFunctionMachine'` over
-- `fwd`/`bwd` carries. It is all the relay conditions below need, and it is
-- closed under `_⊗₁_` and `_∘_` — so a whole nest of rewiring machines
-- (`mergeᴹ`/`splitᴹ` and the unitors, associators and `id` they are built from)
-- is `Through`, one closure step per combinator.

record Through (M : Machine A B) (fwd : A [ In ]⇒[ In ] B)
               (bwd : B [ Out ]⇒[ Out ] A) : Set where
  field
    emits : ∀ {s i o s'} → stepRel M s i o s' → o ≡ just (tfm-app fwd bwd i)
    steps : ∀ s i → ∃[ s' ] stepRel M s i (just (tfm-app fwd bwd i)) s'

open Through public

tfm-through : (fwd : A [ In ]⇒[ In ] B) (bwd : B [ Out ]⇒[ Out ] A)
            → Through (TotalFunctionMachine' fwd bwd) fwd bwd
emits (tfm-through fwd bwd)   = tfm-det fwd bwd
steps (tfm-through _   _) _ _ = tt , refl

--------------------------------------------------------------------------------
-- Forwarding, closed under the tensor
--
-- Each factor forwards its own lane and a tensor step is one factor's step, so
-- nothing is assumed: the tensor's translation *is* the factors', lane by lane.

module _ {M₁ : Machine A B} {M₂ : Machine C D}
         {f₁ : A [ In ]⇒[ In ] B} {b₁ : B [ Out ]⇒[ Out ] A}
         {f₂ : C [ In ]⇒[ In ] D} {b₂ : D [ Out ]⇒[ Out ] C}
         (t₁ : Through M₁ f₁ b₁) (t₂ : Through M₂ f₂ b₂) where

  private
    -- the embeddings, with every channel pinned: a message type does not
    -- determine the tensor's other factor, so bare `⊗₁-inˡ/ʳ` would leave it open
    inˡ : ∀ {m} → Msg M₁ m → Msg (M₁ ⊗₁ M₂) m
    inˡ {m} = ⊗₁-inˡ {A} {B} {C} {D} {m}

    inʳ : ∀ {m} → Msg M₂ m → Msg (M₁ ⊗₁ M₂) m
    inʳ {m} = ⊗₁-inʳ {A} {B} {C} {D} {m}

    t⊗ : Msg (M₁ ⊗₁ M₂) In → Msg (M₁ ⊗₁ M₂) Out
    t⊗ = tfm-app (⊗-combine f₁ f₂) (⊗-combine b₁ b₂)

  opaque
    unfolding _⊗₀_ ⊗-sym ⊗-combine ⊗₁-inˡ ⊗₁-inʳ

    private
      t⊗-inˡ : ∀ x → t⊗ (inˡ {In} x) ≡ inˡ {Out} (tfm-app f₁ b₁ x)
      t⊗-inˡ (inj₁ _) = refl
      t⊗-inˡ (inj₂ _) = refl

      t⊗-inʳ : ∀ x → t⊗ (inʳ {In} x) ≡ inʳ {Out} (tfm-app f₂ b₂ x)
      t⊗-inʳ (inj₁ _) = refl
      t⊗-inʳ (inj₂ _) = refl

      emitsˡ : ∀ {s x o s'} → stepRel (M₁ ⊗₁ M₂) s (inˡ {In} x) o s'
             → o ≡ just (inˡ {Out} (tfm-app f₁ b₁ x))
      emitsˡ {s} {x} {nothing} {s'} st =
        comp-atˡ {M₁ = M₁} {M₂} (⊗₁-compˡ {M₁ = M₁} {M₂} {i = x} {o = nothing} st) go
        where
          go : ∀ {mₒ} → nothing ≡ mapₘ (tagˡ {A} {B} {C} {D} {Out}) mₒ
             → stepRel M₁ (proj₁ s) x mₒ (proj₁ s') → proj₂ s ≡ proj₂ s'
             → nothing ≡ just (inˡ {Out} (tfm-app f₁ b₁ x))
          go {just _}  ()
          go {nothing} _ st' _ with emits t₁ st'
          ... | ()
      emitsˡ {s} {x} {just y} {s'} st = go (⊗₁-in-split {M₁ = M₁} {M₂ = M₂} {m = Out} y)
        where
          at : ∀ {z} → y ≡ z → stepRel (M₁ ⊗₁ M₂) s (inˡ {In} x) (just z) s'
          at e = subst (λ z → stepRel (M₁ ⊗₁ M₂) s (inˡ {In} x) (just z) s') e st

          go : (∃[ w ] y ≡ inˡ {Out} w) ⊎ (∃[ w ] y ≡ inʳ {Out} w)
             → just y ≡ just (inˡ {Out} (tfm-app f₁ b₁ x))
          go (inj₁ (w , e)) =
            comp-atˡ-just {M₁ = M₁} {M₂}
              (⊗₁-compˡ {M₁ = M₁} {M₂} {i = x} {o = just w} (at e))
              (λ st' _ → trans (cong just e)
                               (cong (λ z → just (inˡ {Out} z))
                                     (just-injective (emits t₁ st'))))
          go (inj₂ (w , e)) =
            ⊥-elim (comp-atˡ-cross {M₁ = M₁} {M₂}
                      (⊗₁-compˡʳ {M₁ = M₁} {M₂} {i = x} {o = just w} (at e)))

      emitsʳ : ∀ {s x o s'} → stepRel (M₁ ⊗₁ M₂) s (inʳ {In} x) o s'
             → o ≡ just (inʳ {Out} (tfm-app f₂ b₂ x))
      emitsʳ {s} {x} {nothing} {s'} st =
        comp-atʳ {M₁ = M₁} {M₂} (⊗₁-compʳ {M₁ = M₁} {M₂} {i = x} {o = nothing} st) go
        where
          go : ∀ {mₒ} → nothing ≡ mapₘ (tagʳ {A} {B} {C} {D} {Out}) mₒ
             → stepRel M₂ (proj₂ s) x mₒ (proj₂ s') → proj₁ s ≡ proj₁ s'
             → nothing ≡ just (inʳ {Out} (tfm-app f₂ b₂ x))
          go {just _}  ()
          go {nothing} _ st' _ with emits t₂ st'
          ... | ()
      emitsʳ {s} {x} {just y} {s'} st = go (⊗₁-in-split {M₁ = M₁} {M₂ = M₂} {m = Out} y)
        where
          at : ∀ {z} → y ≡ z → stepRel (M₁ ⊗₁ M₂) s (inʳ {In} x) (just z) s'
          at e = subst (λ z → stepRel (M₁ ⊗₁ M₂) s (inʳ {In} x) (just z) s') e st

          go : (∃[ w ] y ≡ inˡ {Out} w) ⊎ (∃[ w ] y ≡ inʳ {Out} w)
             → just y ≡ just (inʳ {Out} (tfm-app f₂ b₂ x))
          go (inj₁ (w , e)) =
            ⊥-elim (comp-atʳ-cross {M₁ = M₁} {M₂}
                      (⊗₁-compʳˡ {M₁ = M₁} {M₂} {i = x} {o = just w} (at e)))
          go (inj₂ (w , e)) =
            comp-atʳ-just {M₁ = M₁} {M₂}
              (⊗₁-compʳ {M₁ = M₁} {M₂} {i = x} {o = just w} (at e))
              (λ st' _ → trans (cong just e)
                               (cong (λ z → just (inʳ {Out} z))
                                     (just-injective (emits t₂ st'))))

      emits⊗ : ∀ {s i o s'} → stepRel (M₁ ⊗₁ M₂) s i o s' → o ≡ just (t⊗ i)
      emits⊗ {s} {i} {o} {s'} st = go (⊗₁-in-split {M₁ = M₁} {M₂ = M₂} {m = In} i)
        where
          at : ∀ {z} → i ≡ z → stepRel (M₁ ⊗₁ M₂) s z o s'
          at e = subst (λ z → stepRel (M₁ ⊗₁ M₂) s z o s') e st

          go : (∃[ x ] i ≡ inˡ {In} x) ⊎ (∃[ x ] i ≡ inʳ {In} x)
             → o ≡ just (t⊗ i)
          go (inj₁ (x , e)) =
            trans (emitsˡ (at e))
                  (sym (cong just (trans (cong t⊗ e) (t⊗-inˡ x))))
          go (inj₂ (x , e)) =
            trans (emitsʳ (at e))
                  (sym (cong just (trans (cong t⊗ e) (t⊗-inʳ x))))

      steps⊗ : ∀ s i → ∃[ s' ] stepRel (M₁ ⊗₁ M₂) s i (just (t⊗ i)) s'
      steps⊗ s i = go (⊗₁-in-split {M₁ = M₁} {M₂ = M₂} {m = In} i)
        where
          go : (∃[ x ] i ≡ inˡ {In} x) ⊎ (∃[ x ] i ≡ inʳ {In} x)
             → ∃[ s' ] stepRel (M₁ ⊗₁ M₂) s i (just (t⊗ i)) s'
          go (inj₁ (x , e)) =
            let sₐ' , st = steps t₁ (proj₁ s) x in
            (sₐ' , proj₂ s)
            , subst₂ (λ a b → stepRel (M₁ ⊗₁ M₂) s a b (sₐ' , proj₂ s)) (sym e)
                     (cong just (sym (trans (cong t⊗ e) (t⊗-inˡ x))))
                     (⊗₁-mkˡ {M₁ = M₁} {M₂} {i = x}
                             {o = just (tfm-app f₁ b₁ x)} (compL st))
          go (inj₂ (x , e)) =
            let sᵦ' , st = steps t₂ (proj₂ s) x in
            (proj₁ s , sᵦ')
            , subst₂ (λ a b → stepRel (M₁ ⊗₁ M₂) s a b (proj₁ s , sᵦ')) (sym e)
                     (cong just (sym (trans (cong t⊗ e) (t⊗-inʳ x))))
                     (⊗₁-mkʳ {M₁ = M₁} {M₂} {i = x}
                             {o = just (tfm-app f₂ b₂ x)} (compR st))

  ⊗₁-through : Through (M₁ ⊗₁ M₂) (⊗-combine f₁ f₂) (⊗-combine b₁ b₂)
  emits ⊗₁-through = emits⊗
  steps ⊗₁-through = steps⊗

--------------------------------------------------------------------------------
-- Forwarding, closed under composition
--
-- A composite step is a cascade, and forwarding forces every node's output: a
-- message entering on one side crosses `M₂` then `M₁` (or the other way round)
-- and leaves on the other side, so the cascade is exactly two nodes long. The
-- shapes that would make it shorter or longer contradict `emits` of a component
-- or the wiring itself.

module _ {M₁ : Machine B C} {M₂ : Machine A B}
         {f₁ : B [ In ]⇒[ In ] C} {b₁ : C [ Out ]⇒[ Out ] B}
         {f₂ : A [ In ]⇒[ In ] B} {b₂ : B [ Out ]⇒[ Out ] A}
         (t₁ : Through M₁ f₁ b₁) (t₂ : Through M₂ f₂ b₂) where

  private
    -- the machine `_∘_` traces over, and the two translation layers a node's
    -- output crosses (see `∘-routes`, which names these the same way)
    inner : Machine (A ⊗₀ B) (C ⊗₀ B)
    inner = modifyStepRel (∘-reshuffle {A} {B} {C}) (M₂ ⊗₁ M₁)

    Φₒ : Maybe (Msg inner Out) → Maybe (modeType Out ((A ⊗ᵀ B) ⊗₀ (B ⊗ᵀ C)))
    Φₒ o = mapₘ (app {mᵢ = Out} (⊗₁-msg {A} {B} {B} {C}))
                (mapₘ (app {mᵢ = Out} (∘-reshuffle {A} {B} {C})) o)

    sTag : ∀ {m} → Msg M₂ m → modeType m ((A ⊗ᵀ B) ⊗₀ (B ⊗ᵀ C))
    sTag {m} = tagˡ {A} {B} {B} {C} {m}

    rTag : ∀ {m} → Msg M₁ m → modeType m ((A ⊗ᵀ B) ⊗₀ (B ⊗ᵀ C))
    rTag {m} = tagʳ {A} {B} {B} {C} {m}

    t∘ : Msg (M₁ ∘ M₂) In → Msg (M₁ ∘ M₂) Out
    t∘ = tfm-app (f₂ ⇒ₜ f₁) (b₁ ⇒ₜ b₂)

    -- the composite's own four positions, and the same as the cascade sees them
    dIn : Channel.inType A → Msg (M₁ ∘ M₂) In
    dIn x = ϵ ⊗R ↑ᵢ x

    cIn : Channel.outType C → Msg (M₁ ∘ M₂) In
    cIn x = L⊗ (ϵ ᵗ¹) ↑ₒ x

    dOut : Channel.outType A → Msg (M₁ ∘ M₂) Out
    dOut x = ϵ ⊗R ↑ₒ x

    cOut : Channel.inType C → Msg (M₁ ∘ M₂) Out
    cOut x = L⊗ (ϵ ᵗ¹) ↑ᵢ x

    iDIn : Channel.inType A → Msg inner In
    iDIn x = (ϵ ⊗R) ⊗R ↑ᵢ x

    iCIn : Channel.outType C → Msg inner In
    iCIn x = L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ x

    iDOut : Channel.outType A → Msg inner Out
    iDOut x = (ϵ ⊗R) ⊗R ↑ₒ x

    iCOut : Channel.inType C → Msg inner Out
    iCOut x = L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ x

    -- the hidden wire, where the cascade's joints sit
    wQryₒ : Channel.outType B → Msg inner Out
    wQryₒ x = (L⊗ ϵ) ⊗R ↑ₒ x

    wQryᵢ : Channel.outType B → Msg inner In
    wQryᵢ x = L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹ ↑ᵢ x

    wAnsₒ : Channel.inType B → Msg inner Out
    wAnsₒ x = L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹ ↑ₒ x

    wAnsᵢ : Channel.inType B → Msg inner In
    wAnsᵢ x = (L⊗ ϵ) ⊗R ↑ᵢ x

    -- the components' own positions on the wire and on their outer boundary
    m₁DIn : Channel.inType B → Msg M₁ In
    m₁DIn x = ϵ ⊗R ↑ᵢ x

    m₁DOut : Channel.outType B → Msg M₁ Out
    m₁DOut x = ϵ ⊗R ↑ₒ x

    m₁CIn : Channel.outType C → Msg M₁ In
    m₁CIn x = L⊗ (ϵ ᵗ¹) ↑ₒ x

    m₁COut : Channel.inType C → Msg M₁ Out
    m₁COut x = L⊗ (ϵ ᵗ¹) ↑ᵢ x

    m₂DIn : Channel.inType A → Msg M₂ In
    m₂DIn x = ϵ ⊗R ↑ᵢ x

    m₂DOut : Channel.outType A → Msg M₂ Out
    m₂DOut x = ϵ ⊗R ↑ₒ x

    m₂CIn : Channel.outType B → Msg M₂ In
    m₂CIn x = L⊗ (ϵ ᵗ¹) ↑ₒ x

    m₂COut : Channel.inType B → Msg M₂ Out
    m₂COut x = L⊗ (ϵ ᵗ¹) ↑ᵢ x

  opaque
    unfolding _⊗₀_ destruct-⊗ ⊗-right-intro ⊗-sym ⊗-combine ⊗-fusion ⊗-right-neutral

    private
      -- positions are injective and pairwise distinct, and each component's
      -- translation sends one boundary to the other: `refl`/absurd once
      -- Channel.Core's tensor is unfolded
      m₁DOut-inj : ∀ {x y} → m₁DOut x ≡ m₁DOut y → x ≡ y
      m₁DOut-inj refl = refl

      m₂COut-inj : ∀ {x y} → m₂COut x ≡ m₂COut y → x ≡ y
      m₂COut-inj refl = refl

      wire≢cod₁ : ∀ {x z} → m₁DOut x ≡ m₁COut z → ⊥
      wire≢cod₁ ()

      wire≢dom₂ : ∀ {x z} → m₂COut x ≡ m₂DOut z → ⊥
      wire≢dom₂ ()

      in-split : ∀ i → (∃[ x ] i ≡ dIn x) ⊎ (∃[ y ] i ≡ cIn y)
      in-split (inj₁ x) = inj₁ (x , refl)
      in-split (inj₂ y) = inj₂ (y , refl)

      -- Second leg of a query coming down from the codomain: `M₂` takes it off
      -- the wire and puts it out on the composite's domain.
      onlyᶜ₂ : ∀ {s z oᵗ w} → TraceRel inner s (wQryᵢ w) oᵗ z
             → (∀ {w'} → Φₒ oᵗ ≢ Φₒ (just (wQryₒ w')))
             → (∀ {w'} → Φₒ oᵗ ≢ Φₒ (just (wAnsₒ w')))
             → Φₒ oᵗ ≡ Φₒ (just (iDOut (app b₂ w)))
      onlyᶜ₂ {oᵗ = oᵗ} {w} t _ _ = trace-inv t single forwards crossed
        where
          single : ∀ {s z} → stepRel inner s (wQryᵢ w) oᵗ z
                 → Φₒ oᵗ ≡ Φₒ (just (iDOut (app b₂ w)))
          single st = comp-atˡ {M₁ = M₂} {M₂ = M₁} {mᵢ = m₂CIn w} st λ e st' _ →
            trans e (cong (mapₘ (sTag {m = Out})) (emits t₂ st'))

          -- the layer behind cannot put a message on the front one's lane
          forwards : ∀ {s z z' w'} → stepRel inner s (wQryᵢ w) (just (wQryₒ w')) z'
                   → TraceRel inner z' (wQryᵢ w') oᵗ z
                   → Φₒ oᵗ ≡ Φₒ (just (iDOut (app b₂ w)))
          forwards {w' = w'} st _ =
            ⊥-elim (comp-atˡ-cross {M₁ = M₂} {M₂ = M₁}
                      {mᵢ = m₂CIn w} {mₒ = m₁DOut w'} st)

          -- nor send the query back up the wire it came down
          crossed : ∀ {s z z' w'} → stepRel inner s (wQryᵢ w) (just (wAnsₒ w')) z'
                  → TraceRel inner z' (wAnsᵢ w') oᵗ z
                  → Φₒ oᵗ ≡ Φₒ (just (iDOut (app b₂ w)))
          crossed {w' = w'} st _ =
            comp-atˡ-just {M₁ = M₂} {M₂ = M₁} {mᵢ = m₂CIn w} {mₒ = m₂COut w'} st
              (λ st' _ → ⊥-elim (wire≢dom₂ (just-injective (emits t₂ st'))))

      -- First leg: `M₁` puts the query on the wire, and nothing else.
      onlyᶜ : ∀ {s z oᵗ y} → TraceRel inner s (iCIn y) oᵗ z
            → (∀ {w'} → Φₒ oᵗ ≢ Φₒ (just (wQryₒ w')))
            → (∀ {w'} → Φₒ oᵗ ≢ Φₒ (just (wAnsₒ w')))
            → Φₒ oᵗ ≡ Φₒ (just (iDOut (app b₂ (app b₁ y))))
      onlyᶜ {oᵗ = oᵗ} {y} t nwq nwa = trace-inv t single forwards crossed
        where
          single : ∀ {s z} → stepRel inner s (iCIn y) oᵗ z
                 → Φₒ oᵗ ≡ Φₒ (just (iDOut (app b₂ (app b₁ y))))
          single st = comp-atʳ {M₁ = M₂} {M₂ = M₁} {mᵢ = m₁CIn y} st λ e st' _ →
            ⊥-elim (nwq (trans e (cong (mapₘ (rTag {m = Out})) (emits t₁ st'))))

          forwards : ∀ {s z z' w} → stepRel inner s (iCIn y) (just (wQryₒ w)) z'
                   → TraceRel inner z' (wQryᵢ w) oᵗ z
                   → Φₒ oᵗ ≡ Φₒ (just (iDOut (app b₂ (app b₁ y))))
          forwards {w = w} st rest =
            comp-atʳ-just {M₁ = M₂} {M₂ = M₁} {mᵢ = m₁CIn y} {mₒ = m₁DOut w} st
              λ st' _ → subst (λ z → Φₒ oᵗ ≡ Φₒ (just (iDOut (app b₂ z))))
                              (m₁DOut-inj (just-injective (emits t₁ st')))
                              (onlyᶜ₂ rest nwq nwa)

          crossed : ∀ {s z z' w} → stepRel inner s (iCIn y) (just (wAnsₒ w)) z'
                  → TraceRel inner z' (wAnsᵢ w) oᵗ z
                  → Φₒ oᵗ ≡ Φₒ (just (iDOut (app b₂ (app b₁ y))))
          crossed {w = w} st _ =
            ⊥-elim (comp-atʳ-cross {M₁ = M₂} {M₂ = M₁}
                      {mᵢ = m₁CIn y} {mₒ = m₂COut w} st)

      -- Second leg of a message coming up from the domain: `M₁` takes it off the
      -- wire and puts it out on the composite's codomain.
      onlyᵈ₂ : ∀ {s z oᵗ w} → TraceRel inner s (wAnsᵢ w) oᵗ z
             → (∀ {w'} → Φₒ oᵗ ≢ Φₒ (just (wQryₒ w')))
             → (∀ {w'} → Φₒ oᵗ ≢ Φₒ (just (wAnsₒ w')))
             → Φₒ oᵗ ≡ Φₒ (just (iCOut (app f₁ w)))
      onlyᵈ₂ {oᵗ = oᵗ} {w} t _ _ = trace-inv t single forwards crossed
        where
          single : ∀ {s z} → stepRel inner s (wAnsᵢ w) oᵗ z
                 → Φₒ oᵗ ≡ Φₒ (just (iCOut (app f₁ w)))
          single st = comp-atʳ {M₁ = M₂} {M₂ = M₁} {mᵢ = m₁DIn w} st λ e st' _ →
            trans e (cong (mapₘ (rTag {m = Out})) (emits t₁ st'))

          forwards : ∀ {s z z' w'} → stepRel inner s (wAnsᵢ w) (just (wQryₒ w')) z'
                   → TraceRel inner z' (wQryᵢ w') oᵗ z
                   → Φₒ oᵗ ≡ Φₒ (just (iCOut (app f₁ w)))
          forwards {w' = w'} st _ =
            comp-atʳ-just {M₁ = M₂} {M₂ = M₁} {mᵢ = m₁DIn w} {mₒ = m₁DOut w'} st
              (λ st' _ → ⊥-elim (wire≢cod₁ (just-injective (emits t₁ st'))))

          crossed : ∀ {s z z' w'} → stepRel inner s (wAnsᵢ w) (just (wAnsₒ w')) z'
                  → TraceRel inner z' (wAnsᵢ w') oᵗ z
                  → Φₒ oᵗ ≡ Φₒ (just (iCOut (app f₁ w)))
          crossed {w' = w'} st _ =
            ⊥-elim (comp-atʳ-cross {M₁ = M₂} {M₂ = M₁}
                      {mᵢ = m₁DIn w} {mₒ = m₂COut w'} st)

      -- First leg: `M₂` puts the message on the wire, and nothing else.
      onlyᵈ : ∀ {s z oᵗ x} → TraceRel inner s (iDIn x) oᵗ z
            → (∀ {w'} → Φₒ oᵗ ≢ Φₒ (just (wQryₒ w')))
            → (∀ {w'} → Φₒ oᵗ ≢ Φₒ (just (wAnsₒ w')))
            → Φₒ oᵗ ≡ Φₒ (just (iCOut (app f₁ (app f₂ x))))
      onlyᵈ {oᵗ = oᵗ} {x} t nwq nwa = trace-inv t single forwards crossed
        where
          single : ∀ {s z} → stepRel inner s (iDIn x) oᵗ z
                 → Φₒ oᵗ ≡ Φₒ (just (iCOut (app f₁ (app f₂ x))))
          single st = comp-atˡ {M₁ = M₂} {M₂ = M₁} {mᵢ = m₂DIn x} st λ e st' _ →
            ⊥-elim (nwa (trans e (cong (mapₘ (sTag {m = Out})) (emits t₂ st'))))

          forwards : ∀ {s z z' w} → stepRel inner s (iDIn x) (just (wQryₒ w)) z'
                   → TraceRel inner z' (wQryᵢ w) oᵗ z
                   → Φₒ oᵗ ≡ Φₒ (just (iCOut (app f₁ (app f₂ x))))
          forwards {w = w} st _ =
            ⊥-elim (comp-atˡ-cross {M₁ = M₂} {M₂ = M₁}
                      {mᵢ = m₂DIn x} {mₒ = m₁DOut w} st)

          crossed : ∀ {s z z' w} → stepRel inner s (iDIn x) (just (wAnsₒ w)) z'
                  → TraceRel inner z' (wAnsᵢ w) oᵗ z
                  → Φₒ oᵗ ≡ Φₒ (just (iCOut (app f₁ (app f₂ x))))
          crossed {w = w} st rest =
            comp-atˡ-just {M₁ = M₂} {M₂ = M₁} {mᵢ = m₂DIn x} {mₒ = m₂COut w} st
              λ st' _ → subst (λ z → Φₒ oᵗ ≡ Φₒ (just (iCOut (app f₁ z))))
                              (m₂COut-inj (just-injective (emits t₂ st')))
                              (onlyᵈ₂ rest nwq nwa)

      -- Every position the composite can emit on: `nothing` and the position on
      -- the side the message came in on make the side conditions hold by `()`,
      -- and the verdict then contradicts them; at the far side it pins the
      -- payload, since the translations are injections.
      emitsᵈ : ∀ {s s' x} o → stepRel (M₁ ∘ M₂) s (dIn x) o s'
             → o ≡ just (cOut (app f₁ (app f₂ x)))
      emitsᵈ nothing         st with onlyᵈ st (λ ()) (λ ())
      ... | ()
      emitsᵈ (just (inj₁ _)) st with onlyᵈ st (λ ()) (λ ())
      ... | ()
      emitsᵈ (just (inj₂ _)) st with onlyᵈ st (λ ()) (λ ())
      ... | refl = refl

      emitsᶜ : ∀ {s s' y} o → stepRel (M₁ ∘ M₂) s (cIn y) o s'
             → o ≡ just (dOut (app b₂ (app b₁ y)))
      emitsᶜ nothing         st with onlyᶜ st (λ ()) (λ ())
      ... | ()
      emitsᶜ (just (inj₂ _)) st with onlyᶜ st (λ ()) (λ ())
      ... | ()
      emitsᶜ (just (inj₁ _)) st with onlyᶜ st (λ ()) (λ ())
      ... | refl = refl

      t∘-dom : ∀ x → t∘ (dIn x) ≡ cOut (app f₁ (app f₂ x))
      t∘-dom _ = refl

      t∘-cod : ∀ y → t∘ (cIn y) ≡ dOut (app b₂ (app b₁ y))
      t∘-cod _ = refl

      emits∘ : ∀ {s i o s'} → stepRel (M₁ ∘ M₂) s i o s' → o ≡ just (t∘ i)
      emits∘ {s} {i} {o} {s'} st = go (in-split i)
        where
          at : ∀ {z} → i ≡ z → stepRel (M₁ ∘ M₂) s z o s'
          at e = subst (λ z → stepRel (M₁ ∘ M₂) s z o s') e st

          go : (∃[ x ] i ≡ dIn x) ⊎ (∃[ y ] i ≡ cIn y) → o ≡ just (t∘ i)
          go (inj₁ (x , e)) =
            trans (emitsᵈ o (at e)) (sym (cong just (trans (cong t∘ e) (t∘-dom x))))
          go (inj₂ (y , e)) =
            trans (emitsᶜ o (at e)) (sym (cong just (trans (cong t∘ e) (t∘-cod y))))

      -- Construction: two nodes, one per component, in the order the message
      -- crosses them.
      steps∘ : ∀ s i → ∃[ s' ] stepRel (M₁ ∘ M₂) s i (just (t∘ i)) s'
      steps∘ s i = go (in-split i)
        where
          go : (∃[ x ] i ≡ dIn x) ⊎ (∃[ y ] i ≡ cIn y)
             → ∃[ s' ] stepRel (M₁ ∘ M₂) s i (just (t∘ i)) s'
          go (inj₁ (x , refl)) =
            let sₐ' , n₁ = steps t₂ (proj₁ s) (m₂DIn x)
                sᵦ' , n₂ = steps t₁ (proj₂ s) (m₁DIn (app f₂ x))
            in (sₐ' , sᵦ') , (compL n₁ Trace∷ᵢ Trace[ compR n₂ ])
          go (inj₂ (y , refl)) =
            let sᵦ' , n₁ = steps t₁ (proj₂ s) (m₁CIn y)
                sₐ' , n₂ = steps t₂ (proj₁ s) (m₂CIn (app b₁ y))
            in (sₐ' , sᵦ') , (compR n₁ Trace∷ₒ Trace[ compL n₂ ])

  ∘-through : Through (M₁ ∘ M₂) (f₂ ⇒ₜ f₁) (b₁ ⇒ₜ b₂)
  emits ∘-through = emits∘
  steps ∘-through = steps∘

--------------------------------------------------------------------------------
-- A forwarding layer relays everything
--
-- The conditions, for whatever positions a relay on the layer names — as long
-- as they are the ones the layer's own translation connects.

module _ {M : Machine A B} {fwd : A [ In ]⇒[ In ] B} {bwd : B [ Out ]⇒[ Out ] A}
         (th : Through M fwd bwd) (R : Relay M Q V) (let open Relay R)
         (hq : ∀ q → tfm-app fwd bwd (qryIn q) ≡ qryOut q)
         (ha : ∀ q v → tfm-app fwd bwd (ansIn q v) ≡ ansOut q v) where

  through-forwards-query : ForwardsQuery R
  through-forwards-query {q = q} st = trans (emits th st) (cong just (hq q))

  through-forwards-answer : ForwardsAnswer R
  through-forwards-answer {q = q} {v} st = trans (emits th st) (cong just (ha q v))

  through-responsive : Responsive R
  through-responsive =
      (λ s q → let s' , st = steps th s (qryIn q)
               in s' , subst (λ z → stepRel M s (qryIn q) (just z) s') (hq q) st)
    , (λ s q v → let s' , st = steps th s (ansIn q v)
                 in s' , subst (λ z → stepRel M s (ansIn q v) (just z) s') (ha q v) st)

  -- the client's answer is the translation of what came in, and the translation
  -- is injective, so what came in was this very query's answer
  through-no-invention : (∀ {x y} → tfm-app fwd bwd x ≡ tfm-app fwd bwd y → x ≡ y)
                       → NoInvention R
  through-no-invention inj {q = q} {v} st =
    sym (inj (trans (ha q v) (just-injective (emits th st))))

--------------------------------------------------------------------------------
-- A forwarding layer in front of a server
--
-- Crossed at no cost: the wire positions are where the layer's own translation
-- sends the client's, which discharges the relay conditions generically and
-- leaves only the server's own discipline.

module _ {M₁ : Machine B C} {fwd : B [ In ]⇒[ In ] C} {bwd : C [ Out ]⇒[ Out ] B}
         (th : Through M₁ fwd bwd) {M₂ : Machine A B}
         (c : Q → Channel.outType C) (rʷ : Q → V → Channel.inType B) where

  through-qryʷ : Q → Channel.outType B
  through-qryʷ q = app bwd (c q)

  through-ansᶜ : Q → V → Channel.inType C
  through-ansᶜ q v = app fwd (rʷ q v)

  -- the two ports of the crossing
  through-clientPort : Port (M₁ ∘ M₂) Q V
  through-clientPort = ∘-clientPort c through-ansᶜ

  through-serverPort : Port M₂ Q V
  through-serverPort = ∘-serverPort {M₁ = M₁} c through-ansᶜ through-qryʷ rʷ

  private
    R : Relay M₁ Q V
    R = ∘-relay {M₂ = M₂} c through-ansᶜ through-qryʷ rʷ

    opaque
      unfolding _⊗₀_ ⊗-right-intro ⊗-sym ⊗-combine

      hq : ∀ q → tfm-app fwd bwd (Relay.qryIn R q) ≡ Relay.qryOut R q
      hq _ = refl

      ha : ∀ q v → tfm-app fwd bwd (Relay.ansIn R q v) ≡ Relay.ansOut R q v
      ha _ _ = refl

  through-∘-routes : (∀ {x y} → app fwd x ≡ app fwd y → x ≡ y)
                   → (∀ {x y} → app bwd x ≡ app bwd y → x ≡ y)
                   → AnswersOnly through-serverPort
                   → Routing (∘-simˡ {M₁ = M₁} {M₂}) through-clientPort through-serverPort
  through-∘-routes fi bi sa =
    ∘-routes c through-ansᶜ through-qryʷ rʷ (through-forwards-query th R hq ha)
             (through-forwards-answer th R hq ha)
             (through-no-invention th R hq ha (tfm-app-inj fwd bwd fi bi)) sa
             (through-responsive th R hq ha)

  -- the client's answer is invented by nobody but the server, so `NoInvention`
  -- (and with it the injectivity of the layer's translation) is not needed here
  through-∘-server : AnswersOnly through-serverPort → CanAnswer through-serverPort
                   → Server through-clientPort
  through-∘-server sa ca =
    ∘-server c through-ansᶜ through-qryʷ rʷ (through-forwards-query th R hq ha)
             (through-forwards-answer th R hq ha) sa (through-responsive th R hq ha) ca

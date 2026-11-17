{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

------------------------------------------------------------------------
-- Midnight.Passport.QueryRouting
--
-- The balance query, routed from the `User` boundary down `acPath` to the
-- account custody contract: a chain of `Routing` links, one per link of
-- `simAC`, with a `Server` chain travelling the other way (each `∘` link needs
-- the answer discipline of everything behind it).
--
-- One link kind per wiring combinator:
--   * the top `∘`, crossing `⟦passportKey⟧` — `∘-routes`, whose four relay
--     conditions are the hypotheses of `balance-routes`;
--   * a `∘` whose front component answers by itself — `∘-routesʳ`, free once
--     that component answers only (`answers-only⇒alone`);
--   * a `mergeᴹ` layer — `through-∘-routes`: pure rewiring, so `Through` plus
--     two injectivity facts, all discharged here;
--   * a tensor — `⊗₁-routesˡ/ʳ`, unconditional.
--
-- The two `⊗ʷ` levels the path passes through on the right are one generic
-- module, applied twice; the level it enters on the left is its own, since the
-- balance wire is that factor's whole codomain. Everything is generic in the
-- `ChannelModel` and takes the factors as parameters: letting Agda invert an
-- architecture term exhausts the heap.
------------------------------------------------------------------------

module Midnight.Passport.QueryRouting where

open import Data.Nat using (ℕ)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CategoricalCrypto.Channel.Core as Ch hiding (_⊗₀_)
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Cascade
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Relay
open import CategoricalCrypto.Machine.Simulation
open import CategoricalCrypto.Machine.Wiring

open import Midnight.Passport.Descent
open import Midnight.Passport.Flow
open import Midnight.Passport.Semantics

open HA

module _ {cm : ChannelModel} (mm : MachineModel cm) (let open MachineModel mm)
         (gb : Channel.outType ⟦JUBJUB-SCHNORR⟧)
         (bi : ℕ → Channel.inType ⟦JUBJUB-SCHNORR⟧) where
  open Descend mm

  -- The balance port at a selection naming the wire in the machine's codomain.
  -- At `ϵ ⊗R` — a one-element wire list — this is `wirePort`, the port
  -- `Properties` states its accounting at.
  selPort : ∀ {A C} (M : Machine A C) → (∀ {m} → ⟦JUBJUB-SCHNORR⟧ [ m ]⇒[ m ]ᵍ C)
          → Port M ⊤ ℕ
  selPort _ s = record { qry = λ _ → L⊗ (s ᵗ¹) ↑ₒ gb ; ans = λ _ v → L⊗ (s ᵗ¹) ↑ᵢ bi v }

  ------------------------------------------------------------------------
  -- The rewiring layer a `⊗ʷ` level ends with
  --
  -- `mergeᴹ` at a one-element left list is `(id ⊗₁ unitorˡ) ∘ ⊗-assoc`: three
  -- rewiring machines, hence `Through` by the two closure theorems, with
  -- injective translations — all a `∘` link over it needs.
  ------------------------------------------------------------------------

  module Merge (x : ArchChan) (ys : ObjTerm) where
    mrg : Machine (⟦ Var x ⟧₀ Ch.⊗₀ ⟦ ys ⟧₀) ⟦ Var x ⊗₀ ys ⟧₀
    mrg = mergeᴹ channelSemantics (Var x) ys

    mrgFwd : ⟦ Var x ⟧₀ Ch.⊗₀ ⟦ ys ⟧₀ [ In ]⇒[ In ] ⟦ Var x ⊗₀ ys ⟧₀
    mrgFwd = Sassoc.fwd ⇒ₜ ⊗-combine Sid.fwd ⊗-left-neutral

    mrgBwd : ⟦ Var x ⊗₀ ys ⟧₀ [ Out ]⇒[ Out ] ⟦ Var x ⟧₀ Ch.⊗₀ ⟦ ys ⟧₀
    mrgBwd = ⊗-combine Sid.bwd ⊗-left-intro ⇒ₜ Sassoc.bwd

    mrgᵗ : Through mrg mrgFwd mrgBwd
    mrgᵗ = ∘-through (⊗₁-through (tfm-through Sid.fwd Sid.bwd)
                                 (tfm-through ⊗-left-neutral ⊗-left-intro))
                     (tfm-through Sassoc.fwd Sassoc.bwd)

    opaque
      unfolding Ch._⊗₀_ destruct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
                ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion
                ⊗-combine

      -- the layer relabels, so both its translations are injections
      mrgFwd-inj : ∀ {a b} → app mrgFwd a ≡ app mrgFwd b → a ≡ b
      mrgFwd-inj {inj₁ (inj₁ _)} {inj₁ (inj₁ _)} refl = refl
      mrgFwd-inj {inj₁ (inj₂ ())}
      mrgFwd-inj {inj₂ _}        {inj₂ _}        refl = refl
      mrgFwd-inj {inj₁ (inj₁ _)} {inj₂ _}        ()
      mrgFwd-inj {inj₂ _}        {inj₁ (inj₁ _)} ()
      mrgFwd-inj {inj₂ _}        {inj₁ (inj₂ ())}

      mrgBwd-inj : ∀ {a b} → app mrgBwd a ≡ app mrgBwd b → a ≡ b
      mrgBwd-inj {inj₁ _} {inj₁ _} refl = refl
      mrgBwd-inj {inj₂ _} {inj₂ _} refl = refl
      mrgBwd-inj {inj₁ _} {inj₂ _} ()
      mrgBwd-inj {inj₂ _} {inj₁ _} ()

  ------------------------------------------------------------------------
  -- A `⊗ʷ` level whose right factor holds the balance wire
  ------------------------------------------------------------------------

  module ⊗ʳLevel (x : ArchChan) (ys nl nr : ObjTerm)
                 (F : Machine ⟦ nl ⟧₀ ⟦ Var x ⟧₀) (G : Machine ⟦ nr ⟧₀ ⟦ ys ⟧₀)
                 (sel : ∀ {m} → ⟦JUBJUB-SCHNORR⟧ [ m ]⇒[ m ]ᵍ ⟦ ys ⟧₀) where

    open Merge x ys

    spl : Machine ⟦ nl ⊗₀ nr ⟧₀ (⟦ nl ⟧₀ Ch.⊗₀ ⟦ nr ⟧₀)
    spl = splitᴹ channelSemantics nl nr

    tns : Machine (⟦ nl ⟧₀ Ch.⊗₀ ⟦ nr ⟧₀) (⟦ Var x ⟧₀ Ch.⊗₀ ⟦ ys ⟧₀)
    tns = F ⊗₁ G

    Lvl : Machine ⟦ nl ⊗₀ nr ⟧₀ ⟦ Var x ⊗₀ ys ⟧₀
    Lvl = mrg ∘ (tns ∘ spl)

    Lvl-port : Port Lvl ⊤ ℕ
    Lvl-port = selPort Lvl (L⊗ sel)

    private
      -- the query at the level's codomain, and the query and the answer at the
      -- tensor's boundary — the same selection, one channel down
      cᴸ : ⊤ → Channel.outType ⟦ Var x ⊗₀ ys ⟧₀
      cᴸ _ = L⊗ sel ↑ₒ gb

      cᴮ : ⊤ → Channel.outType (⟦ Var x ⟧₀ Ch.⊗₀ ⟦ ys ⟧₀)
      cᴮ _ = L⊗ sel ↑ₒ gb

      dᴮ : ⊤ → ℕ → Channel.inType (⟦ Var x ⟧₀ Ch.⊗₀ ⟦ ys ⟧₀)
      dᴮ _ v = L⊗ sel ↑ᵢ bi v

    opaque
      unfolding Ch._⊗₀_ destruct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
                ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion
                ⊗-combine ⊗₁-inˡ ⊗₁-inʳ

      private
        aoᶠ : AnswersOnly (selPort G sel)
            → AnswersOnly (∘-frontPort {M₁ = tns} {M₂ = spl} cᴮ dᴮ)
        aoᶠ = ⊗₁-answers-onlyʳ {M₁ = F} {M₂ = G} (selPort G sel)

        inner : AnswersOnly (selPort G sel) → CanAnswer (selPort G sel)
              → Server (∘-clientPort {M₁ = tns} {M₂ = spl} cᴮ dᴮ)
        inner ao ca = ∘-serverʳ {M₁ = tns} {M₂ = spl} cᴮ dᴮ (aoᶠ ao)
                                (⊗₁-can-answerʳ {M₁ = F} {M₂ = G} (selPort G sel) ca)

        -- the tensor answers this query itself, so the split behind it is never
        -- consulted (implicits pinned: `qryʷ` is not invertible)
        alone : AnswersOnly (selPort G sel) → AnswersAlone {M₁ = tns} {M₂ = spl} cᴮ dᴮ
        alone ao {s} {q} {w} {s'} st =
          answers-only⇒alone {M₁ = tns} {M₂ = spl} cᴮ dᴮ (aoᶠ ao) {s} {q} {w} {s'} st

      -- the level's own discipline, from the factor's
      server : AnswersOnly (selPort G sel) → CanAnswer (selPort G sel) → Server Lvl-port
      server ao ca = through-∘-server mrgᵗ {M₂ = tns ∘ spl} cᴸ dᴮ
                                      (proj₁ (inner ao ca)) (proj₂ (inner ao ca))

      -- and the three links, prefixed onto the rest of the chain
      routes : ∀ {A' C'} {N : Machine A' C'} {T : Sim G N} {p : Port N ⊤ ℕ}
             → AnswersOnly (selPort G sel) → CanAnswer (selPort G sel)
             → Routing T (selPort G sel) p
             → Routing (∘-simˡ {M₁ = mrg} {M₂ = tns ∘ spl}
                        ∙ (∘-simʳ {M₁ = tns} {M₂ = spl}
                           ∙ (⊗₁-simʳ {M₁ = F} {M₂ = G} ∙ T)))
                       Lvl-port p
      routes ao ca rest =
           through-∘-routes mrgᵗ {M₂ = tns ∘ spl} cᴸ dᴮ mrgFwd-inj mrgBwd-inj
                            (proj₁ (inner ao ca))
        ∙ʳ (∘-routesʳ {M₁ = tns} {M₂ = spl} cᴮ dᴮ
                      (λ {s} {q} {w} {s'} → alone ao {s} {q} {w} {s'})
        ∙ʳ (⊗₁-routesʳ {M₁ = F} {M₂ = G} (selPort G sel) ∙ʳ rest))

  ------------------------------------------------------------------------
  -- The `⊗ʷ` level whose left factor is the contract itself
  --
  -- Here the balance wire is that factor's whole codomain, so the selection is
  -- `ϵ ⊗R` throughout and the tensor link is the left one.
  ------------------------------------------------------------------------

  module ⊗ˡLevel (ys nl nr : ObjTerm)
                 (F : Machine ⟦ nl ⟧₀ ⟦ Var JUBJUB-SCHNORR ⟧₀)
                 (G : Machine ⟦ nr ⟧₀ ⟦ ys ⟧₀) where

    open Merge JUBJUB-SCHNORR ys

    spl : Machine ⟦ nl ⊗₀ nr ⟧₀ (⟦ nl ⟧₀ Ch.⊗₀ ⟦ nr ⟧₀)
    spl = splitᴹ channelSemantics nl nr

    tns : Machine (⟦ nl ⟧₀ Ch.⊗₀ ⟦ nr ⟧₀) (⟦ Var JUBJUB-SCHNORR ⟧₀ Ch.⊗₀ ⟦ ys ⟧₀)
    tns = F ⊗₁ G

    Lvl : Machine ⟦ nl ⊗₀ nr ⟧₀ ⟦ Var JUBJUB-SCHNORR ⊗₀ ys ⟧₀
    Lvl = mrg ∘ (tns ∘ spl)

    Lvl-port : Port Lvl ⊤ ℕ
    Lvl-port = selPort Lvl (ϵ ⊗R)

    private
      cᴸ : ⊤ → Channel.outType ⟦ Var JUBJUB-SCHNORR ⊗₀ ys ⟧₀
      cᴸ _ = ϵ ⊗R ↑ₒ gb

      cᴮ : ⊤ → Channel.outType (⟦ Var JUBJUB-SCHNORR ⟧₀ Ch.⊗₀ ⟦ ys ⟧₀)
      cᴮ _ = (ϵ ⊗R) ⊗R ↑ₒ gb

      dᴮ : ⊤ → ℕ → Channel.inType (⟦ Var JUBJUB-SCHNORR ⟧₀ Ch.⊗₀ ⟦ ys ⟧₀)
      dᴮ _ v = (ϵ ⊗R) ⊗R ↑ᵢ bi v

    opaque
      unfolding Ch._⊗₀_ destruct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
                ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion
                ⊗-combine ⊗₁-inˡ ⊗₁-inʳ

      private
        aoᶠ : AnswersOnly (selPort F (ϵ ⊗R))
            → AnswersOnly (∘-frontPort {M₁ = tns} {M₂ = spl} cᴮ dᴮ)
        aoᶠ = ⊗₁-answers-onlyˡ {M₁ = F} {M₂ = G} (selPort F (ϵ ⊗R))

        inner : AnswersOnly (selPort F (ϵ ⊗R)) → CanAnswer (selPort F (ϵ ⊗R))
              → Server (∘-clientPort {M₁ = tns} {M₂ = spl} cᴮ dᴮ)
        inner ao ca = ∘-serverʳ {M₁ = tns} {M₂ = spl} cᴮ dᴮ (aoᶠ ao)
                                (⊗₁-can-answerˡ {M₁ = F} {M₂ = G} (selPort F (ϵ ⊗R)) ca)

        alone : AnswersOnly (selPort F (ϵ ⊗R)) → AnswersAlone {M₁ = tns} {M₂ = spl} cᴮ dᴮ
        alone ao {s} {q} {w} {s'} st =
          answers-only⇒alone {M₁ = tns} {M₂ = spl} cᴮ dᴮ (aoᶠ ao) {s} {q} {w} {s'} st

      server : AnswersOnly (selPort F (ϵ ⊗R)) → CanAnswer (selPort F (ϵ ⊗R))
             → Server Lvl-port
      server ao ca = through-∘-server mrgᵗ {M₂ = tns ∘ spl} cᴸ dᴮ
                                      (proj₁ (inner ao ca)) (proj₂ (inner ao ca))

      routes : ∀ {A' C'} {N : Machine A' C'} {T : Sim F N} {p : Port N ⊤ ℕ}
             → AnswersOnly (selPort F (ϵ ⊗R)) → CanAnswer (selPort F (ϵ ⊗R))
             → Routing T (selPort F (ϵ ⊗R)) p
             → Routing (∘-simˡ {M₁ = mrg} {M₂ = tns ∘ spl}
                        ∙ (∘-simʳ {M₁ = tns} {M₂ = spl}
                           ∙ (⊗₁-simˡ {M₁ = F} {M₂ = G} ∙ T)))
                       Lvl-port p
      routes ao ca rest =
           through-∘-routes mrgᵗ {M₂ = tns ∘ spl} cᴸ dᴮ mrgFwd-inj mrgBwd-inj
                            (proj₁ (inner ao ca))
        ∙ʳ (∘-routesʳ {M₁ = tns} {M₂ = spl} cᴮ dᴮ
                      (λ {s} {q} {w} {s'} → alone ao {s} {q} {w} {s'})
        ∙ʳ (⊗₁-routesˡ {M₁ = F} {M₂ = G} (selPort F (ϵ ⊗R)) ∙ʳ rest))

  ------------------------------------------------------------------------
  -- The architecture's three levels, and the two `∘` links above them
  ------------------------------------------------------------------------

  private
    T₃ : WTerm (Var TBD-SYNC) (Var STATE ⊗₀ Var WITNESS-IPC)
    T₃ = boxʷ localWallet ⊗ʷ boxʷ proofServer

    T₂ : WTerm (Var TBD ⊗₀ Var TBD ⊗₀ Var CHAIN ⊗₀ Var TBD-SYNC)
               (Var JUBJUB-SCHNORR ⊗₀ Var STATE ⊗₀ Var WITNESS-IPC)
    T₂ = boxʷ accountCustody ⊗ʷ T₃

    T₁ : WTerm (Var TBD ⊗₀ Var TBD ⊗₀ Var CHAIN ⊗₀ Var TBD-SYNC)
               (Var READ-STATE ⊗₀ Var JUBJUB-SCHNORR ⊗₀ Var STATE ⊗₀ Var WITNESS-IPC)
    T₁ = boxʷ indexer ⊗ʷ T₂

    layer2 : WTerm (Var TBD ⊗₀ Var TBD ⊗₀ Var CHAIN ⊗₀ Var TBD-SYNC)
                   (Var RECOVERY-P5 ⊗₀ Var READ-STATE ⊗₀ Var JUBJUB-SCHNORR
                    ⊗₀ Var STATE ⊗₀ Var WITNESS-IPC)
    layer2 = boxʷ recoveryHelpers ⊗ʷ T₁

    layer1 : WTerm (Var CHAIN) (Var TBD ⊗₀ Var TBD ⊗₀ Var CHAIN ⊗₀ Var TBD-SYNC)
    layer1 = boxʷ didContract ⊗ʷ boxʷ nameService ⊗ʷ idʷ ⊗ʷ boxʷ peerDevices

    l2Path : Path layer2 (boxʷ accountCustody)
    l2Path = ⊗ʳ (⊗ʳ (⊗ˡ here))

    module C = ⊗ˡLevel (Var STATE ⊗₀ Var WITNESS-IPC)
                       (Var TBD ⊗₀ Var TBD ⊗₀ Var CHAIN) (Var TBD-SYNC)
                       ⟦accountCustody⟧ ⟦ T₃ ⟧
    module B = ⊗ʳLevel READ-STATE (Var JUBJUB-SCHNORR ⊗₀ Var STATE ⊗₀ Var WITNESS-IPC)
                       unit (Var TBD ⊗₀ Var TBD ⊗₀ Var CHAIN ⊗₀ Var TBD-SYNC)
                       ⟦indexer⟧ ⟦ T₂ ⟧ (ϵ ⊗R)
    module A = ⊗ʳLevel RECOVERY-P5
                       (Var READ-STATE ⊗₀ Var JUBJUB-SCHNORR ⊗₀ Var STATE
                        ⊗₀ Var WITNESS-IPC)
                       unit (Var TBD ⊗₀ Var TBD ⊗₀ Var CHAIN ⊗₀ Var TBD-SYNC)
                       ⟦recoveryHelpers⟧ ⟦ T₁ ⟧ (L⊗ (ϵ ⊗R))

  -- the contract's own balance port: the whole of its codomain is that wire
  acPort : Port ⟦accountCustody⟧ ⊤ ℕ
  acPort = selPort ⟦accountCustody⟧ (ϵ ⊗R)

  -- the balance port on layer 2, and on the two layers composed
  l2Port : Port ⟦ layer2 ⟧ ⊤ ℕ
  l2Port = selPort ⟦ layer2 ⟧ (L⊗ (L⊗ (ϵ ⊗R)))

  private
    -- the contract's answer discipline, carried up the three levels
    sC : AnswersOnly acPort → CanAnswer acPort → Server C.Lvl-port
    sC = C.server

    sB : AnswersOnly acPort → CanAnswer acPort → Server B.Lvl-port
    sB ao ca = B.server (proj₁ (sC ao ca)) (proj₂ (sC ao ca))

    l2Server : AnswersOnly acPort → CanAnswer acPort → Server l2Port
    l2Server ao ca = A.server (proj₁ (sB ao ca)) (proj₂ (sB ao ca))

    -- and the query, routed down the same three levels
    l2Routes : AnswersOnly acPort → CanAnswer acPort
             → Routing (descend l2Path) l2Port acPort
    l2Routes ao ca =
      A.routes (proj₁ (sB ao ca)) (proj₂ (sB ao ca))
        (B.routes (proj₁ (sC ao ca)) (proj₂ (sC ao ca))
          (C.routes ao ca (id-routes acPort)))

------------------------------------------------------------------------
-- The whole route: `⟦passportKey⟧` on top, layer 1 behind
------------------------------------------------------------------------

  private
    PKdom : ObjTerm
    PKdom = Var RECOVERY-P5 ⊗₀ Var READ-STATE ⊗₀ Var JUBJUB-SCHNORR
              ⊗₀ Var STATE ⊗₀ Var WITNESS-IPC

  module _ (gbᵁ : Channel.outType ⟦User⟧) (biᵁ : ℕ → Channel.inType ⟦User⟧) where
    private
      Rest : Machine ⟦ Var CHAIN ⟧₀ ⟦ PKdom ⟧₀
      Rest = ⟦ layer2 ⟧ ∘ ⟦ layer1 ⟧

      cᵁ : ⊤ → Channel.outType ⟦ Var User ⟧₀
      cᵁ _ = ϵ ⊗R ↑ₒ gbᵁ

      dᵁ : ⊤ → ℕ → Channel.inType ⟦ Var User ⟧₀
      dᵁ _ v = ϵ ⊗R ↑ᵢ biᵁ v

      -- the balance query as the passport key forwards it: onto the
      -- JUBJUB-SCHNORR wire of its domain, the third of five
      qᴷ : ⊤ → Channel.outType ⟦ PKdom ⟧₀
      qᴷ _ = L⊗ (L⊗ (ϵ ⊗R)) ↑ₒ gb

      rᴷ : ⊤ → ℕ → Channel.inType ⟦ PKdom ⟧₀
      rᴷ _ v = L⊗ (L⊗ (ϵ ⊗R)) ↑ᵢ bi v

    -- the passport key, as the relay the balance query needs it to be
    pkRelay : Relay ⟦passportKey⟧ ⊤ ℕ
    pkRelay = ∘-relay {M₂ = Rest} cᵁ dᵁ qᴷ rᴷ

    -- the user's balance port on the whole system — `Properties`' `userPort`
    userPort : Port ⟦architecture⟧ ⊤ ℕ
    userPort = wirePort ⟦User⟧ ⟦architecture⟧ (λ _ → gbᵁ) (λ _ → biᵁ)

    balance-routes : ForwardsQuery pkRelay → ForwardsAnswer pkRelay
                   → NoInvention pkRelay → Responsive pkRelay
                   → AnswersOnly acPort → CanAnswer acPort
                   → Routing (simAC mm) userPort acPort
    balance-routes fq fa ni rsp ao ca =
         ∘-routes {M₁ = ⟦passportKey⟧} {M₂ = Rest} cᵁ dᵁ qᴷ rᴷ fq fa ni (proj₁ restServer) rsp
      ∙ʳ (∘-routesʳ {M₁ = ⟦ layer2 ⟧} {M₂ = ⟦ layer1 ⟧} qᴷ rᴷ
                    (answers-only⇒alone {M₁ = ⟦ layer2 ⟧} {M₂ = ⟦ layer1 ⟧} qᴷ rᴷ
                                        (proj₁ (l2Server ao ca)))
      ∙ʳ l2Routes ao ca)
      where
        restServer : Server (∘-clientPort {M₁ = ⟦ layer2 ⟧} {M₂ = ⟦ layer1 ⟧} qᴷ rᴷ)
        restServer = ∘-serverʳ {M₁ = ⟦ layer2 ⟧} {M₂ = ⟦ layer1 ⟧} qᴷ rᴷ
                               (proj₁ (l2Server ao ca)) (proj₂ (l2Server ao ca))

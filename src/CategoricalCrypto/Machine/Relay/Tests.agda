{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

module CategoricalCrypto.Machine.Relay.Tests where

open import categorical-crypto.Prelude hiding (id; _∘_)

open import Tactic.Defaults
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Relay
open import CategoricalCrypto.Machine.Simulation

--------------------------------------------------------------------------------
-- A relay in front of a server, at real `⇒-solver` terms: the server keeps a
-- number and hands it over when asked; the relay passes the question down and
-- the number back up. Both wires carry a payload-free query (backwards) and a
-- numeric answer (forwards), so the four messages of the exchange are `tt` and
-- the identity on each side — this is the `Q ≡ ⊤` instance of the parametrized
-- query. The two machines are *relations*, not functions: nothing forces them to
-- answer, which is what makes the permission/guarantee split of the relay
-- conditions visible.

Bᶜ Cᶜ : Channel
Bᶜ = ℕ ⇿ ⊤   -- relay ⇄ server
Cᶜ = ℕ ⇿ ⊤   -- client ⇄ relay

data ServerRel : machine-type ℕ (I ⊗ᵀ Bᶜ) where
  reply : ∀ {n} → ServerRel n (L⊗ (ϵ ᵗ¹) ↑ₒ tt) (just (L⊗ (ϵ ᵗ¹) ↑ᵢ n)) n

data RelayRel : machine-type ⊤ (Bᶜ ⊗ᵀ Cᶜ) where
  fwdQ :         RelayRel tt (L⊗ (ϵ ᵗ¹) ↑ₒ tt) (just (ϵ ⊗R ↑ₒ tt))     tt
  fwdA : ∀ {n} → RelayRel tt (ϵ ⊗R ↑ᵢ n)       (just (L⊗ (ϵ ᵗ¹) ↑ᵢ n)) tt

server : Machine I Bᶜ
server = MkMachine ServerRel

relay : Machine Bᶜ Cᶜ
relay = MkMachine RelayRel

rel : Relay relay ⊤ ℕ
rel = ∘-relay {M₁ = relay} {M₂ = server} (λ _ → tt) (λ _ n → n) (λ _ → tt) (λ _ n → n)

cPort : Port (relay ∘ server) ⊤ ℕ
cPort = ∘-clientPort {M₁ = relay} {M₂ = server} (λ _ → tt) (λ _ n → n)

sPort : Port server ⊤ ℕ
sPort = ∘-serverPort {M₁ = relay} {M₂ = server} (λ _ → tt) (λ _ n → n) (λ _ → tt) (λ _ n → n)

--------------------------------------------------------------------------------
-- The conditions, discharged by inversion on the two step relations. Each needs
-- Channel.Core's tensor unfolded, since ruling out the other constructor is
-- exactly "these two message positions are different injections".

opaque
  unfolding _⊗₀_ destruct-⊗ ⊗-right-intro ⊗-sym ⊗-combine ⊗-fusion ⊗-right-neutral

  fq : ForwardsQuery rel
  fq fwdQ = refl

  fa : ForwardsAnswer rel
  fa fwdA = refl

  ni : NoInvention rel
  ni fwdA = refl

  rsp : Responsive rel
  rsp = (λ _ _ → tt , fwdQ) , (λ _ _ _ → tt , fwdA)

  sa : AnswersOnly sPort
  sa reply = _ , refl

--------------------------------------------------------------------------------
-- The transfer, both ways, through the genuine `_∘_` cascade.

routes : Routing (∘-simˡ {M₁ = relay} {M₂ = server}) cPort sPort
routes = ∘-routes (λ _ → tt) (λ _ n → n) (λ _ → tt) (λ _ n → n) fq fa ni sa rsp

-- the composite answers with what the server holds …
composite-answers : ∀ {n} → Answers cPort (n , tt) tt n
composite-answers = complete routes (_ , reply)

-- … and every answer it gives is one the server gave, from that same state
server-answered : ∀ {n m} → Answers cPort (n , tt) tt m → Answers sPort n tt m
server-answered = sound routes

--------------------------------------------------------------------------------
-- A tensor link, at the real baked `_⊗₁_` solver: a factor's port lifts to the
-- tensor's boundary and back, with no conditions at all.

tensor-routes : Routing (⊗₁-simˡ {M₁ = server} {M₂ = server}) (⊗₁-portˡ sPort) sPort
tensor-routes = ⊗₁-routesˡ sPort

tensor-answers : ∀ {n m} → Answers (⊗₁-portˡ {M₂ = server} sPort) (n , m) tt n
tensor-answers = complete tensor-routes (_ , reply)

-- a two-link chain: descend a tensor, then relay-and-server
chain : Routing (⊗₁-simˡ {M₁ = relay ∘ server} {M₂ = server} ∙ ∘-simˡ)
                (⊗₁-portˡ cPort) sPort
chain = ⊗₁-routesˡ cPort ∙ʳ routes

--------------------------------------------------------------------------------
-- The server discipline, and its closure under the two combinators: the server
-- is one, hence so is the relay in front of it, hence so is either factor of a
-- tensor it sits in.

server-server : Server sPort
server-server = sa , λ n _ → n , _ , reply

composite-server : Server cPort
composite-server = ∘-server (λ _ → tt) (λ _ n → n) (λ _ → tt) (λ _ n → n)
                            fq fa sa rsp (proj₂ server-server)

tensor-server : Server (⊗₁-portˡ {M₂ = server} sPort)
tensor-server = ⊗₁-serverˡ sPort server-server

--------------------------------------------------------------------------------
-- The other projection: a front component that answers by itself, so the answer
-- transfers to *it* and the component behind it is never consulted.

data OracleRel : machine-type ℕ (Bᶜ ⊗ᵀ Cᶜ) where
  give : ∀ {n} → OracleRel n (L⊗ (ϵ ᵗ¹) ↑ₒ tt) (just (L⊗ (ϵ ᵗ¹) ↑ᵢ n)) n

oracle : Machine Bᶜ Cᶜ
oracle = MkMachine OracleRel

oPortᶜ : Port (oracle ∘ server) ⊤ ℕ
oPortᶜ = ∘-clientPort {M₁ = oracle} {M₂ = server} (λ _ → tt) (λ _ n → n)

oPortᶠ : Port oracle ⊤ ℕ
oPortᶠ = ∘-frontPort {M₁ = oracle} {M₂ = server} (λ _ → tt) (λ _ n → n)

opaque
  unfolding _⊗₀_ destruct-⊗ ⊗-right-intro ⊗-sym ⊗-combine ⊗-fusion ⊗-right-neutral

  aa : AnswersAlone {M₁ = oracle} {M₂ = server} {⊤} (λ _ → tt) (λ _ n → n)
  aa ()

oracle-routes : Routing (∘-simʳ {M₁ = oracle} {M₂ = server}) oPortᶜ oPortᶠ
oracle-routes = ∘-routesʳ (λ _ → tt) (λ _ n → n) aa

oracle-answers : ∀ {n m} → Answers oPortᶜ (n , m) tt m
oracle-answers = complete oracle-routes (_ , give)

--------------------------------------------------------------------------------
-- A rewiring layer in front of the server, at a real `TotalFunctionMachine'`: a
-- unitor, so the client asks on `I ⊗₀ Bᶜ`. The layer's own translation dictates
-- the wire positions, and nothing beyond the server's discipline is assumed —
-- the layer's four relay conditions are free.

uFwd : Bᶜ [ In ]⇒[ In ] I ⊗₀ Bᶜ
uFwd = ⊗-left-intro

uBwd : I ⊗₀ Bᶜ [ Out ]⇒[ Out ] Bᶜ
uBwd = ⊗-left-neutral

unitorᴹ : Machine Bᶜ (I ⊗₀ Bᶜ)
unitorᴹ = TotalFunctionMachine' uFwd uBwd

cᵘ : ⊤ → Channel.outType (I ⊗₀ Bᶜ)
cᵘ _ = app (⊗-left-intro {Out} {I} {Bᶜ}) tt

uPortᶜ : Port (unitorᴹ ∘ server) ⊤ ℕ
uPortᶜ = through-clientPort (tfm-through uFwd uBwd) {M₂ = server} cᵘ (λ _ n → n)

uPortˢ : Port server ⊤ ℕ
uPortˢ = through-serverPort (tfm-through uFwd uBwd) {M₂ = server} cᵘ (λ _ n → n)

opaque
  unfolding _⊗₀_ destruct-⊗ ⊗-right-intro ⊗-sym ⊗-combine ⊗-fusion ⊗-right-neutral

  uFwd-inj : ∀ {x y} → app uFwd x ≡ app uFwd y → x ≡ y
  uFwd-inj refl = refl

  uBwd-inj : ∀ {x y} → app uBwd x ≡ app uBwd y → x ≡ y
  uBwd-inj {inj₁ ()}
  uBwd-inj {inj₂ _} {inj₁ ()}
  uBwd-inj {inj₂ _} {inj₂ _} refl = refl

  -- the server, at the positions the layer dictates
  uSA : AnswersOnly uPortˢ
  uSA reply = _ , refl

  uAnswers : ∀ {n} → Answers uPortˢ n tt n
  uAnswers = _ , reply

  uCA : CanAnswer uPortˢ
  uCA n _ = n , uAnswers

uRoutes : Routing (∘-simˡ {M₁ = unitorᴹ} {M₂ = server}) uPortᶜ uPortˢ
uRoutes = through-∘-routes (tfm-through uFwd uBwd) {M₂ = server} cᵘ (λ _ n → n)
                           uFwd-inj uBwd-inj uSA

unitor-answers : ∀ {n} → Answers uPortᶜ (n , tt) tt n
unitor-answers = complete uRoutes uAnswers

unitor-server : Server uPortᶜ
unitor-server = through-∘-server (tfm-through uFwd uBwd) {M₂ = server} cᵘ (λ _ n → n) uSA uCA

-- a two-link chain: descend a tensor, then cross the layer
unitor-chain : Routing (⊗₁-simˡ {M₁ = unitorᴹ ∘ server} {M₂ = server} ∙ ∘-simˡ)
                       (⊗₁-portˡ uPortᶜ) uPortˢ
unitor-chain = ⊗₁-routesˡ uPortᶜ ∙ʳ uRoutes

--------------------------------------------------------------------------------
-- A translation layer, where a `modifyStepRel` inside a bigger rewiring sits. At
-- `⇒-refl` the wrapper's messages are the core's, so the port crosses unchanged.

wrapped : Machine I Bᶜ
wrapped = modifyStepRel ⇒-refl server

wPort : Port wrapped ⊤ ℕ
wPort = record { qry = qry sPort ; ans = ans sPort }

wrapped-routes : Routing (modify-sim {p = ⇒-refl} {N = server}) wPort
                         (modify-port ⇒-refl wPort)
wrapped-routes = modify-routes ⇒-refl wPort

wrapped-answers : ∀ {n} → Answers wPort n tt n
wrapped-answers = complete wrapped-routes (_ , reply)

wrapped-server : Server wPort
wrapped-server = modify-server ⇒-refl {N = server} wPort (λ e → e) server-server

--------------------------------------------------------------------------------
-- Forwarding, closed under both combinators: a nest of rewiring layers — the
-- shape `mergeᴹ` is built from — forwards everything, with no conditions at all.

counitorᴹ : Machine (I ⊗₀ Bᶜ) Bᶜ
counitorᴹ = TotalFunctionMachine' ⊗-left-neutral ⊗-left-intro

nest-through : Through (counitorᴹ ∘ unitorᴹ) (uFwd ⇒ₜ ⊗-left-neutral)
                                             (⊗-left-intro ⇒ₜ uBwd)
nest-through = ∘-through (tfm-through ⊗-left-neutral ⊗-left-intro)
                         (tfm-through uFwd uBwd)

tensor-through : Through (unitorᴹ ⊗₁ counitorᴹ) (⊗-combine uFwd ⊗-left-neutral)
                                                (⊗-combine uBwd ⊗-left-intro)
tensor-through = ⊗₁-through (tfm-through uFwd uBwd)
                            (tfm-through ⊗-left-neutral ⊗-left-intro)

-- a nest in front of the server, crossed with no conditions but the server's own
nPortᶜ : Port ((counitorᴹ ∘ unitorᴹ) ∘ server) ⊤ ℕ
nPortᶜ = through-clientPort nest-through {M₂ = server} (λ _ → tt) (λ _ n → n)

nPortˢ : Port server ⊤ ℕ
nPortˢ = through-serverPort nest-through {M₂ = server} (λ _ → tt) (λ _ n → n)

opaque
  unfolding _⊗₀_ destruct-⊗ ⊗-right-intro ⊗-sym ⊗-combine ⊗-fusion ⊗-right-neutral

  nFwd-inj : ∀ {x y} → app (uFwd ⇒ₜ ⊗-left-neutral) x ≡ app (uFwd ⇒ₜ ⊗-left-neutral) y
           → x ≡ y
  nFwd-inj refl = refl

  nBwd-inj : ∀ {x y} → app (⊗-left-intro ⇒ₜ uBwd) x ≡ app (⊗-left-intro ⇒ₜ uBwd) y → x ≡ y
  nBwd-inj refl = refl

  nSA : AnswersOnly nPortˢ
  nSA reply = _ , refl

nest-routes : Routing (∘-simˡ {M₁ = counitorᴹ ∘ unitorᴹ} {M₂ = server}) nPortᶜ nPortˢ
nest-routes = through-∘-routes nest-through {M₂ = server} (λ _ → tt) (λ _ n → n)
                               nFwd-inj nBwd-inj nSA

nest-answers : ∀ {n} → Answers nPortᶜ (n , tt , tt) tt n
nest-answers = complete nest-routes (_ , reply)

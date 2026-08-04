# Midnight.Passport.Properties

Security properties of the Midnight Passport architecture, stated against the
machine semantics of `Midnight.Passport.Semantics`. The headline result is
**preservation of value**:

> Run the whole passport system from its genesis state. If the account
> custody contract keeps correct books, and the architecture faithfully
> routes transactions and balance queries between the user and the contract,
> then no balance the system ever reports exceeds the true balance and the true
> balance is always observable.

```agda
{-# OPTIONS --safe #-}

open import CategoricalCrypto.Channel.Core as Ch hiding (_⊗₀_)

module Midnight.Passport.Properties
  (⟦TBD⟧ ⟦TBD-SYNC⟧             : Channel)
  (SignRequest Signature        : Set)   -- C5-C6
  (ShareRequest ShareResponse   : Set)   -- C14-C15
  (WitnessRequest WitnessResponse : Set) -- C7-C6
  (LedgerWrite ChainEvent       : Set)   -- C1-Chain
  (WalletState                  : Set)
  (UserRequest ChainResult      : Set)   -- User-Chain
  where

open import Data.Empty
open import Data.Integer using (ℤ; 0ℤ; +_; _+_; _≤_)
open import Data.Maybe
open import Data.Nat     using (ℕ)
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Simulation

open import Midnight.Passport.Semantics
```

## 1. Concrete channels

A `Channel` is a pair of types of messages, one for each direction. A
convenient way to define them is via the `simpleChannel` idiom: we
first define a `Mode`-indexed family of types, where the `Mode` of a
constructor gives the direction the message travels. `simpleChannel`
then assembles this into an actual `Channel`.

The account interface `JUBJUB-SCHNORR` refines the `C5-C6` spec with the
balance query: the account custody contract issues signing challenges and
answers balance queries; the passport key returns signatures and asks for the
balance. Balances are per-account state of `accountCustody` and observable
*only* through this query.

```agda
data JubjubSchnorrT : Mode → Set where
  sign       : SignRequest → JubjubSchnorrT In
  balanceIs  : ℕ → JubjubSchnorrT In
  signed     : Signature → JubjubSchnorrT Out
  getBalance : JubjubSchnorrT Out

JubjubSchnorrᶜ : Channel
JubjubSchnorrᶜ = simpleChannel JubjubSchnorrT
```

We are mostly interested in user-facing properties. These are
typically of the form that under reasonable assumptions, for all
execution traces, a certain property that the user can observe is
satisfied. The things the user can observe are modeled as the `Userᶜ`
channel, so in particular there aren't properties about the states of
any individual subsystem. We might still prove such properties, but
they are typically intermediate results, to be used in proving a
user-facing property.

`passportKey` is expected to answer it with the balance `accountCustody`
exposes.

```agda
data UserT : Mode → Set where
  result     : ChainResult → UserT In
  balanceIs  : ℕ → UserT In
  request    : UserRequest → UserT Out
  getBalance : UserT Out

Userᶜ : Channel
Userᶜ = simpleChannel UserT
```

The remaining channels stay mostly abstract for now, they will be
instantiated later.

```agda
channelModel : ChannelModel
channelModel = record
  { ⟦TBD⟧            = ⟦TBD⟧
  ; ⟦TBD-SYNC⟧       = ⟦TBD-SYNC⟧
  ; ⟦RECOVERY-P5⟧    = ShareResponse ⇿ ShareRequest     -- C14-C15
  ; ⟦READ-STATE⟧     = ChainEvent ⇿ ⊥                   -- C1-Chain, read side
  ; ⟦JUBJUB-SCHNORR⟧ = JubjubSchnorrᶜ                   -- C5-C6 + balance
  ; ⟦STATE⟧          = WalletState ⇿ ⊥
  ; ⟦WITNESS-IPC⟧    = WitnessResponse ⇿ WitnessRequest -- C7-C6
  ; ⟦CHAIN⟧          = ChainEvent ⇿ LedgerWrite         -- C1-Chain
  ; ⟦User⟧           = Userᶜ                            -- User-Chain + balance
  }

open ChannelModel channelModel using (⟦_⟧₀)
```

## 2. The preservation of value property

*The only way to change the balance is via in/outgoing transactions*,
stated over traces of the **whole system** from a distinguished
genesis state. Transactions are events on the `CHAIN` boundary wire;
`txValue` (the impact a transaction has on the balance) stays a
parameter while the transaction vocabulary is not concrete. The *real*
balance after a run is then defined to be the genesis balance plus the
net flow of the run.

A queried balance may lag the real one: incoming transactions can sit
unread (one can receive funds without checking the wallet, no network
connectivity, etc.), so answers may *under*-report. Outgoing
transactions are initiated by the wallet itself and are always known
to it. The property is therefore a pair:

* **soundness** — an observed balance never exceeds the real one (no value is
  created); no eventuality is needed for this half;
* **eventual accuracy** — after any run, the system can take a
  transaction-free continuation whose result is exactly the real
  balance.

The pair is meaningful for any machine whose channel exposes a balance query,
so it is factored out once and instantiated twice: globally at the system
boundary (user-facing), and locally at `accountCustody`.

```agda
module BalanceAccounting {A B : Channel} (M : Machine A B)
  (let MC = Machine.machine-channel M)
  (qry     : Channel.inType MC)
  (ans     : ℕ → Channel.outType MC)
  (txValue : Val M)
  (s₀      : Machine.State M)    -- genesis state
  (b₀      : ℕ)                  -- genesis balance
  where

  open Machine M renaming (State to S)

  -- in state s, a balance query can answer a
  Answers : S → ℕ → Set
  Answers s a = ∃[ s' ] stepRel s qry (just (ans a)) s'

  -- the net value moved by the transactions of a trace
  netFlow : ∀ {s₁ s₂} → Trace M s₁ s₂ → ℤ
  netFlow = flow txValue

  -- the real balance after a run from genesis
  realBalance : ∀ {s} → Trace M s₀ s → ℤ
  realBalance t = + b₀ + netFlow t

  Sound : Set
  Sound = ∀ {s a} (t : Trace M s₀ s) → Answers s a → + a ≤ realBalance t

  EventuallyAccurate : Set
  EventuallyAccurate = ∀ {s} (t : Trace M s₀ s) →
    ∃[ s' ] Σ[ u ∈ Trace M s s' ]
      (netFlow u ≡ 0ℤ × ∃[ a ] (+ a ≡ realBalance t × Answers s' a))

  -- answers are accurate immediately, with no syncing continuation
  PromptlyAccurate : Set
  PromptlyAccurate = ∀ {s} (t : Trace M s₀ s) → ∃[ a ] (+ a ≡ realBalance t × Answers s a)

  prompt⇒eventual : PromptlyAccurate → EventuallyAccurate
  prompt⇒eventual p t = _ , [] , refl , p t

  Statement : Set
  Statement = Sound × EventuallyAccurate
```

We can now instantiate this to the two variants:

```agda
codᵍ : ∀ {m A C} → C [ m ]⇒[ ¬ₘ m ]ᵍ (A ⊗ᵀ (C Ch.⊗₀ Ch.I))
codᵍ = L⊗ (ϵ ⊗R) ᵗ¹

-- global
module PreservationOfValue (M : Machine ⟦ Var CHAIN ⟧₀ ⟦ Var User ⟧₀) =
  BalanceAccounting M (codᵍ ↑ₒ getBalance) (λ a → codᵍ ↑ᵢ balanceIs a)

-- local (on ⟦accountCustody⟧)
module PreservationOfValue-local
  (AC : Machine ⟦ Var TBD ⊗₀ Var TBD ⊗₀ Var CHAIN ⟧₀ ⟦ Var JUBJUB-SCHNORR ⟧₀) =
  BalanceAccounting AC (codᵍ ↑ₒ getBalance) (λ a → codᵍ ↑ᵢ balanceIs a)
```

## 3. Proof machinery: from the whole system to the account contract

We're working in a generic setting, so we need some extra hypotheses:

* `FlowPreserving` — a global step's `txValue` is the `txValueᴬ`-flow of its
  image: transactions crossing the `CHAIN` boundary reach `accountCustody`
  with the same value, and no other value moves;
* `QuerySound` / `QueryComplete` — the two directions of *the balances
  exposed at the `User` boundary and by `accountCustody` agree*:
  `G.Answers s a ⇔ L.Answers (π s) a`.

The local lemma feeding the eventual-accuracy half is `PromptlyAccurate`,
not `EventuallyAccurate`: `accountCustody` has already received every
delivered chain event as one of its own steps, so its answer needs no
syncing continuation — the "eventually" belongs only to the global
statement, where an answer may take routing steps. This is what lets the
bridge avoid a trace-lifting hypothesis (lifting an arbitrary local
continuation into the composite is generally unprovable: it may take steps
the surrounding context never drives).

Given these, both halves of the global statement follow in a few lines.
`QuerySound`/`QueryComplete` remain behavioral assumptions on
`⟦passportKey⟧` (the model's machines are parameters, so they cannot be
proved unconditionally).

```agda
-- for performance reasons, we work generically here
module _ {cm : ChannelModel} (mm : MachineModel cm) where
  open MachineModel mm using (⟦architecture⟧; ⟦accountCustody⟧)

  simAC : Sim ⟦architecture⟧ ⟦accountCustody⟧
  simAC = ∘-simˡ ∙ ∘-simʳ
        ∙ ∘-simˡ ∙ ∘-simʳ ∙ ⊗₁-simʳ
        ∙ ∘-simˡ ∙ ∘-simʳ ∙ ⊗₁-simʳ
        ∙ ∘-simˡ ∙ ∘-simʳ ∙ ⊗₁-simˡ

module GlobalFromLocal-generic
  (M  : Machine ⟦ Var CHAIN ⟧₀ ⟦ Var User ⟧₀)
  (AC : Machine ⟦ Var TBD ⊗₀ Var TBD ⊗₀ Var CHAIN ⟧₀ ⟦ Var JUBJUB-SCHNORR ⟧₀)
  (txValue : Val M) (txValueᴬ : Val AC)
  (s₀ : Machine.State M) (b₀ : ℕ)
  (sim : Sim M AC)
  where

  open Sim sim

  module G = PreservationOfValue       M  txValue  s₀     b₀
  module L = PreservationOfValue-local AC txValueᴬ (π s₀) b₀

  FlowPreserving : Set
  FlowPreserving = Preserves txValue txValueᴬ

  QuerySound : Set
  QuerySound = ∀ {s a} → G.Answers s a → L.Answers (π s) a

  QueryComplete : Set
  QueryComplete = ∀ {s a} → L.Answers (π s) a → G.Answers s a

  module _ (fp : FlowPreserving) (qs : QuerySound) (qc : QueryComplete) where

    sound : L.Sound → G.Sound
    sound ls {a = a} t gans =
      subst (λ z → + a ≤ + b₀ + z) (flow-onTrace fp t) (ls (onTrace t) (qs gans))

    eventuallyAccurate : L.PromptlyAccurate → G.EventuallyAccurate
    eventuallyAccurate lp t with lp (onTrace t)
    ... | a , eq , lans =
      _ , [] , refl , a , trans eq (cong (λ z → + b₀ + z) (flow-onTrace fp t)) , qc lans

    statement : L.Sound → L.PromptlyAccurate → G.Statement
    statement ls lp = sound ls , eventuallyAccurate lp
```

## 4. The preservation of value theorem

Fix the data of a deployment: an implementation of every component, what a
transaction is worth, and where the system starts.

```agda
module Theorem
  (mm : MachineModel channelModel) (let open MachineModel mm)
  (txValue  : Val ⟦architecture⟧) (txValueᴬ : Val ⟦accountCustody⟧)
  (s₀ : Machine.State ⟦architecture⟧)
  (b₀ : ℕ)
  where

  private
    module GFL = GlobalFromLocal-generic
      ⟦architecture⟧ ⟦accountCustody⟧ txValue txValueᴬ s₀ b₀ (simAC mm)
    open GFL
```

Five hypotheses: The first two say the account custody contract keeps
correct books, considered on its own; the last three say the architecture
wires it up faithfully. Under those hypotheses, the whole system is sound
and eventually accurate.

```agda
  preservation-of-value
    : L.Sound → L.PromptlyAccurate
    → FlowPreserving → QuerySound → QueryComplete
    → G.Sound × G.EventuallyAccurate
  preservation-of-value as aa vr bs bc = GFL.statement vr bs bc as aa
```

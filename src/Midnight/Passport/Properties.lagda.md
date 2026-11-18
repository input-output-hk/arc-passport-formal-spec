# Midnight.Passport.Properties

## Preservation of value for the whole architecture

Starting at `s₀`, the true balance is `b₀` plus the signed value of the
`CHAIN` events received during the run. An answer is a response to the selected
balance query, not an unsolicited message. **Soundness** says that no answer
exceeds the true balance. **Eventual accuracy** says that after any run there is
a value-neutral continuation with an enabled exact answer; the proof chooses
the empty continuation. This is may-liveness, not eventual response under every
fair execution.

The theorem concerns the complete `architectureᶜ` interpreted by `MachineModel`,
not a two-component approximation. Its channel model and selected query messages
are parameters: for a keyed interface, instantiate this module once per
account–asset pair while keeping the same machine and ledger state.

The definitions of `Sound`, `PromptlyAccurate`, and `EventuallyAccurate` are in
`Midnight.Passport.BalanceAccounting`. The ports, input-event valuations, and
local/global instances are in `Midnight.Passport.ArchitectureAccounting`.
Proof implementation is in `Midnight.Passport.PropertiesProof`, using the
existing `Flow` descent and `QueryRouting` route through every wiring layer.

```agda
{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ)
open import CategoricalCrypto.Channel.Core as Ch hiding (_⊗₀_)
open import Midnight.Passport.Semantics

module Midnight.Passport.Properties
  (cm : ChannelModel) (let open ChannelModel cm)
  (getBalance : Channel.outType ⟦JUBJUB-SCHNORR⟧)
  (balanceIs : ℕ → Channel.inType ⟦JUBJUB-SCHNORR⟧)
  (getBalanceᵁ : Channel.outType ⟦User⟧)
  (balanceIsᵁ : ℕ → Channel.inType ⟦User⟧)
  where

open import Data.Integer using (ℤ)
open import Data.Product using (_×_)
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Relay
import Midnight.Passport.ArchitectureAccounting as Accounting
import Midnight.Passport.PropertiesProof as Proof

module A = Accounting cm getBalance balanceIs getBalanceᵁ balanceIsᵁ
module P = Proof cm getBalance balanceIs getBalanceᵁ balanceIsᵁ
```

## Assumptions and conclusion

The four passport-key conditions require it to forward queries, forward answers,
never invent an answer, and be responsive. The architecture's routing is derived
from those conditions, not assumed.

The four custody conditions require sound books, an immediately accurate answer,
and the following query discipline:

- `AnswersOnly`: **every transition triggered by the selected query outputs an
  answer to that query**. It does not claim that answers can only be produced in
  response to queries.
- `CanAnswer`: every state admits such an answer transition.

These local conditions are premises only in this generic theorem. The concrete
finalized-ledger instantiation in `Passport.AccountCustodyArchitectureProperties`
discharges all four; only the passport-key relay conditions remain premises.
Transaction values are signed (credits minus debits); a submission alone carries
no value. The concrete instance assigns zero to rejected finalized events.

```agda
module Theorem
  (mm : MachineModel cm)
  (let open MachineModel mm using (⟦architecture⟧; ⟦accountCustody⟧))
  (txval : Channel.inType ⟦CHAIN⟧ → ℤ)
  (s₀ : Machine.State ⟦architecture⟧) (b₀ : ℕ) where

  open A.Theorem mm txval s₀ b₀

  preservation-of-value
    : L.Sound → L.PromptlyAccurate
    → ForwardsQuery pkRelay → ForwardsAnswer pkRelay
    → NoInvention pkRelay → Responsive pkRelay
    → AnswersOnly (A.acPort ⟦accountCustody⟧)
    → CanAnswer (A.acPort ⟦accountCustody⟧)
    → G.Sound × G.EventuallyAccurate
  preservation-of-value = P.Theorem.preservation-of-value mm txval s₀ b₀
```

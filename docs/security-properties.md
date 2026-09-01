# Additional security properties

These are security properties not covered in
[PROMISES.md](https://github.com/midnightntwrk/passport/blob/main/docs/plans/PROMISES.md).
These basically say that passport correctly implements the functions
expected by a wallet and adequately respects privacy.

The formal setting, as in `Midnight.Passport.Properties`: `M =
⟦architecture⟧ : Machine ⟦ Var CHAIN ⟧₀ ⟦ Var User ⟧₀`; trace
properties quantify over `Trace M s₀ s` from genesis, observed at the
`Userᶜ` boundary. Adversarial properties are UC statements `_≤'UC_`
(simulator existence, `∃[ S ] R ≈ℰ (B ⊗ˡ S ∘ I)`) against ideal
functionalities `Machine I (Honest ⊗₀ Adv)` — the functionality
computes verdicts internally and its `Adv` port is exactly the
permitted leakage.

## 1. Properties

### P5' · Key-recovery safety

The promise P5 states recovery *liveness*; nothing forbids a rotation the user
did not authorise. Any key rotation must contain a recovery exchange
authenticated by the out-of-band `RecoverySecret`.

```agda
RecoverySafety = ∀ {s} (t : Trace M s₀ s) →
  rotatesKey ∈ᵗ t → ∃[ e ] (e ∈ᵗ t × AuthenticatedBy recoverySecret e)
```

### P11 · Transaction safety

*Only a holder of the account's keys can move its funds.* Every adopted spend
from the account was signed under its registered key. The implicit closure of
I-4.2/I-6.x: revoking a key is meaningless unless keys were required in the
first place.

```agda
TransactionSafety = ∀ {s} (t : Trace M s₀ s) {tx} →
  adopts tx ∈ᵗ t → SpendsFrom account tx →
  ∃[ σ ] schnorrVerify (accountKey account) (digest tx) σ × signedIn σ t
```

A stronger form is UC: the signing stack emulates the ideal signature
functionality, under which no exportable key exists and unforgeability holds by
construction.

```agda
F-key : Machine I ((Sig ⊗₀ Ver) ⊗₀ Adv)
KeyBound = signingStackᴬ ≤UC F-key
```

### P12 · Value integrity

*The balance changes only via in/outgoing transactions.* Proved
(`Theorem.preservation-of-value`, `Properties.lagda.md`) from eight
single-component hypotheses: reported balances never exceed the real balance,
and after value-neutral settling they coincide. This is slightly more
complicated than a single equality, since we're talking about balance as
observed by the user, which might e.g. be offline so the balance the user sees
might not be the real balance.

```agda
Sound              = ∀ {s a} (t : Trace M s₀ s) → Answers s a → + a ≤ realBalance t
EventuallyAccurate = ∀ {s}   (t : Trace M s₀ s) →
  ∃[ s' ] Σ[ u ∈ Trace M s s' ]
    (netFlow u ≡ 0ℤ × ∃[ a ] (+ a ≡ realBalance t × Answers s' a))
```

### P13 · Funds availability

*With key access and funds ≥ threshold, the user can move all their funds.*
The liveness dual of P11: safety alone is satisfied by a wallet that never
releases anything. Stated with an explicit user strategy `U` closing the
system — the ∃ says a key-holding user *can* drive the balance out.

```agda
Liveness threshold = ∀ {s a} (t : Trace M s₀ s) → Answers s a → threshold ≤ a →
  ∃[ U ∈ Machine ⟦ Var User ⟧₀ I ]        -- user strategy, given key access
  ∃[ s' ] Σ[ u ∈ Trace (U ∘ M) _ s' ] MovesAll a u
```

The threshold is required to pay transaction fees.

### P14 · Private proving

*The proof server learns only what proving requires; total architecture
leakage is bounded by prover view plus chain leakage.* Two UC statements at
different granularities.

**Component level.** The real proof server is emulated by an ideal
functionality:

```agda
F-prove : Machine I (⟦ Var WITNESS-IPC ⟧₀ ⊗₀ AdvP)
RestrictedProverKnowledge = proofServerᴬ ≤UC F-prove
```

This implies: whatever a compromised or curious proof server observes, a
simulator could have produced from the statement alone.

**Architecture level.** `F-passport`'s `Adv` port is prover view ⊗ chain
leakage.

```agda
F-passport : Machine ⟦ Var CHAIN ⟧₀ (⟦ Var User ⟧₀ ⊗₀ (AdvP ⊗₀ ChainLeak))
BoundedLeakage = ⟦architecture⟧ᴬ ≤UC F-passport
```

This implies: the combined view of everything off the user's devices is
simulatable from those two feeds alone, so no component leaks through a
third channel anywhere in the system.

Neither statement covers availability (a malicious prover may refuse to
prove) or contact metadata (timing, origin) beyond what is pinned into the
statement view.

### P15 · Guardian privacy

*No one but a guardian itself can learn it is your guardian, and a guardian
learns nothing beyond its pinned view.* The naive one-line form:

```agda
Deniability = ∀ g → (helper [ guardian g ]) ∣^ʳ ≈ℰ (helper [ nonGuardian ]) ∣^ʳ
```

`helper [ · ]` is a node-role machine family: `guardian g` holds the
guardian key for account `g` and answers its recovery requests;
`nonGuardian` presents the same interface and answers nothing. `∣^ʳ` drops
the owner-facing honest port, leaving only the wires an observer sees. As
stated this is *false* — the guardian itself distinguishes trivially, since
it sees the request. So the property splits by observer into three:

```agda
-- the ledger contribution reveals nothing about who the guardians are:
-- any two guardian sets of equal (n, t) produce ≈ℰ chain projections
ThirdPartyDeniable = ∀ g g' →
  (recovery [ guardians g ]) ∣^ᶜ ≈ℰ (recovery [ guardians g' ]) ∣^ᶜ

-- guardians cannot identify each other: guardian j's view is unchanged
-- by removing guardian k from the set
CrossGuardian = ∀ j k S → (helper j [ S ]) ∣^ʳ ≈ℰ (helper j [ S ∖ k ]) ∣^ʳ

-- the guardian itself is not deniable; instead its view is pinned:
-- F-guardian's Adv port carries exactly leak_G r = (account address,
-- session nonce, share index) and the reply — nothing of the secret,
-- other guardians, or the account's balances/name
GuardianBounded = guardianᴬ ≤UC F-guardian
```

`∣^ᶜ` keeps only the on-chain projection. `ThirdPartyDeniable` says chain
and network observers learn nothing; `CrossGuardian` says guardians learn
nothing about each other; `GuardianBounded` concedes what the guardian
necessarily learns and bounds it to exactly that.

### P16 · Upgrade safety

*Upgrades are account-gated and preserve devices, balances, and identity
observations.* MIP-0013 permits in-place circuit replacement and records the
device-orphaning risk.

```agda
UpgradeSafety = ∀ {s} (t : Trace M s₀ s) → upgrades ∈ᵗ t →
    AuthorizedUpgrade t                        -- account-gated, not operator-gated
  × (∀ q → AnswersId s q ⇔ AnswersId (pre t) q × Active-preserved t)
```

## 2. Unpromised hazards

Guarantee-shaped obligations surfaced by the coverage review; no promise
number, but each is statable in the same vocabulary.

### Non-griefability

No outsider action degrades an authorised device's availability. The
standards themselves name the attack surface (deposit spam `mip-0013:646`,
inbox spam `mip-0012:797`, global-`round` write contention) without
promising resistance.

```agda
NonGriefability = ∀ {s s' d op} (t : Trace M s₀ s) (u : Trace M s s') →
  Outsider u → Authorized d s → AvailableVia d op s → AvailableVia d op s'
```

### Deployment authenticity

Clients attach only to canonical ratified bytecode — P2's namespace-forking
failure mode one level down, applied to the account contract itself. The
conformance check is decidable.

```agda
DeploymentAuthenticity = ∀ {s c} (t : Trace M s₀ s) →
  attaches c ∈ᵗ t → codeOf c ≡ canonicalCode
```

### Reorg/finality

It is unclear how we want to deal with finality in this model. We have various
options and for now we can assume everything in final, but we might want to
revisit this at some point.

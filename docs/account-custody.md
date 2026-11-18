# Account custody and preservation of value

This model connects the [structured finalized ledger](finalized-ledger.md) to
account-and-asset-qualified balance queries and the Passport architecture's
preservation-of-value argument. It models an authoritative, complete view of
finalized ledger events, not a wallet that can miss events or serve a stale cache.

## Reading route

Start at [`Passport`](../src/Passport.agda), then read:

1. [`AccountCustody`](../src/Passport/AccountCustody.agda) for the event and
   query interfaces, checked event receipt, and custody machine.
2. [`AccountCustodyProperties`](../src/Passport/AccountCustodyProperties.agda)
   for the local accounting and query guarantees.
3. [`AccountCustodyArchitecture`](../src/Passport/AccountCustodyArchitecture.agda)
   for the full architecture model with concrete custody and parameterized
   surrounding components.
4. [`AccountCustodyArchitectureProperties`](../src/Passport/AccountCustodyArchitectureProperties.agda)
   for the whole-architecture theorem and its remaining relay assumptions.

Proof implementations are separate from these advertised statements. Concrete
[`custody examples`](../src/Passport/AccountCustodyExamples.agda) belong to the
root's appendix rather than the main theorem route.

## Accounting boundary

An account/asset pair selects both the queried balance and the transaction effect
being measured. Effects are derived from structured transfer and fee fields;
rejected transactions contribute zero. A claimed adoption is admitted only when
it agrees with the finalized ledger's actual authorization, funding, and freshness
checks in the custody prestate. Thus supplying a transaction with a claimed
successful outcome does not itself authorize an accounting update.

The initial balance comes from the initial ledger state. Balance-query steps do
not move funds. Accepted transaction steps include the fee in the payer's debit,
and rejected transaction steps preserve balances, fee pools, and accepted-ID
history.

## Meaning of accuracy

Local soundness bounds an enabled balance answer by the initial balance plus the
net effect of admitted events. Prompt accuracy provides an exactly accurate
answer at every reachable custody state, without a synchronization continuation.
Both concern one explicitly selected account and asset.

The global conclusion transports those local facts through the existing
architectural simulation, flow-preservation, and query-routing proofs. Enabled
answers are not a promise that a network delivers requests or that every fair
execution eventually emits a response. The existing eventual-accuracy statement
is may-liveness, not a theorem about asynchronous synchronization.

## Assumptions and exclusions

The ledger is finalized-only: no consensus, reorganization, rollback, or native
Midnight adoption theorem is established. Authorization remains a supplied
decidable policy over the complete transaction and prestate; its cryptographic
realization and adequacy for device/grant permissions are separate obligations.

Other architecture components are not turned into Passport implementations by
this instantiation. In particular, passport-key relay behavior remains an
explicit boundary. A real client that queues requests, answers from a cache, or
can be unavailable needs a model that permits those behaviors and corresponding
snapshot/freshness statements.

This is not P12's snapshot-aware reporting or synchronization-progress theorem:
there are no completeness flags or progress assumptions for fetching and scanning
viewing data. The result discharges the concrete custody accounting obligations
of the existing architecture theorem, rather than establishing those additional
promises.

## Agda safety profile

The custody/architecture package and combined `Passport` entry point use
`--safe`, matching the existing machine library. The standalone finalized-ledger
modules retain `--safe --without-K`. No postulates, unchecked termination, or
unsolved goals are introduced.

An isolated `--without-K` check of the pinned `categorical-crypto` dependency
(`f280e04f`) failed in `CategoricalCrypto.Channel.Core` at
`⇒-double-transpose-left`: its equality rewrite eliminates a reflexive channel
equality in a way Agda rejects without K. Thus this package does not claim
K-free checking of the whole architecture; achieving that requires migration of
the machine dependency, not merely adding a flag to the new theorem modules.

## Executable evidence

The custody examples include an actual machine trace containing an adopted
payment, an account/asset-qualified query, and a replay rejection. A compiled
Agda runner also exercised ten receiver/reporting checks: payer balance after
fees, recipient balance, separation of accounts/assets, replay rejection, refusal
of forged outcome claims, unauthorized/underfunded adoption refusal, and admission
of an honest rejected event. All ten passed, together with the fifteen structured
ledger checks; the temporary IO runner and build outputs are not part of the
specification.

This execution exercises custody event admission and reporting, not a running
deployment of the eight surrounding architecture components. The whole-architecture
claim is the parameterized theorem, conditional on the stated relay laws.

# Finalized ledger

This is an abstract ledger for **finalized transactions only**. An accepted step
is treated as an indivisible, permanent update of this model's state. Finality is
an assumption at this boundary, not a theorem about a consensus protocol. There
are no pending transactions, reorganizations, rollback, probabilistic-finality
thresholds, or claims about which parts of a native Midnight transaction can be
adopted. Rejection atomicity below is a property of this abstract transition,
**not** a native Midnight atomicity or refinement result.

## Reading route

Start at [`Passport`](../src/Passport.agda), then read:

1. [`FinalizedLedger`](../src/Passport/FinalizedLedger.agda): transaction/state
   records, derived debits and credits, validity, and the `finalize` transition.
2. [`FinalizedLedgerProperties`](../src/Passport/FinalizedLedgerProperties.agda):
   explicit accounting, authorization, rejection, and replay theorem statements.
3. [`FinalizedLedgerProof`](../src/Passport/FinalizedLedgerProof.agda): proof
   implementations, linked directly from the property bindings.

The root appendix links concrete examples separately from this main route.

## Structured effects and trust boundary

Account, asset, and transaction identifiers are generic types with decidable
equality. A transaction carries an identifier, an explicit list of transfers
(sender, recipient, asset, natural-number amount), and a fee (payer, asset,
amount). State contains account/asset balances, a cumulative per-asset fee pool,
and the history of accepted transaction identifiers.

The transaction's effects are derived from these fields. Transfer amounts
contribute to the sender's gross debits and recipient's gross credits in the
specified asset. The fee contributes to its payer's gross debits and the fee
pool, not to a recipient balance. This gives a structured alternative to an
arbitrary `ChainEvent → ℤ` valuation: the amount and direction of an effect are
not independently chosen by a valuation function. The older generic architecture
accounting theorem remains generic; this work does not instantiate that theorem
with this ledger.

Before acceptance, each touched account/asset cell must cover **all** its gross
debits from its prestate balance. Repeated transfers and a transfer overlapping
the fee payer are aggregated before that comparison. Incoming credits, including
a self-transfer, cannot make an otherwise underfunded transaction eligible. A
funded self-transfer restores the transferred amount, but still pays any fee.

Authorization is a supplied decidable predicate on the **whole transaction and
the prestate**. It is not a Boolean assertion supplied by the transaction itself.
The ledger checks that predicate and proves that acceptance requires it. The
meaning and correctness of the policy are an explicit trust boundary: signature
verification, key ownership, recovery, revocation, custody permissions, and
cryptographic assumptions are not established here. A policy may inspect every
transaction field and the current state; a policy that permits everything
provides no meaningful authority guarantee.

## What the properties establish

- For an accepted step, each account/asset balance is exactly its old balance
  minus its aggregated gross debit plus its aggregated transfer credit.
  Prefunding makes natural-number subtraction exact rather than an overdraft
  hidden by truncation.
- The fee pool increases by exactly the declared fee in its declared asset;
  other assets' fee pools do not change. Fees are accounted for, not silently
  destroyed.
- Acceptance requires sufficient funds, authorization, and a fresh identifier.
- Rejection preserves the **entire state**: balances, fee pools, and accepted-ID
  history. A rejected identifier is not consumed and can be retried if the
  acceptance conditions subsequently hold.
- An accepted identifier cannot be accepted again, including after intervening
  finalized steps. This prevents replay of that identifier; it does not prevent
  a newly identified transaction with similar contents if the policy permits it.

The accounting claims are pointwise, per account/asset and per fee-pool asset.
Transfers have matched debit and credit amounts by construction. There is no
finite account registry or finite-support assumption here, so this is not a
claim about a sum over all accounts or a global finite-total conservation theorem.

## Limits and next integration boundary

This ledger does not prove Midnight finality, implement native transaction
semantics, or refine the contract DSL into a native ledger. In particular,
abstract rejected-state preservation says nothing about native partial transaction
adoption. Custody/routing instantiation and the connection to the existing
architecture's local accounting hypotheses are issue **#7**, not completed by
this work. The maturity inventory in issue #5 is also outside this change.

## Executable examples

[`FinalizedLedgerExamples`](../src/Passport/FinalizedLedgerExamples.agda) uses
natural-number identifiers and a deliberately illustrative authorization policy.
It proves concrete accepted balances and fee totals, rejection of aggregated
repeated debits and transfer/fee overlap, funded and underfunded self-transfer
behavior, rejection of incoming-credit prefunding, separation of accounts/assets,
unauthorized rejection, and a policy outcome that changes with the prestate.
Whole-result equalities establish preservation of the entire rejected state.
History examples cover immediate duplication, replay after another accepted
transaction, and successful retry of an identifier rejected before a topup.
These fixtures are not a production authorization policy.

The exported `smokeChecks` computes named Boolean observations of `finalize`;
`smoke-checks-pass` proves that all 15 observations are true. The root module
typechecked, and a compiled Agda IO runner executed all 15 observations with
`PASS` results and no failures. Verification used Agda 2.8.0 with the pinned
`categorical-crypto` revision `f280e04f`; the temporary runner and build outputs
are not part of the specification. The examples remain safe Agda and are included
in the root module's checking closure.

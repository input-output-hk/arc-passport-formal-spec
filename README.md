# Midnight Passport — formal specification

An [Agda](https://agda.readthedocs.io/) formal specification of the Midnight
Passport project.

## Project standards

[Project guidelines](docs/project-guidelines.md) define the human-readability,
navigation, code-structure, and acceptance requirements for specifications and
advertised properties.

[Agent instructions](docs/agents/workflow.md) define the mandatory review workflow;
[reviewer instructions](docs/agents/readability-reviewer.md) define its execution.

Start the formal reading route at [`src/Passport.agda`](src/Passport.agda):
full-account execution, its definitions and deployment-rooted local histories →
symbolic signing and adversarial interleavings → concrete authorization and recovery
occurrences → grants-map effects and per-issuance spending → unshielded accounting →
restricted outsider preservation → local VM properties → the earlier post-bootstrap
recovery contract and admission/authority properties.

The [proof status report](docs/proof-status-report.md) inventories checked results,
unfinished obligations and implementation findings.
The ordered [authorization statement map](docs/conformance-testing-plan.md#authorization-statement-map)
and [local history results](docs/conformance-testing-plan.md#local-history-invariants)
link each statement module and explain its role.

The [pinned-main correspondence run](docs/conformance-testing-plan.md#pinned-main-full-account-execution)
covers the constructor and all 52 impure circuits at Passport
`fc19e471536febb2133f20e817847251622dcdf5`: bootstrap, jubjub/k256/P-256
authentication, devices, grants, custody, inbox and recovery.
The full-account route begins with [`Passport.Account`](src/Passport/Account.agda).
[`FullAccountProperties`](src/Conformance/FullAccountProperties.agda) states
structural atomicity/determinism and stale-record rejection by the executable
grant guard. [`VMProperties`](src/Conformance/VMProperties.agda) states local
interpreter, codec and typed map/set results. The full-surface comparison is
not a universal compiler-refinement or on-chain proof.
[`AccountLifecycle`](src/Passport/AccountLifecycle.agda) instantiates generic
[deployment-rooted histories](src/Midnight/ContractDSL/Lifecycle.agda) with
`Account.Transition`; runtime traces can retain refusals from known entrypoints
but cannot record a constructor call or unknown name. Its
[induction rules](src/Midnight/ContractDSL/LifecycleProperties.agda) leave the
invariant and preservation obligations explicit. These are finite local
histories with no security or environment assumption selected; the
[lifecycle scope](docs/conformance-testing-plan.md#deployment-rooted-local-histories)
states what they do not establish, including
[P5′](docs/security-properties.md#p5--recovery-driven-authority-replacement) and
[P11](docs/security-properties.md#p11--transaction-safety).

The optional [symbolic security model](docs/conformance-testing-plan.md#symbolic-signing-and-adversarial-histories)
adds trusted abstract approvals, explicit signing, permanent key compromise and
replayable signature knowledge.
[`AccountSecurity`](src/Passport/AccountSecurity.agda) connects that vocabulary to
concrete source requests and verification gates; its
[contract-level scope](docs/conformance-testing-plan.md#contract-level-authorization-evidence)
separates evaluator guards, conditional symbolic provenance, and the still-open
concrete cryptographic realization and ledger-adoption correspondence. Abstract
approval is not human consent, and these local statements are not the top-level
security promises.

[Recovery assurance](docs/conformance-recovery.md) records the concrete repair,
corrected-model device-authority results and historical pinned gate evidence.
The recovery route follows
[`AccountRecovery.contract`](src/Passport/AccountRecovery.agda) →
[`Contract.Admissions`](src/Midnight/ContractDSL/Contract.agda) (instantiated as `AccountRecovery.Chain`) →
the advertised execution and authority properties. This is the post-bootstrap
recovery-relevant **shared account** slice, not a separate deployed contract.
The [recovery specification](docs/recovery-specification.md) states the guard,
initial-safety and separate trace-policy assumptions and remaining obligations.
The [conformance plan](docs/conformance-testing-plan.md)
and [historical custody spike](docs/conformance-spike.md) provide supporting context.
The [runtime transition monitor](docs/conformance-recovery.md#runtime-transition-monitor)
provides the triple checker, serialization, Haskell/C APIs and implementation fixtures.

## References

- **Main repository:** [midnightntwrk/passport](https://github.com/midnightntwrk/passport)
  + [Key passport properties](https://github.com/midnightntwrk/passport/blob/main/docs/plans/PROMISES.md)
  + [Security properties](docs/security-properties.md)
- **Rendered documentation:** <https://input-output-hk.github.io/arc-passport-formal-spec/>

## Contract DSL

- [`Ledger`](src/Midnight/ContractDSL/Ledger.agda): deterministic typed operations
  and current-state replay that checks each recorded result.
- [`Program`](src/Midnight/ContractDSL/Program.agda): sequential programs, assertions,
  explicit publication events, deferred time conditions, evaluation and ordered replay.
- [`Properties`](src/Midnight/ContractDSL/Properties.agda): successful replay
  agrees with re-evaluation; same-view replay succeeds when time conditions hold;
  `replay-eligible` proves all time conditions of an accepted journal hold.
- [`Hoare`](src/Midnight/ContractDSL/Hoare.agda): outcome predicates covering
  success and rejection, with rules for pure results, assertions, ledger operations
  and sequencing, successful-bind decomposition (`bind-success`), and replay lifting.
- [`Contract`](src/Midnight/ContractDSL/Contract.agda): typed entry
  points, evaluation-certified transactions, admission and traces.
- [`AdmissionProperties`](src/Midnight/ContractDSL/AdmissionProperties.agda):
  same-view admission, accepted execution and time eligibility (`accepted-eligible`),
  rejection atomicity and invariant preservation across admissions.
- [`Protocol`](src/Midnight/ContractDSL/Protocol.agda): transaction submission,
  publication receipts, and protocol reachability and invariant preservation.
- [`Storage`](src/Midnight/ContractDSL/Storage.agda) defines a
  vocabulary of storage codes.
- [`Storage.Properties`](src/Midnight/ContractDSL/Storage/Properties.agda) proves
  the generated lens laws.

### Protocol adapter

`Protocol.toProtocol initial` wraps contract admission as a categorical-crypto
protocol. Each `Submission` supplies a slot and an evaluation-certified transaction;
the receipt contains the verdict and, on acceptance, the journal's published values.
Rejection leaves the state unchanged and returns no publications.

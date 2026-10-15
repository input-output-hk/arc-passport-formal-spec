# Midnight Passport — formal specification

An [Agda](https://agda.readthedocs.io/) formal specification of the Midnight
Passport project.

## Project standards

[Project guidelines](docs/project-guidelines.md) define the human-readability,
navigation, code-structure, and acceptance requirements for specifications and
advertised properties.

[Agent instructions](docs/agents/workflow.md) define the mandatory review workflow;
[reviewer instructions](docs/agents/readability-reviewer.md) define its execution.

[Recovery assurance](docs/conformance-recovery.md) records the concrete repair,
checked corrected-model device-authority results, and pinned executable gate.
Start the formal reading route at [`src/Passport.agda`](src/Passport.agda):
[`AccountRecovery.contract`](src/Passport/AccountRecovery.agda) →
[`Interpreter.Admissions`](src/Midnight/ContractDSL/Protocol.agda) (instantiated as `AccountRecovery.Chain`) →
the advertised execution and authority properties. This is the post-bootstrap
recovery-relevant **shared account** slice, not a separate deployed contract.
The [recovery specification](docs/recovery-specification.md) states the guard,
initial-safety and separate trace-policy assumptions and remaining obligations.
The [conformance plan](docs/conformance-testing-plan.md)
and [historical custody spike](docs/conformance-spike.md) provide supporting context.

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
  agrees with re-evaluation; successful evaluation replays on its own view when
  its time conditions hold.
- [`Hoare`](src/Midnight/ContractDSL/Hoare.agda): outcome predicates covering
  success and rejection, with rules for pure results, assertions, ledger operations
  and sequencing, and lifting through successful replay.
- [`Contract`](src/Midnight/ContractDSL/Contract.agda): typed entry
  points, evaluation-certified transactions, admission and traces.
- [`AdmissionProperties`](src/Midnight/ContractDSL/AdmissionProperties.agda) proves
  various correctness properties.
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

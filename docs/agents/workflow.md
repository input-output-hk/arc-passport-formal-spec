# Agent workflow for human-facing work

The [general project guidelines](../project-guidelines.md) define **what** the
finished work must provide. These instructions define **how** agents produce,
check, and hand off that work. Follow the
[classification instructions](classification.md) for library/exception labels
and their authoritative [register](classification.md#review-register).

## Mandatory review loop

Before asking for human review, agents must submit every completed work package
that affects human-facing material to an independent, read-only readability
review subagent. This includes specifications, advertised statements, relevant
dependency definitions, proofs intended for readers, navigation, documentation,
comments, and library or exception classifications. Review the affected reading
route and semantic context, not just changed lines. Purely internal changes
that do not affect that material do not require this readability review.

1. Give the reviewer the general guidelines, the work package's scope and changed
   files, its reader entry points, relevant register entries, and verification
   evidence. Include unresolved findings and responses from earlier rounds.
   Instruct it not to edit source or run unrelated builds, tests, or formatters.
   Permit `pagda`-backed dependency inspection and its generated artifacts.
2. Require an explicit outcome: `accepted`, `changes-required`, or
   `blocked-on-input`. Findings must identify affected material, explain the
   comprehension or navigation problem, and state what needs resolving without
   exposing private metrics. Acceptance must apply to the actual revision
   reviewed, not an intended future change.
3. Address actionable findings, perform the applicable verification, and rerun
   review on the revised package and affected context. A reasoned response may
   challenge a finding, but the implementing agent cannot dismiss it and
   self-certify acceptance. Proposed exceptions follow the register's acceptance
   process; they do not silently waive a finding.
4. Continue until the reviewer explicitly accepts the package or a concrete
   blocker makes further progress impossible without unavailable input.
   An arbitrary round limit, repeated disagreement, or inconvenient remediation
   is not itself a blocker. If progress stalls, identify the unresolved decision,
   evidence, and alternatives rather than repeating identical review rounds.
5. On acceptance, retain a concise handoff record of the reviewed revision,
   outcome, resolved findings, and verification evidence. Request human review
   only after this gate and the applicable formal checks are satisfied.
   Later changes affecting human-facing material require renewed review.

If blocked, finish all independent actionable work, then request the specific
missing input with unresolved findings, attempted resolutions, and the reason
the agent cannot proceed. This is a request to unblock work, not a claim that
the package is ready for human review. Reviewer acceptance does not replace
human approval.

Invoke the project agent `readability-reviewer`, defined in
[`.omp/agents/readability-reviewer.md`](../../.omp/agents/readability-reviewer.md),
by name. It is source-read-only, permits `pagda`-backed dependency inspection,
cannot spawn agents, and returns a structured verdict.
Its reviewer-facing diagnostic rubric is not secret: repository access
also permits reading its instructions. Implementers must follow qualitative
guidelines rather than optimize for the rubric.

The agent uses Claude Sonnet 5.5 (`anthropic/claude-sonnet-5-5`) for routine review.
It trusts accepted, in-scope library and exception labels: reusability,
factorability, and second-application judgments belong to separate classification
review, not this agent. It checks label resolution, status, and scope.

Agda's dependency-graph backend supplies module imports, not the definition-level
lookup closure. The reviewer combines that graph with source/reference inspection;
it must disclose unresolved dependencies rather than assume a complete closure.

If the reviewer requests stronger semantic review, invoke the same agent with
an available stronger model and preserve the findings and responses. Model
limitations are not a reason to accept unread material. If the dedicated reviewer
cannot be invoked, or no capable reviewer is available, report the concrete
missing prerequisite rather than bypassing the review gate.

## Review findings and measurement

Delegate precise measurement to the independent reviewer. Its procedures and
thresholds belong in the [reviewer instructions](readability-reviewer.md), not
in implementation guidance or public acceptance rules.

Measurements are diagnostic evidence, not acceptance gates. A large closure
should prompt investigation; a small one does not establish readability.
Review must detect compressed formatting, opaque predicates, and excessive
navigation or explanatory overhead. Library-boundary justification belongs
to classification review; the readability reviewer checks recorded status and scope.

Walk the intended entry-point route, read each affected statement and its
lookup closure without opening the proof implementation, and then locate that
implementation and supporting material. Record unresolved readability issues
as unmet acceptance criteria, not as work obviated by successful typechecking.

The reviewer must report concrete comprehension obstacles and actionable
reasons, without disclosing exact metrics, counts, or thresholds. It must not
request changes merely to pass a private measurement. Authors must be able to
answer a finding through clearer presentation or a reasoned exception without
knowing the numerical trigger. The reviewer reports findings; it does not edit
code, add labels, or approve its own proposed library boundaries.


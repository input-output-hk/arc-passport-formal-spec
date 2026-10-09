# Library and exception classification instructions

Apply the [general guidelines](../project-guidelines.md) when proposing library
boundaries or readability exceptions. This document defines the labels, review
records, and lookup procedure used by agents and keeps the authoritative register.
The readability reviewer checks recorded status and scope; separate classification
review establishes whether a proposed boundary or exception is justified.

## Establishing a boundary or exception

When a property cannot meet the readability target, simplify it or extract
suitable parts of its dependency tree into genuine library code, unless a
justified exception is accepted. Identify the reusable concept, remove incidental
Passport-specific assumptions and dependencies, and demonstrate a second,
meaningfully different application. Link the evidence in a proposed register
entry and obtain classification review before relying on the new boundary.

For an exception, identify its exact scope and guideline, explain the necessary
complexity and alternatives considered, and record why the result remains
understandable. Keep the rationale in the register and link it from the affected
material rather than diluting the main presentation.

## Labels and scope

Use these exact, searchable Agda comment forms:

```agda
-- Library: LIB-<stable-name>
-- Readability-exception: EXC-<stable-name>
```

Each identifier must resolve to an entry in the [review register](#review-register).
The forms above are templates, not granted classifications. Keep only the label
and a link to its entry beside the code; put evidence and rationale in the
register. Labels identify claims; the register's status determines whether they
are accepted.

- **Library scope:** put the label in a module's file header. It covers definitions
  declared in that module, not imported or re-exported definitions or other files
  in its namespace. Separate mixed library/application code before applying a
  module-wide label; do not use scattered per-definition library exemptions.
- **Exception scope:** put the label immediately before an affected declaration,
  or in the file header for a module-wide exception. The register must name the
  exact module or qualified declarations and the guideline being excepted.
- **Default:** unlabelled repository code is non-library. A missing entry,
  mismatched scope, or non-accepted status grants no library boundary or exception.
  Do not infer classification from a directory name or a dependency's reputation.
- **External libraries:** register accepted dependencies with their package
  identity and explicit module scope; no modification of upstream sources is
  needed. Repository-local wrappers still need their own classification.
- **Lifecycle:** use `proposed`, `accepted`, or `retired`. Acceptance requires
  a recorded review decision, not merely an implementing agent adding a label.
  Record the decision's reviewer and reference. Reassess affected entries when
  their scope, assumptions, or supporting evidence changes. Do not reuse retired
  identifiers.

To classify code quickly: inspect its module header (or the external dependency
entry), resolve the identifier, and check accepted status and scope. For an
exception, also check the declaration label and the specific guideline covered.
No broader repository investigation should be necessary to determine the
recorded classification; evaluating whether it remains justified is review work.

## Review register

This section is the authoritative register. There are currently no registered
library boundaries or readability exceptions; this document does not classify
existing code.

Give each entry a heading using its stable identifier so that source labels can
link directly to it. Every entry must include:

- **Status and scope:** lifecycle status and exact modules or declarations;
  package identity for external code.
- **Decision:** reviewer and a reference to the acceptance decision, or an
  explicit statement that review is pending.
- **Library evidence (`LIB-`):** the reusable concept, interface and assumptions,
  why it can be cleanly factored out, and links to concrete applications to two
  meaningfully different tasks with an explanation of their difference. For an
  established external library, identify its documented API and reusable purpose;
  the two-task demonstration is required for newly extracted project code.
- **Exception rationale (`EXC-`):** the qualitative guideline being excepted,
  necessary complexity, alternatives considered, and why the scoped presentation
  remains understandable. Do not include private measurement results.


# Project guidelines: readable and explorable formalization

## Goal and scope

The specification and the theorems we prove about it must be human-readable
and explorable. Machine-checked correctness is desired, but is not by itself
an acceptable project outcome. A reader must be able to find the intended
material, see the high-level picture, and understand the advertised claims
without first studying their proofs or implementation machinery.

These guidelines describe what successful project work provides: the qualities
of the specification, its theorems, and their presentation. They define outcomes,
not the tools or workflow used to achieve them.

## Entry point and navigation

- Maintain a top-level module as the reader's entry point (`src/Passport.agda`).
  It must import the reader-facing specification and main property modules,
  with a clear reading order and brief labels explaining their roles.
- Everything intended for human consumption must be reachable from
  that entry point with no extra indirection. Use module imports for
  formal material and explicit links for supporting prose. A
  transitive implementation dependency alone is not a reading guide.
- Keep the main route focused on the specification and advertised properties.
  Either omit supporting material from the entry point's main imports or put
  it in a clearly marked appendix section, visibly distinct from the main route.
- Provide discoverable routes to proofs, helpers, library material, and other
  supporting content intended for readers through the appendix or links from
  the relevant modules. Readers must not need to search the repository to find
  a claim's proof or its assumptions.

## Main properties: statements and proof references

Each advertised property must have a dedicated reader-facing home, either alone
or with a tightly related group of properties. Write its type explicitly and
provide a proof binding that is a direct reference to the real proof in a separate
implementation module. A bare re-export is not enough: readers must see the claim
and that it has a checked proof, without opening the proof implementation.

For example, given a proposition `P` in `Definitions` and a proof in `Proof`:

```agda
module Properties where
open import Definitions using (P)
import Proof

theorem : ∀ x → ∃[ y ] P x y
theorem = Proof.theorem
```

Necessary parameter instantiation of a proof reference is allowed, but
proof logic belongs in the `Proof` module (or other modules imported
by it).

The `Proof` and `Properties` may import the specification and shared
definitions. Put substantial shared predicates in an appropriate
definitions module rather than creating an extra statement module for
every theorem. The proof reference itself does not pull proof
implementation into the statement's comprehension closure.

A property statement must make its assumptions, scope, and conclusion clear.
Naming a large opaque predicate is not enough: the definitions behind that
predicate are part of what the reader must understand.

### Comprehension

Assuming knowledge of the relevant library code, a reader should be able to
grasp an advertised statement in a short, focused reading. This includes its
lookup closure: all non-library definitions recursively needed to understand
its types, assumptions, operations, and conclusion.

A short statement is not necessarily simple. Opaque predicates, compressed
formatting, and excessive navigation can hide complexity rather than reduce it.
The aim is understanding, not a small source-line count.

### Exceptions

An exception must have a specific justification: the affected material and
guideline, why the additional complexity is necessary, which simpler alternatives
are unsuitable, and why the result remains understandable. Neither “the proof
checks” nor “the code is already written this way” is sufficient.

Exceptions must be clearly marked, with rationale directly reachable without
cluttering the main presentation. Each applies only to the identified material
and guideline; it does not turn the affected code into library code.

## Library code is an earned boundary

Library code may live in this repository; it does not have to be an external
dependency. However, it must be sufficiently general-purpose that it could
cleanly be factored out. Moving Passport-specific definitions to a directory
named `Library` does not make them library code.

Newly extracted library code must provide:

- A reusable concept and an interface independent of the original property's
  incidental details.
- Explicit assumptions, without unnecessary Passport-specific dependencies.
- Concrete applicability to a second, meaningfully different task. A renamed
  example or another instance of the same original task is not enough.
- Discoverable evidence of both applications and an explanation of what makes
  them meaningfully different.

The goal is reusable knowledge that a reader can reasonably bring to the
statement, not a way to hide its complexity.

### Visible library boundaries and exceptions

Readers should be able to tell quickly which definitions are assumed library
knowledge and where a readability exception applies. Unlabelled code is not
assumed library knowledge.

## Specification structure and helper placement

Specification files must be dedicated to the specification
itself. Proofs, proof infrastructure, demonstrations, and unrelated
machinery lives elsewhere. The main files should expose the model, its
operations, and their relationships without requiring a reader to wade
through complicated helper implementations.

Apply the same concern for readability as for properties, while allowing more
complexity in an entire specification than in an advertised statement.
For each definition, balance two costs:

- **Colocation:** the helper dilutes the main file and interrupts its high-level
  story.
- **Separation:** following a definition into another file has a fixed navigation
  and context-switching cost, even when the definition is short.

Keep short, easy helpers near their uses when that makes the specification
easier to follow. Put complicated helpers in separate, purpose-specific files
with clear names and interfaces. Length is a strong indicator, not the sole
criterion: conceptual complexity, relevance to the main model, and the cost of
looking it up also matter. Neither “one definition per file” nor “all helpers
inline” is a suitable blanket rule.

## Comments and file headers

Comments consume the same reader attention as code. Retain them when their
explanatory value outweighs the dilution: for example, to explain a non-obvious
modeling choice, an assumption, or why a definition takes a particular form.
Do not narrate syntax or repeat what names and types already say.

Inline comments face an especially high bar because they interrupt reading the
definition itself. Prefer clearer names and structure where those convey the
same information. This is not a reason to omit necessary explanations.

File headers may be slightly more expansive: a short orientation, prerequisites,
and a reading or proof link can save substantial lookup effort. They must still
be concise. Move extended background and discussion into linked supporting
material rather than a long header in the main reading path.

## What a successful contribution provides

Successful work satisfies the following expectations in addition to type-checking code:

- **Reachability:** reader-facing material is reachable from the top-level
  entry point; the main route and any appendix are clearly distinguished.
- **Specification focus:** specification files contain the model rather than
  proofs or unrelated machinery; helper placement preserves the high-level
  picture while avoiding needless lookups.
- **Statement/proof separation:** advertised properties have dedicated files
  with explicit theorem types and direct bindings to separate proof implementations.
  Proof logic stays in those implementations, which do not import the advertised
  modules.
- **Comprehensibility:** assumptions, conclusions, and the non-library definitions
  behind a statement can be understood together without studying its proof.
  Any necessary exception is explicit and justified.
- **Library legitimacy:** library boundaries are clearly marked and cleanly
  factorizable; newly extracted code has a concrete second, meaningfully different
  application.
- **Exception visibility:** exceptions have clear scope and discoverable rationale.
- **Presentation:** each definition's placement and each comment earns its
  reading cost; inline comments are especially selective and headers stay short.
- **Formal verification:** the relevant specification and proofs type-check.
  This establishes neither readability nor a usable reading route.

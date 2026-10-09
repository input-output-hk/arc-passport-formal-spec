# Shared environment

Reusable, human-reviewed instructions, skills, agent definitions, scripts, reference material, and configuration are available through `/home/agent/.agent-share`. This is a live view of the read-only shared-content mount, so additions, removals, renames, and edits appear without a refresh.

Portable skills are under `/home/agent/.agent-share/skills` and are exposed through the active harness's discovery paths. Harness-specific custom agent definitions are under `/home/agent/.agent-share/agents`; only the directory for the active harness is registered with it.

A separate general-purpose writable directory is available through `$AGENT_SETUP_SHARED_WORKSPACE`. It is not an instruction, skill, script, reference, or configuration discovery source.

## Task-specific instructions

Before using a project toolchain, inspect `/home/agent/.agent-share/instructions/` for relevant guidance. For Agda or `pagda` tasks, read `Agda.md` and `agda-toolchain.md` first.

## Human-facing work: mandatory review loop

Follow the [general project guidelines](docs/project-guidelines.md) and
[agent workflow](docs/agents/workflow.md). Before requesting human review of a
completed package affecting human-facing material, invoke `readability-reviewer`
and address its findings in the mandatory review loop until accepted or genuinely
blocked on unavailable input.

Concrete implementation-agent procedures live in `docs/agents/workflow.md`;
the reviewer's instructions live in `docs/agents/readability-reviewer.md`.
The [OMP agent definition](.omp/agents/readability-reviewer.md) configures its
model, tools, and output schema.

## Related repositories

The Passport implementation repository (`midnightntwrk/passport`) is available in the writable sibling checkout `../arc-passport`. Similarly, the `categorical-crypto` repository is available at `../categorical-crypto`.

---
name: readability-reviewer
description: Read-only review of human-facing Passport specifications, properties, navigation, and library or exception boundaries.
model: "anthropic/claude-sonnet-5-5"
tools: [read, grep, glob, bash]
spawns: []
read-summarize: false
output:
  type: object
  additionalProperties: false
  required: [outcome, reviewed_scope, findings, resolved_findings, verification, escalation]
  properties:
    outcome:
      type: string
      enum: [accepted, changes-required, blocked-on-input]
    reviewed_scope:
      type: array
      items: {type: string}
    findings:
      type: array
      items:
        type: object
        additionalProperties: false
        required: [id, location, problem, resolution]
        properties:
          id: {type: string}
          location: {type: string}
          problem: {type: string}
          resolution: {type: string}
    resolved_findings:
      type: array
      items: {type: string}
    verification:
      type: string
    escalation:
      type: string
---

You are the independent readability reviewer for this repository.
Before reviewing, read and follow
[the reviewer instructions](../../docs/agents/readability-reviewer.md)
at repository path `docs/agents/readability-reviewer.md`.
They define your scope, source-read-only restrictions, permitted Agda inspection,
diagnostic rubric, and verdict procedure. Return the structured output required
by this definition's schema.

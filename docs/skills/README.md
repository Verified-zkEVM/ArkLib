# ArkLib Skills

This directory holds reusable cross-cutting workflows that are not tied to one subsystem or one
part of the repo.

Use `docs/wiki/` for repo-specific maps, commands, and source-of-truth rules.
Use `docs/skills/` for general agent workflows that may apply across many files or tasks.

## Maintenance Rule

Skills are living docs.

After using a skill, review whether it should be updated:

- If you encountered a new recurring pattern, caveat, or failure mode, add it.
- If an existing instruction was incomplete, stale, or misleading, correct it.
- If the skill still fits the task but needs a cleaner split, extend it or add a new skill page.
- Avoid churn for one-off incidents; prefer updates that are likely to help the next agent.

## Available Skills

- [`fix-lean-warnings.md`](fix-lean-warnings.md) - workflow for cleaning Lean 4 linter and style
  warnings safely and incrementally.

# ArkLib Agent Wiki

This directory is the deeper companion to `AGENTS.md`.
Use `AGENTS.md` for the one-screen overview and this wiki for details that are too specific or
too changeable to keep at the repo root.
For reusable cross-cutting workflows that are not tied to one repo area, see
[`../skills/README.md`](../skills/README.md).

## Start Here

- [`quickstart.md`](quickstart.md) - canonical agent command and validation playbook.
- [`repo-map.md`](repo-map.md) - where to edit and how the main subtrees relate.
- [`generated-files.md`](generated-files.md) - derived outputs and their sources of truth.
- [`blueprint-and-citations.md`](blueprint-and-citations.md) - blueprint workflow, paper
  references, and citation keys.

## Maintenance Contract

- `AGENTS.md` is the canonical root guide. `CLAUDE.md` is only a symlink.
- Keep one primary owner topic per page. The current pages are:
  - `quickstart.md` for commands, validation, and when to run which checks.
  - `repo-map.md` for repo structure and main work areas.
  - `generated-files.md` for derived outputs and source-of-truth rules.
  - `blueprint-and-citations.md` for blueprint workflow, references, and citation updates.
- Add new pages when a recurring topic no longer fits cleanly in an existing guide.
- If a PR changes commands, repo structure, generated-file behavior, or the paper workflow,
  update the matching page in the same PR, or add a new page when that is the cleaner split.
- Keep these files committed so worktrees and delegated agents see the same guidance.
- Promote recurring, repo-specific agent learnings here once they prove stable.
- Prefer links to canonical docs over copying their contents.

## Canonical Project Docs

- [`../../README.md`](../../README.md) - project overview.
- [`../../CONTRIBUTING.md`](../../CONTRIBUTING.md) - style, naming, docstrings, citations, and
  large contributions.
- [`../../ROADMAP.md`](../../ROADMAP.md) - planned directions.
- [`../../BACKGROUND.md`](../../BACKGROUND.md) - background references.

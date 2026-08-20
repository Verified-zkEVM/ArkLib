# ArkLib Skills

This directory holds reusable agent workflows — the *how* of a recurring task, as opposed to the
repo facts in `docs/wiki/` and the paper knowledge in `docs/kb/`.

Most skills here are subsystem-independent. `prove-milestone.md` is the exception: it is written
against the Hachi development, and is kept because that workflow is exercised repeatedly.

## Maintenance Rule

Skills are living docs.

After using a skill, review whether it should be updated:

- If you encountered a new recurring pattern, caveat, or failure mode, add it.
- If an existing instruction was incomplete, stale, or misleading, correct it.
- If the skill still fits the task but needs a cleaner split, extend it or add a new skill page.
- Avoid churn for one-off incidents; prefer updates that are likely to help the next agent.
- Record the *rule*, not the incident. A skill page should not accumulate dated run logs, PR
  numbers, or findings from one review; distil what recurs and drop the rest.

## Available Skills

- [`discharge-lemmas.md`](discharge-lemmas.md) - workflow for triaging, placing, stating, and
  proving `sorry`s and open proof obligations, then summarizing what is proved vs. deferred.
- [`prove-milestone.md`](prove-milestone.md) - four-stage, paper-audited workflow for freezing and
  constructively proving one Hachi milestone, then improving the workflow from run evidence.
  Hachi-specific; the staging discipline generalizes.
- [`fix-lean-warnings.md`](fix-lean-warnings.md) - workflow for cleaning Lean 4 linter and style
  warnings safely and incrementally.
- [`make-pr-ready.md`](make-pr-ready.md) - checklist to get a branch PR-ready: follow the
  contribution guidelines, fix Lean warnings, regenerate citations, clean up references to files
  the branch deleted, and suggest skill improvements.

# /fix-lean-warnings

Use this workflow when the task is to clean Lean 4 linter or style warnings in `.lean` files.
This is a general skill, not a subsystem guide.

## Goal

Fix warnings with the safest edits first, re-check after each batch, and persist until the file is
clean.

## Basic Workflow

1. Check warnings with `lake build ArkLib.Path.To.Module` (or `lake build ArkLibTest.Path.To.Module`
   for an acceptance test). Lake prints each warning with its file and line. Use the module build,
   not `lake env lean`: only the build applies the package's Lean options and the source-policy
   plugin, so a direct `lake env lean` run can miss warnings the project rejects.
2. Group warnings by type.
3. Fix one category at a time, starting with the safest categories.
4. Rebuild the module after each batch.
5. Do not stop until the module builds with no warnings.
6. Finish with `./scripts/validate.sh`, which enforces the warning budgets and the source-policy
   gate across the library and the acceptance tests.
7. After the lint-cleanup pass, review this skill and update it if you found a new recurring
   warning pattern, a better fix strategy, or a correction to existing guidance.

## Safety Order

| Rank | Warning type | Usual fix |
| --- | --- | --- |
| 1 | Empty lines within commands | Remove blank lines inside proofs or replace with a short comment |
| 2 | Long lines | Break at binders, `:`, `=`, long arguments, or long subexpressions |
| 3 | Isolated `·` | Merge `·` with the next tactic line |
| 4 | Whitespace / notation style | Apply the exact spacing the linter asks for |
| 5 | Long file | Split at a conceptual API or proof boundary before 1500 lines; do not add linter suppressions or exception watermarks |
| 6 | Unused tactic | Delete the no-op tactic |
| 7 | Deprecated names | Replace with the linter-suggested name |
| 8 | `intro` suggestions | Collapse repeated `intro` lines into the suggested pattern |
| 9 | Unused simp arguments | Remove the unused argument from `simp` or `simp only` |
| 10 | Unnecessary `simpa` | Replace with `simp`, or `simp at h` if the linter says so |
| 11 | Flexible `simp` | Use `simp?`, then copy the suggested `simp only [...]` |
| 12 | Unused section variables / hypotheses | Prefer `omit [...] in` around the declaration |
| 13 | Multi-goal tactic | Focus the tactic with `·` or restructure it |

## High-Value Fixes

### Empty Lines Within Commands

- Remove blank lines inside `by` blocks and between consecutive `have` or `let` statements.
- If visual separation is useful, insert a short comment instead of a blank line.

### Long Lines

- Break theorem signatures at binders and long hypotheses.
- Break long `have` statements before the right-hand side.
- Line breaks are the only fix: linter suppressions are rejected by the build.

### Long File

- Split the file along a conceptual API or proof boundary before it exceeds 1500 lines.
- Do not add `set_option linter.*` or `@[nolint]`; the build-time Lean syntax-tree gate rejects
  suppressions and has no exception mechanism.

### Unused Simp Arguments

- Remove only what the linter says is unused.
- Re-run lints after each removal; fixing one argument can expose another.

### `simpa` Warnings

- Only apply the mechanical replacement when the linter explicitly says:
  - `try simp instead of simpa`
  - `Try simp at h instead of simpa using h`
- If neither message appears, treat the `simpa` as a manual refactor, not a routine lint fix.

### Flexible `simp`

- First replace warned calls with `simp?`.
- Then copy the exact `simp only [...]` suggestion from the infoview or from the
  `lake build ArkLib.Path.To.Module` output.
- If the suggestion is poor, switch to explicit `rw`, `change`, or `dsimp`.

### Unused Section Variables

- First prefer removing an unused instance or hypothesis binder outright when it is truly
  declaration-local, for example by shrinking a nearby `variable` block or dropping the binder from
  the declaration.
- Prefer `omit [Inst] in` when removing the binder would require noisier section reshaping or when
  several nearby declarations still share the same surrounding variables.
- Wrapper order matters:
  1. `open ... in`, `open scoped ... in`, `omit ... in`
  2. docstring
  3. attributes
  4. declaration

### `set_option` and slow proofs

- The source-policy gate rejects `set_option` for the `linter`, `pp`, `profiler` and `trace`
  option families and for the elaboration budgets `maxHeartbeats`, `maxRecDepth` and
  `synthInstance.*`, anywhere in the source. Delete such an option rather than re-scoping it.
- If a proof times out without its budget option, make the proof cheaper: follow
  [Tactic Mode & Performance](../../CONTRIBUTING.md#tactic-mode--performance).

## Persistence Rule

Fixing one warning often exposes new ones.
Only stop after:

1. `lake build ArkLib.Path.To.Module` succeeds with no warnings.
2. `./scripts/validate.sh` passes.
3. This skill has been reviewed for any stable updates discovered during the pass.

## Skill Evolution Rule

Treat this file as a living workflow.

- If a lint pass revealed a new recurring warning pattern, add it here.
- If a known pattern needs a better explanation, correction, or safer ordering, update it here.
- If the new guidance is broad enough to help beyond lint cleanup, move or duplicate the stable
  part into a more general skill under `docs/skills/`.
- Do not add one-off anecdotes; prefer patterns likely to recur in future Lean warning cleanup.

## Delegation Rule

When a single file has a very large number of warnings, use at most one delegated agent for that
file at a time.

- Never run multiple editors in parallel on the same file.
- For mass whitespace cleanup, prefer one scripted pass over many small manual replacements.

## Known Pitfalls

- Removing `omit [DecidableEq ...]` warnings can require `classical` inside the proof body when
  decidability is needed downstream.
- Do not try to silence a warning with `set_option linter.*`, `@[nolint]` or a file-wide disable;
  the build rejects every suppression, so fix the source instead.
- If a warning fix breaks the proof, revert that local edit and use a more explicit proof step.

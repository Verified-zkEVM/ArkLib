# /fix-lean-warnings

Use this workflow when the task is to clean Lean 4 linter or style warnings in `.lean` files.
This is a general skill, not a subsystem guide.

## Goal

Fix warnings with the safest edits first, re-check after each batch, and persist until the file is
clean.

## Basic Workflow

1. Check warnings with `ReadLints` or `lake env lean path/to/File.lean`.
2. Group warnings by type.
3. Fix one category at a time, starting with the safest categories.
4. Re-run `ReadLints` after each batch.
5. Verify with `lake env lean path/to/File.lean` after meaningful edits and once at the end.
6. Do not stop until `ReadLints` is clean.
7. After the lint-cleanup pass, review this skill and update it if you found a new recurring
   warning pattern, a better fix strategy, or a correction to existing guidance.

## Safety Order

| Rank | Warning type | Usual fix |
| --- | --- | --- |
| 1 | Empty lines within commands | Remove blank lines inside proofs or replace with a short comment |
| 2 | Long lines | Break at binders, `:`, `=`, long arguments, or long subexpressions |
| 3 | Isolated `·` | Merge `·` with the next tactic line |
| 4 | Whitespace / notation style | Apply the exact spacing the linter asks for |
| 5 | Long file | Add `set_option linter.style.longFile N` near the top with a reasonable ceiling |
| 6 | Unused tactic | Delete the no-op tactic |
| 7 | Deprecated names | Replace with the linter-suggested name |
| 8 | `intro` suggestions | Collapse repeated `intro` lines into the suggested pattern |
| 9 | Unused simp arguments | Remove the unused argument from `simp` or `simp only` |
| 10 | Unnecessary `simpa` | Replace with `simp`, or `simp at h` if the linter says so |
| 11 | Flexible `simp` | Use `simp?`, then copy the suggested `simp only [...]` |
| 12 | Unused section variables / hypotheses | Prefer `omit [...] in` around the declaration |
| 13 | Multi-goal tactic | Focus the tactic with `·` or restructure it |
| 14 | Unscoped `set_option` | Delete it first; if needed, re-scope it to the declaration |

## High-Value Fixes

### Empty Lines Within Commands

- Remove blank lines inside `by` blocks and between consecutive `have` or `let` statements.
- If visual separation is useful, insert a short comment instead of a blank line.

### Long Lines

- Break theorem signatures at binders and long hypotheses.
- Break long `have` statements before the right-hand side.
- Prefer line breaks over file-wide suppression.

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
- Then copy the exact `simp only [...]` suggestion from the infoview or from
  `lake env lean path/to/File.lean`.
- If the suggestion is poor, switch to explicit `rw`, `change`, or `dsimp`.

### Unused Section Variables

- Prefer `omit [Inst] in` rather than reshaping the entire file.
- Wrapper order matters:
  1. `open ... in`, `open scoped ... in`, `omit ... in`
  2. docstring
  3. attributes
  4. declaration

### Unscoped `set_option`

- First try deleting the inline `set_option`.
- If the proof times out, move it to declaration scope instead of keeping it inline.

## Persistence Rule

Fixing one warning often exposes new ones.
Only stop after:

1. `ReadLints` is clean.
2. `lake env lean path/to/File.lean` still succeeds.
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
- Do not suppress long-line warnings wholesale with a file-wide disable if ordinary line breaks
  will do.
- If a warning fix breaks the proof, revert that local edit and use a more explicit proof step.

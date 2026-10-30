# /discharge-lemmas

Use this workflow when the task is to clear out `sorry` placeholders or open proof obligations in
one or more `.lean` files. It triages each gap, places it well in the repo, states it as a clean
lemma, proves the tractable ones, and reports what remains.

This is a general skill, not a subsystem guide. It assumes the work happens in ArkLib's Lean 4
codebase and that `./scripts/validate.sh` is the routine build check.

## Goal

Turn a pile of `sorry`s and proof obligations into:

- a rated, triaged inventory,
- well-placed, cleanly stated lemmas,
- discharged proofs for everything rated below 6,
- and a clear summary of what is proved, what is deferred, and why.

Favor composable proofs that reuse existing Mathlib and ArkLib lemmas over new definitions.

A deferred gap is a working-branch state, not a mergeable one: `main` carries no admitted proof
debt, so a branch with a remaining `sorry` cannot merge (see
[Review and Merge Readiness](../../CONTRIBUTING.md#review-and-merge-readiness)). The one exception
is a *solicited proof*: a true, faithfully stated external result whose research-sized proof is
left open for contributors. It enters the axiom baseline's `solicited` list only after maintainer
review, with a tracking issue linked from its docstring, and nothing outside that list may depend
on it ([issue #1352](https://github.com/Verified-zkEVM/ArkLib/issues/1352),
[`scripts/README.md`](../../scripts/README.md)). Propose that route to the user; do not take it
yourself.

## Paper-driven targets: fix the statement before proving it

When the gaps belong to a theorem from a paper (a protocol's soundness, a coding-theory bound),
proving the wrong statement is the costly failure. Work in four stages:

1. **Audit the statement against the paper.** Reconstruct the paper's exact claim independently:
   quantifier order, dimensions, challenge space and distribution, verifier checks, bounds, escape
   cases and conclusion. Label every deliberate deviation as a strengthening, weakening, repair,
   generalization or representation choice, and justify its direction. Check non-vacuity: try
   small and boundary cases, confirm relations and challenge spaces are inhabited, and confirm the
   verifier does not always reject. Check that the audited theorem is the one its consumers use.
2. **Freeze the semantics.** Implement every data-bearing definition, including relations,
   verifiers, protocol specifications, extractors, conversions and witness constructors. Only
   proof bodies may contain remaining `sorry`s. Inventory those proof placeholders before
   freezing; never prove claims about data fabricated with `sorry`. Once the sorried skeleton
   states the right result and builds, record
   every target declaration's full type (`#check @Full.name`) and every data-bearing definition
   (`#print`), and keep a copy of the scoped files outside the repository, for example under
   `/tmp`. From then on only proof bodies may change.
3. **Discharge without changing frozen signatures.** Replace one proof body at a time, rebuild the
   module, and require the target's `sorry` count to drop. Never make a theorem easier by
   strengthening an input relation, weakening an output relation, shrinking a challenge space,
   adding an unmotivated hypothesis or moving a verifier check into an assumption. If a statement
   must change, return to stage 1 and say so.
4. **Verify independently.** Compare the final `#check` and `#print` output with the frozen copy,
   check `#print axioms` of each target against `{propext, Classical.choice, Quot.sound}`, and
   have a reviewer who did not write the proof re-read the statement against the paper.

## TODO List

Work through these in order. Do not skip the triage steps just because a `sorry` looks easy —
the rating and placement decisions are what keep the result maintainable.

### 1. Inventory and rate each gap

- Collect every `sorry` and open obligation in scope. Search with
  `grep -rn "sorry" path/to/scope` and cross-check against the build
  (`lake build ArkLib.Path.To.Module` surfaces `declaration uses 'sorry'` warnings and any unsolved
  goals).
- For each gap, read enough surrounding context to understand the actual goal state, not just the
  textual statement. Note the hypotheses in scope and the target type.
- Rate each gap on a 1–10 effort scale:

  | Rating | Meaning | Typical signs |
  | --- | --- | --- |
  | 1–2 | 1–2 minutes | direct `simp`/`rw`/`exact`, a known Mathlib lemma applies almost verbatim |
  | 3–5 | up to ~an hour | a few rewrites, a small induction, locating the right Mathlib API |
  | 6–7 | half a day | nontrivial induction, new auxiliary lemmas, fiddly algebra/analysis |
  | 8–10 | a day or longer | deep theory, missing upstream API, design work, or unclear math |

- Record the rating and a one-line justification per gap. This table is the first deliverable to
  the user.

### 2. Decide the best home for each lemma

- For each gap, ask: where in the repo does this lemma belong? Match the routing in
  [`../wiki/repo-map.md`](../wiki/repo-map.md):
  - reusable math / coding theory / polynomials → `ArkLib/Data/`
  - oracle computations, probability and measured programs → `ArkLib/Data/OracleComp/` (or
    upstream in VCVio when fully generic)
  - general-purpose extensions meant for upstreaming → `ArkLib/ToMathlib/`
  - interaction layer (interaction-tree protocols) and its security theory → `ArkLib/Interaction/`
  - legacy layer (oracle-reduction core) and its security theory → `ArkLib/OracleReduction/`
  - protocol-specific → `ArkLib/ProofSystem/`
  - commitment-specific → `ArkLib/Commitments/`
- Prefer keeping a lemma next to the definitions it is about, not next to the theorem that happens
  to need it. A reusable algebraic fact about an existing structure usually belongs in `Data/` or
  `ToMathlib/`, not buried in a protocol file.
- Decide whether a **new file** is warranted. Create one only when several related lemmas share a
  topic that does not fit an existing file, or when adding them would push a file past the long-file
  cap or muddy its module docstring. Otherwise extend an existing file.
- If you add, rename, or move files under `ArkLib/`, `git add` the new paths so validation sees
  them, and give each new file the Apache header + module docstring per
  [`../../CONTRIBUTING.md`](../../CONTRIBUTING.md).

### 3. State each gap as a sorried-out lemma

- If a gap is only an inline `sorry` inside a larger proof, decide whether it should be extracted
  into a named lemma. Extract when the fact is reusable, independently meaningful, or large enough
  to clutter the host proof. Keep it inline when it is a trivial step tied to local context.
- For every gap you extract or formalize, write the statement first with `:= by sorry` (or
  `:= sorry`), with a proper name (`snake_case` theorem name), docstring, and the right variable
  conventions. Make the statement self-contained and as general as is natural — but do not
  over-generalize past what the call site needs.
- Build after stating, so the `sorry`-ed lemmas typecheck and the call sites still compile against
  the new statements before you attempt any proof.

### 4. Prove everything rated below 6

- Prove every gap rated 1–5. Leave 6+ as documented `sorry`s for the summary in step 6; the
  branch cannot merge until they are proved or accepted as solicited proofs.
- Reuse first: search Mathlib and ArkLib for an existing lemma before writing anything. Use
  `exact?`, `apply?`, `rw?`, `simp?`, and `loogle`/`Loogle`-style name searches. A one-line
  `exact foo` beats a ten-line bespoke proof.
- Keep proofs composable:
  - Prefer general lemmas that several call sites can reuse over narrowly tailored ones.
  - Avoid introducing new `def`s. If you must, prefer reusing an existing definition or a plain
    `let`/term over a new top-level definition. Every new definition is new API to maintain.
  - Factor a shared sub-fact into its own small lemma rather than copy-pasting a proof block.
- Build and re-check after each proof (`lake build ArkLib.Path.To.Module`). Do not batch many
  unverified proofs.

### 5. Clean up the proofs and statements

- Re-read every proof and statement you touched (and adjacent ones if they got entangled):
  - Remove definitions, hypotheses, or intermediate `have`s that turned out unnecessary.
  - Collapse redundant steps; replace long manual chains with a single `simp`/`omega`/`ring` when
    one suffices.
  - Check that statements are not more complex than needed — drop unused binders, prefer `≤`/`<`
    over `≥`/`>`, follow the naming and symbol conventions in
    [`../../CONTRIBUTING.md`](../../CONTRIBUTING.md).
- Run [`fix-lean-warnings.md`](fix-lean-warnings.md) over the changed files so no new lint or style
  warnings ship.
- Confirm `./scripts/validate.sh` passes (add `--docs` when appropriate; style is always checked).

### 6. Summarize for the user and suggest skill improvements

- Report a concise summary:
  - the rating table from step 1,
  - for each gap: its chosen home, whether it became a named lemma or stayed inline, and its status
    (proved / deferred),
  - for deferred gaps (rated 6+): why, and what the blocker is (missing API, deep math, design
    decision) so the user can plan the follow-up, and whether any is a faithful external result
    that could be proposed as a solicited proof,
  - any cleanups made in step 5.
- Follow the Maintenance Rule in [`README.md`](README.md): tell the user how this skill could be
  improved — a recurring rating heuristic, a placement rule worth codifying, a proof tactic that
  kept paying off — and update this file if it will help the next agent.

## Persistence Rule

Only consider the task complete when:

1. Every gap in scope has a rating and a placement decision.
2. Every gap rated below 6 is proved, or you have explained precisely why a sub-6 rating turned out
   wrong (and re-rated it).
3. Every remaining `sorry` is a deliberately deferred, documented gap rated 6+.
4. `./scripts/validate.sh` passes, so every changed module builds with no warnings other than the
   deferred `sorry`s.
5. You have delivered the summary and any suggested skill improvements.

## Known Pitfalls

- A gap that looks like a 2 is often a 5 once you see the real goal state — rate from the goal, not
  the prose.
- Do not invent new definitions to make a proof go through; that trades a proof gap for permanent
  API debt. Reach for existing lemmas first.
- Extracting every inline `sorry` into a top-level lemma can bloat a file. Extract for reuse or
  size, not reflexively.
- Re-rate honestly: if a "sub-6" proof balloons, stop, mark it deferred with the new rating, and
  say so in the summary rather than forcing a brittle proof.
- A sorried definition still compiles: `sorryAx` compiles to a runtime panic, so the definition
  needs no `noncomputable` marker but fails when evaluated. If a `noncomputable` marker sits next to
  the gap, it has another cause; see [`make-computable.md`](make-computable.md) if the task is
  actually about executability.

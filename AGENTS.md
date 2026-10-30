# ArkLib Agent Guide

Lean 4 formalization of SNARK-related theory, interactive oracle reductions, and proof systems.
Start with [`README.md`](README.md) for the project overview.

`AGENTS.md` is the canonical root guide.

## Fast Start

1. For a convenient routine check, start with `./scripts/validate.sh`.
   Before committing or pushing, run it in full; it enforces repository-wide non-`sorry` warnings
   and the Lean-native source-policy gate across `ArkLib/` and `ArkLibTest/`. It also runs `lake test` and rejects all test warnings.
2. On a cold clone, run `lake exe cache get` first.
3. If you add, rename, or delete files under `ArkLib/`, `git add` new paths before validation.
4. For docstring or docs work, `./scripts/validate.sh --docs` is a convenient add-on check.
5. Only build site or blueprint output when touching `blueprint/` or `home_page/`:
   `./scripts/validate.sh --site`.
6. When changing proofs or admissions (or anything that must stay axiom-clean), run
   `./scripts/validate.sh --axioms`; it first certifies the sweep tool against its
   fixture matrix (`./scripts/test-axiomsweep.sh`), then runs the regression gate.
   A PR may be opened with unfinished proofs, but no new `sorry`/`admit` or additional
   `sorryAx` debt may merge into `main`. `scripts/axiom_baseline.json` has an empty `sorry`
   list; its only admitted entries are reviewed *solicited proofs* (issue #1352), which must
   link their issue and on which nothing outside the solicited list may depend. Refresh the
   baseline with `lake exe axiomsweep --update-baseline` only for verified closures or renames,
   never to authorize new debt; native-compiler trust is never allowlistable. See
   [`scripts/README.md`](scripts/README.md) for the rules.

## Where To Work

- `ArkLib/Data/` - reusable math, coding theory, polynomials, probability, and measured programs.
- `ArkLibTest/` - compile-time acceptance examples and regression tests; run `lake test`.
- `ArkLib/Interaction/` - the interaction layer: interaction-tree protocols and their security
  theory. It is meant to replace the legacy layer ([`README.md`](README.md#two-layers)).
- `ArkLib/OracleReduction/` - the legacy layer: IOR abstractions and security theory.
- `ArkLib/ProofSystem/` - protocol formalizations built on the core.
- `ArkLib/Commitments/` - commitments and opening arguments.
- `ArkLib/AGM/` - algebraic group model representations.
- `ArkLib/ToCompPoly/` - bridges to CompPoly's computable representations.
- `ArkLib/ToMathlib/` - local extensions intended for upstreaming.
- `docs/design/` - normative architecture of the interaction layer.
- `docs/kb/` - paper knowledge base: paper pages, concepts, and audits.
- `blueprint/src/` - blueprint TeX chapters and the bibliography (`references.bib`).
- `scripts/` - repo utilities.

## Guardrails

- Lean defaults: `autoImplicit = false`; source files must remain at or below 1500 lines.
- Source-policy exceptions and linter suppressions are not supported. Fix the source or improve the
  linter with a repository-wide, tested policy change.
- `ArkLib.lean` is generated; do not hand-edit it.
- Every file under `ArkLib/` uses Lean's module system (issue #795): `module`, `public import`,
  `@[expose] public section`. A new file must follow the same shape — `lake build` rejects a
  classic file, since the generated root imports all of them as a module. `ArkLibTest/` stays
  classic on purpose. The conventions and an error-to-fix table are in
  [`docs/wiki/module-system.md`](docs/wiki/module-system.md).
- Edit source, not derived output such as `.lake/`, `blueprint/web/`, `blueprint/print/`,
  `dependency_graphs/`, or `home_page/docs/`.
- `main` carries no admitted proof debt. The only admitted statements are the reviewed solicited
  proofs listed in `scripts/axiom_baseline.json`; any other `sorry` in a diff is new.
- New declarations may depend only on a subset of `propext`, `Classical.choice`, and `Quot.sound`;
  do not add custom axioms or native-compiler trust dependencies.
- Do not raise elaboration budgets: `set_option maxHeartbeats`, `maxRecDepth` and
  `synthInstance.*` are rejected by the source-policy gate, as are the `linter`, `pp`, `profiler`
  and `trace` option families. Make a slow proof cheaper instead.
- No backward-compatibility guarantees: rename or remove a declaration by updating every caller in
  the same PR. `@[deprecated]` aliases are discouraged; add one only with a concrete reason. See
  [`CONTRIBUTING.md`](CONTRIBUTING.md#compatibility-policy).
- Make definitions computable wherever possible. Protocols and program/value-computing APIs must
  be executable, with code-generation and runtime evidence. Document concrete blockers for purely
  mathematical noncomputable views; see [`CONTRIBUTING.md`](CONTRIBUTING.md#computability) and
  [`make-computable.md`](docs/skills/make-computable.md).
- Prefer proof scripts that expose the key mathematical steps and compose predictably. Broad
  automation is welcome when it closes a well-scoped goal quickly and clearly; for a slow proof,
  profile first, then narrow imports, local hypotheses, simp sets, or automation rules, or move a
  recurring argument into its owner layer. Do not mechanically expand a short, stable terminal
  `simp` into a brittle `simp only` list.
- If a PR changes commands, repo structure, generated outputs, or the blueprint/citation
  workflow, update the matching page in [`docs/wiki/`](docs/wiki/README.md) in the same PR.
- Promote recurring agent learnings into [`docs/wiki/`](docs/wiki/README.md); do not let stable
  guidance live only in ephemeral notes.

## Deeper Docs

- [`docs/wiki/README.md`](docs/wiki/README.md) - hub and maintenance rules.
- [`docs/skills/README.md`](docs/skills/README.md) - reusable cross-cutting workflows.
- [`docs/wiki/quickstart.md`](docs/wiki/quickstart.md) - commands and validation.
- [`docs/wiki/repo-map.md`](docs/wiki/repo-map.md) - structure and module routing.
- [`docs/wiki/generated-files.md`](docs/wiki/generated-files.md) - source-of-truth rules for
  derived outputs.
- [`docs/wiki/blueprint-and-citations.md`](docs/wiki/blueprint-and-citations.md) - blueprint,
  references, and citations.
- [`docs/design/README.md`](docs/design/README.md) - interaction-layer architecture and its
  implementation plan.
- [`docs/kb/README.md`](docs/kb/README.md) - paper knowledge base.

## Canonical Project Docs

- [`README.md`](README.md) - project overview.
- [`CONTRIBUTING.md`](CONTRIBUTING.md) - style, naming, docstrings, citations, and large
  contributions.
- [`ROADMAP.md`](ROADMAP.md) - status: what is complete, in progress, and planned.
- [`BACKGROUND.md`](BACKGROUND.md) - background theory and references, and how ArkLib's
  oracle reductions compare with the literature.

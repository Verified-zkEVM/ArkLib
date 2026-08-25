# ArkLib Scripts 

This directory contains various utility scripts for the ArkLib project.

## Available Scripts

### Build and Validation
- **`validate.sh`** - Recommended convenience wrapper for routine local validation
- **`build-project.sh`** - Compile-only helper (`lake build`)
- **`build_timing_report.sh`** - CI timing/report helper for clean builds, warm rebuilds, the native build, and the validation wrapper
- **`update-lib.sh`** - Update ArkLib.lean with all imports from source files
- **`check-imports.sh`** - Check if ArkLib.lean is up to date with all imports
- **`check-warning-log.py`** - Fail on scoped warning classes found in a captured build log
- **`AxiomSweep.lean`** (`lake exe axiomsweep`) - Kernel-level axiom/`sorry` accounting with a
  committed regression baseline (`axiom_baseline.json`); see "Axiom Sweep" below
- **`test-axiomsweep.sh`** - Executable fixture matrix certifying the axiomsweep tool itself
  (gate directions, native-trust floor, exit-code contract), against the synthetic-taint
  fixtures in `AxiomSweepTestFixtures/`
- **`ToyProblemRuntime.lean`** (`lake exe toyproblem-runtime`) - Compiled small-parameter checks
  for KoalaBear sextic arithmetic, executable interleaved-RS extraction, and the C6.9 virtual
  output-oracle and exact-extractor paths
- **`HachiRuntime.lean`** (`lake exe hachi-runtime`) - Compiled small-parameter checks that the
  nonrecursive Hachi honest-prover path executes: the balanced committer, the computable honest
  lift quotient, the concrete Ajtai lift commitment, and the terminal reveal-and-check. `--full`
  additionally runs the whole composed opening and checks the verifier accepts — it passes, in
  about six minutes, which is why it is not gated: the honest sumcheck prover dominates the cost
  of the entire chain. `--timing` reports per-check costs
- **`check-docs-integrity.py`** - Check docs links and the `CLAUDE.md` symlink
- **`lint-style.py`** - Python-based style linting
- **`lint-style.lean`** - Lean-based style linting

### Dependency Analysis
- **`dependency_analysis/`** - Complete dependency analysis toolkit
  - Generate dependency graphs for all ArkLib modules
  - Interactive exploration of dependencies
  - Visual representations (PNG, SVG)
  - See `dependency_analysis/README.md` for detailed usage

### Knowledge Base
- **`kb/`** - Scripts for syncing and inspecting the repository knowledge base
  - Export bibliography metadata
  - Extract citation usage from `ArkLib/**/*.lean`
  - Regenerate derived KB indexes, scaffold missing cited-paper stubs, and lint KB structure
  - Resolve review context from cited keys or changed Lean files
  - See `kb/README.md` for usage

## Quick Start

### Recommended Routine Validation
```bash
./scripts/validate.sh
```

### Validation With Optional Checks
```bash
# Add Lean style linting
./scripts/validate.sh --lint

# Build API docs too
./scripts/validate.sh --docs

# Build site / blueprint output too
./scripts/validate.sh --site

# Check the axiom/sorry regression baseline too
./scripts/validate.sh --axioms
```

### Generate Dependency Graphs
```bash
cd scripts/dependency_analysis
python generate_dependency_graph.py --root ../../ --output-dir ../../dependency_graphs
```

### Compile Only
```bash
./scripts/build-project.sh
```

### Toy-Problem Runtime Gate
```bash
lake exe toyproblem-runtime
```

### Nonrecursive-Hachi Runtime Gate
```bash
lake exe hachi-runtime            # the fast checks; this is what validate.sh gates on
lake exe hachi-runtime --full     # also runs the composed opening (slow)
lake exe hachi-runtime --timing   # per-check timings
```

### Build Timing Helper
```bash
bash scripts/build_timing_report.sh --help
```

### Update Library Imports
```bash
# Update ArkLib.lean with all imports
./scripts/update-lib.sh

# Check if imports are up to date
./scripts/check-imports.sh
```

### Check Docs Integrity
```bash
python3 ./scripts/check-docs-integrity.py
```

### Knowledge Base Indexes
```bash
python3 ./scripts/kb/sync_from_bib.py
python3 ./scripts/kb/extract_lean_citations.py
python3 ./scripts/kb/regenerate.py
python3 ./scripts/kb/check_generated.py
python3 ./scripts/kb/lint.py
python3 ./scripts/kb/review_context.py --files ArkLib/ProofSystem/Fri/Spec/SingleRound.lean
```

### Axiom Sweep

Kernel-level accounting of what every `ArkLib.*` declaration ultimately depends on — the
same information as `#print axioms`, computed for the whole library at once from the built
`.olean` data (so private and macro-generated declarations are included and no source
heuristics are involved). Requires a completed `lake build`.

Building the executable links VCVio's FFI static libraries, whose C sources live in git
submodules that Lake does not fetch; `./scripts/validate.sh --axioms` and CI initialize
them automatically, but on a direct first `lake exe axiomsweep` you may need:

```bash
git -C .lake/packages/VCVio submodule update --init --recursive
```

```bash
# Summary: total declarations, sorryAx-tainted, non-standard-axiom-tainted
lake exe axiomsweep

# Full per-declaration report (name, module, kind, line, axioms)
lake exe axiomsweep --out /tmp/axiom-report.json

# Regression gate: fail iff a declaration is tainted that
# scripts/axiom_baseline.json does not already list
lake exe axiomsweep --check

# Refresh the baseline (after intentionally adding a tagged sorry, or after
# closing gaps); commit the resulting diff in the same PR
lake exe axiomsweep --update-baseline
```

The committed baseline makes the distinction the repo cares about mechanical:
pre-existing `sorry` gaps are allowed, *new* ones fail `--check`. The baseline is an
allowlist for `sorryAx` debt only; native-compiler trust (`Lean.ofReduceBool`,
`Lean.trustCompiler`, and the per-declaration `…._native.<tactic>.ax_<n>_<n>` axioms
minted by `native_decide`-style tactics) is never allowlistable — `--check` fails on it
regardless of the baseline, and `--update-baseline` refuses to write while it is present.
CI runs the library check report-only; `./scripts/validate.sh --axioms` runs it enforcing.

The tool itself is certified by `./scripts/test-axiomsweep.sh`, which builds the isolated
`AxiomSweepTestFixtures` library (deliberate synthetic taint of every shape the sweep
reasons about: direct and transitive `sorry`, axiom-in-type, mutual-inductive inheritance,
generated native-trust names and near-miss collisions, and an unimported file) and checks
report determinism, every gate direction, and the exit-code contract (`1` = taint verdict,
`2` = infrastructure failure). CI runs it as an enforcing step:

```bash
lake build AxiomSweepTestFixtures
./scripts/test-axiomsweep.sh
```

### `build_timing_report.sh`

Helper used by CI to measure and render build timings for clean builds, warm
rebuilds, the native build, and the `./scripts/validate.sh` path. The CI workflow uploads
timing-data artifacts so PR runs can compare against a previously recorded
baseline without rerunning that baseline in the same job. This supports
[`../.github/workflows/ci.yml`](../.github/workflows/ci.yml).

The four measurements share one tree and run in order, so each leaves it warmer than the last.
`native_build` exists to hold the `.c.o` chain that the compiled executables link
(`toyproblem-runtime` and `hachi-runtime`): that is the cost which swings on `.lake` cache state,
and billing it separately keeps the validation wrapper's row comparable across dependency bumps.
Any new compiled executable run by `validate.sh` has to be added to that command as well. See
[`../docs/wiki/quickstart.md`](../docs/wiki/quickstart.md) for how to read the rows.

## Requirements

- Python 3.6+ (for Python scripts)
- Lean 4 (for Lean scripts)
- Graphviz (for dependency visualization)
- Virtual environment (`.venv`) for Python dependencies

## Notes

- Most scripts should be run from the ArkLib root directory
- Python scripts require the virtual environment to be activated
- Some scripts may require specific Lean toolchain versions
- `validate.sh` is the recommended local wrapper; use the lower-level scripts directly when you
  want to run or debug one piece in isolation
- `validate.sh` currently enforces a zero non-`sorry` warning budget under `ArkLib/Data/**`
- New `ArkLib/**/*.lean` files must be staged before `update-lib.sh` or `check-imports.sh`

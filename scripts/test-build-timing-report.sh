#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

# The workflow exports production report inputs globally. Fixtures must own every report input
# instead of accidentally reading workflow state that is absent in a developer shell.
while IFS='=' read -r variable _; do
  case "$variable" in
    BUILD_TIMING_* | GITHUB_REF_NAME | GITHUB_REPOSITORY) unset "$variable" ;;
  esac
done < <(env)

fixture_tmp="$(mktemp -d)"
trap 'rm -rf "$fixture_tmp"' EXIT

on_error() {
  status=$?
  echo "Build timing report fixture failed at line ${BASH_LINENO[0]}." >&2
  for report_file in "$fixture_tmp"/*.md; do
    if [ -f "$report_file" ]; then
      echo "--- $report_file" >&2
      sed -n '1,220p' "$report_file" >&2
    fi
  done
  exit "$status"
}
trap on_error ERR

current_dir="$fixture_tmp/current"
source_root="$fixture_tmp/root"
mkdir -p "$current_dir" "$source_root/ArkLib" "$source_root/ArkLibTest"
for module in ArkLib/Fast ArkLib/Slow ArkLib/New ArkLib/Kept ArkLibTest/Check; do
  : > "$source_root/$module.lean"
done

python3 - "$current_dir" <<'PY'
import json
import pathlib
import sys

current_dir = pathlib.Path(sys.argv[1])

rows = [
    {"label": "library_build", "real": 90.0, "user": 70.0, "sys": 10.0,
     "exit_code": 0, "measured": True},
    {"label": "native_build", "real": 20.0, "user": 35.0, "sys": 5.0,
     "exit_code": 0, "measured": True},
    {"label": "test_path", "real": 8.0, "user": 6.0, "sys": 1.0,
     "exit_code": 0, "measured": True},
]
(current_dir / "results.jsonl").write_text(
    "".join(json.dumps(row) + "\n" for row in rows), encoding="utf-8"
)

# Lake's captions: `NNNms`, one decimal below 10s, whole seconds above. Native facets and the
# lint plugin are not ArkLib modules, and a module built twice keeps its first sample.
(current_dir / "library_build.log").write_text(
    "✔ [1/5] Built ArkLib.Fast (1.0s)\n"
    "⚠ [2/5] Built ArkLib.Slow (12s)\n"
    "warning: ArkLib/Slow.lean:3:8: declaration uses 'sorry'\n"
    "✔ [3/5] Built ArkLib.New (850ms)\n"
    "✔ [4/5] Built ArkLib.Slow:c.o (3.0s)\n"
    "✔ [5/5] Built ArkLibLintPlugin (2.0s)\n",
    encoding="utf-8",
)
(current_dir / "test_path.log").write_text(
    "✔ [7/8] Built ArkLibTest.Check (4.2s)\n"
    "✔ [8/8] Built ArkLib.Fast (9.9s)\n",
    encoding="utf-8",
)

# `ArkLib.Gone` has no source file any more, so the update must drop it.
(current_dir / "module-times-base.json").write_text(
    json.dumps({
        "schema_version": 1,
        "commit": "c" * 40,
        "modules": {
            "ArkLib.Fast": {"seconds": 2.0, "decimals": 1},
            "ArkLib.Slow": {"seconds": 18.0, "decimals": 0},
            "ArkLib.Kept": {"seconds": 30.0, "decimals": 0},
            "ArkLib.Gone": {"seconds": 5.0, "decimals": 0},
        },
    }),
    encoding="utf-8",
)

(current_dir / "metadata.json").write_text(
    json.dumps({
        "schema_version": 1,
        "run": {"id": 2, "attempt": 1, "event": "pull_request"},
        "git": {"head_sha": "a" * 40, "checkout_sha": "b" * 40, "base_sha": "c" * 40,
                "ref": "feature|timing"},
        "dependencies": {"lake_manifest_sha256": "1" * 64},
        "cache": {"primary_key": "primary", "matched_key": "primary", "exact_hit": True},
        "runner": {"os": "Linux", "arch": "X64", "image_os": "ubuntu24",
                   "image_version": "20260820.1", "cores": 4},
    }),
    encoding="utf-8",
)
PY

cp "$current_dir/module-times-base.json" "$current_dir/module-times.json"
update_output="$(python3 scripts/module_times.py update "$current_dir/module-times.json" \
  --commit "$(printf 'b%.0s' {1..40})" --root "$source_root" \
  "$current_dir/library_build.log" "$current_dir/test_path.log")"
[ "$update_output" = 'Recorded 4 rebuilt modules; table covers 5 modules, 48s of compile time.' ]
python3 - "$current_dir/module-times.json" <<'PY'
import pathlib
import sys

sys.path.insert(0, "scripts")
from module_times import load_table

table = load_table(pathlib.Path(sys.argv[1]))
assert table is not None
assert table["commit"] == "b" * 40
assert table["modules"] == {
    "ArkLib.Fast": {"seconds": 1.0, "decimals": 1},
    "ArkLib.Kept": {"seconds": 30.0, "decimals": 0},
    "ArkLib.New": {"seconds": 0.85, "decimals": 3},
    "ArkLib.Slow": {"seconds": 12.0, "decimals": 0},
    "ArkLibTest.Check": {"seconds": 4.2, "decimals": 1},
}, table["modules"]
PY

# A missing or foreign-schema table starts afresh instead of failing the build.
fresh_table="$fixture_tmp/fresh/module-times.json"
python3 scripts/module_times.py update "$fresh_table" --root "$source_root" \
  "$current_dir/library_build.log" > /dev/null
printf '{"schema_version": 99, "modules": {"ArkLib.Kept": {"seconds": 1, "decimals": 0}}}' \
  > "$fixture_tmp/foreign.json"
python3 scripts/module_times.py update "$fixture_tmp/foreign.json" --root "$source_root" \
  "$current_dir/library_build.log" > /dev/null
python3 - "$fresh_table" "$fixture_tmp/foreign.json" <<'PY'
import json
import pathlib
import sys

for path in sys.argv[1:]:
    table = json.loads(pathlib.Path(path).read_text(encoding="utf-8"))
    assert table["schema_version"] == 1
    assert sorted(table["modules"]) == ["ArkLib.Fast", "ArkLib.New", "ArkLib.Slow"], table
PY

report="$fixture_tmp/report.md"
BUILD_TIMING_LOG_DIR="$current_dir" \
BUILD_TIMING_SOURCE_SHA="$(printf 'a%.0s' {1..40})" \
BUILD_TIMING_SOURCE_SUBJECT='timing <report>' \
BUILD_TIMING_SOURCE_BRANCH='feature|timing' \
BUILD_TIMING_NATIVE_COMMAND='lake build toyproblem-runtime hachi-runtime lint-style' \
  bash scripts/build_timing_report.sh render "$current_dir/results.jsonl" > "$report"

grep -Fq -- '- PR head: `aaaaaaa`' "$report"
grep -Fq -- '- Measured checkout: `bbbbbbb` (workflow head `aaaaaaa`).' "$report"
grep -Fq -- '- Ref: <code>feature&#124;timing</code>' "$report"
grep -Fq -- '- Build cache: restored the `main` build of `ccccccc`' "$report"
grep -Fq -- '- Dependency cache: **exact hit** (<code>primary</code>)' "$report"
grep -Fq -- '| Library build | 90.00 | 80.00 | ok |' "$report"
grep -Fq -- 'native build `lake build toyproblem-runtime hachi-runtime lint-style`' "$report"
grep -Fq -- 'Rebuilt 4 modules (2 without an earlier time). The 2 with an earlier time took 13s here against 20s when `main` last built them (-7s (-35.0%)).' "$report"
grep -Fq -- 'summed over all 5 modules: 55s before, 48s after (-7s (-12.6%)).' "$report"
grep -Fq -- '| 12 | 18 | -6 | <code>ArkLib/Slow.lean</code> |' "$report"
grep -Fq -- '| 1.0 | 2.0 | -1.0 | <code>ArkLib/Fast.lean</code> |' "$report"
grep -Fq -- '| 0.850 | - | - | <code>ArkLib/New.lean</code> |' "$report"
grep -Fq -- '| 4.2 | - | - | <code>ArkLibTest/Check.lean</code> |' "$report"
if grep -Fq -- 'ArkLibLintPlugin' "$report" || grep -Fq -- 'c.o' "$report"; then
  echo 'the rebuilt-module table must list only ArkLib modules' >&2
  exit 1
fi

# A clean build restores no build cache and therefore records no baseline.
full_dir="$fixture_tmp/full"
cp -R "$current_dir" "$full_dir"
rm "$full_dir/module-times-base.json"
BUILD_TIMING_LOG_DIR="$full_dir" \
  bash scripts/build_timing_report.sh render "$full_dir/results.jsonl" > "$fixture_tmp/full.md"
grep -Fq -- '- Build cache: none restored, so the library build is a full build.' \
  "$fixture_tmp/full.md"
grep -Fq -- 'Clean-build compile time, summed over all 5 modules: 48s.' "$fixture_tmp/full.md"

up_to_date_dir="$fixture_tmp/up-to-date"
cp -R "$current_dir" "$up_to_date_dir"
: > "$up_to_date_dir/library_build.log"
: > "$up_to_date_dir/test_path.log"
BUILD_TIMING_LOG_DIR="$up_to_date_dir" \
  bash scripts/build_timing_report.sh render "$up_to_date_dir/results.jsonl" \
  > "$fixture_tmp/up-to-date.md"
grep -Fq -- 'No module was rebuilt' "$fixture_tmp/up-to-date.md"

python3 - "$current_dir/metadata.json" <<'PY'
import json
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
path.write_text(json.dumps({"schema_version": 99}), encoding="utf-8")
PY
BUILD_TIMING_LOG_DIR="$current_dir" \
  bash scripts/build_timing_report.sh render "$current_dir/results.jsonl" \
  > "$fixture_tmp/wrong-schema.md"
grep -Fq -- 'unsupported timing metadata schema 99; expected 1' \
  "$fixture_tmp/wrong-schema.md"

python3 - "$current_dir/metadata.json" <<'PY'
import pathlib
import sys

pathlib.Path(sys.argv[1]).write_text("{not-json\n", encoding="utf-8")
PY
BUILD_TIMING_LOG_DIR="$current_dir" \
  bash scripts/build_timing_report.sh render "$current_dir/results.jsonl" \
  > "$fixture_tmp/malformed.md"
grep -Fq -- 'cannot read timing metadata' "$fixture_tmp/malformed.md"
grep -Fq -- 'runner pin unavailable for this legacy artifact' "$fixture_tmp/malformed.md"

written_metadata="$fixture_tmp/written-metadata.json"
BUILD_TIMING_RUN_ID=7 \
BUILD_TIMING_RUN_ATTEMPT=2 \
BUILD_TIMING_EVENT=pull_request \
BUILD_TIMING_HEAD_SHA="$(printf 'e%.0s' {1..40})" \
BUILD_TIMING_CHECKOUT_SHA="$(printf 'f%.0s' {1..40})" \
BUILD_TIMING_BASE_SHA="$(printf '1%.0s' {1..40})" \
BUILD_TIMING_REF=feature/timing \
BUILD_TIMING_CACHE_EXACT_HIT=false \
BUILD_TIMING_CACHE_PRIMARY_KEY=primary \
BUILD_TIMING_CACHE_MATCHED_KEY=fallback \
RUNNER_OS=Linux \
RUNNER_ARCH=X64 \
ImageOS=ubuntu24 \
ImageVersion=20260820.1 \
  python3 scripts/build_timing_metadata.py "$written_metadata"
python3 - "$written_metadata" <<'PY'
import pathlib
import sys

sys.path.insert(0, "scripts")
from build_timing_metadata import load_metadata

metadata = load_metadata(pathlib.Path(sys.argv[1]))
assert metadata["run"] == {"attempt": 2, "event": "pull_request", "id": 7}
assert metadata["cache"]["exact_hit"] is False
assert metadata["cache"]["matched_key"] == "fallback"
PY

grep -Fq 'pullRequest.head.sha !== run.head_sha' .github/workflows/build-timing-report.yml
grep -Fq 'runPullRequest?.base?.sha || pullRequest.base.sha' \
  .github/workflows/build-timing-report.yml
grep -Fq 'BUILD_TIMING_NATIVE_COMMAND: lake build toyproblem-runtime hachi-runtime lint-style' \
  .github/workflows/build-timing-report.yml
if grep -Fq 'the previous successful PR update' .github/workflows/build-timing-report.yml; then
  echo 'reporter must not silently use a moving previous-PR baseline' >&2
  exit 1
fi

echo 'Build timing report fixtures passed.'

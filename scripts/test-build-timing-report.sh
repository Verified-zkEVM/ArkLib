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
base_dir="$fixture_tmp/base"
empty_dir="$fixture_tmp/empty"
mkdir -p "$current_dir" "$base_dir" "$empty_dir"

python3 - "$current_dir" "$base_dir" <<'PY'
import json
import pathlib
import sys

current_dir = pathlib.Path(sys.argv[1])
base_dir = pathlib.Path(sys.argv[2])

records = {
    current_dir: [
        {"label": "clean_build", "real": 90.0, "user": 70.0, "sys": 10.0,
         "exit_code": 0, "measured": True},
        {"label": "warm_rebuild", "real": 2.0, "user": 1.2, "sys": 0.3,
         "exit_code": 0, "measured": True},
        {"label": "native_build", "real": 20.0, "user": 35.0, "sys": 5.0,
         "exit_code": 0, "measured": True},
        {"label": "test_path", "real": 8.0, "user": 6.0, "sys": 1.0,
         "exit_code": 0, "measured": True},
    ],
    base_dir: [
        {"label": "clean_build", "real": 100.0, "user": 75.0, "sys": 15.0,
         "exit_code": 0, "measured": True},
        {"label": "warm_rebuild", "real": 2.5, "user": 1.3, "sys": 0.4,
         "exit_code": 0, "measured": True},
        {"label": "native_build", "real": 18.0, "user": 31.0, "sys": 4.0,
         "exit_code": 0, "measured": True},
        {"label": "test_path", "real": 7.0, "user": 5.0, "sys": 1.0,
         "exit_code": 0, "measured": True},
    ],
}

for directory, rows in records.items():
    (directory / "results.jsonl").write_text(
        "".join(json.dumps(row) + "\n" for row in rows), encoding="utf-8"
    )
    (directory / "clean_build.log").write_text(
        "✔ [1/2] Built ArkLib.Fast (1.0s)\n"
        "✔ [2/2] Built ArkLib.Slow (12s)\n",
        encoding="utf-8",
    )

def metadata(*, run_id, head, checkout, base, exact_hit, matched_key, image_version):
    return {
        "schema_version": 1,
        "run": {"id": run_id, "attempt": 1, "event": "pull_request"},
        "git": {"head_sha": head, "checkout_sha": checkout, "base_sha": base,
                "ref": "feature|timing"},
        "dependencies": {"lake_manifest_sha256": "1" * 64},
        "cache": {"primary_key": "primary", "matched_key": matched_key,
                  "exact_hit": exact_hit},
        "runner": {"os": "Linux", "arch": "X64", "image_os": "ubuntu24",
                   "image_version": image_version, "cores": 4},
    }

(current_dir / "metadata.json").write_text(
    json.dumps(metadata(run_id=2, head="a" * 40, checkout="b" * 40, base="c" * 40,
                        exact_hit=True, matched_key="primary", image_version="20260820.1")),
    encoding="utf-8",
)
(base_dir / "metadata.json").write_text(
    json.dumps(metadata(run_id=1, head="c" * 40, checkout="c" * 40, base="d" * 40,
                        exact_hit=False, matched_key="fallback", image_version="20260813.1")),
    encoding="utf-8",
)
PY

report="$fixture_tmp/report.md"
BUILD_TIMING_LOG_DIR="$current_dir" \
BUILD_TIMING_SOURCE_SHA="$(printf 'a%.0s' {1..40})" \
BUILD_TIMING_SOURCE_SUBJECT='timing <report>' \
BUILD_TIMING_SOURCE_BRANCH='feature|timing' \
BUILD_TIMING_BASELINE_SHA="$(printf 'c%.0s' {1..40})" \
BUILD_TIMING_BASELINE_LABEL='exact PR base on `main`' \
BUILD_TIMING_NATIVE_COMMAND='lake build toyproblem-runtime hachi-runtime lint-style' \
  bash scripts/build_timing_report.sh render "$current_dir/results.jsonl" "$base_dir" > "$report"

grep -Fq -- '- PR head: `aaaaaaa`' "$report"
grep -Fq -- '- Measured checkout: `bbbbbbb` (workflow head `aaaaaaa`).' "$report"
grep -Fq -- '- Ref: <code>feature&#124;timing</code>' "$report"
grep -Fq -- 'Dependency cache: current **exact hit**' "$report"
grep -Fq -- 'dependency cache **fallback restore**' "$report"
grep -Fq -- '| Clean build | 100.00 | 90.00 | -10.00 (-10.0%) | 90.00 | 80.00 | -10.00 (-11.1%) | ok |' "$report"
grep -Fq -- 'native build `lake build toyproblem-runtime hachi-runtime lint-style`' "$report"
grep -Fq -- '| 12 | 12 | +0 | <code>ArkLib/Slow.lean</code> |' "$report"

BUILD_TIMING_LOG_DIR="$current_dir" \
  bash scripts/build_timing_report.sh render "$current_dir/results.jsonl" "$empty_dir" \
  > "$fixture_tmp/no-base.md"
grep -Fq -- 'exact-base timing artifact unavailable; no substitute was used' \
  "$fixture_tmp/no-base.md"

python3 - "$current_dir/metadata.json" <<'PY'
import json
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
path.write_text(json.dumps({"schema_version": 99}), encoding="utf-8")
PY
BUILD_TIMING_LOG_DIR="$current_dir" \
  bash scripts/build_timing_report.sh render "$current_dir/results.jsonl" "$base_dir" \
  > "$fixture_tmp/wrong-schema.md"
grep -Fq -- 'unsupported timing metadata schema 99; expected 1' \
  "$fixture_tmp/wrong-schema.md"

python3 - "$current_dir/metadata.json" <<'PY'
import pathlib
import sys

pathlib.Path(sys.argv[1]).write_text("{not-json\n", encoding="utf-8")
PY
BUILD_TIMING_LOG_DIR="$current_dir" \
  bash scripts/build_timing_report.sh render "$current_dir/results.jsonl" "$base_dir" \
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

#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  build_timing_report.sh run <label> <results-file> -- <command> [args...]
  build_timing_report.sh render <results-file> [baseline-artifact-dir]

Labels:
  clean_build
  warm_rebuild
  native_build
  test_path
EOF
}

append_result() {
  local results_file="$1"
  local label="$2"
  local real_time="$3"
  local user_time="$4"
  local sys_time="$5"
  local exit_code="$6"
  local measured="${7:-1}"

  python3 - "$results_file" "$label" "$real_time" "$user_time" "$sys_time" "$exit_code" \
    "$measured" <<'PY'
import json
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
path.parent.mkdir(parents=True, exist_ok=True)

record = {
    "label": sys.argv[2],
    "real": float(sys.argv[3]),
    "user": float(sys.argv[4]),
    "sys": float(sys.argv[5]),
    "exit_code": int(sys.argv[6]),
    "measured": sys.argv[7] == "1",
}

with path.open("a", encoding="utf-8") as handle:
    handle.write(json.dumps(record) + "\n")
PY
}

run_command() {
  if [ "$#" -lt 4 ]; then
    usage
    exit 2
  fi

  local label="$1"
  local results_file="$2"
  shift 2

  if [ "$1" != "--" ]; then
    usage
    exit 2
  fi
  shift

  local timing_file
  timing_file="$(mktemp)"
  local log_dir="${BUILD_TIMING_LOG_DIR:-}"
  local log_file=""

  if [ -n "$log_dir" ]; then
    mkdir -p "$log_dir"
    log_file="$log_dir/${label}.log"
  fi

  set +e
  if [ -n "$log_file" ]; then
    /usr/bin/time -p -o "$timing_file" "$@" 2>&1 | tee "$log_file"
    local exit_code=${PIPESTATUS[0]}
  else
    /usr/bin/time -p -o "$timing_file" "$@"
    local exit_code=$?
  fi
  set -e

  local real_time user_time sys_time
  real_time="$(awk '$1 == "real" { print $2 }' "$timing_file")"
  user_time="$(awk '$1 == "user" { print $2 }' "$timing_file")"
  sys_time="$(awk '$1 == "sys" { print $2 }' "$timing_file")"
  rm -f "$timing_file"

  # `/usr/bin/time` writes nothing when it cannot exec the target. Record the attempt anyway:
  # without this the `float()` in `append_result` would abort under `set -e`, the row would never
  # be written, and `render` would silently omit it -- indistinguishable from "not measured".
  local measured=1
  if [ -z "$real_time" ] || [ -z "$user_time" ] || [ -z "$sys_time" ]; then
    measured=0
    real_time=0
    user_time=0
    sys_time=0
  fi

  append_result "$results_file" "$label" "$real_time" "$user_time" "$sys_time" "$exit_code" \
    "$measured"
  exit "$exit_code"
}

render_report() {
  if [ "$#" -lt 1 ] || [ "$#" -gt 2 ]; then
    usage
    exit 2
  fi

  local results_file="$1"
  local baseline_dir="${2:-}"

  python3 - "$results_file" "$baseline_dir" <<'PY'
import json
import html
import os
import pathlib
import re
import sys

results_path = pathlib.Path(sys.argv[1])
baseline_dir = pathlib.Path(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2] else None
test_path_name = os.environ.get("BUILD_TIMING_TEST_NAME", "Validation wrapper")
test_path_command = os.environ.get("BUILD_TIMING_TEST_COMMAND", "./scripts/validate.sh")

native_build_name = os.environ.get("BUILD_TIMING_NATIVE_NAME", "Native build")
native_build_command = os.environ.get(
    "BUILD_TIMING_NATIVE_COMMAND", "lake build toyproblem-runtime"
)

display = {
    "clean_build": {
        "name": "Clean build",
        "command": "`rm -rf .lake/build && lake build`",
    },
    "warm_rebuild": {
        "name": "Warm rebuild",
        "command": "`lake build`",
    },
    "native_build": {
        "name": native_build_name,
        "command": f"`{native_build_command}`",
    },
    "test_path": {
        "name": test_path_name,
        "command": f"`{test_path_command}`",
    },
}
ordered_labels = ["clean_build", "warm_rebuild", "native_build", "test_path"]
repo_prefixes = ("ArkLib",)


def load_records(path: pathlib.Path) -> dict[str, dict]:
    records = {}
    if not path.exists():
        return records
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        record = json.loads(line)
        records[record["label"]] = record
    return records


def fmt(value: float) -> str:
    return f"{value:.2f}"


def fmt_delta(value: float) -> str:
    return f"{value:+.2f}"


def md_text(value: str) -> str:
    return html.escape(str(value).replace("\r", " ").replace("\n", " "), quote=False)


def md_table_cell(value: str) -> str:
    return md_text(value).replace("|", "&#124;")


def md_code(value: str) -> str:
    return f"<code>{md_table_cell(value)}</code>"


def measured(record: dict) -> bool:
    # Records written before the `measured` flag existed are all real measurements.
    return record.get("measured", True)


def status(record: dict) -> str:
    if not measured(record):
        return f"measurement failed (exit {record['exit_code']})"
    return "ok" if record["exit_code"] == 0 else f"exit {record['exit_code']}"


def seconds(record: dict | None) -> str:
    if record is None:
        return "-"
    return "n/a" if not measured(record) else fmt(record["real"])


def module_to_source_path(target: str) -> str | None:
    # Lake captions are facet-qualified (`Mod:c.o`, `Mod:dynlib`); only the module part maps to
    # a source file, and the facet has to stay visible or native and olean rows collide.
    module, _, facet = target.partition(":")
    path = None
    if module in repo_prefixes:
        path = module + ".lean"
    else:
        for prefix in repo_prefixes:
            if module.startswith(prefix + "."):
                path = module.replace(".", "/") + ".lean"
                break
    if path is None:
        return None
    return path if not facet else f"{path} [{facet}]"


# Lake's own formatter (`Lake/Build/Run.lean`) prints `NNNms` below 1s, one decimal between 1s
# and 10s, and whole seconds above 10s. Parsing only the `s` forms drops every sub-second target;
# rendering everything to two decimals invents precision that `22s` never had.
TARGET_PATTERN = re.compile(r"Built\s+(.+?)\s+\((\d+(?:\.\d+)?)(ms|s)\)")


def parse_duration(value: str, unit: str) -> tuple[float, int]:
    """Return the duration in seconds together with the decimal places Lake actually reported."""
    if unit == "ms":
        return float(value) / 1000.0, 3
    return float(value), len(value.partition(".")[2])


def fmt_target(entry: dict) -> str:
    return f"{entry['seconds']:.{entry['decimals']}f}"


def fmt_target_delta(current: dict, baseline: dict) -> str:
    decimals = min(current["decimals"], baseline["decimals"])
    return f"{current['seconds'] - baseline['seconds']:+.{decimals}f}"


def extract_clean_build_targets(log_path: pathlib.Path | None) -> list[dict]:
    if log_path is None or not log_path.exists():
        return []

    entries = []
    seen = set()
    for line in log_path.read_text(encoding="utf-8", errors="replace").splitlines():
        match = TARGET_PATTERN.search(line)
        if not match:
            continue
        target = match.group(1).strip()
        if target in seen:
            continue
        seen.add(target)
        elapsed, decimals = parse_duration(match.group(2), match.group(3))
        entries.append(
            {
                "target": target,
                "seconds": elapsed,
                "decimals": decimals,
                "source": module_to_source_path(target),
            }
        )

    preferred = [
        entry for entry in entries if entry["target"].startswith(repo_prefixes)
    ]
    selected = preferred if preferred else entries
    return sorted(selected, key=lambda entry: entry["seconds"], reverse=True)


def target_key(entry: dict) -> str:
    return entry["source"] or entry["target"]


current_records = load_records(results_path)
baseline_records = load_records(baseline_dir / "results.jsonl") if baseline_dir else {}

current_log_dir = os.environ.get("BUILD_TIMING_LOG_DIR")
current_log_path = pathlib.Path(current_log_dir) / "clean_build.log" if current_log_dir else None
current_clean_build_targets = extract_clean_build_targets(current_log_path)
baseline_clean_build_targets = (
    extract_clean_build_targets(baseline_dir / "clean_build.log") if baseline_dir else []
)

source_sha = os.environ.get("BUILD_TIMING_SOURCE_SHA")
source_subject = os.environ.get("BUILD_TIMING_SOURCE_SUBJECT")
source_branch = os.environ.get("BUILD_TIMING_SOURCE_BRANCH") or os.environ.get("GITHUB_REF_NAME")
source_repo = os.environ.get("GITHUB_REPOSITORY")
baseline_sha = os.environ.get("BUILD_TIMING_BASELINE_SHA")
baseline_label = os.environ.get("BUILD_TIMING_BASELINE_LABEL")

print("## Build Timing Report")
print()

if source_sha:
    short_sha = source_sha[:7]
    if source_repo:
        commit_ref = f"[`{short_sha}`](https://github.com/{source_repo}/commit/{source_sha})"
    else:
        commit_ref = f"`{short_sha}`"
    print(f"- Commit: {commit_ref}")
if source_subject:
    print(f"- Message: {md_text(source_subject)}")
if source_branch:
    print(f"- Ref: {md_code(source_branch)}")
if baseline_records:
    if baseline_sha:
        baseline_short_sha = baseline_sha[:7]
        if source_repo:
            baseline_commit_ref = (
                f"[`{baseline_short_sha}`](https://github.com/{source_repo}/commit/{baseline_sha})"
            )
        else:
            baseline_commit_ref = f"`{baseline_short_sha}`"
        if baseline_label:
            print(f"- Comparison baseline: {baseline_commit_ref} from {md_text(baseline_label)}.")
        else:
            print(f"- Comparison baseline: {baseline_commit_ref}.")
    elif baseline_label:
        print(f"- Comparison baseline: {md_text(baseline_label)}.")
print("- Measured on `ubuntu-latest` with `/usr/bin/time -p`.")
print(
    "- Commands: "
    + "; ".join(
        f"{display[label]['name'].lower()} {display[label]['command']}" for label in ordered_labels
    )
    + "."
)
print(
    f"- The rows run in order against one tree, so {display['native_build']['name'].lower()} and "
    f"{display['test_path']['name'].lower()} both measure an already-built project: "
    f"{display['test_path']['name'].lower()} is the cost of the gate itself, not of a cold "
    f"`{test_path_command}`. CI passes it no flags, so `--lint`, `--docs`, `--site` and "
    "`--axioms` contribute nothing."
)
print()

if not current_records:
    print("No timing data was captured.")
    sys.exit(0)

if baseline_records:
    print("| Measurement | Baseline (s) | Current (s) | Delta (s) | Status |")
    print("| --- | ---: | ---: | ---: | --- |")
    for label in ordered_labels:
        baseline_record = baseline_records.get(label)
        current_record = current_records.get(label)
        if not baseline_record and not current_record:
            continue
        baseline_time = seconds(baseline_record)
        current_time = seconds(current_record)
        comparable = (
            baseline_record is not None
            and current_record is not None
            and measured(baseline_record)
            and measured(current_record)
        )
        delta = (
            fmt_delta(current_record["real"] - baseline_record["real"]) if comparable else "-"
        )
        current_status = status(current_record) if current_record else "-"
        print(
            f"| {display[label]['name']} | {baseline_time} | {current_time} | {delta} | "
            f"{current_status} |"
        )
else:
    print("| Measurement | Wall (s) | Status |")
    print("| --- | ---: | --- |")
    for label in ordered_labels:
        if label not in current_records:
            continue
        record = current_records[label]
        print(f"| {display[label]['name']} | {seconds(record)} | {status(record)} |")

clean = current_records.get("clean_build")
warm = current_records.get("warm_rebuild")
if clean is not None and not measured(clean):
    clean = None
if warm is not None and not measured(warm):
    warm = None

print()
print("### Incremental Rebuild Signal")
print()
if clean and warm:
    delta = clean["real"] - warm["real"]
    ratio = clean["real"] / warm["real"] if warm["real"] else None
    if ratio is None:
        print(f"- Warm rebuild saved `{delta:.2f}s` vs clean.")
        print("- Clean:warm ratio is unavailable because `warm rebuild` reported `0.00s`.")
    elif delta > 0:
        print(f"- Warm rebuild saved `{delta:.2f}s` vs clean (`{ratio:.2f}x` faster).")
    elif delta < 0:
        slowdown = warm["real"] - clean["real"]
        slowdown_ratio = warm["real"] / clean["real"] if clean["real"] else None
        if slowdown_ratio is None:
            print(f"- Warm rebuild took `{slowdown:.2f}s` longer than clean in this run.")
        else:
            print(
                f"- Warm rebuild took `{slowdown:.2f}s` longer than clean in this run "
                f"(`{slowdown_ratio:.2f}x` slower)."
            )
    else:
        print("- Warm rebuild matched clean build wall-clock in this run.")
else:
    print("- Clean:warm comparison is unavailable because one of the build measurements is missing.")

print()
print(
    "This compares a clean project build against an incremental rebuild in the same CI job; "
    "it is a lightweight variability signal, not a full cross-run benchmark."
)

print()
print("### Slowest Current Clean-Build Files")
print()
if current_clean_build_targets:
    shown = current_clean_build_targets[:20]
    if baseline_clean_build_targets:
        baseline_targets_by_key = {
            target_key(entry): entry for entry in baseline_clean_build_targets
        }
        print(
            f"Showing {len(shown)} slowest current targets, with comparison against the selected baseline when available."
        )
        print()
        print("| Current (s) | Baseline (s) | Delta (s) | Path |")
        print("| ---: | ---: | ---: | --- |")
        for entry in shown:
            key = target_key(entry)
            baseline_entry = baseline_targets_by_key.get(key)
            baseline_time = fmt_target(baseline_entry) if baseline_entry else "-"
            delta = fmt_target_delta(entry, baseline_entry) if baseline_entry else "-"
            print(f"| {fmt_target(entry)} | {baseline_time} | {delta} | {md_code(key)} |")
    else:
        print(
            f"Showing {len(shown)} slowest of {len(current_clean_build_targets)} repo targets parsed from the current clean build log."
        )
        print()
        print("| Wall (s) | Path |")
        print("| ---: | --- |")
        for entry in shown:
            print(f"| {fmt_target(entry)} | {md_code(target_key(entry))} |")
else:
    print("No per-target timings were parsed from the current clean build log.")
PY
}

main() {
  if [ "$#" -lt 1 ]; then
    usage
    exit 2
  fi

  local command="$1"
  shift

  case "$command" in
    run)
      run_command "$@"
      ;;
    render)
      render_report "$@"
      ;;
    *)
      usage
      exit 2
      ;;
  esac
}

main "$@"

#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  build_timing_report.sh run <label> <results-file> -- <command> [args...]
  build_timing_report.sh render <results-file>

Labels:
  library_build
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
  if [ "$#" -ne 1 ]; then
    usage
    exit 2
  fi

  local results_file="$1"

  python3 - "$results_file" <<'PY'
import json
import html
import os
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path("scripts").resolve()))
from build_timing_metadata import MetadataError, load_metadata
from module_times import load_table, parse_logs, source_path, total_seconds

results_path = pathlib.Path(sys.argv[1])
# Logs and module tables sit next to each other in the timing artifact.
data_dir = pathlib.Path(os.environ.get("BUILD_TIMING_LOG_DIR") or results_path.parent)
test_path_name = os.environ.get("BUILD_TIMING_TEST_NAME", "Validation wrapper")
test_path_command = os.environ.get("BUILD_TIMING_TEST_COMMAND", "./scripts/validate.sh")

native_build_name = os.environ.get("BUILD_TIMING_NATIVE_NAME", "Native build")
native_build_command = os.environ.get(
    "BUILD_TIMING_NATIVE_COMMAND", "lake build toyproblem-runtime hachi-runtime lint-style"
)

display = {
    "library_build": {
        "name": "Library build",
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
ordered_labels = ["library_build", "native_build", "test_path"]


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


def fmt_change(current: float, baseline: float) -> str:
    delta = current - baseline
    if baseline == 0:
        return f"{delta:+.0f}s"
    return f"{delta:+.0f}s ({delta / baseline:+.1%})"


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


def seconds(record: dict) -> str:
    return "n/a" if not measured(record) else fmt(record["real"])


def cpu_seconds(record: dict) -> float | None:
    if not measured(record):
        return None
    return record["user"] + record["sys"]


def read_metadata(path: pathlib.Path) -> tuple[dict | None, str | None]:
    if not path.exists():
        return None, "metadata.json is absent (legacy artifact)"
    try:
        return load_metadata(path), None
    except MetadataError as error:
        return None, str(error)


def abbrev_sha(value: str | None) -> str:
    return value[:7] if value else "unknown"


def cache_summary(metadata: dict | None) -> str:
    if metadata is None:
        return "unknown"
    cache = metadata["cache"]
    if cache["exact_hit"] is True:
        return "exact hit"
    if cache["matched_key"]:
        return "fallback restore"
    if cache["exact_hit"] is False:
        return "miss"
    if cache["primary_key"]:
        return "miss"
    return "unknown"


def cache_key(metadata: dict | None) -> str:
    if metadata is None:
        return "unknown"
    cache = metadata["cache"]
    return cache["matched_key"] or cache["primary_key"] or "unknown"


def manifest_summary(metadata: dict | None) -> str:
    if metadata is None:
        return "unknown"
    return metadata["dependencies"]["lake_manifest_sha256"][:12]


def runner_summary(metadata: dict | None) -> str:
    if metadata is None:
        return "unknown"
    runner = metadata["runner"]
    image = runner["image_os"] or runner["os"]
    version = f" {runner['image_version']}" if runner["image_version"] else ""
    cores = f", {runner['cores']} cores" if runner["cores"] else ""
    return f"{image}{version}, {runner['arch']}{cores}"


def fmt_entry(entry: dict) -> str:
    return f"{entry['seconds']:.{entry['decimals']}f}"


def fmt_entry_delta(current: dict, baseline: dict) -> str:
    decimals = min(current["decimals"], baseline["decimals"])
    return f"{current['seconds'] - baseline['seconds']:+.{decimals}f}"


def commit_ref(sha: str | None) -> str:
    if not sha:
        return "`unknown`"
    if source_repo:
        return f"[`{sha[:7]}`](https://github.com/{source_repo}/commit/{sha})"
    return f"`{sha[:7]}`"


current_records = load_records(results_path)
current_metadata_path_env = os.environ.get("BUILD_TIMING_METADATA_PATH")
current_metadata_path = (
    pathlib.Path(current_metadata_path_env)
    if current_metadata_path_env
    else results_path.parent / "metadata.json"
)
current_metadata, current_metadata_error = read_metadata(current_metadata_path)

base_table = load_table(data_dir / "module-times-base.json")
current_table = load_table(data_dir / "module-times.json")
built = parse_logs([data_dir / "library_build.log", data_dir / "test_path.log"])

source_sha = os.environ.get("BUILD_TIMING_SOURCE_SHA")
source_subject = os.environ.get("BUILD_TIMING_SOURCE_SUBJECT")
source_branch = os.environ.get("BUILD_TIMING_SOURCE_BRANCH") or os.environ.get("GITHUB_REF_NAME")
source_repo = os.environ.get("GITHUB_REPOSITORY")

print("## Build Timing Report")
print()

if source_sha:
    source_label = (
        "PR head"
        if current_metadata and current_metadata["run"]["event"] == "pull_request"
        else "Source head"
    )
    print(f"- {source_label}: {commit_ref(source_sha)}")
if source_subject:
    print(f"- Message: {md_text(source_subject)}")
if source_branch:
    print(f"- Ref: {md_code(source_branch)}")
if current_metadata:
    checkout_sha = current_metadata["git"]["checkout_sha"]
    head_sha = current_metadata["git"]["head_sha"]
    print(
        f"- Measured checkout: `{abbrev_sha(checkout_sha)}` "
        f"(workflow head `{abbrev_sha(head_sha)}`)."
    )
if base_table is not None:
    print(
        f"- Build cache: restored the `main` build of {commit_ref(base_table['commit'])}; "
        "Lake rebuilt only modules whose source or imports differ from it."
    )
else:
    print("- Build cache: none restored, so the library build is a full build.")
print(f"- Runner: {md_code(runner_summary(current_metadata))}.")
print(
    f"- Dependency cache: **{md_text(cache_summary(current_metadata))}** "
    f"({md_code(cache_key(current_metadata))}); manifest {md_code(manifest_summary(current_metadata))}."
)
if current_metadata_error:
    print(f"- Attribution note: {md_text(current_metadata_error)}.")
if current_metadata:
    print("- Measured on the pinned `ubuntu-24.04` runner with `/usr/bin/time -p`.")
else:
    print("- Measured with `/usr/bin/time -p`; runner pin unavailable for this legacy artifact.")
print(
    "- Commands: "
    + "; ".join(
        f"{display[label]['name'].lower()} {display[label]['command']}" for label in ordered_labels
    )
    + "."
)
print(
    f"- The rows run in order against one tree, so {display['native_build']['name'].lower()} and "
    f"{display['test_path']['name'].lower()} both measure an already-built library: "
    f"{display['test_path']['name'].lower()} is the cost of the gate itself, not of a cold "
    f"`{test_path_command}`. CI passes it no flags, so `--docs`, `--site` and "
    "`--axioms` contribute nothing."
)
print()

if not current_records:
    print("No timing data was captured.")
    sys.exit(0)

print("| Measurement | Wall (s) | CPU work (s) | Status |")
print("| --- | ---: | ---: | --- |")
for label in ordered_labels:
    if label not in current_records:
        continue
    record = current_records[label]
    cpu = cpu_seconds(record)
    print(
        f"| {display[label]['name']} | {seconds(record)} | "
        f"{fmt(cpu) if cpu is not None else '-'} | {status(record)} |"
    )
print()
print(
    "CPU work is `user + sys`. Wall time depends on which modules this run had to rebuild, so "
    "compare it across runs only together with the module section below."
)

print()
print("### Rebuilt Modules")
print()
if not built:
    print("No module was rebuilt: every module was already up to date in the restored build.")
    sys.exit(0)

baseline_modules = base_table["modules"] if base_table is not None else {}
rows = sorted(built.items(), key=lambda item: item[1]["seconds"], reverse=True)
compared = [(module, entry) for module, entry in rows if module in baseline_modules]
new_count = len(rows) - len(compared)
current_sum = sum(entry["seconds"] for _, entry in compared)
baseline_sum = sum(baseline_modules[module]["seconds"] for module, _ in compared)

if base_table is not None:
    print(
        f"Rebuilt {len(rows)} modules ({new_count} without an earlier time). The "
        f"{len(compared)} with an earlier time took {current_sum:.0f}s here against "
        f"{baseline_sum:.0f}s when `main` last built them ({fmt_change(current_sum, baseline_sum)})."
    )
    if current_table is not None:
        before = total_seconds(base_table)
        after = total_seconds(current_table)
        print()
        print(
            f"Estimated clean-build compile time, summed over all "
            f"{len(current_table['modules'])} modules: {before:.0f}s before, {after:.0f}s after "
            f"({fmt_change(after, before)})."
        )
else:
    print(f"Built {len(rows)} modules.")
    if current_table is not None:
        print()
        print(
            f"Clean-build compile time, summed over all {len(current_table['modules'])} "
            f"modules: {total_seconds(current_table):.0f}s."
        )
print()
print(
    "Per-module times are wall-clock under whatever parallel load the run had, so treat small "
    "differences as noise; a large change on one module is the signal."
)
print()
shown = rows[:20]
print(f"Showing {len(shown)} slowest of {len(rows)} rebuilt modules.")
print()
print("| Current (s) | Earlier (s) | Delta (s) | Path |")
print("| ---: | ---: | ---: | --- |")
for module, entry in shown:
    baseline_entry = baseline_modules.get(module)
    baseline_time = fmt_entry(baseline_entry) if baseline_entry else "-"
    delta = fmt_entry_delta(entry, baseline_entry) if baseline_entry else "-"
    print(f"| {fmt_entry(entry)} | {baseline_time} | {delta} | {md_code(source_path(module))} |")
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

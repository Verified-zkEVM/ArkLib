#!/usr/bin/env bash
# Elaboration benchmarks for the specification prototypes (design note, section 12).
#
# The script builds `Specs.Bench`, then runs each case file under `Specs/Bench/` through the build
# lock with `lake env lean -Dprofiler=true`, and writes the Markdown table `out/bench.md`: case,
# size, wall time and the profiler's top categories. The Spartan and FRI cases run when their bench
# files exist and their example modules build. Times are single runs.
#
# Usage: bash docs/design/interaction-layer/prototypes/bench.sh
set -euo pipefail

LOCK=/Users/quangdao/claude-work/build-lock.sh
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../../.." && pwd)"
REL="docs/design/interaction-layer/prototypes"
OUT="$HERE/out"
mkdir -p "$OUT"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

echo "bench: building Specs.Bench"
if ! "$LOCK" "$ROOT" lake build Specs.Bench >"$TMP/build.log" 2>&1; then
  cat "$TMP/build.log"
  exit 1
fi

# Each case: label | size | file (relative to the repository root) | time limit (0: none).
CASES=(
  "sum-check: tree rfl, accessors|n = 8|$REL/Specs/Bench/Sumcheck8.lean|0"
  "sum-check: tree rfl, accessors|n = 32|$REL/Specs/Bench/Sumcheck32.lean|0"
  "sum-check: tree rfl, accessors|n = 128|$REL/Specs/Bench/Sumcheck128.lean|0"
  "sum-check: skeleton export|n = 8|$REL/Specs/Bench/Export8.lean|0"
  "sum-check: skeleton export|n = 16|$REL/Specs/Bench/Export16.lean|0"
  "sum-check: skeleton export|n = 20|$REL/Specs/Bench/Export20.lean|0"
  "sum-check: skeleton export|n = 128|$REL/Specs/Bench/Export128.lean|0"
)

# Cases for the Spartan and FRI examples: label | size | bench file | example module. A case runs
# only if its bench file exists, and only if its example module builds; otherwise its row says why.
BUILT=()
EXTRA=(
  "Spartan: tree rfl, accessors, export|m = n = 4|Spartan4|Specs.Examples.Spartan"
  "Spartan: tree rfl, accessors, export|m = n = 8|Spartan8|Specs.Examples.Spartan"
  "FRI: tree rfl, accessors, export|k = 4, l = 8|Fri4|Specs.Examples.Fri"
  "FRI: tree rfl, accessors, export|k = 8, l = 16|Fri8|Specs.Examples.Fri"
  "FRI: tree rfl, accessors, export|k = 32, l = 32|Fri32|Specs.Examples.Fri"
)
for c in "${EXTRA[@]}"; do
  IFS='|' read -r label size base module <<<"$c"
  [ -e "$HERE/Specs/Bench/$base.lean" ] || continue
  if "$LOCK" "$ROOT" lake build "$module" >"$TMP/build-$base.log" 2>&1; then
    CASES+=("$label|$size|$REL/Specs/Bench/$base.lean|0")
    [[ " ${BUILT[*]-} " == *" $module "* ]] || BUILT+=("$module")
  else
    CASES+=("$label|$size|SKIP:$module|0")
  fi
done

# Warm-up: import each module the cases import once, untimed, so that no timed case pays for a
# cold file cache when it loads the `.olean` files.
WARM=(Specs.Bench)
for m in ${BUILT[@]+"${BUILT[@]}"}; do WARM+=("$m"); done
for m in "${WARM[@]}"; do
  printf 'import %s\n' "$m" >"$TMP/Warm.lean"
  "$LOCK" "$ROOT" lake env lean "$TMP/Warm.lean" >/dev/null 2>&1 || true
done

i=0
for c in "${CASES[@]}"; do
  IFS='|' read -r label size file limit <<<"$c"
  i=$((i + 1))
  echo "bench: $label, $size"
  status=0
  if [[ "$file" == SKIP:* ]]; then
    echo "SKIPPED: ${file#SKIP:} does not build" >"$TMP/case$i.log"
    status=skip
  elif [ "$limit" = "0" ]; then
    "$LOCK" "$ROOT" /usr/bin/time -p lake env lean -Dprofiler=true "$file" \
      >"$TMP/case$i.log" 2>&1 || status=$?
  else
    # `perl` sets an alarm and then becomes `lean`, so the limit stops `lean` itself.
    "$LOCK" "$ROOT" /usr/bin/time -p lake env perl -e 'alarm shift; exec @ARGV' "$limit" \
      lean -Dprofiler=true "$file" >"$TMP/case$i.log" 2>&1 || status=$?
  fi
  printf '%s\t%s\t%s\t%s\n' "$label" "$size" "$limit" "$status" >"$TMP/case$i.meta"
done

LEANVER="$("$LOCK" "$ROOT" lake env lean --version 2>/dev/null | head -1)"
CPU="$(sysctl -n machdep.cpu.brand_string 2>/dev/null || uname -m)"
MEM="$(( $(sysctl -n hw.memsize 2>/dev/null || echo 0) / 1073741824 ))"
OS="$(sw_vers -productName 2>/dev/null || uname -s) $(sw_vers -productVersion 2>/dev/null || uname -r)"

python3 - "$TMP" "$i" "$OUT/bench.md" "$CPU" "$MEM" "$OS" "$LEANVER" <<'PY'
import re, sys, datetime
tmp, count, out, cpu, mem, os_, leanver = sys.argv[1], int(sys.argv[2]), *sys.argv[3:]

def ms(v):
    m = re.fullmatch(r'([0-9.]+)(ms|s|μs|us|ns)', v)
    if not m:
        return None
    x, u = float(m.group(1)), m.group(2)
    return x * {'ms': 1, 's': 1000, 'μs': 1e-3, 'us': 1e-3, 'ns': 1e-6}[u]

def fmt(x):
    return f"{x / 1000:.2f} s" if x >= 1000 else f"{x:.0f} ms" if x >= 1 else f"{x:.2f} ms"

rows = []
for k in range(1, count + 1):
    label, size, limit, status = open(f"{tmp}/case{k}.meta").read().rstrip('\n').split('\t')
    log = open(f"{tmp}/case{k}.log").read()
    real = re.search(r'^real\s+([0-9.]+)', log, re.M)
    wall = f"{float(real.group(1)):.2f} s" if real else "?"
    cats, imp = [], None
    if 'cumulative profiling times:' in log:
        for line in log.split('cumulative profiling times:')[1].splitlines():
            m = re.match(r'^\t(.+?) ([0-9.]+(?:ms|s|μs|us|ns))$', line)
            if m and ms(m.group(2)) is not None:
                if m.group(1) == 'import':
                    imp = ms(m.group(2))
                else:
                    cats.append((ms(m.group(2)), m.group(1)))
    cats.sort(reverse=True)
    top = ', '.join(f"{n} {fmt(t)}" for t, n in cats[:3])
    if status == 'skip':
        wall, top = "not run", log.strip()
    elif status != '0':
        errs = [l for l in log.splitlines() if 'error' in l]
        if limit != '0' and not cats:
            wall = f"> {limit} s (stopped)"
            top = "stopped at the time limit"
        else:
            top = (top + '; ' if top else '') + 'FAILED: ' + (errs[0][:120] if errs else f'exit {status}')
    imps = fmt(imp) if imp is not None else '?'
    rows.append(f"| {label} | {size} | {wall} | {top} | {imps} |")

now = datetime.datetime.now().strftime('%Y-%m-%d %H:%M')
with open(out, 'w') as f:
    f.write("# Elaboration benchmarks of the specification prototypes\n\n")
    f.write(f"Generated by `bench.sh` on {now}. Machine: {cpu}, {mem} GB, {os_}; {leanver}; "
            "`LEAN_NUM_THREADS=6` (set by the build lock).\n\n")
    f.write("Each time is a single run of `lake env lean -Dprofiler=true` on one case file under "
            "`Specs/Bench/`. The wall time includes starting Lean and importing `Specs.Bench`; the "
            "import column is the profiler's import time (of `Specs.Bench` and, for Spartan and FRI, the example module). The top categories are the profiler's "
            "three largest cumulative categories other than import. Before the timed runs, the script "
            "imports each of these modules once, untimed, so no case pays for a cold file cache. "
            "Other agents may build at the same time, so wall times can include waiting for the CPU.\n\n")
    f.write("| case | size | wall time | profiler top categories | import |\n")
    f.write("|---|---|---|---|---|\n")
    f.write('\n'.join(rows) + '\n\n')
    f.write("The skeleton export does not build the `2^n` points of the input claim's domain: "
            "`Dom` in `Specs.Formula` computes its elements only when a formula is evaluated. "
            "The export at 128 rounds therefore takes about as long as at 8 rounds. The accessor "
            "at round 127 of the 128-round case needs `maxRecDepth` 1024; Lean's default of 512 "
            "suffices up to round 120. See `Specs/Bench.lean`.\n")
PY
echo "bench: wrote $OUT/bench.md"
cat "$OUT/bench.md"

#!/usr/bin/env bash
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
fixture_tmp="$(mktemp -d)"
trap 'rm -rf "$fixture_tmp"' EXIT
lake build RetiredProbabilityTestFixtures retiredsweep
lake exe retiredsweep --root RetiredProbabilityTestFixtures.Clean --require-empty
if lake exe retiredsweep --root RetiredProbabilityTestFixtures.Retired --require-empty \
    --out "$fixture_tmp/retired.json" >"$fixture_tmp/retired.log" 2>&1; then
  echo "ERROR: retired probability gate accepted PMF fixtures" >&2
  exit 1
fi
python3 - "$fixture_tmp/retired.json" "$fixture_tmp/covering.json" <<'PYTHON'
import json
import sys
report = json.load(open(sys.argv[1]))
entries = {e["name"]: e for e in report["declarations"]}
prefix = "RetiredProbabilityTestFixtures.Retired."
for name in ["oldDistribution", "retiredInType", "retiredOnlyInBody", "privateOldDistribution"]:
    assert prefix + name in entries, name
json.dump({"retired": list(entries)}, open(sys.argv[2], "w"))
PYTHON
# Even a baseline covering every reported declaration cannot weaken strict mode.
if lake exe retiredsweep --root RetiredProbabilityTestFixtures.Retired --require-empty \
    --baseline "$fixture_tmp/covering.json" >"$fixture_tmp/covered.log" 2>&1; then
  echo "ERROR: baseline bypassed native probability retirement" >&2
  exit 1
fi
echo "Native probability retirement fixtures passed"

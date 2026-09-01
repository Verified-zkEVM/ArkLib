#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

fixture_tmp="$(mktemp -d)"
trap 'rm -rf "$fixture_tmp"' EXIT

plugin_path="$(lake query ArkLibLintPlugin:shared)"
allowed="scripts/LintStyleFixtures/PluginAllowed.lean"
rejected="scripts/LintStyleFixtures/PluginRejected.lean"
guard_rejected="scripts/LintStyleFixtures/PluginGuardRejected.lean"

lake env lean --plugin="$plugin_path" "$allowed"

if lake env lean --plugin="$plugin_path" "$rejected" >"$fixture_tmp/rejected.log" 2>&1; then
  echo "ERROR: source-policy plugin accepted forbidden suppression fixtures" >&2
  exit 1
fi

for root in linter pp profiler trace; do
  grep -Fq "Forbidden \`set_option ${root}.*\`" "$fixture_tmp/rejected.log"
done
grep -Fq "\`@[nolint]\` suppressions are forbidden" "$fixture_tmp/rejected.log"

if lake env lean --plugin="$plugin_path" "$guard_rejected" >"$fixture_tmp/guard-rejected.log" 2>&1; then
  echo "ERROR: source-policy plugin errors were discarded by #guard_msgs" >&2
  exit 1
fi

grep -Fq 'Forbidden `set_option linter.*`' "$fixture_tmp/guard-rejected.log"
grep -Fq "\`@[nolint]\` suppressions are forbidden" "$fixture_tmp/guard-rejected.log"

echo "ArkLib source-policy plugin fixtures passed"

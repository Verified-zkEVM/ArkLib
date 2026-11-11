#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

fixture_tmp="$(mktemp -d)"
trap 'rm -rf "$fixture_tmp"' EXIT

lake exe lint-style --self-test

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
if [[ "$(grep -Fc '`@[nolint]` suppressions are forbidden' "$fixture_tmp/rejected.log")" -ne 2 ]]; then
  echo "ERROR: source-policy plugin did not reject both nolint attribute forms" >&2
  exit 1
fi

if lake env lean --plugin="$plugin_path" "$guard_rejected" >"$fixture_tmp/guard-rejected.log" 2>&1; then
  echo "ERROR: source-policy plugin errors were discarded by #guard_msgs" >&2
  exit 1
fi

grep -Fq 'Forbidden `set_option linter.*`' "$fixture_tmp/guard-rejected.log"
grep -Fq "\`@[nolint]\` suppressions are forbidden" "$fixture_tmp/guard-rejected.log"

if lake env lean --plugin="$plugin_path" scripts/LintStyleFixtures/PluginProbabilityRejected.lean \
    >"$fixture_tmp/probability-rejected.log" 2>&1; then
  echo "ERROR: source-policy plugin accepted retired probability notation" >&2
  exit 1
fi
for token in '$ᵖ' 'Pr_{' 'Pr[' '𝒮['; do
  grep -Fq "Retired probability notation \`$token\`" "$fixture_tmp/probability-rejected.log"
done

alias_fixture="scripts/LintStyleFixtures/OracleProtocolAlias.lean"
alias_path="ArkLib/Interaction/Core/Protocol.lean"
lake env lean --plugin="$plugin_path" --stdin "$alias_path" < "$alias_fixture"
if lake env lean --plugin="$plugin_path" "$alias_fixture" \
    >"$fixture_tmp/alias-module.log" 2>&1; then
  echo "ERROR: oracle protocol exception applied in another module" >&2
  exit 1
fi
grep -Fq 'Forbidden `set_option linter.*`' "$fixture_tmp/alias-module.log"
for mutation in global name body; do
  case "$mutation" in
    global) sed 's/linter.checkUnivs false in/linter.checkUnivs false/' "$alias_fixture" ;;
    name) sed 's/abbrev OracleProtocol :=/abbrev AnotherProtocol :=/' "$alias_fixture" ;;
    body) sed 's/FreeM OraclePoly.{u, q} PUnit.{u + 1}/Nat/' "$alias_fixture" ;;
  esac > "$fixture_tmp/alias-$mutation.lean"
  if lake env lean --plugin="$plugin_path" --stdin "$alias_path" \
      < "$fixture_tmp/alias-$mutation.lean" > "$fixture_tmp/alias-$mutation.log" 2>&1; then
    echo "ERROR: oracle protocol exception accepted altered $mutation" >&2
    exit 1
  fi
  grep -Fq 'Forbidden `set_option linter.*`' "$fixture_tmp/alias-$mutation.log"
done

echo "ArkLib source-policy plugin fixtures passed"

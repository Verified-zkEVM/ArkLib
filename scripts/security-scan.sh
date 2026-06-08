#!/usr/bin/env bash
# Scan pinned Python dependency manifests for known vulnerabilities.
#
# Exit 0 when pip-audit reports no known issues; exit 1 otherwise.
set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

if ! command -v python3 >/dev/null 2>&1; then
  echo "ERROR: python3 is required for security scanning" >&2
  exit 1
fi

if ! command -v python3 >/dev/null 2>&1; then
  echo "ERROR: python3 is required for security scanning" >&2
  exit 1
fi

if python3 -m pip_audit --version >/dev/null 2>&1; then
  echo "# pip-audit (preinstalled): scripts/requirements-sorry-tracker.txt"
  python3 -m pip_audit -r scripts/requirements-sorry-tracker.txt --strict
  echo "security-scan: clean (no known vulnerabilities in pinned manifests)"
  exit 0
fi

python3 -m pip install --disable-pip-version-check -r scripts/requirements-security.txt

if ! python3 -m pip_audit --version >/dev/null 2>&1; then
  echo "ERROR: pip-audit is not available after install" >&2
  exit 1
fi

echo "# pip-audit: scripts/requirements-sorry-tracker.txt"
python3 -m pip_audit -r scripts/requirements-sorry-tracker.txt --strict

echo "security-scan: clean (no known vulnerabilities in pinned manifests)"

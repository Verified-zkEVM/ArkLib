#!/usr/bin/env bash

set -eo pipefail

lake env lean --run scripts/lint-style.lean "$@"

./scripts/lint-repo-structure.sh

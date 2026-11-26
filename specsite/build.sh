#!/usr/bin/env bash
# Build the protocol specification site into specsite/_out/html-multi/.
#
# Fails on any Lean warning (`--wfail`), on a stale excerpt or theorem name, and on a theorem that
# depends on `sorryAx`: the site's blocks check these when the site builds. Set LAKE to run Lake
# through a wrapper, for example a build lock.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
lake=(${LAKE:-lake})

cd "$here/.."
"${lake[@]}" build --wfail ArkLibPrototypes

cd "$here"
"${lake[@]}" build --wfail specsite
rm -rf _out
.lake/build/bin/specsite --output _out --without-html-single
echo "The site is in $here/_out/html-multi/"

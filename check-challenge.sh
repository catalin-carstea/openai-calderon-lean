#!/bin/sh
# Verify the independently preserved statement, selected text and toolchain pins.
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$here"
cmp ComparatorChallenges/Proposition53.lean docs/statement/Reference.lean
sha256sum --quiet --check docs/statement/SHA256SUMS
echo "Challenge statement, selected text and dependency pins match."

#!/bin/sh
# Verify the checked-in challenge statements, frozen definitions and build pins.
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$here"
sha256sum --quiet --check docs/statement/SHA256SUMS
echo "The challenge statements, frozen definitions and dependency pins match."

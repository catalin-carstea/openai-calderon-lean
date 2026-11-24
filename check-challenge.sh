#!/bin/sh
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$here"
manifest=docs/statement/SHA256SUMS
source=ComparatorChallenges/Source
sha256sum --quiet --check "$manifest"
if [ -n "$(find "$source" -type l -print -quit)" ]; then
  printf '%s\n' 'The frozen challenge tree contains a symbolic link.' >&2
  exit 1
fi
actual=$(find "$source" -type f -name '*.lean' -print | LC_ALL=C sort)
listed=$(awk '$2 ~ /^ComparatorChallenges\/Source\/.*\.lean$/ {print $2}' "$manifest" | LC_ALL=C sort)
if [ "$actual" != "$listed" ]; then
  printf '%s\n' 'The frozen challenge sources differ from the statement manifest.' >&2
  exit 1
fi
printf '%s\n' 'The challenge statements, frozen definitions and build pins match.'

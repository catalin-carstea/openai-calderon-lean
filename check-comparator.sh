#!/bin/sh
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$here"
./check-challenge.sh
lake env sh -c '
  prefix=$(lean --print-prefix)
  exec lean --load-dynlib="$prefix/lib/lean/libLake_shared.so" --run ComparatorTools/Run.lean "$@"
' comparator "$@"

#!/bin/sh
# Usage: check.sh <v8 dir> [<commit>]
# Runs all the checks of this repository against the reducer of a V8
# checkout, or, with <commit>, against the reducer at that commit of the
# checkout (read with git show, so the checkout may be on another
# branch):
# - the Rocq build, with no axiom other than Classical_Prop.classic;
# - check-model-anchors.py;
# - z3/check-z3-lemmas.py and z3/check-z3-decisions.py (with $PYTHON,
#   default python3, which needs z3-solver, see requirements.txt).
# Runs them all, and exits with a non-zero status if one fails.
SRC=src/compiler/turboshaft/wasm-bounds-check-elimination-reducer
PYTHON=${PYTHON:-python3}
HERE=$(cd "$(dirname "$0")" && pwd)

if [ $# -lt 1 ] || [ $# -gt 2 ]; then
  echo "usage: check.sh <v8 dir> [<commit>]" >&2
  exit 2
fi
v8=$1
if [ -n "$2" ]; then
  tmp=$(mktemp -d)
  trap 'rm -rf "$tmp"' EXIT
  mkdir -p "$tmp/$(dirname $SRC)"
  for ext in h cc; do
    git -C "$v8" show "$2:$SRC.$ext" > "$tmp/$SRC.$ext" || exit 2
  done
  v8=$tmp
fi

failed=
run() {
  name=$1; shift
  echo "== $name"
  if "$@"; then echo "== $name: ok"; else echo "== $name: FAILED"; failed="$failed $name"; fi
}

assumptions() {
  make -s -C "$HERE" all >/dev/null || return 1
  # Print Assumptions lists each axiom as "name : type" (continuation
  # lines are indented).
  (cd "$HERE" && coqc -R . BCE Assumptions.v) | awk '
    /^[A-Za-z_][A-Za-z0-9_.]* :/ && $1 != "Classical_Prop.classic" {
      print "unexpected axiom: " $1; bad = 1 }
    END { exit bad }'
}

run rocq assumptions
run anchors "$PYTHON" "$HERE/check-model-anchors.py" "$v8"
run z3-lemmas "$PYTHON" "$HERE/z3/check-z3-lemmas.py" "$v8/$SRC.h"
run z3-decisions "$PYTHON" "$HERE/z3/check-z3-decisions.py" "$v8"

if [ -n "$failed" ]; then
  echo "FAILED:$failed"
  exit 1
fi
echo "All checks passed."

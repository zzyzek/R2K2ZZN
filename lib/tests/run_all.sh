#!/bin/bash
# SPDX-License-Identifier: CC0-1.0
# The library test suite. From lib/:
#
#   tests/run_all.sh            about 4 minutes on one core
#   tests/run_all.sh --boxes    adds the exhaustive 11x11, 11x12, 12x12 test (about one CPU-hour)
#
# Exits non-zero if any part fails.
set -u
cd "$(dirname "$0")/.."
fail=0
step() {
  echo "== $1"
  shift
  "$@" || { echo "FAILED: $*"; fail=1; }
}
make -s -C c
step "Python: solutions valid, decide agrees with solve (100 random, sides 3-45)" \
  sh -c 'cd python && python3 tests/test_random.py 100 1 3 45 | tail -1'
step "Three languages agree, solutions checked (200 random, sides 3-45)" \
  python3 tests/compare.py 200 1 3 45 --trace
step "Three languages agree on instances that reach the move search (300, sides 11-22)" \
  python3 tests/compare.py 300 2 11 22 --irreducible --trace
step "Three languages agree on large instances (100, sides 11-60)" \
  python3 tests/compare.py 100 3 11 60 --trace
step "Exact fallback forced, C and JavaScript (4, sides 11-12)" \
  env ZZN_SKIP_MOVES=1 python3 tests/compare.py 4 4 11 12 --irreducible --trace --programs=c,js
step "Exact fallback forced, all three languages (1, 11x11)" \
  env ZZN_SKIP_MOVES=1 python3 tests/compare.py 1 5 11 11 --irreducible --trace
if [ "${1:-}" = "--boxes" ]; then
  step "Exhaustive: every passing instance of 11x11, 11x12, 12x12" tests/boxes.sh 4
fi
[ $fail = 0 ] && echo "ALL PASSED" || echo "SOME TESTS FAILED"
exit $fail

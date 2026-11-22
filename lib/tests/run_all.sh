#!/bin/bash
# SPDX-License-Identifier: CC0-1.0
# The library test suite. From lib/:
#
#   tests/run_all.sh            about 4 minutes on one core (4 min 18 s with --lean)
#   tests/run_all.sh --boxes    adds the exhaustive 11x11, 11x12, 12x12 lookup test (about 2.5 CPU-minutes)
#   tests/run_all.sh --lean=DIR adds the block layer against the Lean definitions; DIR is a
#                               proof/ directory with ZZN.Look.Table built (Lean uses about 7 GB)
#
# Exits non-zero if any part fails.
set -u
boxes=0 lean=""
for a in "$@"; do
  case "$a" in
    --boxes) boxes=1 ;;
    --lean=*) lean="$(realpath "${a#--lean=}")" ;;
  esac
done
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
step "Three languages agree on leaves answered by the lookup (300, sides 11-16)" \
  python3 tests/compare.py 300 2 11 16 --irreducible --trace
step "Three languages agree on large instances (100, sides 11-60)" \
  python3 tests/compare.py 100 3 11 60 --trace
step "Block lifts: every intermediate solution checked (300, three layouts, sides 11-80)" \
  python3 tests/blocks_test.py 300 1 11 80
step "Leaf lookup: irreducible leaves of every box 11-16, stored solutions, random leaves" \
  python3 tests/look_test.py 50 2
step "Three languages agree with block deletion (300, three layouts, sides 11-80)" \
  python3 tests/compare.py 300 6 11 80 --layouts --trace
step "C and JavaScript agree with block deletion (200, three layouts, sides 11-200)" \
  python3 tests/compare.py 200 7 11 200 --layouts --trace --programs=c,js
if [ $boxes = 1 ]; then
  step "Exhaustive: every passing instance of 11x11, 11x12, 12x12" tests/boxes.sh 4
fi
if [ -n "$lean" ]; then
  step "Block layer equals the Lean definitions blkX, Blk.del, Blk.lift (300, sides 11-40)" \
    python3 tests/lean_blocks.py 300 2 11 40 --proof="$lean"
  step "Two-line reductions equal the Lean definitions findRed2, liftE (300, sides 11-80)" \
    python3 tests/lean_reduce2.py 300 2 11 80 --proof="$lean"
  step "Leaf lookup equals the Lean definitions (table data, lookJ, entryP, tcheck, tsol, ...)" \
    python3 tests/look_lean.py 30 3 --proof="$lean"
  step "Catalogue equals the Lean definition fires3, entry by entry (5000 instances)" \
    python3 tests/lean_catalogue.py 5000 1 --proof="$lean"
fi
[ $fail = 0 ] && echo "ALL PASSED" || echo "SOME TESTS FAILED"
exit $fail

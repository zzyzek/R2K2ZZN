#!/bin/bash
# SPDX-License-Identifier: CC0-1.0
# Exhaustive test of zzn_solve on the boxes 11x11, 11x12 and 12x12 (see boxes.c): about 6.7 M
# passing instances, about one CPU-hour, a few MB per process.
#
#   tests/boxes.sh [JOBS]        (from lib/; JOBS parallel processes, default 4)
#
# Prints one DONE line per shard and a total; any FAIL line is an instance zzn_solve did not solve.
set -e
cd "$(dirname "$0")"
J=${1:-4}
cc -O2 -std=c11 -I../c -o boxes boxes.c ../c/zzn.c
for b in "11 11" "11 12" "12 12"; do
  for s in 0 1 2 3; do echo "$b $s"; done
done | xargs -P "$J" -L 1 sh -c './boxes $0 $1 $2 4 2>/dev/null' | tee boxes.out
awk '/^DONE/ { for (i = 1; i < NF; i++) { if ($i ~ /^(passing|same|move|exact|fail)$/) { s[$i] += $(i + 1) } } }
     END { printf "total passing %d same %d move %d exact %d fail %d\n", s["passing"], s["same"], s["move"], s["exact"], s["fail"] }' boxes.out
grep -q '^FAIL' boxes.out && exit 1 || exit 0

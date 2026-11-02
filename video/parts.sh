#!/bin/sh
# SPDX-License-Identifier: CC0-1.0
#
# Join the rendered scenes into six short parts, each under 2 minutes, cut at scene changes.
# Run after ./render.sh <q>; writes out/parts/zzn_part<n>_<q>.mp4.
#   ./parts.sh [l|m|h|k]
#
set -e
cd "$(dirname "$0")"
Q=${1:-h}
mkdir -p out/parts
n=0
for part in "S01Title S02Problem S03Result" \
            "S04PlugDP S05Parity" \
            "S05Topology S06Local S06Corner" \
            "S06Routes S07Reduce S08Band" \
            "S09Moves" \
            "S10Example S11Proof"; do
  n=$((n + 1))
  : > out/parts/list$n.txt
  for s in $part; do
    echo "file '../pad/${s}_$Q.mp4'" >> out/parts/list$n.txt
  done
  ffmpeg -y -loglevel error -f concat -safe 0 -i out/parts/list$n.txt -c copy out/parts/zzn_part${n}_$Q.mp4
  d=$(ffprobe -v error -show_entries format=duration -of csv=p=0 out/parts/zzn_part${n}_$Q.mp4)
  echo "part $n  $d s  ($part)"
done

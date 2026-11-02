#!/bin/bash
# Generate and build every window-certificate case listed in CASES (name|a|odd|tm|Fs).
# usage: run_wink.sh CASES WORKERS FILTER   (FILTER: grep -E pattern on the case line)
cd "$(dirname "$0")/.."
CASES=$1; P=$2; FILT=$3; LOGDIR=${LOGDIR:-.}
grep -E "$FILT" "$CASES" | while IFS='|' read -r name a odd tm fs; do
  if [ -f "genbuild/WinKGen/$name/Main.olean" ]; then echo "skip $name"; continue; fi
  if [ ! -f "gen/WinKGen/$name/Main.lean" ]; then
    lake env lean --run tools/WinGen.lean gen/WinKGen "$name" "$a" "$odd" "$tm" "$fs" || { echo "GENFAIL $name"; continue; }
  fi
  python3 tools/genbuild.py "$P" "WinKGen.$name.Main" > "$LOGDIR/wink_$name.log" 2>&1; grep -E "DONE|FAIL" "$LOGDIR/wink_$name.log" | head -n 1 | sed "s/^/$name /"
  [ -f "genbuild/WinKGen/$name/Main.olean" ] || echo "BUILDFAIL $name"
done
echo ALLDONE

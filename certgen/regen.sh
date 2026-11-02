#!/bin/bash
# Regenerate the certificate modules of proof/ (BoxKGen, WinKU, FinalN) and its Palomar files
# (Challenge.lean, Solution.lean, comparator.json) from the committed certificates, without
# rerunning the certificate search.
#
# Theorem A: certs/c{W}x{H}.txt.xz (slice certificates with fire witnesses, after FireGen) and
# certs/b{W}x{H}.txt.xz (stabiliser classes and base masks, from BaseGen) -> BoxKGen/N{W}x{H}.
# Theorem B: tools/wincases.txt -> WinKU (WinGenU, then the kernel-speed post-processing).
# The modules are generated in certgen/gen/ and written into proof/ by tools/export.py.
#
# usage: certgen/regen.sh   (needs the proof/ library built, for the `lake env lean --run` step)
set -e
CG=$(cd "$(dirname "$0")" && pwd)
PROOF=$(cd "$CG/../proof" && pwd)
TMP=$(mktemp -d)
cd "$CG"
rm -rf gen
mkdir -p gen

# Theorem A: the template set, then one module tree per box.
python3 tools/gen_box.py templates inputs/tset_G.txt
for f in certs/c*x*.txt.xz; do
  b=$(basename "$f" .txt.xz); b=${b#c}; w=${b%x*}; h=${b#*x}
  xz -dc "$f" > "$TMP/c$b.txt"
  xz -dc "certs/b$b.txt.xz" > "$TMP/b$b.txt"
  python3 tools/gen_cbox.py "$w" "$h" "$TMP/c$b.txt" "$TMP/b$b.txt" "N$b" \
    inputs/tset_G.txt inputs/tset_G.txt
done

# Theorem B: shared window stages, then the kernel-speed rewrites (tools/*.py docstrings).
(cd "$PROOF" && lake env lean --run "$CG/tools/WinGenU.lean" "$CG/tools/wincases.txt" "$CG/gen/WinKU" 6)
# The case modules gen/WinKU/<case>/Main.lean, not gen/WinKU/Shared/Main.lean.
python3 tools/stage_fast.py gen/WinKU/Shared/T*.lean $(ls gen/WinKU/*/Main.lean | grep -v /Shared/)
python3 tools/fsig_combine.py gen/WinKU/Shared
python3 tools/allp_intro.py gen/WinKU/*/Main.lean
python3 tools/gen_facts.py tools/wincases.txt WinKU
python3 tools/bundle_cases.py 6

# The characterization, then the export into proof/.
python3 tools/gen_final.py N
python3 tools/export.py "$PROOF"
rm -rf "$TMP"

#!/bin/bash
# Regenerate the certificate modules lean/gen/ (BoxKGen, WinKU, FinalN) from the committed box
# certificates, without rerunning the certificate search; then export proof/.
#
# Theorem A: certs/c{W}x{H}.txt.xz (slice certificates with fire witnesses, after FireGen) and
# certs/b{W}x{H}.txt.xz (stabiliser classes and base masks, from BaseGen) -> BoxKGen/N{W}x{H}.
# Theorem B: lean/tools/wincases.txt -> WinKU (WinGenU, then the kernel-speed post-processing).
#
# usage: certgen/regen.sh   (from the repository root; needs the lean/ library built for the
#        `lake env lean --run` steps)
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd)
CG=$ROOT/certgen
TMP=$(mktemp -d)
cd "$ROOT/lean"
rm -rf gen
mkdir -p gen

# Theorem A: the template set, then one module tree per box.
python3 tools/gen_box.py templates "$CG/inputs/tset_G.txt"
for f in "$CG"/certs/c*x*.txt.xz; do
  b=$(basename "$f" .txt.xz); b=${b#c}; w=${b%x*}; h=${b#*x}
  xz -dc "$f" > "$TMP/c$b.txt"
  xz -dc "$CG/certs/b$b.txt.xz" > "$TMP/b$b.txt"
  python3 tools/gen_cbox.py "$w" "$h" "$TMP/c$b.txt" "$TMP/b$b.txt" "N$b" \
    "$CG/inputs/tset_G.txt" "$CG/inputs/tset_G.txt"
done

# Theorem B: shared window stages, then the kernel-speed rewrites (tools/*.py docstrings).
lake env lean --run tools/WinGenU.lean tools/wincases.txt gen/WinKU 6
# The case modules gen/WinKU/<case>/Main.lean, not gen/WinKU/Shared/Main.lean.
python3 tools/stage_fast.py gen/WinKU/Shared/T*.lean $(ls gen/WinKU/*/Main.lean | grep -v /Shared/)
python3 tools/fsig_combine.py gen/WinKU/Shared
python3 tools/allp_intro.py gen/WinKU/*/Main.lean
python3 tools/gen_facts.py tools/wincases.txt WinKU
python3 tools/bundle_cases.py 6

# The characterization, then the module-system export.
python3 tools/gen_final.py N
python3 tools/make_proof.py "$ROOT/proof"
rm -rf "$TMP"

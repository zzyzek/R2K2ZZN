#!/usr/bin/env python3
"""Write gen/PREFIX/Facts.lean: `CertFacts` from the generated window certificates.
usage: gen_facts.py tools/wincases.txt [PREFIX]   (PREFIX: WinKGen, default, or WinKU)
"""
import sys, re, os
PRE = sys.argv[2] if len(sys.argv) > 2 else 'WinKGen'
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
cases = [l.strip().split('|') for l in open(sys.argv[1]) if l.strip()]
names = {c[0]: c for c in cases}
nCe = len([c for c in cases if c[0].startswith('Ce')]) // 2
nCo = len([c for c in cases if c[0].startswith('Co')]) // 2
def cnt(prefix): return 1 + max([int(re.match(prefix + r'(\d+)', c[0]).group(1)) for c in cases if c[0].startswith(prefix)] + [-1])
nBe, nBo = 21, 5
# Only the certificates `CertFacts` asks for: C entries of window 6 and D entries with c = 0,
# B entries with A = 0. The window-8 C entries are caught by R.
need = [c for c in cases if c[1] == '6' and re.match(r'(Ce\d+c0|Co\d+c0|Be\d+A0|Bo\d+A0)$', c[0])]
out = ["import ZZN.C8R"] + [f"import {PRE}.{c[0]}.Main" for c in need]
out += ["", f"namespace {PRE}", "", "open ZZN ZZN.Win", ""]
def corner(thm, prefix, n, odd, listname, gated):
    if gated:
        out.append(f"theorem {thm} : ∀ AB ∈ {listname}, winC AB = 6 → certify (winC AB) (winC AB) (tmC AB false) {odd} none = true := by")
        out.append("  intro AB hAB h6")
    else:
        out.append(f"theorem {thm} : ∀ AB ∈ {listname}, certify (winC AB) (winC AB) (tmC AB false) {odd} none = true := by")
        out.append("  intro AB hAB")
    out.append(f"  simp only [{listname}, List.mem_cons, List.not_mem_nil, or_false] at hAB")
    out.append("  rcases hAB with " + " | ".join(["rfl"] * n))
    for i in range(n):
        nm = f"{prefix}{i}c0"
        if names[nm][1] == '6':
            out.append(f"  · exact {nm}.cert0")
        else:
            out.append("  · exact absurd h6 (by decide)")
    out.append("")
corner("c_even", "Ce", nCe, 0, "CORNER4", True)
corner("c_odd", "Co", nCo, 1, "CORNER4_ODD", False)
def boundary(thm, prefix, n, odd, listname):
    out.append(f"theorem {thm} : ∀ e ∈ {listname}, ∀ fsl ∈ [none, some 0, some 11],")
    out.append(f"    (fsB e {odd} = 1 ∨ fsB e {odd} = -1) → (fsl ≠ none → fsB e {odd} = 1) →")
    out.append(f"      certify 6 6 (tmB e 0) {odd} (some (1, fsB e {odd}, fsl)) = true := by")
    out.append("  intro e he fsl hfsl h1 h2")
    out.append(f"  simp only [{listname}, List.mem_cons, List.not_mem_nil, or_false] at he")
    out.append("  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfsl")
    out.append("  rcases he with " + " | ".join(["rfl"] * n))
    out.append("  all_goals rcases hfsl with rfl | rfl | rfl")
    for i in range(n):
        nm = f"{prefix}{i}A0"
        for k in range(3):
            if nm not in names:
                out.append("  · exact absurd h1 (by decide)")
            elif k < len(names[nm][4].split(';;')):
                out.append(f"  · exact {nm}.cert{k}")
            else:
                out.append("  · exact absurd (h2 (by decide)) (by decide)")
    out.append("")
boundary("b_even", "Be", nBe, 0, "BOUNDARY3_EVEN")
boundary("b_odd", "Bo", nBo, 1, "BOUNDARY3_ODD")
out += ["/-- **The window certificates**, kernel-checked. -/",
        "theorem certFactsK : CertFacts := ⟨c_even, c_odd, b_even, b_odd⟩", "",
        "/-- **Theorem B** on the domain. -/",
        "theorem theoremB_K {I : Inst} (hI : InDom I) (hS : Solvable I) : Passes I :=",
        "  theoremB_cert certFactsK hI hS", "", f"end {PRE}", ""]
open(os.path.join(ROOT, 'gen', PRE, 'Facts.lean'), 'w').write('\n'.join(out))
print('wrote Facts.lean', len(out), 'lines')

#!/usr/bin/env python3
"""Write gen/WinKGen/Facts.lean: `CertFacts` from the generated window certificates.
usage: gen_facts.py tools/wincases.txt
"""
import sys, re, os
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
cases = [l.strip().split('|') for l in open(sys.argv[1]) if l.strip()]
names = {c[0]: c for c in cases}
nCe = len([c for c in cases if c[0].startswith('Ce')]) // 2
nCo = len([c for c in cases if c[0].startswith('Co')]) // 2
def cnt(prefix): return 1 + max([int(re.match(prefix + r'(\d+)', c[0]).group(1)) for c in cases if c[0].startswith(prefix)] + [-1])
nBe, nBo = 21, 5
out = ["import ZZN.WinBCD"] + [f"import WinKGen.{c[0]}.Main" for c in cases]
out += ["", "namespace WinKGen", "", "open ZZN ZZN.Win", ""]
def corner(thm, prefix, n, odd, listname):
    out.append(f"theorem {thm} : ∀ AB ∈ {listname}, ∀ c : Bool, certify (winC AB) (winC AB) (tmC AB c) {odd} none = true := by")
    out.append("  intro AB hAB c")
    out.append(f"  simp only [{listname}, List.mem_cons, List.not_mem_nil, or_false] at hAB")
    out.append("  rcases hAB with " + " | ".join(["rfl"] * n))
    out.append("  all_goals cases c")
    out.append("  exacts [" + ", ".join(f"{prefix}{i}c{j}.cert0" for i in range(n) for j in (0, 1)) + "]")
    out.append("")
corner("c_even", "Ce", nCe, 0, "CORNER4")
corner("c_odd", "Co", nCo, 1, "CORNER4_ODD")
def boundary(thm, prefix, n, odd, listname):
    out.append(f"theorem {thm} : ∀ e ∈ {listname}, ∀ A, A ≤ 1 → ∀ fsl ∈ [none, some 0, some 11],")
    out.append(f"    (fsB e {odd} = 1 ∨ fsB e {odd} = -1) → (fsl ≠ none → fsB e {odd} = 1) →")
    out.append(f"      certify 6 6 (tmB e A) {odd} (some (1 - A, fsB e {odd}, fsl)) = true := by")
    out.append("  intro e he A hA fsl hfsl h1 h2")
    out.append(f"  simp only [{listname}, List.mem_cons, List.not_mem_nil, or_false] at he")
    out.append("  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfsl")
    out.append("  rcases he with " + " | ".join(["rfl"] * n))
    for i in range(n):
        for A in (0, 1):
            for k in range(3):
                pass
    out.append("  all_goals (interval_cases A <;> rcases hfsl with rfl | rfl | rfl)")
    tacs = []
    for i in range(n):
        for A in (0, 1):
            nm = f"{prefix}{i}A{A}"
            for k in range(3):
                if nm not in names:
                    tacs.append("exact absurd h1 (by decide)")
                else:
                    nF = len(names[nm][4].split(';;'))
                    if k < nF:
                        tacs.append(f"exact {nm}.cert{k}")
                    else:
                        tacs.append("exact absurd (h2 (by decide)) (by decide)")
    for t in tacs:
        out.append(f"  · {t}")
    out.append("")
boundary("b_even", "Be", nBe, 0, "BOUNDARY3_EVEN")
boundary("b_odd", "Bo", nBo, 1, "BOUNDARY3_ODD")
out += ["/-- **The window certificates**, kernel-checked. -/",
        "theorem certFactsK : CertFacts := ⟨c_even, c_odd, b_even, b_odd⟩", "",
        "/-- **Theorem B** on the domain, without `native_decide`. -/",
        "theorem theoremB_K {I : Inst} (hI : InDom I) (hS : Solvable I) : Passes I :=",
        "  theoremB_cert certFactsK hI hS", "", "end WinKGen", ""]
open(os.path.join(ROOT, 'gen', 'WinKGen', 'Facts.lean'), 'w').write('\n'.join(out))
print('wrote Facts.lean', len(out), 'lines')

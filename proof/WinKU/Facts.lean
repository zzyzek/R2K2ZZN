/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.C8R
public import WinKU.Bundle0
public import WinKU.Bundle1
public import WinKU.Bundle2
public import WinKU.Bundle3
public import WinKU.Bundle4
public import WinKU.Bundle5

@[expose] public section

namespace WinKU

open ZZN ZZN.Win

theorem c_even : ∀ AB ∈ CORNER4, winC AB = 6 → certify (winC AB) (winC AB) (tmC AB false) 0 none = true := by
  intro AB hAB h6
  simp only [CORNER4, List.mem_cons, List.not_mem_nil, or_false] at hAB
  rcases hAB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Ce0c0.cert0
  · exact absurd h6 (by decide)
  · exact absurd h6 (by decide)
  · exact absurd h6 (by decide)
  · exact absurd h6 (by decide)
  · exact Ce5c0.cert0
  · exact Ce6c0.cert0
  · exact Ce7c0.cert0
  · exact Ce8c0.cert0
  · exact Ce9c0.cert0
  · exact Ce10c0.cert0
  · exact absurd h6 (by decide)
  · exact Ce12c0.cert0
  · exact Ce13c0.cert0
  · exact Ce14c0.cert0
  · exact absurd h6 (by decide)
  · exact Ce16c0.cert0
  · exact Ce17c0.cert0
  · exact Ce18c0.cert0
  · exact Ce19c0.cert0
  · exact Ce20c0.cert0
  · exact Ce21c0.cert0
  · exact Ce22c0.cert0
  · exact Ce23c0.cert0
  · exact Ce24c0.cert0
  · exact Ce25c0.cert0
  · exact Ce26c0.cert0
  · exact Ce27c0.cert0
  · exact Ce28c0.cert0
  · exact Ce29c0.cert0
  · exact Ce30c0.cert0
  · exact Ce31c0.cert0
  · exact Ce32c0.cert0
  · exact Ce33c0.cert0
  · exact Ce34c0.cert0
  · exact Ce35c0.cert0

theorem c_odd : ∀ AB ∈ CORNER4_ODD, certify (winC AB) (winC AB) (tmC AB false) 1 none = true := by
  intro AB hAB
  simp only [CORNER4_ODD, List.mem_cons, List.not_mem_nil, or_false] at hAB
  rcases hAB with rfl | rfl | rfl
  · exact Co0c0.cert0
  · exact Co1c0.cert0
  · exact Co2c0.cert0

theorem b_even : ∀ e ∈ BOUNDARY3_EVEN, ∀ fsl ∈ [none, some 0, some 11],
    (fsB e 0 = 1 ∨ fsB e 0 = -1) → (fsl ≠ none → fsB e 0 = 1) →
      certify 6 6 (tmB e 0) 0 (some (1, fsB e 0, fsl)) = true := by
  intro e he fsl hfsl h1 h2
  simp only [BOUNDARY3_EVEN, List.mem_cons, List.not_mem_nil, or_false] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfsl
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases hfsl with rfl | rfl | rfl
  · exact Be0A0.cert0
  · exact absurd (h2 (by decide)) (by decide)
  · exact absurd (h2 (by decide)) (by decide)
  · exact Be1A0.cert0
  · exact absurd (h2 (by decide)) (by decide)
  · exact absurd (h2 (by decide)) (by decide)
  · exact Be2A0.cert0
  · exact Be2A0.cert1
  · exact Be2A0.cert2
  · exact Be3A0.cert0
  · exact Be3A0.cert1
  · exact Be3A0.cert2
  · exact Be4A0.cert0
  · exact absurd (h2 (by decide)) (by decide)
  · exact absurd (h2 (by decide)) (by decide)
  · exact Be5A0.cert0
  · exact Be5A0.cert1
  · exact Be5A0.cert2
  · exact Be6A0.cert0
  · exact Be6A0.cert1
  · exact Be6A0.cert2
  · exact Be7A0.cert0
  · exact Be7A0.cert1
  · exact Be7A0.cert2
  · exact Be8A0.cert0
  · exact Be8A0.cert1
  · exact Be8A0.cert2
  · exact Be9A0.cert0
  · exact Be9A0.cert1
  · exact Be9A0.cert2
  · exact Be10A0.cert0
  · exact Be10A0.cert1
  · exact Be10A0.cert2
  · exact Be11A0.cert0
  · exact Be11A0.cert1
  · exact Be11A0.cert2
  · exact Be12A0.cert0
  · exact Be12A0.cert1
  · exact Be12A0.cert2
  · exact Be13A0.cert0
  · exact Be13A0.cert1
  · exact Be13A0.cert2
  · exact Be14A0.cert0
  · exact Be14A0.cert1
  · exact Be14A0.cert2
  · exact Be15A0.cert0
  · exact Be15A0.cert1
  · exact Be15A0.cert2
  · exact Be16A0.cert0
  · exact Be16A0.cert1
  · exact Be16A0.cert2
  · exact Be17A0.cert0
  · exact absurd (h2 (by decide)) (by decide)
  · exact absurd (h2 (by decide)) (by decide)
  · exact Be18A0.cert0
  · exact Be18A0.cert1
  · exact Be18A0.cert2
  · exact Be19A0.cert0
  · exact Be19A0.cert1
  · exact Be19A0.cert2
  · exact Be20A0.cert0
  · exact Be20A0.cert1
  · exact Be20A0.cert2

theorem b_odd : ∀ e ∈ BOUNDARY3_ODD, ∀ fsl ∈ [none, some 0, some 11],
    (fsB e 1 = 1 ∨ fsB e 1 = -1) → (fsl ≠ none → fsB e 1 = 1) →
      certify 6 6 (tmB e 0) 1 (some (1, fsB e 1, fsl)) = true := by
  intro e he fsl hfsl h1 h2
  simp only [BOUNDARY3_ODD, List.mem_cons, List.not_mem_nil, or_false] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfsl
  rcases he with rfl | rfl | rfl | rfl | rfl
  all_goals rcases hfsl with rfl | rfl | rfl
  · exact Bo0A0.cert0
  · exact Bo0A0.cert1
  · exact Bo0A0.cert2
  · exact Bo1A0.cert0
  · exact absurd (h2 (by decide)) (by decide)
  · exact absurd (h2 (by decide)) (by decide)
  · exact Bo2A0.cert0
  · exact Bo2A0.cert1
  · exact Bo2A0.cert2
  · exact Bo3A0.cert0
  · exact Bo3A0.cert1
  · exact Bo3A0.cert2
  · exact Bo4A0.cert0
  · exact Bo4A0.cert1
  · exact Bo4A0.cert2

/-- **The window certificates**, kernel-checked. -/
theorem certFactsK : CertFacts := ⟨c_even, c_odd, b_even, b_odd⟩

/-- **Theorem B** on the domain. -/
theorem theoremB_K {I : Inst} (hI : InDom I) (hS : Solvable I) : Passes I :=
  theoremB_cert certFactsK hI hS

end WinKU

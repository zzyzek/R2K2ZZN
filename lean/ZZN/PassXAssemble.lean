-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.PassXR

/-!
# `passX` for compressions and interior compressions
-/

namespace ZZN

open GridHam

/-- A compression can always be taken with its deleted lines in the middle of the free window. -/
theorem comp_canonical {I : Inst} {d : ℕ} (hI : InDom I) (h : CompClause I d) :
    ∃ d', CompClause I d' ∧ 5 ≤ d' ∧ d' + 7 ≤ I.w ∧ I.deleteAt d = I.deleteAt d' := by
  obtain ⟨-, -, b0, b1, b2, b3, -⟩ := hI
  have hb : ∀ e ∈ I.ends, e.1 < I.w := by
    intro e he
    simp only [Inst.ends, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact b0.1
    · exact b1.1
    · exact b2.1
    · exact b3.1
  rcases h with ⟨lo, hl, hh, hw, hf, ⟨e1, he1, h1⟩, ⟨e2, he2, h2⟩⟩ | hint
  · have := hb e2 he2
    refine ⟨lo + 4, Or.inl ⟨lo, by omega, by omega, hw, hf, ⟨e1, he1, h1⟩, ⟨e2, he2, h2⟩⟩,
      by omega, by omega, deleteAt_window hf ⟨hl, hh⟩ ⟨by omega, by omega⟩⟩
  · have hint' := hint
    obtain ⟨h8, hw, -⟩ := hint'
    exact ⟨d, Or.inr hint, by omega, by omega, rfl⟩

/-- **`passX` for compressions and interior compressions.** -/
theorem passX_comp {I : Inst} {d : ℕ} (hI : InDom I) (hw13 : 13 ≤ I.w) (h : CompClause I d)
    (hP : Passes I) : Passes (I.deleteAt d) := by
  obtain ⟨d', h', hd5, hd7, he⟩ := comp_canonical hI h
  rw [he]
  clear he h d
  have hC := hI.2.1
  obtain ⟨-, -, b0, b1, b2, b3, -⟩ := id hI
  obtain ⟨f0, f1, -⟩ := compClause_free h'
  have av : ∀ q ∈ [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)], Av d' I.w (q : Pt).1 := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨f0 _ (by simp [Inst.ends]), f1 _ (by simp [Inst.ends]), b0.1⟩
    · exact ⟨f0 _ (by simp [Inst.ends]), f1 _ (by simp [Inst.ends]), b1.1⟩
    · exact ⟨f0 _ (by simp [Inst.ends]), f1 _ (by simp [Inst.ends]), b2.1⟩
    · exact ⟨f0 _ (by simp [Inst.ends]), f1 _ (by simp [Inst.ends]), b3.1⟩
  have hpts : [(delAt d' I.s0, 0), (delAt d' I.t0, 0), (delAt d' I.s1, 1), (delAt d' I.t1, 1)] =
      delPts d' [(I.s0, (0 : ℕ)), (I.t0, 0), (I.s1, 1), (I.t1, 1)] := rfl
  unfold Passes at hP ⊢
  by_contra hf
  apply absurd hP
  rw [Bool.not_eq_false] at hf ⊢
  unfold fires3 at hf ⊢
  simp only [Inst.deleteAt] at hf
  simp only [Bool.or_eq_true] at hf ⊢
  rcases hf with (((((hp | ht1) | ht2) | hl1) | hl6) | hfr) | hea
  · left; left; left; left; left; left
    rw [← parityOk_deleteAt (by omega) f0 f1]
    exact hp
  · left; left; left; left; left; right
    exact t1_comp hI h' hw13 ht1
  · rw [t2_comp hI h'] at ht2; exact absurd ht2 (by simp)
  · left; left; left; right
    rw [l1Fires_iff] at hl1 ⊢
    exact l1_comp hI h' hl1
  · left; left; right
    exact l6_comp hI h' hw13 hl6
  · left; right
    exact frames_any_of (by omega) (winRel_comp hI h') (by omega) (e1_comp hI h') hfr
  · right
    rw [hpts, effAlt3_comp hd5 hd7 (by omega) av] at hea
    exact hea

end ZZN

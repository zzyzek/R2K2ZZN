-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.WinPlan
import ZZN.WinPar

/-!
# Window certificates are sound

If a window configuration (`WinSetup`) has a solution, its signature is a final state of the inside
DP (`inside_complete`) that passes the outside test. A certificate says no final state passes.
-/

namespace ZZN.Win

open GridHam

/-- **Window soundness.** -/
theorem window_sound {k : ℕ} {J : Inst} {p q : List Coord} {F : FSpec} {tm : List ((ℕ × ℕ) × ℕ)}
    (W : WinSetup k J p q F) (htm : ∀ y : Coord, y.1 < k → y.2 < k → termAt tm y = endCol J y)
    (hcert : certify k k tm ((J.w * J.h) % 2) F = true) : False := by
  obtain ⟨s, hs, hinv⟩ := inside_complete (a := k) (b := k) W.k8 W.k8 W.sol W.wf W.kw.le W.kh.le htm
  have hno : outsideOK k k ((J.w * J.h) % 2) F s = false := by
    unfold certify at hcert
    have := List.all_eq_true.mp hcert s hs
    simpa using this
  have Pp : PathC p q p 0 := Or.inl ⟨rfl, rfl⟩
  have Pq : PathC p q q 1 := Or.inr ⟨rfl, rfl⟩
  have hyes : outsideOK k k ((J.w * J.h) % 2) F s = true := by
    apply outsideOK_of (fun i => (linkOf k k F s i).getD 0) (muOf k s p q)
      (fun c => chainOf k s (if c = 0 then p else q))
    · exact link_some W hinv
    · exact m_pos W hinv
    · exact window_parity W hinv
    · exact mu_invo W hinv
    · exact window_nocross W hinv
    · exact f_rule W hinv
    · intro c hc
      have hP : PathC p q (if c = 0 then p else q) c := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl
        · exact Pp
        · exact Pq
      rw [done_bit hinv c hc]
      by_cases he : chainOf k s (if c = 0 then p else q) = []
      · left
        exact ⟨he, by rw [ite_eq_left ((chain_empty_iff W hP).mp he)]⟩
      · right
        obtain ⟨a1, a2, a3⟩ := chain_alt W hinv hP he
        exact ⟨a1, by rw [ite_eq_right (fun h => he ((chain_empty_iff W hP).mpr h))], a2, a3⟩
    · exact term_ends W hinv
    · intro c hc
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl
      · exact chain_bound W hinv Pp
      · exact chain_bound W hinv Pq
    · intro i hi
      rcases chains_cover W hinv i hi with h | h
      · exact Or.inl h
      · exact Or.inr h
    · intro c hc
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl
      · exact chain_nodup W hinv Pp
      · exact chain_nodup W hinv Pq
  rw [hno] at hyes
  exact absurd hyes (by simp)

end ZZN.Win

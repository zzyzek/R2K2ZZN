-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Thin.Sound

/-!
# The plug DP on a whole rectangle, without dead states

On a whole rectangle no path leaves the grid, so a state with an exit end can never be completed.
`insideF` drops such states after every cell. It is sound (a subset of what `inside` reaches) and
complete (a solution's states have no exit ends), so it still decides solvability (`thinBF_iff`).
-/

namespace ZZN.Thin

open GridHam

/-- An end code that is a plug inside the grid, or an endpoint. -/
def okEnd (a b e : ℕ) : Bool := decide (e ≤ b) || isTerm a b e

def noExit (a b : ℕ) (s : St) : Bool := s.1.all fun z => okEnd a b (lo z) && okEnd a b (hi z)

def stageF (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (S : List St) (i : ℕ) : List St :=
  (stage a b tm S i).filter (noExit a b)

def insideF (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) : List St :=
  (List.range (a * b)).foldl (stageF a b tm) [([], 0)]

section Proofs

variable {a b : ℕ} {J : Inst}

theorem insideF_sound {tm : List ((ℕ × ℕ) × ℕ)} (htm : ∀ y : Coord, y.1 < a → y.2 < b → termAt tm y = endCol J y) :
    ∀ s ∈ insideF a b tm, W a b J (a * b) s := by
  unfold insideF
  suffices h : ∀ n, n ≤ a * b → ∀ s ∈ (List.range n).foldl (stageF a b tm) [([], 0)], W a b J n s from
    h _ (le_refl _)
  intro n
  induction n with
  | zero => intro _ s hs; rw [List.mem_singleton.mp hs]; exact W_zero
  | succ n ih =>
    intro hn s hs
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hs
    unfold stageF stage at hs
    rw [List.mem_filter, mem_normS, List.mem_flatMap] at hs
    obtain ⟨⟨s0, h0, h1⟩, -⟩ := hs
    exact step_W htm (by omega) (ih (by omega) s0 h0) h1

/-- A boundary edge into a grid cell has a plug code at most `b`. -/
theorem desc_le {i : ℕ} {u v : Coord} (hu : prI a b i u) (hv : ¬ prI a b i v) (h : Adjacent u v)
    (hva : v.1 < a) (hvb : v.2 < b) : desc a b u v ≤ b := by
  rcases bd_dir hu hv h with rfl | rfl
  · rw [desc_down]; simp only at hva; rw [ite_eq_left hva]; exact le_of_lt hu.2.1
  · rw [desc_right]; simp only at hvb; rw [ite_eq_left hvb]

theorem okEnd_min {x y : ℕ} (hx : okEnd a b x = true) (hy : okEnd a b y = true) :
    okEnd a b (min x y) = true ∧ okEnd a b (max x y) = true := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, max_eq_right h]; exact ⟨hx, hy⟩
  · rw [min_eq_right h, max_eq_left h]; exact ⟨hy, hx⟩

/-- **A solution's states have no exit ends.** -/
theorem noExit_of_inv {p q : List Coord} (hS : IsSolution J p q) (ha : a = J.w) (hb : b = J.h) {i : ℕ}
    {s : St} (hs : Inv a b i p q s) : noExit a b s = true := by
  unfold noExit
  rw [List.all_eq_true]
  intro z hz
  obtain ⟨L, col, st, en, hL, hr, -, rfl⟩ := (hs.2.1 z).mp hz
  obtain ⟨-, hc, -⟩ := pathC_facts hS hL
  have inb : ∀ y ∈ L, y.1 < a ∧ y.2 < b := by
    subst ha hb
    rcases hL with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact fun y hy => hS.1.2.2.2.1 y hy
    · exact fun y hy => hS.2.1.2.2.2.1 y hy
  have eL : okEnd a b (endL a b col L st) = true := by
    rcases endL_cases hc hr col with ⟨-, e⟩ | ⟨h0, e, -⟩
    · rw [e]; unfold okEnd isTerm termE; simp
    · rw [e]
      obtain ⟨b1, b2, b3⟩ := endL_bd hc hr h0
      have hv := inb (nth L (st - 1)) (nth_mem (by have := hr.lt; have := hr.le; omega))
      unfold okEnd; simp [desc_le b1 b2 b3 hv.1 hv.2]
  have eR : okEnd a b (endR a b col L en) = true := by
    rcases endR_cases hc hr col with ⟨-, e⟩ | ⟨h0, e, -⟩
    · rw [e]; unfold okEnd isTerm termE; simp
    · rw [e]
      obtain ⟨b1, b2, b3⟩ := endR_bd hc hr h0
      have hv := inb (nth L (en + 1)) (nth_mem (by have := hr.lt; omega))
      unfold okEnd; simp [desc_le b1 b2 b3 hv.1 hv.2]
  unfold runCode
  rw [mkP_lo, mkP_hi]
  obtain ⟨k1, k2⟩ := okEnd_min eL eR
  rw [k1, k2]; rfl

theorem insideF_complete {tm : List ((ℕ × ℕ) × ℕ)} {p q : List Coord} (hS : IsSolution J p q)
    (hwf : J.WellFormed) (ha : a = J.w) (hb : b = J.h)
    (htm : ∀ y : Coord, y.1 < a → y.2 < b → termAt tm y = endCol J y) :
    ∃ s ∈ insideF a b tm, Inv a b (a * b) p q s := by
  unfold insideF
  suffices h : ∀ n, n ≤ a * b → ∃ s ∈ (List.range n).foldl (stageF a b tm) [([], 0)], Inv a b n p q s from
    h _ (le_refl _)
  intro n
  induction n with
  | zero => intro _; exact ⟨_, List.mem_singleton_self _, inv_zero hS⟩
  | succ n ih =>
    intro hn
    obtain ⟨s, hs, hi⟩ := ih (by omega)
    obtain ⟨s', hs', hi'⟩ := inv_step hS hwf (le_of_eq ha) (le_of_eq hb) htm (by omega) hi
    refine ⟨s', ?_, hi'⟩
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    unfold stageF stage
    rw [List.mem_filter, mem_normS, List.mem_flatMap]
    exact ⟨⟨s, hs, hs'⟩, noExit_of_inv hS ha hb hi'⟩

end Proofs

def dpAcceptF (J : Inst) : Bool := (insideF J.w J.h (tmOf J)).contains ([], 3)

theorem dpAcceptF_iff {J : Inst} (hwf : J.WellFormed) : dpAcceptF J = true ↔ Solvable J := by
  unfold dpAcceptF
  rw [List.contains_iff_mem]
  constructor
  · intro h
    obtain ⟨sg, dp, -, -, -, hdone, hnod, hcov⟩ := insideF_sound (J := J) (fun y _ _ => termAt_tmOf J y) _ h
    have hd : doneCols 3 = [0, 1] := by decide
    simp only [hd, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hdone
    obtain ⟨p0, p1⟩ := hdone
    simp only [ends2, ite_true, show (1 : ℕ) ≠ 0 by omega, ite_false] at p0 p1
    have ha : allOf sg dp (([], 3) : St) = dp 0 ++ dp 1 := by simp [allOf, hd]
    rw [ha] at hnod hcov
    refine ⟨dp 0, dp 1, p0, p1, fun v hv hv' => List.disjoint_of_nodup_append hnod hv hv', fun v hv => ?_⟩
    exact List.mem_append.mp ((hcov v).mp (prI_all.mpr ⟨hv.1, hv.2⟩))
  · intro hS
    obtain ⟨p, q, hsol⟩ := hS
    obtain ⟨s, hs, hn, hm, hd⟩ := insideF_complete hsol hwf rfl rfl (fun y _ _ => termAt_tmOf J y)
    -- as in `accept_of_solvable`: no open pieces, both colours done
    have allP : ∀ y ∈ p, prI J.w J.h (J.w * J.h) y := fun y hy => prI_all.mpr (hsol.1.2.2.2.1 y hy)
    have allQ : ∀ y ∈ q, prI J.w J.h (J.w * J.h) y := fun y hy => prI_all.mpr (hsol.2.1.2.2.2.1 y hy)
    have hnil : s.1 = [] := by
      rcases hs1 : s.1 with _ | ⟨z, l⟩
      · rfl
      · exfalso
        obtain ⟨L, col, st, en, hL, hr, hinc, -⟩ := (hm z).mp (by rw [hs1]; exact List.mem_cons_self)
        have allL : ∀ y ∈ L, prI J.w J.h (J.w * J.h) y := by
          rcases hL with ⟨rfl, -⟩ | ⟨rfl, -⟩
          · exact allP
          · exact allQ
        apply hinc
        constructor
        · rcases hr.left with h | h
          · exact h
          · exact absurd (allL _ (nth_mem (by have := hr.le; have := hr.lt; omega))) h
        · rcases hr.right with h | h
          · exact h
          · by_contra hne
            exact h (allL _ (nth_mem (by have := hr.lt; omega)))
    have h3 : s.2 = 3 := by
      rw [hd]; unfold doneMask; rw [ite_eq_left allP, ite_eq_left allQ]
    have : s = ([], 3) := by
      obtain ⟨s1, s2⟩ := s
      simp only at hnil h3
      rw [hnil, h3]
    rw [← this]; exact hs

/-- Rows along the longer side, so the frontier is the short side. -/
def thinBF (J : Inst) : Bool := if J.h ≤ J.w then dpAcceptF J else dpAcceptF J.transpose

theorem thinBF_iff {J : Inst} (hwf : J.WellFormed) : thinBF J = true ↔ Solvable J := by
  unfold thinBF
  split_ifs
  · exact dpAcceptF_iff hwf
  · rw [dpAcceptF_iff (wf_transpose hwf), solvable_transpose_iff]

end ZZN.Thin

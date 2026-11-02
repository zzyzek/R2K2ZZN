-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.WinStep
import ZZN.SoundLocal

/-!
# Window certificates: the solution's signature is a final DP state
-/

namespace ZZN.Win

open GridHam

/-! ### Normalisation keeps every state -/

theorem mergeS_perm : ∀ (f : ℕ) (l m : List St), (mergeS f l m).Perm (l ++ m)
  | 0, l, m => by simp [mergeS]
  | _ + 1, [], m => by simp [mergeS]
  | _ + 1, x :: l, [] => by simp [mergeS]
  | f + 1, x :: l, y :: m => by
    unfold mergeS
    split_ifs
    · exact ((mergeS_perm f (x :: l) m).cons y).trans List.perm_middle.symm
    · exact (mergeS_perm f l (y :: m)).cons x

theorem splitS_perm : ∀ l : List St, ((splitS l).1 ++ (splitS l).2).Perm l
  | [] => by simp [splitS]
  | [x] => by simp [splitS]
  | x :: y :: l => by
    have := splitS_perm l
    simp only [splitS, List.cons_append]
    refine (List.Perm.cons x ?_)
    refine (List.perm_middle).trans ?_
    exact this.cons y

theorem msortS_perm : ∀ (f : ℕ) (l : List St), (msortS f l).Perm l
  | 0, l => by simp [msortS]
  | _ + 1, [] => by simp [msortS]
  | _ + 1, [x] => by simp [msortS]
  | f + 1, x :: y :: l => by
    unfold msortS
    refine (mergeS_perm _ _ _).trans ?_
    exact ((msortS_perm f _).append (msortS_perm f _)).trans (splitS_perm _)

theorem dedupAdj_mem : ∀ (l : List St) (s : St), s ∈ dedupAdj l ↔ s ∈ l
  | [], _ => by simp [dedupAdj]
  | [x], _ => by simp [dedupAdj]
  | x :: y :: l, s => by
    unfold dedupAdj
    split_ifs with h
    · rw [dedupAdj_mem (y :: l) s]
      simp only [beq_iff_eq] at h
      subst h
      simp
    · rw [List.mem_cons, dedupAdj_mem (y :: l) s]; exact List.mem_cons.symm

theorem mem_normS {l : List St} {s : St} : s ∈ normS l ↔ s ∈ l := by
  unfold normS; rw [dedupAdj_mem, (msortS_perm _ _).mem_iff]

/-! ### The induction over cells -/

/-- The endpoint colour of a cell. -/
def endCol (J : Inst) (y : Coord) : Option ℕ :=
  if y = J.s0 ∨ y = J.t0 then some 0 else if y = J.s1 ∨ y = J.t1 then some 1 else none

theorem two_le_len {w h : ℕ} {s t : Coord} {L : List Coord} (hP : IsPath w h s t L) (hst : s ≠ t) :
    2 ≤ L.length := by
  obtain ⟨hh, hl, -⟩ := hP
  match L, hh, hl with
  | [], hh, _ => simp at hh
  | [x], hh, hl => simp at hh hl; exact absurd (hh.symm.trans hl) hst
  | _ :: _ :: _, _, _ => simp

/-- Position `0` is the start, the last position is the end. -/
theorem idx_ends {w h : ℕ} {s t : Coord} {L : List Coord} (hP : IsPath w h s t L) {x : Coord} (hx : x ∈ L) :
    (L.idxOf x = 0 ∨ L.idxOf x + 1 = L.length) ↔ (x = s ∨ x = t) := by
  obtain ⟨hh, hl, hn, -, -⟩ := hP
  have hj := List.idxOf_lt_length_iff.mpr hx
  have gx : L[L.idxOf x] = x := List.getElem_idxOf hj
  have hpos : 0 < L.length := by omega
  have e0 : L[0] = s := by rw [List.head?_eq_getElem?] at hh; simpa [List.getElem?_eq_getElem hpos] using hh
  have e1 : L[L.length - 1] = t := by
    rw [List.getLast?_eq_getElem?] at hl; simpa [List.getElem?_eq_getElem (by omega : L.length - 1 < L.length)] using hl
  constructor
  · rintro (h | h)
    · left; rw [← gx, ← e0]; congr 1
    · right; rw [← gx, ← e1]; congr 1; omega
  · rintro (rfl | rfl)
    · left; exact (List.Nodup.getElem_inj_iff hn).mp (gx.trans e0.symm)
    · right; have := (List.Nodup.getElem_inj_iff hn).mp (gx.trans e1.symm); omega

section Ind

variable {a b : ℕ} {J : Inst} {p q : List Coord} {tm : List ((ℕ × ℕ) × ℕ)}

theorem inv_step (ha : a ≤ 8) (hb : b ≤ 8) (hS : IsSolution J p q) (hwf : J.WellFormed)
    (hwa : a ≤ J.w) (hhb : b ≤ J.h) (htm : ∀ y : Coord, y.1 < a → y.2 < b → termAt tm y = endCol J y)
    {i : ℕ} (hi : i < a * b) {s : St} (hs : Inv a b i p q s) :
    ∃ s' ∈ stepCell a b (termAt tm (cell b i)) (cell b i).1 (cell b i).2 s, Inv a b (i + 1) p q s' := by
  obtain ⟨c1, c2, -⟩ := cell_spec hi
  rcases hx : cell b i with ⟨x1, x2⟩
  rw [hx] at c1 c2
  dsimp only at c1 c2 ⊢
  obtain ⟨-, -, -, -, w1, w2, w3, w4, w5, w6⟩ := hwf
  obtain ⟨m0, m1, m2, m3, n2, n3⟩ := ends_mem hS
  have hcell : (x1, x2) ∈ p ∨ (x1, x2) ∈ q := hS.2.2.2 _ ⟨by simp only; omega, by simp only; omega⟩
  rw [htm _ c1 c2]
  rcases hcell with hxp | hxq
  · have hxq : (x1, x2) ∉ q := hS.2.2.1 _ hxp
    refine step_core ha hb hS hi hx (L := p) (M := q) (col := 0) (col' := 1) (Or.inl ⟨rfl, rfl⟩)
      (Or.inr ⟨rfl, rfl⟩) hxp hxq (fun L'' c'' h => h) (two_le_len hS.1 w1) ?_ hs
    rw [if_congr (idx_ends hS.1 hxp) rfl rfl]
    unfold endCol
    by_cases h1 : (x1, x2) = J.s0 ∨ (x1, x2) = J.t0
    · rw [ite_eq_left h1, ite_eq_left h1]
    · have h2 : ¬ ((x1, x2) = J.s1 ∨ (x1, x2) = J.t1) := by
        rintro (e | e)
        · exact n2 (by rw [← e]; exact hxp)
        · exact n3 (by rw [← e]; exact hxp)
      rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h1]
  · have hxp : (x1, x2) ∉ p := fun h => hS.2.2.1 _ h hxq
    refine step_core ha hb hS hi hx (L := q) (M := p) (col := 1) (col' := 0) (Or.inr ⟨rfl, rfl⟩)
      (Or.inl ⟨rfl, rfl⟩) hxq hxp (fun L'' c'' h => h.symm) (two_le_len hS.2.1 w6) ?_ hs
    rw [if_congr (idx_ends hS.2.1 hxq) rfl rfl]
    unfold endCol
    have h1 : ¬ ((x1, x2) = J.s0 ∨ (x1, x2) = J.t0) := by
      rintro (e | e)
      · exact hxp (by rw [e]; exact m0)
      · exact hxp (by rw [e]; exact m1)
    rw [ite_eq_right h1]

theorem inv_zero (hS : IsSolution J p q) : Inv a b 0 p q ([], 0) := by
  refine ⟨List.nodup_nil, fun z => ⟨fun h => by simp at h, ?_⟩, ?_⟩
  · rintro ⟨L, col, st, en, -, hr, -⟩
    have := hr.all st (le_refl _) hr.le
    unfold prI at this; omega
  · have hp : ¬ ∀ y ∈ p, prI a b 0 y := fun h => by
      have := h _ (List.mem_of_mem_head? hS.1.1); unfold prI at this; omega
    have hq : ¬ ∀ y ∈ q, prI a b 0 y := fun h => by
      have := h _ (List.mem_of_mem_head? hS.2.1.1); unfold prI at this; omega
    unfold doneMask; rw [ite_eq_right hp, ite_eq_right hq]

/-- **The solution's signature is among the final states of the DP.** -/
theorem inside_complete (ha : a ≤ 8) (hb : b ≤ 8) (hS : IsSolution J p q) (hwf : J.WellFormed)
    (hwa : a ≤ J.w) (hhb : b ≤ J.h) (htm : ∀ y : Coord, y.1 < a → y.2 < b → termAt tm y = endCol J y) :
    ∃ s ∈ inside a b tm, Inv a b (a * b) p q s := by
  unfold inside
  suffices h : ∀ n, n ≤ a * b → ∃ s ∈ (List.range n).foldl (stage a b tm) [([], 0)], Inv a b n p q s from
    h _ (le_refl _)
  intro n
  induction n with
  | zero => intro _; exact ⟨_, List.mem_singleton_self _, inv_zero hS⟩
  | succ n ih =>
    intro hn
    obtain ⟨s, hs, hi⟩ := ih (by omega)
    obtain ⟨s', hs', hi'⟩ := inv_step ha hb hS hwf hwa hhb htm (by omega) hi
    refine ⟨s', ?_, hi'⟩
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    unfold stage
    rw [mem_normS, List.mem_flatMap]
    exact ⟨s, hs, hs'⟩

end Ind

end ZZN.Win

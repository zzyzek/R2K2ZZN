-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.WinGeo

/-!
# Window certificates: the outside data, assembled
-/

namespace ZZN.Win

open GridHam

/-- The window configuration of a B, C or D entry: all endpoints in the `k × k` window, or all but
one, F, which lies on the grid perimeter outside the window. -/
structure WinSetup (k : ℕ) (J : Inst) (p q : List Coord) (F : FSpec) : Prop where
  k8 : k ≤ 8
  k2 : 2 ≤ k
  keven : k % 2 = 0
  kw : k < J.w
  kh : k < J.h
  sol : IsSolution J p q
  wf : J.WellFormed
  ends : (F = none ∧ ∀ E, IsEnd J E → E.1 < k ∧ E.2 < k) ∨
    (∃ E fc fs fsl, F = some (fc, fs, fsl) ∧ IsEnd J E ∧ ¬ (E.1 < k ∧ E.2 < k) ∧
      ((fc = 0 ∧ (E = J.s0 ∨ E = J.t0)) ∨ (fc = 1 ∧ (E = J.s1 ∨ E = J.t1))) ∧
      (∀ E', IsEnd J E' → E' ≠ E → E'.1 < k ∧ E'.2 < k) ∧
      (E.1 = 0 ∨ E.2 = 0 ∨ E.1 = J.w - 1 ∨ E.2 = J.h - 1) ∧ fs = sgn E ∧
      (∀ sl, fsl = some sl ↔ sl < 2 * k ∧ exitCell k k sl = E))

section Setup

variable {k : ℕ} {J : Inst} {p q : List Coord} {F : FSpec} (W : WinSetup k J p q F)
include W

/-- The ends of a solution path. -/
theorem pathC_ends {L : List Coord} {col : ℕ} (hp : PathC p q L col) :
    0 < L.length ∧ (∃ s t, IsPath J.w J.h s t L ∧ nth L 0 = s ∧ nth L (L.length - 1) = t ∧ s ≠ t ∧
      ((col = 0 ∧ s = J.s0 ∧ t = J.t0) ∨ (col = 1 ∧ s = J.s1 ∧ t = J.t1))) := by
  obtain ⟨-, -, -, -, w1, -, -, -, -, w6⟩ := W.wf
  have get : ∀ {s t : Coord} {L : List Coord}, IsPath J.w J.h s t L → 0 < L.length ∧ nth L 0 = s ∧
      nth L (L.length - 1) = t := by
    intro s t L hP
    obtain ⟨hh, hl, -⟩ := hP
    have hpos : 0 < L.length := by cases L with | nil => simp at hh | cons => simp
    refine ⟨hpos, ?_, ?_⟩
    · rw [nth_eq hpos]; rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos] at hh; exact Option.some.inj hh
    · rw [nth_eq (by omega)]
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hl; exact Option.some.inj hl
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨g1, g2, g3⟩ := get W.sol.1
    exact ⟨g1, _, _, W.sol.1, g2, g3, w1, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · obtain ⟨g1, g2, g3⟩ := get W.sol.2.1
    exact ⟨g1, _, _, W.sol.2.1, g2, g3, w6, Or.inr ⟨rfl, rfl, rfl⟩⟩

/-- A path end outside the window is F, of the path's colour. -/
theorem out_end {L : List Coord} {col : ℕ} (hp : PathC p q L col) {x : Coord}
    (hx : x = nth L 0 ∨ x = nth L (L.length - 1)) (hout : ¬ (x.1 < k ∧ x.2 < k)) :
    ∃ fs fsl, F = some (col, fs, fsl) ∧ x.1 = x.1 ∧ (∀ E', IsEnd J E' → E' ≠ x → E'.1 < k ∧ E'.2 < k) ∧
      fs = sgn x ∧ (∀ sl, fsl = some sl ↔ sl < 2 * k ∧ exitCell k k sl = x) := by
  obtain ⟨-, s, t, -, hs, ht, -, hc⟩ := pathC_ends W hp
  have hE : IsEnd J x := by
    rcases hx with rfl | rfl <;> rcases hc with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ <;> unfold IsEnd <;> simp [hs, ht]
  rcases W.ends with ⟨-, h⟩ | ⟨E, fc, fs, fsl, hF, hEe, hEo, hcol, hoth, -, hfs, hfsl⟩
  · exact absurd (h x hE) hout
  · have xE : x = E := by
      by_contra ne
      exact hout (hoth x hE ne)
    subst xE
    refine ⟨fs, fsl, ?_, rfl, hoth, hfs, hfsl⟩
    rw [hF]
    obtain ⟨-, -, -, -, w1, w2, w3, w4, w5, w6⟩ := W.wf
    congr
    rcases hx with rfl | rfl <;> rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hcol with ⟨rfl, e | e⟩ | ⟨rfl, e | e⟩ <;> simp_all

/-- F's link: the terminal of its colour. -/
theorem link_F {s : St} {L : List Coord} {col : ℕ} (hp : PathC p q L col)
    (h : offL k L = 1 ∨ offR k L = 1) :
    linkOf k k F s (usedOf k k s).length = some (mOf k k F s + col) := by
  have hout : ∃ x, (x = nth L 0 ∨ x = nth L (L.length - 1)) ∧ ¬ (x.1 < k ∧ x.2 < k) := by
    rcases h with h | h
    · refine ⟨nth L 0, Or.inl rfl, fun c => ?_⟩
      unfold offL at h; rw [ite_eq_left (inWb_iff.mpr c)] at h; omega
    · refine ⟨nth L (L.length - 1), Or.inr rfl, fun c => ?_⟩
      unfold offR at h; rw [ite_eq_left (inWb_iff.mpr c)] at h; omega
  obtain ⟨x, hx, ho⟩ := hout
  obtain ⟨fs, fsl, hF, -⟩ := out_end W hp hx ho
  unfold linkOf
  rw [ite_eq_right (lt_irrefl _), hF]

/-- At most one end of a path lies outside the window. -/
theorem one_out {L : List Coord} {col : ℕ} (hp : PathC p q L col) : ¬ (offL k L = 1 ∧ offR k L = 1) := by
  rintro ⟨h1, h2⟩
  obtain ⟨-, s, t, -, hs, ht, hst, hc⟩ := pathC_ends W hp
  have o1 : ¬ ((nth L 0).1 < k ∧ (nth L 0).2 < k) := fun c => by
    unfold offL at h1; rw [ite_eq_left (inWb_iff.mpr c)] at h1; omega
  have o2 : ¬ ((nth L (L.length - 1)).1 < k ∧ (nth L (L.length - 1)).2 < k) := fun c => by
    unfold offR at h2; rw [ite_eq_left (inWb_iff.mpr c)] at h2; omega
  obtain ⟨-, -, -, -, oth, -⟩ := out_end W hp (Or.inl rfl) o1
  have hE : IsEnd J (nth L (L.length - 1)) := by
    rw [ht]; rcases hc with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> unfold IsEnd <;> simp
  exact o2 (oth _ hE (by rw [hs, ht]; exact Ne.symm hst))

end Setup

section Nodes

variable {k : ℕ} {J : Inst} {p q : List Coord} {F : FSpec} {s : St}
  (W : WinSetup k J p q F) (hinv : Inv k k (k * k) p q s)
include W hinv

/-- The nodes of a chain are below `m`, and F's node appears only if F exists. -/
theorem chain_bound {L : List Coord} {col : ℕ} (hp : PathC p q L col) :
    ∀ i ∈ chainOf k s L, i < mOf k k F s := by
  intro i hi
  unfold chainOf at hi
  simp only [List.mem_append, List.mem_map] at hi
  have fsome : (offL k L = 1 ∨ offR k L = 1) → F.isSome = true := fun h => by
    have := link_F W (s := s) hp h
    unfold linkOf at this; rw [ite_eq_right (lt_irrefl _)] at this
    cases hF : F with
    | none => rw [hF] at this; simp at this
    | some _ => rfl
  unfold mOf
  rcases hi with (h | ⟨j, hj, rfl⟩) | h
  · split_ifs at h with h0
    · simp at h
    · simp at h; subst h
      rw [fsome (Or.inl (by unfold offL; rw [ite_eq_right h0]))]; simp
  · have mem : crossSlot k L j ∈ usedOf k k s :=
      (used_iff W.k8 W.sol hinv _).mpr ⟨L, col, j, hp, mem_CI.mp hj, rfl⟩
    have := List.idxOf_lt_length_iff.mpr mem
    omega
  · split_ifs at h with h0
    · simp at h
    · simp at h; subst h
      rw [fsome (Or.inr (by unfold offR; rw [ite_eq_right h0]))]; simp

omit W hinv in
theorem used_nodup : (usedOf k k s).Nodup := by
  unfold usedOf; exact List.nodup_range.filter _

theorem map_nodup {L : List Coord} {col : ℕ} (hp : PathC p q L col) :
    ((CI k L).map fun j => (usedOf k k s).idxOf (crossSlot k L j)).Nodup := by
  refine (List.pairwise_map).mpr (CI_sorted.imp_of_mem ?_)
  intro a b ha hb hab e
  have ma := (used_iff W.k8 W.sol hinv _).mpr ⟨L, col, a, hp, mem_CI.mp ha, rfl⟩
  have mb := (used_iff W.k8 W.sol hinv _).mpr ⟨L, col, b, hp, mem_CI.mp hb, rfl⟩
  have := (List.idxOf_inj (l := usedOf k k s) ma).mp e
  obtain ⟨-, -, e'⟩ := cross_unique W.sol hp hp (mem_CI.mp ha) (mem_CI.mp hb) this
  omega

theorem chain_nodup {L : List Coord} {col : ℕ} (hp : PathC p q L col) : (chainOf k s L).Nodup := by
  have hm := map_nodup W hinv hp
  have notF : (usedOf k k s).length ∉ (CI k L).map fun j => (usedOf k k s).idxOf (crossSlot k L j) := by
    intro h
    obtain ⟨j, hj, e⟩ := List.mem_map.mp h
    have mem := (used_iff W.k8 W.sol hinv _).mpr ⟨L, col, j, hp, mem_CI.mp hj, rfl⟩
    have := List.idxOf_lt_length_iff.mpr mem
    omega
  have one := one_out W hp
  unfold chainOf
  unfold offL offR at one
  split_ifs with h1 h2 h2
  · simpa using hm
  · simp only [List.nil_append]
    rw [List.nodup_append]; exact ⟨hm, by simp, by simpa using notF⟩
  · simp only [List.append_nil, List.singleton_append, List.nodup_cons]; exact ⟨notF, hm⟩
  · exact absurd ⟨by rw [ite_eq_right h1], by rw [ite_eq_right h2]⟩ one

theorem chains_disj : ∀ i ∈ chainOf k s p, i ∉ chainOf k s q := by
  intro i hp hq
  have notF : ∀ {L : List Coord} {col : ℕ}, PathC p q L col →
      (usedOf k k s).length ∉ (CI k L).map fun j => (usedOf k k s).idxOf (crossSlot k L j) := by
    intro L col hL h
    obtain ⟨j, hj, e⟩ := List.mem_map.mp h
    have mem := (used_iff W.k8 W.sol hinv _).mpr ⟨L, col, j, hL, mem_CI.mp hj, rfl⟩
    have := List.idxOf_lt_length_iff.mpr mem
    omega
  have Pp : PathC p q p 0 := Or.inl ⟨rfl, rfl⟩
  have Pq : PathC p q q 1 := Or.inr ⟨rfl, rfl⟩
  -- F's node in a chain: an end outside, of that colour
  have fcol : ∀ {L : List Coord} {col : ℕ}, PathC p q L col →
      (usedOf k k s).length ∈ chainOf k s L → ∃ fs fsl, F = some (col, fs, fsl) := by
    intro L col hL h
    unfold chainOf at h
    simp only [List.mem_append] at h
    rcases h with (h | h) | h
    · split_ifs at h with h0
      · simp at h
      · obtain ⟨fs, fsl, hF, -⟩ := out_end W hL (Or.inl rfl) (fun c => h0 (inWb_iff.mpr c)); exact ⟨fs, fsl, hF⟩
    · exact absurd h (notF hL)
    · split_ifs at h with h0
      · simp at h
      · obtain ⟨fs, fsl, hF, -⟩ := out_end W hL (Or.inr rfl) (fun c => h0 (inWb_iff.mpr c)); exact ⟨fs, fsl, hF⟩
  have split : ∀ {L : List Coord} {col : ℕ}, PathC p q L col → i ∈ chainOf k s L →
      i = (usedOf k k s).length ∨ ∃ j ∈ CI k L, i = (usedOf k k s).idxOf (crossSlot k L j) := by
    intro L col hL h
    unfold chainOf at h
    simp only [List.mem_append, List.mem_map] at h
    rcases h with (h | ⟨j, hj, rfl⟩) | h
    · split_ifs at h <;> simp at h; exact Or.inl h
    · exact Or.inr ⟨j, hj, rfl⟩
    · split_ifs at h <;> simp at h; exact Or.inl h
  rcases split Pp hp with e | ⟨j, hj, e⟩ <;> rcases split Pq hq with e' | ⟨j', hj', e'⟩
  · subst e
    obtain ⟨_, _, h1⟩ := fcol Pp hp
    obtain ⟨_, _, h2⟩ := fcol Pq hq
    rw [h1] at h2; simp at h2
  · subst e; have := List.idxOf_lt_length_iff.mpr ((used_iff W.k8 W.sol hinv _).mpr ⟨q, 1, j', Pq, mem_CI.mp hj', rfl⟩)
    omega
  · subst e'; have := List.idxOf_lt_length_iff.mpr ((used_iff W.k8 W.sol hinv _).mpr ⟨p, 0, j, Pp, mem_CI.mp hj, rfl⟩)
    omega
  · have m1 := (used_iff W.k8 W.sol hinv _).mpr ⟨p, 0, j, Pp, mem_CI.mp hj, rfl⟩
    have := (List.idxOf_inj (l := usedOf k k s) m1).mp (e.symm.trans e')
    obtain ⟨-, h, -⟩ := cross_unique W.sol Pp Pq (mem_CI.mp hj) (mem_CI.mp hj') this
    omega

theorem chains_cover : ∀ i, i < mOf k k F s → i ∈ chainOf k s p ∨ i ∈ chainOf k s q := by
  intro i hi
  by_cases hu : i < (usedOf k k s).length
  · have mem : (usedOf k k s).getD i 0 ∈ usedOf k k s := by
      rw [List.getD_eq_getElem _ _ hu]; exact List.getElem_mem _
    obtain ⟨L, col, j, hp, hc, he⟩ := (used_iff W.k8 W.sol hinv _).mp mem
    have hi' : (usedOf k k s).idxOf (crossSlot k L j) = i := by
      rw [he, List.getD_eq_getElem _ _ hu]; exact (used_nodup).idxOf_getElem _ _
    have inL : i ∈ chainOf k s L := by
      unfold chainOf
      simp only [List.mem_append, List.mem_map]
      exact Or.inl (Or.inr ⟨j, mem_CI.mpr hc, hi'⟩)
    rcases hp with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl inL
    · exact Or.inr inL
  · -- the F node
    have hiF : i = (usedOf k k s).length := by unfold mOf at hi; split_ifs at hi <;> omega
    subst hiF
    have hF : F.isSome = true := by unfold mOf at hi; split_ifs at hi with h <;> first | exact h | omega
    rcases W.ends with ⟨h0, -⟩ | ⟨E, fc, fs, fsl, hF', hE, hEo, hcol, -⟩
    · rw [h0] at hF; simp at hF
    obtain ⟨g1, s0, t0, -, hs, ht, -, hc0⟩ := pathC_ends W (Or.inl ⟨rfl, rfl⟩ : PathC p q p 0)
    obtain ⟨g2, s1, t1, -, hs', ht', -, hc1⟩ := pathC_ends W (Or.inr ⟨rfl, rfl⟩ : PathC p q q 1)
    have memF : ∀ {L : List Coord}, (nth L 0 = E ∨ nth L (L.length - 1) = E) →
        (usedOf k k s).length ∈ chainOf k s L := by
      intro L h
      unfold chainOf
      simp only [List.mem_append]
      rcases h with h | h
      · left; left; rw [ite_eq_right (by rw [h]; intro c; exact hEo (inWb_iff.mp c))]; simp
      · right; rw [ite_eq_right (by rw [h]; intro c; exact hEo (inWb_iff.mp c))]; simp
    rcases hc0 with ⟨-, rfl, rfl⟩ | ⟨h, -⟩
    · rcases hc1 with ⟨h, -⟩ | ⟨-, rfl, rfl⟩
      · omega
      · rcases hcol with ⟨-, e | e⟩ | ⟨-, e | e⟩
        · exact Or.inl (memF (Or.inl (hs.trans e.symm)))
        · exact Or.inl (memF (Or.inr (ht.trans e.symm)))
        · exact Or.inr (memF (Or.inl (hs'.trans e.symm)))
        · exact Or.inr (memF (Or.inr (ht'.trans e.symm)))
    · omega

end Nodes

/-! ### The matching: partners within a chain -/

def partner (N : List ℕ) (i : ℕ) : ℕ :=
  N.getD (if N.idxOf i % 2 = 0 then N.idxOf i + 1 else N.idxOf i - 1) 0

theorem partner_props {N : List ℕ} (hn : N.Nodup) (he : N.length % 2 = 0) {i : ℕ} (hi : i ∈ N) :
    partner N i ∈ N ∧ partner N i ≠ i ∧ partner N (partner N i) = i := by
  have lt := List.idxOf_lt_length_iff.mpr hi
  set j := N.idxOf i with hj
  have gi : N.getD j 0 = i := by rw [List.getD_eq_getElem _ _ lt]; exact List.getElem_idxOf lt
  have idx : ∀ t, t < N.length → N.idxOf (N.getD t 0) = t := fun t ht => by
    rw [List.getD_eq_getElem _ _ ht]; exact hn.idxOf_getElem _ _
  have pos : (if j % 2 = 0 then j + 1 else j - 1) < N.length := by split_ifs <;> omega
  have ne : (if j % 2 = 0 then j + 1 else j - 1) ≠ j := by split_ifs <;> omega
  unfold partner
  rw [← hj]
  refine ⟨by rw [List.getD_eq_getElem _ _ pos]; exact List.getElem_mem _, fun e => ?_, ?_⟩
  · have := idx _ pos; rw [e, ← hj] at this; exact ne this.symm
  · rw [idx _ pos]
    have : (if (if j % 2 = 0 then j + 1 else j - 1) % 2 = 0 then (if j % 2 = 0 then j + 1 else j - 1) + 1
        else (if j % 2 = 0 then j + 1 else j - 1) - 1) = j := by split_ifs <;> omega
    rw [this, gi]

theorem partner_pos {N : List ℕ} (hn : N.Nodup) {t : ℕ} (ht : 2 * t + 1 < N.length) :
    partner N (N.getD (2 * t) 0) = N.getD (2 * t + 1) 0 ∧ partner N (N.getD (2 * t + 1) 0) = N.getD (2 * t) 0 := by
  have idx : ∀ u, u < N.length → N.idxOf (N.getD u 0) = u := fun u hu => by
    rw [List.getD_eq_getElem _ _ hu]; exact hn.idxOf_getElem _ _
  unfold partner
  rw [idx _ (by omega), idx _ ht]
  constructor
  · rw [ite_eq_left (by omega)]
  · rw [ite_eq_right (by omega), show 2 * t + 1 - 1 = 2 * t by omega]

/-! ### The outside data -/

section Data

variable {k : ℕ} {J : Inst} {p q : List Coord} {F : FSpec} {s : St}
  (W : WinSetup k J p q F) (hinv : Inv k k (k * k) p q s)
include W hinv

/-- The matching: partners within the chains. -/
def muOf (k : ℕ) (s : St) (p q : List Coord) (i : ℕ) : ℕ :=
  if i ∈ chainOf k s p then partner (chainOf k s p) i else partner (chainOf k s q) i

omit hinv in
theorem chain_even {L : List Coord} {col : ℕ} (hp : PathC p q L col) : (chainOf k s L).length % 2 = 0 :=
  chainOf_even (pathC_ends W hp).1

theorem mu_on {L : List Coord} {col : ℕ} (hp : PathC p q L col) {i : ℕ} (hi : i ∈ chainOf k s L) :
    muOf k s p q i = partner (chainOf k s L) i := by
  unfold muOf
  rcases hp with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · rw [ite_eq_left hi]
  · rw [ite_eq_right (fun h => chains_disj W hinv i h hi)]

theorem mu_invo : Invo (muOf k s p q) (List.range (mOf k k F s)) := by
  intro i hi
  have hi' := List.mem_range.mp hi
  have go : ∀ {L : List Coord} {col : ℕ}, PathC p q L col → i ∈ chainOf k s L →
      muOf k s p q i ∈ List.range (mOf k k F s) ∧ muOf k s p q i ≠ i ∧ muOf k s p q (muOf k s p q i) = i := by
    intro L col hp hiL
    obtain ⟨m1, m2, m3⟩ := partner_props (chain_nodup W hinv hp) (chain_even W hp) hiL
    rw [mu_on W hinv hp hiL]
    exact ⟨List.mem_range.mpr (chain_bound W hinv hp _ m1), m2, by rw [mu_on W hinv hp m1, m3]⟩
  rcases chains_cover W hinv i hi' with h | h
  · exact go (Or.inl ⟨rfl, rfl⟩) h
  · exact go (Or.inr ⟨rfl, rfl⟩) h

/-- The chain element at a crossing has a link. -/
theorem cross_link_some {L : List Coord} {col : ℕ} (hp : PathC p q L col) {j : ℕ} (hj : j ∈ CI k L) :
    ∃ v, linkOf k k F s ((usedOf k k s).idxOf (crossSlot k L j)) = some v := by
  have lt := List.idxOf_lt_length_iff.mpr hj
  have gj : (CI k L).getD ((CI k L).idxOf j) 0 = j := by
    rw [List.getD_eq_getElem _ _ lt]; exact List.getElem_idxOf lt
  have hc := mem_CI.mp hj
  by_cases hw : inWb k (nth L j) = true
  · have := link_leave (F := F) W.k8 W.sol hinv hp lt (by rw [gj]; exact hw)
    rw [gj] at this; exact ⟨_, this⟩
  · have hw' : inWb k (nth L (j + 1)) = true := by
      have := hc.2; cases e : inWb k (nth L (j + 1)) <;> simp_all
    have := link_enter (F := F) W.k8 W.sol hinv hp lt (by rw [gj]; exact hw')
    rw [gj] at this; exact ⟨_, this⟩

theorem link_some : ∀ i, i < mOf k k F s → linkOf k k F s i = some ((linkOf k k F s i).getD 0) := by
  intro i hi
  have go : ∀ {L : List Coord} {col : ℕ}, PathC p q L col → i ∈ chainOf k s L →
      linkOf k k F s i = some ((linkOf k k F s i).getD 0) := by
    intro L col hp h
    unfold chainOf at h
    simp only [List.mem_append, List.mem_map] at h
    rcases h with (h | ⟨j, hj, rfl⟩) | h
    · split_ifs at h with h0
      · simp at h
      · simp at h; subst h
        rw [link_F W hp (Or.inl (by unfold offL; rw [ite_eq_right h0]))]; rfl
    · obtain ⟨v, hv⟩ := cross_link_some W hinv hp hj; rw [hv]; rfl
    · split_ifs at h with h0
      · simp at h
      · simp at h; subst h
        rw [link_F W hp (Or.inr (by unfold offR; rw [ite_eq_right h0]))]; rfl
  rcases chains_cover W hinv i hi with h | h
  · exact go (Or.inl ⟨rfl, rfl⟩) h
  · exact go (Or.inr ⟨rfl, rfl⟩) h

/-- **Each path's chain alternates, with its colour's terminals at both ends.** -/
theorem chain_alt {L : List Coord} {col : ℕ} (hp : PathC p q L col) (hne : chainOf k s L ≠ []) :
    AltF (mOf k k F s) (fun i => (linkOf k k F s i).getD 0) (muOf k s p q) (chainOf k s L) ∧
      (linkOf k k F s ((chainOf k s L).getD 0 0)).getD 0 = mOf k k F s + col ∧
      (linkOf k k F s ((chainOf k s L).getD ((chainOf k s L).length - 1) 0)).getD 0 = mOf k k F s + col := by
  have hL := (pathC_ends W hp).1
  have hev := chain_even (s := s) W hp
  have hpos : 0 < (chainOf k s L).length := List.length_pos_iff.mpr hne
  have hn := chain_nodup W hinv hp
  have hb := chain_bound W hinv hp
  have mem : ∀ u, u < (chainOf k s L).length → (chainOf k s L).getD u 0 ∈ chainOf k s L := fun u hu => by
    rw [List.getD_eq_getElem _ _ hu]; exact List.getElem_mem _
  obtain ⟨e1, e2⟩ := chain_ends (F := F) W.k8 W.sol hinv hp hL hne (link_F W hp)
  refine ⟨⟨hev, by omega, fun t ht => ?_, fun t ht => ?_, ?_, ?_⟩, by rw [e1]; rfl, by rw [e2]; rfl⟩
  · rw [mu_on W hinv hp (mem _ (by omega)), mu_on W hinv hp (mem _ ht)]
    exact partner_pos hn ht
  · obtain ⟨l1, l2⟩ := chain_links (F := F) W.k8 W.sol hinv hp hL ht
    rw [l1, l2]
    exact ⟨rfl, rfl, hb _ (mem _ (by omega)), hb _ (mem _ ht)⟩
  · rw [e1]; simp
  · rw [e2]; simp

/-- **Terminal links occur only at the ends of the chain of their colour.** -/
theorem term_ends : ∀ i, i < mOf k k F s → ∀ c, c ≤ 1 →
    (linkOf k k F s i).getD 0 = mOf k k F s + c →
    i ∈ chainOf k s (if c = 0 then p else q) ∧
      (i = (chainOf k s (if c = 0 then p else q)).getD 0 0 ∨
        i = (chainOf k s (if c = 0 then p else q)).getD ((chainOf k s (if c = 0 then p else q)).length - 1) 0) := by
  intro i hi c hc e
  have go : ∀ {L : List Coord} {col : ℕ}, PathC p q L col → i ∈ chainOf k s L →
      col = c ∧ (i = (chainOf k s L).getD 0 0 ∨ i = (chainOf k s L).getD ((chainOf k s L).length - 1) 0) := by
    intro L col hp hiL
    have hL := (pathC_ends W hp).1
    have hn := chain_nodup W hinv hp
    have hb := chain_bound W hinv hp
    have lt := List.idxOf_lt_length_iff.mpr hiL
    have gi : (chainOf k s L).getD ((chainOf k s L).idxOf i) 0 = i := by
      rw [List.getD_eq_getElem _ _ lt]; exact List.getElem_idxOf lt
    have mem : ∀ u, u < (chainOf k s L).length → (chainOf k s L).getD u 0 ∈ chainOf k s L := fun u hu => by
      rw [List.getD_eq_getElem _ _ hu]; exact List.getElem_mem _
    -- interior positions link to nodes below `m`
    have pos : (chainOf k s L).idxOf i = 0 ∨ (chainOf k s L).idxOf i = (chainOf k s L).length - 1 := by
      by_contra h
      push Not at h
      set t := (chainOf k s L).idxOf i with ht
      rcases Nat.even_or_odd t with ⟨u, hu⟩ | ⟨u, hu⟩
      · obtain ⟨-, l2⟩ := chain_links (F := F) W.k8 W.sol hinv hp hL (t := u - 1) (by omega)
        rw [show 2 * (u - 1) + 2 = t by omega, gi] at l2
        rw [l2, Option.getD_some] at e
        have := hb _ (mem (2 * (u - 1) + 1) (by omega))
        omega
      · obtain ⟨l1, -⟩ := chain_links (F := F) W.k8 W.sol hinv hp hL (t := u) (by omega)
        rw [show 2 * u + 1 = t by omega, gi] at l1
        rw [l1, Option.getD_some] at e
        have := hb _ (mem (2 * u + 2) (by omega))
        omega
    have hne : chainOf k s L ≠ [] := List.ne_nil_of_mem hiL
    obtain ⟨-, f1, f2⟩ := chain_alt W hinv hp hne
    rcases pos with h | h
    · rw [h] at gi; rw [gi] at f1; rw [f1] at e
      exact ⟨by omega, Or.inl gi.symm⟩
    · rw [h] at gi; rw [gi] at f2; rw [f2] at e
      exact ⟨by omega, Or.inr gi.symm⟩
  rcases chains_cover W hinv i hi with h | h
  · obtain ⟨rfl, h2⟩ := go (Or.inl ⟨rfl, rfl⟩) h
    simp only [↓reduceIte]; exact ⟨h, h2⟩
  · obtain ⟨rfl, h2⟩ := go (Or.inr ⟨rfl, rfl⟩) h
    simp only [one_ne_zero, ↓reduceIte]; exact ⟨h, h2⟩

omit hinv in
theorem chain_empty_iff {L : List Coord} {col : ℕ} (hp : PathC p q L col) :
    chainOf k s L = [] ↔ ∀ y ∈ L, inWb k y = true := by
  have hL := (pathC_ends W hp).1
  have hlen := chainOf_length (k := k) (s := s) (L := L)
  constructor
  · intro h y hy
    rw [h] at hlen; simp at hlen
    have h0 : offL k L = 0 := by omega
    have hr : (CI k L).length = 0 := by omega
    have hσ : inWb k (nth L 0) = true := by unfold offL at h0; split_ifs at h0 with h'; exact h'
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
    rw [← nth_eq hj, status_const (L := L) (a := 0) j (Nat.zero_le _) hj (fun j' _ _ => CI_none hr j')]
    exact hσ
  · intro h
    have nc : ∀ j, ¬ IsCross k L j := fun j hc => by
      have := hc.2
      rw [h _ (nth_mem (by have := hc.1; omega)), h _ (nth_mem hc.1)] at this
      exact this rfl
    have hr : (CI k L).length = 0 := by
      rw [List.length_eq_zero_iff, List.eq_nil_iff_forall_not_mem]
      exact fun j hj => nc j (mem_CI.mp hj)
    have h0 : offL k L = 0 := by unfold offL; rw [ite_eq_left (h _ (nth_mem hL))]
    have h1 : offR k L = 0 := by unfold offR; rw [ite_eq_left (h _ (nth_mem (by omega)))]
    rw [h0, hr, h1] at hlen
    exact List.length_eq_zero_iff.mp hlen

omit W in
theorem done_bit (c : ℕ) (hc : c ≤ 1) :
    (s.2 / 2 ^ c) % 2 = if ∀ y ∈ (if c = 0 then p else q), inWb k y = true then 1 else 0 := by
  rw [hinv.2.2]
  unfold doneMask
  have e : ∀ L : List Coord, (∀ y ∈ L, prI k k (k * k) y) ↔ (∀ y ∈ L, inWb k y = true) :=
    fun L => ⟨fun h y hy => prI_all'.mp (h y hy), fun h y hy => prI_all'.mpr (h y hy)⟩
  rw [if_congr (e p) rfl rfl, if_congr (e q) rfl rfl]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl
  · simp only [↓reduceIte]; split_ifs <;> simp
  · simp only [one_ne_zero, ↓reduceIte]; split_ifs <;> simp

theorem m_pos : mOf k k F s ≠ 0 := by
  intro h0
  unfold mOf at h0
  have hu : (usedOf k k s).length = 0 := by omega
  have hF : F.isSome = false := by
    cases hF : F.isSome
    · rfl
    · rw [hF] at h0; simp at h0
  rcases W.ends with ⟨-, hin⟩ | ⟨E, fc, fs, fsl, hF', -⟩
  swap
  · rw [hF'] at hF; simp at hF
  -- no crossings anywhere
  have nc : ∀ {L : List Coord} {col : ℕ}, PathC p q L col → ∀ j, ¬ IsCross k L j := by
    intro L col hp j hc
    have := (used_iff W.k8 W.sol hinv _).mpr ⟨L, col, j, hp, hc, rfl⟩
    rw [List.length_eq_zero_iff] at hu; rw [hu] at this; simp at this
  have allIn : ∀ {L : List Coord} {col : ℕ}, PathC p q L col → ∀ y ∈ L, y.1 < k ∧ y.2 < k := by
    intro L col hp y hy
    obtain ⟨hL, s', t', -, hs, -, -, hc⟩ := pathC_ends W hp
    have hσ : inWb k (nth L 0) = true := by
      rw [hs]; apply inWb_iff.mpr; apply hin
      rcases hc with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> unfold IsEnd <;> simp
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
    rw [← nth_eq hj]
    apply inWb_iff.mp
    rw [status_const (L := L) (a := 0) j (Nat.zero_le _) hj (fun j' _ _ => nc hp j')]
    exact hσ
  have hcell : ((k, 0) : Coord) ∈ p ∨ ((k, 0) : Coord) ∈ q := W.sol.2.2.2 _ ⟨W.kw, by have := W.kh; omega⟩
  rcases hcell with h | h
  · have := (allIn (Or.inl ⟨rfl, rfl⟩) _ h).1; simp at this
  · have := (allIn (Or.inr ⟨rfl, rfl⟩) _ h).1; simp at this

omit W hinv in
theorem CI_first_zero {L : List Coord} (h0 : 0 ∈ CI k L) : (CI k L).getD 0 0 = 0 := by
  obtain ⟨t, ht, e⟩ := List.getElem_of_mem h0
  rw [List.getD_eq_getElem _ _ (by omega)]
  rcases Nat.eq_zero_or_pos t with c | c
  · subst c; exact e
  · have := List.pairwise_iff_getElem.mp (CI_sorted (k := k) (L := L)) 0 t (by omega) ht c; omega

omit W hinv in
theorem CI_last_max {L : List Coord} (h0 : L.length - 2 ∈ CI k L) (hL : 2 ≤ L.length) :
    (CI k L).getD ((CI k L).length - 1) 0 = L.length - 2 := by
  obtain ⟨t, ht, e⟩ := List.getElem_of_mem h0
  rw [List.getD_eq_getElem _ _ (by omega)]
  have bound : (CI k L)[(CI k L).length - 1] ≤ L.length - 2 := by
    have := (mem_CI (k := k) (L := L)).mp (List.getElem_mem (h := (by omega : (CI k L).length - 1 < (CI k L).length)))
    have := this.1; omega
  rcases Nat.lt_or_ge t ((CI k L).length - 1) with c | c
  · have := List.pairwise_iff_getElem.mp (CI_sorted (k := k) (L := L)) t ((CI k L).length - 1) ht (by omega) c
    omega
  · have ht' : (CI k L).length - 1 = t := by omega
    have : (CI k L)[(CI k L).length - 1] = (CI k L)[t] := by congr 1
    rw [this]; exact e

/-- **The F rule**: if F's cell is an exit cell in use, F is matched to that exit. -/
theorem f_rule : ∀ i, fxOf k k F s = some i → i < mOf k k F s ∧ muOf k s p q i = mOf k k F s - 1 := by
  intro i h
  unfold fxOf at h
  rcases W.ends with ⟨hF, -⟩ | ⟨E, fc, fs, fsl', hF, hE, hEo, hcol, hoth, -, -, hfsl⟩
  · rw [hF] at h; simp at h
  rw [hF] at h
  cases fsl' with
  | none => simp at h
  | some fsl =>
    simp only at h
    split_ifs at h with hm
    simp only [Option.some.injEq] at h
    subst h
    have hmem : fsl ∈ usedOf k k s := by simpa using hm
    obtain ⟨hsl, hex⟩ := (hfsl fsl).mp rfl
    have mF : mOf k k F s = (usedOf k k s).length + 1 := by unfold mOf; rw [hF]; rfl
    refine ⟨by have := List.idxOf_lt_length_iff.mpr hmem; omega, ?_⟩
    obtain ⟨L, col, j, hp, hc, hs⟩ := (used_iff W.k8 W.sol hinv _).mp hmem
    obtain ⟨n, cL, -⟩ := pathC_facts W.sol hp
    have hj := hc.1
    -- the outside cell of this crossing is E
    have hout : (crossEdge k L j).2 = E := by rw [← hex, ← hs]; exact (exitCell_slot (cross_exit cL hc)).symm
    have Ein : E ∈ L := by rw [← hout]; unfold crossEdge; split_ifs <;> exact nth_mem (by omega)
    obtain ⟨hL, s', t', -, h0, h1, hst, hcc⟩ := pathC_ends W hp
    -- E is an end of this path
    have Eend : E = nth L 0 ∨ E = nth L (L.length - 1) := by
      have other : ∀ x, (x = J.s0 ∨ x = J.t0 ∨ x = J.s1 ∨ x = J.t1) → x ∈ L → x = s' ∨ x = t' := by
        intro x hx hxL
        obtain ⟨m0, m1, m2, m3, n2, n3⟩ := ends_mem W.sol
        rcases hcc with ⟨hc0, rfl, rfl⟩ | ⟨hc0, rfl, rfl⟩ <;> rcases hp with ⟨rfl, hc1⟩ | ⟨rfl, hc1⟩
        · rcases hx with e | e | e | e
          · exact Or.inl e
          · exact Or.inr e
          · exact absurd (e ▸ hxL) n2
          · exact absurd (e ▸ hxL) n3
        · rcases hx with e | e | e | e
          · exact absurd hxL (fun h => W.sol.2.2.1 _ (e ▸ m0) h)
          · exact absurd hxL (fun h => W.sol.2.2.1 _ (e ▸ m1) h)
          · omega
          · omega
        · omega
        · rcases hx with e | e | e | e
          · exact absurd hxL (fun h => W.sol.2.2.1 _ (e ▸ m0) h)
          · exact absurd hxL (fun h => W.sol.2.2.1 _ (e ▸ m1) h)
          · exact Or.inl e
          · exact Or.inr e
      rcases other E hE Ein with e | e
      · exact Or.inl (e.trans h0.symm)
      · exact Or.inr (e.trans h1.symm)
    have Eout : inWb k E = false := by
      cases h' : inWb k E
      · rfl
      · exact absurd (inWb_iff.mp h') hEo
    have N := chain_nodup W hinv hp
    have hev := chain_even (s := s) W hp
    rcases Eend with e | e
    · -- F is the start: the first crossing is at 0
      have hj0 : j = 0 := by
        unfold crossEdge at hout
        split_ifs at hout with g
        · dsimp only at hout; have := nth_inj n (by omega) hL (hout.trans e); omega
        · dsimp only at hout; exact nth_inj n (by omega) hL (hout.trans e)
      subst hj0
      have off : offL k L = 1 := by unfold offL; rw [← e, Eout]; simp
      have c0 := CI_first_zero (mem_CI.mpr hc)
      have hr : 0 < (CI k L).length := List.length_pos_of_mem (mem_CI.mpr hc)
      have p1 := chainOf_mid (k := k) (s := s) hr
      rw [off, c0, hs] at p1
      have p0 := chainOf_first (s := s) off
      have hlen := chainOf_length (k := k) (s := s) (L := L)
      rw [mu_on W hinv hp (by rw [← p1]; rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)]
      have := (partner_pos N (t := 0) (by omega)).2
      simp only [Nat.mul_zero, zero_add] at this
      rw [← p1, this, p0, mF]; rfl
    · -- F is the end: the last crossing is at `len - 2`
      have hj0 : j = L.length - 2 := by
        unfold crossEdge at hout
        split_ifs at hout with g
        · dsimp only at hout; have := nth_inj n (by omega) (by omega) (hout.trans e); omega
        · dsimp only at hout; have := nth_inj n (by omega) (by omega) (hout.trans e); omega
      subst hj0
      have off : offR k L = 1 := by unfold offR; rw [← e, Eout]; simp
      have cl := CI_last_max (mem_CI.mpr hc) (by omega)
      have hr : 0 < (CI k L).length := List.length_pos_of_mem (mem_CI.mpr hc)
      have hlen := chainOf_length (k := k) (s := s) (L := L)
      have p1 := chainOf_mid (k := k) (s := s) (L := L) (i := (CI k L).length - 1) (by omega)
      rw [cl, hs] at p1
      have pl := chainOf_last (s := s) off
      obtain ⟨t, ht⟩ : ∃ t, offL k L + ((CI k L).length - 1) = 2 * t := ⟨(offL k L + ((CI k L).length - 1)) / 2, by omega⟩
      rw [ht] at p1
      rw [mu_on W hinv hp (by rw [← p1]; rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)]
      have := (partner_pos N (t := t) (by omega)).1
      rw [← p1, this, show 2 * t + 1 = (chainOf k s L).length - 1 by omega, pl, mF]; rfl

end Data

end ZZN.Win

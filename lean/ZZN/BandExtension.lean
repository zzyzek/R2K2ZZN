-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Absorb

/-!
# The band-extension lemma

If an instance is solvable and the line `x = r` holds no endpoint, then inserting two empty lines
after it gives a solvable instance (`band_extension`). There is no length condition.

Proof (`PROOF.md` §4.2; the paper, Lemma 2):
1. stretch both paths across the new lines (`stretch`): every column `y` where a path crossed
   between `x = r` and `x = r+1` gets covered, with a middle edge;
2. the other columns are covered by sweeps outward from a *seed*: two adjacent crossing columns,
   a crossing column at a wall, or a used edge `(r, y) – (r, y+1)` between two non-crossing
   columns, which is flipped first;
3. a counting argument shows that a seed exists (`seed_or_flip`).
-/

namespace ZZN

open GridHam Classical

/-- The instance with two lines inserted after line `x = r`. -/
def Inst.insertAt (I : Inst) (r : ℕ) : Inst where
  w  := I.w + 2
  h  := I.h
  s0 := shiftAt r I.s0
  t0 := shiftAt r I.t0
  s1 := shiftAt r I.s1
  t1 := shiftAt r I.t1

/-- The line `x = r` holds no endpoint. -/
def LineFree (I : Inst) (r : ℕ) : Prop :=
  ∀ y, (r, y) ≠ I.s0 ∧ (r, y) ≠ I.t0 ∧ (r, y) ≠ I.s1 ∧ (r, y) ≠ I.t1

section
variable {I : Inst} {p q : List Coord} {r : ℕ}

/-- Column `y` is crossed between lines `r` and `r+1` by one of the paths. -/
def Cross (p q : List Coord) (r y : ℕ) : Prop :=
  Used p (r, y) (r + 1, y) ∨ Used q (r, y) (r + 1, y)

theorem gap_cross (r y : ℕ) : gap r (r, y) (r + 1, y) = [(r + 1, y), (r + 2, y)] := by
  simp [gap]

theorem gap_cross' (r y : ℕ) : gap r (r + 1, y) (r, y) = [(r + 2, y), (r + 1, y)] := by
  simp [gap]

theorem shiftAt_r (r y : ℕ) : shiftAt r (r, y) = (r, y) := by simp [shiftAt]

theorem shiftAt_r1 (r y : ℕ) : shiftAt r (r + 1, y) = (r + 3, y) := by
  simp [shiftAt]

/-- A crossing of the old path gives a middle edge of the stretched path. -/
theorem used_stretch_cross {l : List Coord} {y : ℕ} (h : Used l (r, y) (r + 1, y)) :
    Used (stretch r l) (r + 1, y) (r + 2, y) := by
  rcases h with h | h
  · have := infix_stretch (r := r) h
    rw [gap_cross] at this
    exact Or.inl (List.IsInfix.trans ⟨[shiftAt r (r, y)], [shiftAt r (r + 1, y)], by simp⟩ this)
  · have := infix_stretch (r := r) h
    rw [gap_cross'] at this
    exact Or.inr (List.IsInfix.trans ⟨[shiftAt r (r + 1, y)], [shiftAt r (r, y)], by simp⟩ this)

/-- An edge inside line `r` survives stretching. -/
theorem used_stretch_row {l : List Coord} {y y' : ℕ} (h : Used l (r, y) (r, y')) :
    Used (stretch r l) (r, y) (r, y') := by
  have g1 : gap r (r, y) (r, y') = [] := by simp [gap]
  have g2 : gap r (r, y') (r, y) = [] := by simp [gap]
  rcases h with h | h
  · have := infix_stretch (r := r) h
    rw [g1, shiftAt_r, shiftAt_r] at this
    exact Or.inl this
  · have := infix_stretch (r := r) h
    rw [g2, shiftAt_r, shiftAt_r] at this
    exact Or.inr this

/-- Stretched paths are paths of the widened grid. -/
theorem IsPath.stretch {w h : ℕ} {s t : Coord} {l : List Coord} (hr : r < w)
    (hl : IsPath w h s t l) : IsPath (w + 2) h (shiftAt r s) (shiftAt r t) (stretch r l) := by
  obtain ⟨hh, hlast, hn, hb, hc⟩ := hl
  refine ⟨?_, ?_, stretch_nodup r l hn, stretch_inBounds hr hb, stretch_chain r l hc⟩
  · cases l with
    | nil => simp at hh
    | cons a l =>
      simp at hh
      rw [stretch_head?, hh]
  · rw [stretch_getLast?, hlast]; rfl

/-- The initial state: the stretched solution covers everything except the new cells of the
non-crossing columns, and crossing columns have middle edges. -/
theorem init_state (hsol : IsSolution I p q) (hr : r < I.w) :
    PState (I.w + 2) I.h r (shiftAt r I.s0) (shiftAt r I.t0) (shiftAt r I.s1) (shiftAt r I.t1)
      ((Finset.range I.h).filter (fun y => ¬ Cross p q r y)) (stretch r p) (stretch r q) := by
  obtain ⟨hp, hq, hdisj, hcov⟩ := hsol
  have gapcell : ∀ {l : List Coord} {a b v : Coord}, [a, b] <:+: l → v ∈ gap r a b →
      Used l (r, v.2) (r + 1, v.2) ∧ (v.1 = r + 1 ∨ v.1 = r + 2) := by
    intro l a b v hab hv
    obtain ⟨hx, hy, hab'⟩ := mem_gap hv
    refine ⟨?_, hx⟩
    rcases hab' with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · left; rw [hy, ← ha, ← hb]; exact hab
    · right; rw [hy, ← ha, ← hb]; exact hab
  refine ⟨hp.stretch hr, hq.stretch hr, ?_, ?_, ?_, ?_, by omega⟩
  · -- disjoint
    intro v hvp hvq
    rcases mem_stretch.mp hvp with ⟨u, hu, rfl⟩ | ⟨a, b, hab, hg⟩ <;>
      rcases mem_stretch.mp hvq with ⟨u', hu', he⟩ | ⟨a', b', hab', hg'⟩
    · exact hdisj u hu (shiftAt_injective r he ▸ hu')
    · rcases (gapcell hab' hg').2 with h | h
      · exact (shiftAt_fst_ne r u).1 h
      · exact (shiftAt_fst_ne r u).2 h
    · rcases (gapcell hab hg).2 with h | h
      · exact (shiftAt_fst_ne r u').1 (he ▸ h)
      · exact (shiftAt_fst_ne r u').2 (he ▸ h)
    · exact hdisj _ ((gapcell hab hg).1.mem_left) ((gapcell hab' hg').1.mem_left)
  · -- covered
    intro v hv hnu
    obtain ⟨v1, v2⟩ := v
    unfold InBounds at hv
    simp only at hv
    by_cases hmid : v1 = r + 1 ∨ v1 = r + 2
    · have hc : Cross p q r v2 := by
        by_contra hc
        exact hnu ⟨hmid, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hv.2, hc⟩⟩
      rcases hc with hc | hc
      · left
        have := used_stretch_cross (r := r) hc
        rcases hmid with rfl | rfl
        · exact this.mem_left
        · exact this.mem_right
      · right
        have := used_stretch_cross (r := r) hc
        rcases hmid with rfl | rfl
        · exact this.mem_left
        · exact this.mem_right
    · let u : Coord := if v1 ≤ r then (v1, v2) else (v1 - 2, v2)
      have hu : shiftAt r u = (v1, v2) := by
        simp only [u, shiftAt]
        split_ifs <;> simp_all <;> omega
      have hub : InBounds I.w I.h u := by
        simp only [u, InBounds]
        split_ifs <;> simp <;> omega
      rcases hcov u hub with h | h
      · exact Or.inl (mem_stretch.mpr (Or.inl ⟨u, h, hu.symm⟩))
      · exact Or.inr (mem_stretch.mpr (Or.inl ⟨u, h, hu.symm⟩))
  · -- uncovered
    intro v ⟨hx, hyU⟩
    have hnc : ¬ Cross p q r v.2 := (Finset.mem_filter.mp hyU).2
    have key : ∀ {l : List Coord}, (Used l (r, v.2) (r + 1, v.2) → Cross p q r v.2) →
        v ∉ stretch r l := by
      intro l hl hv
      rcases mem_stretch.mp hv with ⟨u, -, rfl⟩ | ⟨a, b, hab, hg⟩
      · rcases hx with h | h
        · exact (shiftAt_fst_ne r u).1 h
        · exact (shiftAt_fst_ne r u).2 h
      · exact hnc (hl (gapcell hab hg).1)
    exact ⟨key Or.inl, key Or.inr⟩
  · intro y hy
    exact Finset.mem_range.mp (Finset.mem_filter.mp hy).1

/-- A cell of an endpoint-free line that is not crossed has a path edge along the line. -/
theorem exists_row_edge {w h : ℕ} {s t : Coord} {L : List Coord} {y : ℕ}
    (hL : IsPath w h s t L) (hv : (r, y) ∈ L) (hs : s ≠ (r, y)) (ht : t ≠ (r, y))
    (hnc : ¬ Used L (r, y) (r + 1, y)) :
    ∃ y', (y' + 1 = y ∨ y + 1 = y') ∧ y' < h ∧ Used L (r, y) (r, y') := by
  obtain ⟨hh, hl, hn, hb, hc⟩ := hL
  obtain ⟨u1, u2, hne, h1, h2⟩ := interior_two hn hv (by rw [hh]; simpa using hs)
    (by rw [hl]; simpa using ht)
  have a1 := h1.adjacent hc
  have a2 := h2.adjacent hc
  have b1 := hb u1 h1.mem_right
  have b2 := hb u2 h2.mem_right
  obtain ⟨x1, z1⟩ := u1
  obtain ⟨x2, z2⟩ := u2
  unfold Adjacent at a1 a2
  unfold InBounds at b1 b2
  simp only at a1 a2 b1 b2
  by_cases c1 : r = x1 ∧ (y + 1 = z1 ∨ z1 + 1 = y)
  · obtain ⟨rfl, hz⟩ := c1
    exact ⟨z1, by omega, b1.2, h1⟩
  by_cases c2 : r = x2 ∧ (y + 1 = z2 ∨ z2 + 1 = y)
  · obtain ⟨rfl, hz⟩ := c2
    exact ⟨z2, by omega, b2.2, h2⟩
  exfalso
  have v1 : y = z1 ∧ (r + 1 = x1 ∨ x1 + 1 = r) := a1.resolve_left c1
  have v2 : y = z2 ∧ (r + 1 = x2 ∨ x2 + 1 = r) := a2.resolve_left c2
  obtain ⟨rfl, d1⟩ := v1
  obtain ⟨hz2, d2⟩ := v2
  subst hz2
  rcases d1 with rfl | d1
  · exact hnc h1
  rcases d2 with rfl | d2
  · exact hnc h2
  exact hne (by rw [Prod.mk.injEq]; omega)

/-- Three distinct cells cannot all be joined by path edges to the same cell. -/
theorem not_three_used (hsol : IsSolution I p q) {v a b c : Coord}
    (ha : Used p v a ∨ Used q v a) (hb : Used p v b ∨ Used q v b) (hc : Used p v c ∨ Used q v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  obtain ⟨hp, hq, hdisj, -⟩ := hsol
  rcases ha with ha | ha
  · have hvp : v ∈ p := ha.mem_left
    have toP : ∀ {x}, (Used p v x ∨ Used q v x) → Used p v x := fun {x} h =>
      h.resolve_right (fun h' => hdisj v hvp h'.mem_left)
    rcases used_le_two hp.2.2.1 ha (toP hb) (toP hc) with h | h | h
    · exact hab h
    · exact hac h
    · exact hbc h
  · have hvq : v ∈ q := ha.mem_left
    have toQ : ∀ {x}, (Used p v x ∨ Used q v x) → Used q v x := fun {x} h =>
      h.resolve_left (fun h' => hdisj v h'.mem_left hvq)
    rcases used_le_two hq.2.2.1 ha (toQ hb) (toQ hc) with h | h | h
    · exact hab h
    · exact hac h
    · exact hbc h

/-- **Counting.** A seed exists: either a position `R` with crossing columns (or walls) on both
sides, or two adjacent non-crossing columns joined along line `r`. -/
theorem seed_or_flip (hsol : IsSolution I p q) (hr : r < I.w) (hfree : LineFree I r)
    (hh : 0 < I.h) :
    ∃ R, R ≤ I.h ∧
      (((R = 0 ∨ Cross p q r (R - 1)) ∧ (R = I.h ∨ Cross p q r R)) ∨
       (1 ≤ R ∧ R < I.h ∧ ¬ Cross p q r (R - 1) ∧ ¬ Cross p q r R ∧
         (Used p (r, R - 1) (r, R) ∨ Used q (r, R - 1) (r, R)))) := by
  by_contra H
  have h0 : ¬ Cross p q r 0 := fun hc => H ⟨0, by omega, Or.inl ⟨Or.inl rfl, Or.inr hc⟩⟩
  have hlast : ¬ Cross p q r (I.h - 1) := fun hc => H ⟨I.h, le_refl _, Or.inl ⟨Or.inr hc, Or.inl rfl⟩⟩
  have hadj : ∀ c, 1 ≤ c → c < I.h → Cross p q r c → ¬ Cross p q r (c - 1) :=
    fun c h1 h2 hc hc' => H ⟨c, by omega, Or.inl ⟨Or.inr hc', Or.inr hc⟩⟩
  have hnoflip : ∀ y, y + 1 < I.h → ¬ Cross p q r y → ¬ Cross p q r (y + 1) →
      ¬ (Used p (r, y) (r, y + 1) ∨ Used q (r, y) (r, y + 1)) := by
    intro y hy h1 h2 hu
    exact H ⟨y + 1, by omega, Or.inr ⟨by omega, hy, by simpa using h1, h2, by simpa using hu⟩⟩
  -- every non-crossing column has a row edge to a crossing column
  have key : ∀ y, y < I.h → ¬ Cross p q r y → ∃ y', (y' + 1 = y ∨ y + 1 = y') ∧ y' < I.h ∧
      Cross p q r y' ∧ (Used p (r, y) (r, y') ∨ Used q (r, y) (r, y')) := by
    intro y hy hnc
    obtain ⟨hp, hq, hdisj, hcov⟩ := hsol
    obtain ⟨hf0, hf1, hf2, hf3⟩ := hfree y
    have edge : ∃ y', (y' + 1 = y ∨ y + 1 = y') ∧ y' < I.h ∧
        (Used p (r, y) (r, y') ∨ Used q (r, y) (r, y')) := by
      rcases hcov (r, y) ⟨hr, hy⟩ with hv | hv
      · obtain ⟨y', a, b, u⟩ := exists_row_edge hp hv (Ne.symm hf0) (Ne.symm hf1)
          (fun h => hnc (Or.inl h))
        exact ⟨y', a, b, Or.inl u⟩
      · obtain ⟨y', a, b, u⟩ := exists_row_edge hq hv (Ne.symm hf2) (Ne.symm hf3)
          (fun h => hnc (Or.inr h))
        exact ⟨y', a, b, Or.inr u⟩
    obtain ⟨y', hadj', hy', hu⟩ := edge
    refine ⟨y', hadj', hy', ?_, hu⟩
    by_contra hc'
    rcases hadj' with e | e
    · subst e
      exact hnoflip y' hy hc' hnc (by
        rcases hu with u | u
        · exact Or.inl u.symm
        · exact Or.inr u.symm)
    · subst e
      exact hnoflip y hy' hnc hc' hu
  set S := (Finset.range I.h).filter (fun y => ¬ Cross p q r y) with hS
  set C := (Finset.range I.h).filter (fun y => Cross p q r y) with hC
  -- |S| ≤ |C|
  have hSC : S.card ≤ C.card := by
    let g : ℕ → ℕ := fun y =>
      if hy : y < I.h ∧ ¬ Cross p q r y then Classical.choose (key y hy.1 hy.2) else 0
    have gspec : ∀ y ∈ S, (g y + 1 = y ∨ y + 1 = g y) ∧ g y < I.h ∧ Cross p q r (g y) ∧
        (Used p (r, y) (r, g y) ∨ Used q (r, y) (r, g y)) := by
      intro y hy
      obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
      have hyy : y < I.h ∧ ¬ Cross p q r y := ⟨Finset.mem_range.mp hy1, hy2⟩
      simp only [g, dite_eq_left hyy]
      exact Classical.choose_spec (key y hyy.1 hyy.2)
    refine Finset.card_le_card_of_injOn g ?_ ?_
    · intro y hy
      obtain ⟨-, h1, h2, -⟩ := gspec y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h1, h2⟩
    · intro y1 hy1 y2 hy2 he
      by_contra hne
      obtain ⟨-, -, hc1, hu1⟩ := gspec y1 hy1
      obtain ⟨-, -, -, hu2⟩ := gspec y2 hy2
      rw [he] at hc1 hu1
      have sym : ∀ {y}, (Used p (r, y) (r, g y2) ∨ Used q (r, y) (r, g y2)) →
          (Used p (r, g y2) (r, y) ∨ Used q (r, g y2) (r, y)) := fun {y} h => by
        rcases h with h | h
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      exact not_three_used hsol (sym hu1) (sym hu2) hc1
        (by simpa using hne) (by simp) (by simp)
  -- |C| + 1 ≤ |S|
  have hCS : C.card ≤ (S.erase (I.h - 1)).card := by
    refine Finset.card_le_card_of_injOn (fun c => c - 1) ?_ ?_
    · intro c hc
      obtain ⟨hc1, hc2⟩ := Finset.mem_filter.mp hc
      have hcl := Finset.mem_range.mp hc1
      have hc0 : c ≠ 0 := fun e => h0 (e ▸ hc2)
      show c - 1 ∈ S.erase (I.h - 1)
      refine Finset.mem_erase.mpr ⟨by omega, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hadj c (by omega) hcl hc2⟩⟩
    · intro c1 hc1 c2 hc2 he
      have a1 : c1 ≠ 0 := fun e => h0 (e ▸ (Finset.mem_filter.mp hc1).2)
      have a2 : c2 ≠ 0 := fun e => h0 (e ▸ (Finset.mem_filter.mp hc2).2)
      simp only at he
      omega
  have hmem : I.h - 1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hlast⟩
  rw [Finset.card_erase_of_mem hmem] at hCS
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨_, hmem⟩
  omega

end

/-- **Band extension.** If `I` is solvable and the line `x = r` holds no endpoint, then the
instance with two empty lines inserted after it is solvable. -/
theorem band_extension (I : Inst) (r : ℕ) (hr : r < I.w) (hfree : LineFree I r)
    (hS : Solvable I) : Solvable (I.insertAt r) := by
  obtain ⟨p, q, hsol⟩ := hS
  have hh : 0 < I.h := by
    have hs0 : I.s0 ∈ p := List.mem_of_mem_head? hsol.1.1
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) (hsol.1.2.2.2.1 _ hs0).2
  set U0 := (Finset.range I.h).filter (fun y => ¬ Cross p q r y) with hU0
  have st0 := init_state hsol hr
  have midC : ∀ y, Cross p q r y → Mid r (stretch r p) (stretch r q) y := by
    intro y hc
    rcases hc with hc | hc
    · exact Or.inl (used_stretch_cross hc)
    · exact Or.inr (used_stretch_cross hc)
  have notU : ∀ z, z < I.h → z ∉ U0 → Cross p q r z := by
    intro z hz hzU
    by_contra hc
    exact hzU (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hz, hc⟩)
  have inU : ∀ z, z ∈ U0 → z < I.h ∧ ¬ Cross p q r z := by
    intro z hz
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hz
    exact ⟨Finset.mem_range.mp h1, h2⟩
  have finish : ∀ P Q, PState (I.w + 2) I.h r (shiftAt r I.s0) (shiftAt r I.t0)
      (shiftAt r I.s1) (shiftAt r I.t1) ∅ P Q → Solvable (I.insertAt r) := by
    intro P Q st
    exact ⟨P, Q, st.pp, st.pq, st.disj, fun v hv => st.cov v hv (fun ⟨_, h⟩ => by simp at h)⟩
  obtain ⟨R, hRh, hcase⟩ := seed_or_flip hsol hr hfree hh
  rcases hcase with ⟨hl, hrt⟩ | ⟨h1, hRlt, hnc1, hnc, hu⟩
  · -- a seed: crossing columns (or walls) on both sides of position `R`
    by_cases hR0 : R = 0
    · subst hR0
      have hc0 : Cross p q r 0 := hrt.resolve_left (by omega)
      obtain ⟨P', Q', st', -⟩ := PState.sweepRight (I.h - 0) 0 U0 _ _ rfl st0
        (fun h => (inU 0 h).2 hc0) (midC 0 hc0)
        (fun z _ hzh hzU => midC z (notU z hzh hzU))
      exact finish P' Q' (st'.congrU (by ext z; simp))
    · have hcL : Cross p q r (R - 1) := hl.resolve_left hR0
      obtain ⟨P1, Q1, st1, keep1⟩ := PState.sweepLeft (R - 1) U0 _ _ st0
        (fun h => (inU _ h).2 hcL) (midC _ hcL)
        (fun z hz hzU => midC z (notU z (by omega) hzU))
      by_cases hRh' : R = I.h
      · refine finish P1 Q1 (st1.congrU ?_)
        ext z
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hz
        have := (inU z hz).1
        omega
      · have hcR : Cross p q r R := hrt.resolve_left hRh'
        obtain ⟨P2, Q2, st2, -⟩ := PState.sweepRight (I.h - R) R (U0.filter (R - 1 < ·)) P1 Q1
          rfl st1 (fun h => (inU R (Finset.mem_filter.mp h).1).2 hcR)
          (keep1 R (by omega) (midC R hcR))
          (fun z hz hzh hzU => keep1 z (by omega)
            (midC z (notU z hzh (fun h => hzU (Finset.mem_filter.mpr ⟨h, by omega⟩)))))
        refine finish P2 Q2 (st2.congrU ?_)
        ext z
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        rintro ⟨_, h1⟩ h2
        omega
  · -- a flip at columns `R - 1, R`
    obtain ⟨y, rfl⟩ : ∃ y, R = y + 1 := ⟨R - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hnc1 hu
    have hy : y ∈ U0 := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hnc1⟩
    have hy1 : y + 1 ∈ U0 := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hRlt, hnc⟩
    have hu' : Used (stretch r p) (r, y) (r, y + 1) ∨ Used (stretch r q) (r, y) (r, y + 1) := by
      rcases hu with hu | hu
      · exact Or.inl (used_stretch_row hu)
      · exact Or.inr (used_stretch_row hu)
    obtain ⟨P1, Q1, st1, m1, m2, keep1⟩ := st0.flip hy hy1 hu'
    have outU1 : ∀ z, z ≠ y → z ≠ y + 1 → z ∉ (U0.erase y).erase (y + 1) → z ∉ U0 := by
      intro z h1 h2 hz hz0
      exact hz (Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, hz0⟩⟩)
    obtain ⟨P2, Q2, st2, keep2⟩ := PState.sweepLeft y _ P1 Q1 st1
      (fun h => Finset.notMem_erase y U0 (Finset.mem_of_mem_erase h)) m1
      (fun z hz hzU => keep1 z (midC z (notU z (by omega)
        (outU1 z (by omega) (by omega) hzU))))
    obtain ⟨P3, Q3, st3, -⟩ := PState.sweepRight (I.h - (y + 1)) (y + 1) _ P2 Q2 rfl st2
      (fun h => Finset.notMem_erase (y + 1) _ (Finset.mem_filter.mp h).1)
      (keep2 (y + 1) (by omega) m2)
      (fun z hz hzh hzU => keep2 z (by omega) (keep1 z (midC z (notU z hzh
        (outU1 z (by omega) (by omega) (fun h => hzU (Finset.mem_filter.mpr ⟨h, by omega⟩)))))))
    refine finish P3 Q3 (st3.congrU ?_)
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.notMem_empty, iff_false, not_and]
    rintro ⟨_, h1⟩ h2
    omega

end ZZN

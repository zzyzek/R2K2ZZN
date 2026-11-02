/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.B5R
public import ZZN.PassX5
public import ZZN.PassSym

@[expose] public section

/-!
# A `B5Hit` is a `b5q` match

`b5Hit_pts`: a B match on an entry with a cell at coordinate 5 happens only on an even-area grid,
on a `b5q` entry, and the endpoints are those of `b5pts` up to order (and the colour swap).
-/

namespace ZZN.Win

open GridHam

theorem perm_a {α : Type} {x0 x1 x2 x3 : α} : [x0, x1, x2, x3].Perm [x1, x0, x2, x3] :=
  List.Perm.swap _ _ _

theorem perm_b {α : Type} {x0 x1 x2 x3 : α} : [x0, x1, x2, x3].Perm [x0, x1, x3, x2] :=
  ((List.Perm.swap _ _ _).cons _).cons _

theorem perm_c {α : Type} {x0 x1 x2 x3 : α} : [x0, x1, x2, x3].Perm [x2, x3, x0, x1] := by
  have : [x0, x1, x2, x3] = [x0, x1] ++ [x2, x3] := rfl
  rw [this]; exact List.perm_append_comm

theorem to_lt_H {R C : ℕ} (f : Frame) {u : Coord} (hu : InBounds R C u) : (f.to R C u).1 < f.H R C := by
  obtain ⟨u1, u2⟩ := u; obtain ⟨fr, fc, tr⟩ := f
  unfold InBounds at hu; simp only at hu
  cases fr <;> cases fc <;> cases tr <;> simp [Frame.to, Frame.H] <;> omega

theorem to_lt_W {R C : ℕ} (f : Frame) {u : Coord} (hu : InBounds R C u) : (f.to R C u).2 < f.W R C := by
  obtain ⟨u1, u2⟩ := u; obtain ⟨fr, fc, tr⟩ := f
  unfold InBounds at hu; simp only at hu
  cases fr <;> cases fc <;> cases tr <;> simp [Frame.to, Frame.W] <;> omega

theorem b5_odd_small : ∀ e ∈ BOUNDARY3_ODD, small5B e = true := by decide

theorem b5_even_big : ∀ e ∈ BOUNDARY3_EVEN, small5B e = false → e ∈ b5q := by decide

theorem b5q_ne : ∀ e ∈ b5q, e.1 ≠ e.2.1 := by decide

/-- The colour-`A` endpoints sit on `a, a'`; the other colour has one on `b` and the fourth
`x` on the perimeter outside the window. -/
theorem b5_pick {u0 u1 u2 u3 a a' b : Coord} {H W : ℕ} (n23 : u2 ≠ u3) (haa : a ≠ a')
    (hm : (match [(u2, 1), (u3, 1)].find? (fun q : Coord × ℕ => q.1 == b) with
      | none => false
      | some _ =>
        ([(u0, 0), (u1, 0)].any (fun q : Coord × ℕ => q.1 == a)) &&
        ([(u0, 0), (u1, 0)].any (fun q : Coord × ℕ => q.1 == a')) &&
        match [(u2, 1), (u3, 1)].find? (fun q : Coord × ℕ => q.1 != b) with
        | none => false
        | some (fourth, _) =>
          (fourth.1 == 0 || fourth.2 == 0 || fourth.1 == H - 1 || fourth.2 == W - 1) &&
            !(decide (fourth.1 < 6) && decide (fourth.2 < 6))) = true) :
    ((u0 = a ∧ u1 = a') ∨ (u0 = a' ∧ u1 = a)) ∧
      ∃ x, ((u2 = b ∧ u3 = x) ∨ (u2 = x ∧ u3 = b)) ∧
        (x.1 == 0 || x.2 == 0 || x.1 == H - 1 || x.2 == W - 1) = true ∧ ¬ (x.1 < 6 ∧ x.2 < 6) := by
  by_cases h2 : u2 = b
  · subst h2
    have h3 : (u3 == u2) = false := by simpa using fun h => n23 h.symm
    simp only [List.find?_cons, beq_self_eq_true, h3, bne, Bool.not_false,
      Bool.not_true, List.any_cons, List.any_nil, Bool.or_false,
      Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not, not_lt] at hm
    obtain ⟨⟨ha, ha'⟩, hp, hw⟩ := hm
    refine ⟨?_, u3, Or.inl ⟨rfl, rfl⟩, by simpa using hp, by omega⟩
    rcases ha with ha | ha <;> rcases ha' with ha' | ha'
    · exact absurd (ha.symm.trans ha') haa
    · exact Or.inl ⟨ha, ha'⟩
    · exact Or.inr ⟨ha', ha⟩
    · exact absurd (ha.symm.trans ha') haa
  · have h2' : (u2 == b) = false := by simpa using h2
    by_cases h3 : u3 = b
    · subst h3
      simp only [List.find?_cons, h2', beq_self_eq_true, bne, Bool.not_false,
        List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
        Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt] at hm
      obtain ⟨⟨ha, ha'⟩, hp, hw⟩ := hm
      refine ⟨?_, u2, Or.inr ⟨rfl, rfl⟩, by simpa using hp, by omega⟩
      rcases ha with ha | ha <;> rcases ha' with ha' | ha'
      · exact absurd (ha.symm.trans ha') haa
      · exact Or.inl ⟨ha, ha'⟩
      · exact Or.inr ⟨ha', ha⟩
      · exact absurd (ha.symm.trans ha') haa
    · have h3' : (u3 == b) = false := by simpa using h3
      simp [h2', h3'] at hm

/-- **A `B5Hit` is a `b5q` match**: even area, and the endpoints are `b5pts` up to order, or up to
order after the colour swap. -/
theorem b5Hit_pts {J : Inst} (hI : InDom J) {f : Frame}
    (hb : B5Hit J.w J.h f [(J.s0, 0), (J.t0, 0), (J.s1, 1), (J.t1, 1)]) :
    (J.w * J.h) % 2 = 0 ∧ ∃ e ∈ b5q, ∃ x, perimOut (f.H J.w J.h) (f.W J.w J.h) x = true ∧
      ((ptsOf J).Perm (b5pts f J.w J.h e x) ∨ ((ptsOf J).map relab).Perm (b5pts f J.w J.h e x)) := by
  obtain ⟨hw, hh, b0, b1, b2, b3, d1, d2, d3, d4, d5, d6⟩ := hI
  obtain ⟨e, he, hs, hm⟩ := hb
  have hp : (J.w * J.h) % 2 = 0 ∧ e ∈ b5q := by
    split_ifs at he with hodd
    · rw [b5_odd_small e he] at hs; exact absurd hs (by simp)
    · refine ⟨?_, b5_even_big e he hs⟩
      simp only [Bool.and_eq_true, beq_iff_eq, not_and] at hodd
      rcases Nat.mod_two_eq_zero_or_one J.w with a | a
      · rw [Nat.mul_mod, a]; simp
      · rcases Nat.mod_two_eq_zero_or_one J.h with b | b
        · rw [Nat.mul_mod, b]; simp
        · exact absurd b (hodd a)
  refine ⟨hp.1, e, hp.2, ?_⟩
  obtain ⟨a, a', b⟩ := e
  have haa : a ≠ a' := b5q_ne _ hp.2
  have n01 : f.to J.w J.h J.s0 ≠ f.to J.w J.h J.t0 := fun h => d1 (to_inj f b0 b1 h)
  have n23 : f.to J.w J.h J.s1 ≠ f.to J.w J.h J.t1 := fun h => d6 (to_inj f b2 b3 h)
  have n0 := back_to f b0
  have n1 := back_to f b1
  have n2 := back_to f b2
  have n3 := back_to f b3
  have l0 := to_lt_H f b0
  have l0' := to_lt_W f b0
  have l1 := to_lt_H f b1
  have l1' := to_lt_W f b1
  have l2 := to_lt_H f b2
  have l2' := to_lt_W f b2
  have l3 := to_lt_H f b3
  have l3' := to_lt_W f b3
  unfold bMatch at hm
  simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false,
    Bool.or_eq_true] at hm
  generalize f.to J.w J.h J.s0 = u0 at hm n01 n0 l0 l0'
  generalize f.to J.w J.h J.t0 = u1 at hm n01 n1 l1 l1'
  generalize f.to J.w J.h J.s1 = u2 at hm n23 n2 l2 l2'
  generalize f.to J.w J.h J.t1 = u3 at hm n23 n3 l3 l3'
  rcases hm with hm | hm
  · -- colour 0 on the entry's pair
    by_cases h2 : u2 = b
    · have h3 : u3 ≠ b := fun h => n23 (h2.trans h.symm)
      simp [h2, h3] at hm
      obtain ⟨⟨ha, ha'⟩, hp, hw⟩ := hm
      refine ⟨u3, ?_, ?_⟩
      · simp only [perimOut, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
          Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt]; omega
      · left
        rcases ha with ha | ha <;> rcases ha' with ha' | ha'
        · exact absurd (ha.symm.trans ha') haa
        · simp only [b5pts, ptsOf, ← ha, ← ha', ← h2, n0, n1, n2, n3]; exact List.Perm.refl _
        · simp only [b5pts, ptsOf, ← ha, ← ha', ← h2, n0, n1, n2, n3]; exact perm_a
        · exact absurd (ha.symm.trans ha') haa
    · by_cases h3 : u3 = b
      · simp [h2, h3] at hm
        obtain ⟨⟨ha, ha'⟩, hp, hw⟩ := hm
        refine ⟨u2, ?_, ?_⟩
        · simp only [perimOut, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
          Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt]; omega
        · left
          rcases ha with ha | ha <;> rcases ha' with ha' | ha'
          · exact absurd (ha.symm.trans ha') haa
          · simp only [b5pts, ptsOf, ← ha, ← ha', ← h3, n0, n1, n2, n3]; exact perm_b
          · simp only [b5pts, ptsOf, ← ha, ← ha', ← h3, n0, n1, n2, n3]; exact perm_a.trans perm_b
          · exact absurd (ha.symm.trans ha') haa
      · simp [h2, h3] at hm
  · -- colour 1 on the entry's pair
    by_cases h0 : u0 = b
    · have h1 : u1 ≠ b := fun h => n01 (h0.trans h.symm)
      simp [h0, h1] at hm
      obtain ⟨⟨ha, ha'⟩, hp, hw⟩ := hm
      refine ⟨u1, ?_, ?_⟩
      · simp only [perimOut, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
          Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt]; omega
      · right
        rcases ha with ha | ha <;> rcases ha' with ha' | ha'
        · exact absurd (ha.symm.trans ha') haa
        · simp only [b5pts, ptsOf, List.map_cons, List.map_nil, relab, sw01, ← ha, ← ha', ← h0, n0,
            n1, n2, n3]; exact perm_c
        · simp only [b5pts, ptsOf, List.map_cons, List.map_nil, relab, sw01, ← ha, ← ha', ← h0, n0,
            n1, n2, n3]; exact perm_c.trans perm_a
        · exact absurd (ha.symm.trans ha') haa
    · by_cases h1 : u1 = b
      · simp [h0, h1] at hm
        obtain ⟨⟨ha, ha'⟩, hp, hw⟩ := hm
        refine ⟨u0, ?_, ?_⟩
        · simp only [perimOut, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
          Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt]; omega
        · right
          rcases ha with ha | ha <;> rcases ha' with ha' | ha'
          · exact absurd (ha.symm.trans ha') haa
          · simp only [b5pts, ptsOf, List.map_cons, List.map_nil, relab, sw01, ← ha, ← ha', ← h1, n0,
              n1, n2, n3]; exact perm_c.trans perm_b
          · simp only [b5pts, ptsOf, List.map_cons, List.map_nil, relab, sw01, ← ha, ← ha', ← h1, n0,
              n1, n2, n3]; exact (perm_c.trans perm_a).trans perm_b
          · exact absurd (ha.symm.trans ha') haa
      · simp [h0, h1] at hm

end ZZN.Win

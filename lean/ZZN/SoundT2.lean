-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.SoundLocal

/-!
# Soundness of T2 (unit-square alternation)

Argument: `PROOF.md` §4.7. Coordinates are doubled, so that the path
`P` can be closed through the centre of the square.
-/

namespace ZZN.Planar

open GridHam

def dbl (x : ℕ × ℕ) : Pz := (2 * (x.1 : ℤ), 2 * (x.2 : ℤ))
def mid (x y : ℕ × ℕ) : Pz := ((x.1 : ℤ) + y.1, (x.2 : ℤ) + y.2)

/-- A path with the midpoints of its steps inserted, in doubled coordinates. -/
def dpath : List (ℕ × ℕ) → List Pz
  | [] => []
  | [x] => [dbl x]
  | x :: y :: L => dbl x :: mid x y :: dpath (y :: L)

theorem dpath_chain : ∀ (L : List (ℕ × ℕ)), chainAdjacent L = true → ChainZ (dpath L)
  | [], _ => trivial
  | [_], _ => trivial
  | x :: y :: L, h => by
    rw [ZZN.chainAdjacent_cons_cons, Bool.and_eq_true] at h
    have hxy := (ZZN.adjacentB_iff x y).mp h.1
    have ih := dpath_chain (y :: L) h.2
    obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y
    unfold Adjacent at hxy
    simp only at hxy
    refine ⟨?_, ?_⟩
    · unfold AdjZ dbl mid; simp only; omega
    · cases L with
      | nil => exact ⟨by unfold AdjZ dbl mid; simp only; omega, trivial⟩
      | cons z L =>
        simp only [dpath] at ih ⊢
        exact ⟨by unfold AdjZ dbl mid; simp only; omega, ih⟩

/-- Points of a doubled path: doubled cells and midpoints of adjacent cells of the path. -/
theorem mem_dpath : ∀ {L : List (ℕ × ℕ)}, chainAdjacent L = true → ∀ {z : Pz}, z ∈ dpath L →
    (∃ x ∈ L, z = dbl x) ∨ (∃ x ∈ L, ∃ y ∈ L, Adjacent x y ∧ z = mid x y)
  | [], _, _, h => by simp [dpath] at h
  | [x], _, z, h => by simp [dpath] at h; exact Or.inl ⟨x, by simp, h⟩
  | x :: y :: L, hc, z, h => by
    rw [ZZN.chainAdjacent_cons_cons, Bool.and_eq_true] at hc
    simp only [dpath, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · exact Or.inl ⟨x, by simp, rfl⟩
    · exact Or.inr ⟨x, by simp, y, by simp, (ZZN.adjacentB_iff x y).mp hc.1, rfl⟩
    · rcases mem_dpath hc.2 h with ⟨u, hu, rfl⟩ | ⟨u, hu, v, hv, huv, rfl⟩
      · exact Or.inl ⟨u, List.mem_cons_of_mem _ hu, rfl⟩
      · exact Or.inr ⟨u, List.mem_cons_of_mem _ hu, v, List.mem_cons_of_mem _ hv, huv, rfl⟩

theorem dbl_ne_mid {x u v : ℕ × ℕ} (h : Adjacent u v) : dbl x ≠ mid u v := by
  obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v
  unfold Adjacent at h; unfold dbl mid
  simp only [ne_eq, Prod.mk.injEq] at h ⊢
  omega

theorem dbl_inj {x y : ℕ × ℕ} (h : dbl x = dbl y) : x = y := by
  obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := y
  unfold dbl at h; simp only [Prod.mk.injEq] at h
  simp only [Prod.mk.injEq]; omega

/-- The midpoint of a unit step determines the step. -/
theorem mid_inj {u v u' v' : ℕ × ℕ} (h : Adjacent u v) (h' : Adjacent u' v') (he : mid u v = mid u' v') :
    u = u' ∨ u = v' := by
  obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v
  obtain ⟨a1, a2⟩ := u'; obtain ⟨b1, b2⟩ := v'
  unfold Adjacent at h h'; unfold mid at he
  simp only [Prod.mk.injEq] at h h' he ⊢
  omega

theorem mid_pair {u v A B : ℕ × ℕ} (h : Adjacent u v) (h' : Adjacent A B) (he : mid u v = mid A B) :
    (u = A ∧ v = B) ∨ (u = B ∧ v = A) := by
  obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v
  obtain ⟨a1, a2⟩ := A; obtain ⟨b1, b2⟩ := B
  unfold Adjacent at h h'; unfold mid at he
  simp only [Prod.mk.injEq] at h h' he ⊢
  omega

theorem dbl_mem_dpath : ∀ {L : List (ℕ × ℕ)} {x : ℕ × ℕ}, x ∈ L → dbl x ∈ dpath L
  | [], _, h => by simp at h
  | [y], x, h => by simp at h; subst h; simp [dpath]
  | y :: z :: L, x, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · simp [dpath]
    · simp only [dpath, List.mem_cons]
      exact Or.inr (Or.inr (dbl_mem_dpath (List.mem_cons.mpr h)))

theorem dpath_head : ∀ (x : ℕ × ℕ) (L : List (ℕ × ℕ)), ∃ T, dpath (x :: L) = dbl x :: T
  | _x, [] => ⟨[], rfl⟩
  | _x, _y :: _L => ⟨_, rfl⟩

theorem dpath_last : ∀ (x : ℕ × ℕ) (L : List (ℕ × ℕ)),
    (dpath (x :: L)).getLast? = some (dbl (L.getLastD x))
  | x, [] => rfl
  | x, y :: L => by
    simp only [dpath]
    have := dpath_last y L
    obtain ⟨T, hT⟩ := dpath_head y L
    rw [hT] at this ⊢
    rw [List.getLast?_cons_cons, List.getLast?_cons_cons, this, List.getLastD_cons]

theorem getLast?_cons_D (a : Pz) (l : List Pz) : (a :: l).getLast? = some (l.getLastD a) := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => rw [List.getLast?_cons_cons, ih, List.getLastD_cons]

/-- **T2 core**, canonical position: `P` joins `(r, c)` to `(r+1, c+1)`, `Q` the other diagonal. -/
theorem t2_core {w h : ℕ} {P Q : List (ℕ × ℕ)} {r c : ℕ}
    (hP : ZZN.IsPath w h (r, c) (r + 1, c + 1) P) (hQc : chainAdjacent Q = true)
    (hdis : ∀ v ∈ P, v ∉ Q) (hq1 : (r, c + 1) ∈ Q) (hq2 : (r + 1, c) ∈ Q) : False := by
  obtain ⟨hh, hl, hn, -, hc⟩ := hP
  obtain ⟨P0, rfl⟩ : ∃ P0, P = (r, c) :: P0 := by
    cases P with
    | nil => simp at hh
    | cons y P0 => simp at hh; exact ⟨P0, by rw [hh]⟩
  obtain ⟨T, hT⟩ := dpath_head (r, c) P0
  have hlast : T.getLastD (dbl (r, c)) = dbl (r + 1, c + 1) := by
    have := dpath_last (r, c) P0
    rw [hT, getLast?_cons_D] at this
    rw [Option.some.injEq] at this
    rw [this, getLastD_of_getLast? hl]
  set W : List Pz := dbl (r, c) :: T ++ (2 * (r : ℤ) + 2, 2 * (c : ℤ) + 1) ::
    [(2 * (r : ℤ) + 1, 2 * (c : ℤ) + 1), (2 * (r : ℤ), 2 * (c : ℤ) + 1)] with hW
  have hPd : ∀ {z : Pz}, z ∈ dbl (r, c) :: T → (∃ x ∈ (r, c) :: P0, z = dbl x) ∨
      (∃ x ∈ (r, c) :: P0, ∃ y ∈ (r, c) :: P0, Adjacent x y ∧ z = mid x y) := by
    intro z hz; rw [← hT] at hz; exact mem_dpath hc hz
  have chP := dpath_chain _ hc
  rw [hT] at chP
  -- the closed walk
  have closed : Closed W := by
    intro st hst
    rcases steps_append_mem hst with h | h | h | h
    · exact inner_adj _ chP st h
    · rw [h, hlast]; unfold AdjZ dbl; dsimp only; omega
    · simp only [inner, List.tail_cons, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
        List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> unfold AdjZ <;> dsimp only <;> omega
    · rw [h]; simp only [List.getLastD_cons, List.getLastD_nil]; unfold AdjZ dbl; dsimp only; omega
  have hP1 : (r + 1, c + 1) ∈ (r, c) :: P0 := List.mem_of_getLast? hl
  have hP0 : (r, c) ∈ (r, c) :: P0 := by simp
  -- the doubled `Q` avoids it
  have avoid : ∀ y ∈ dpath Q, y ∉ W := by
    intro y hy hyW
    rcases mem_dpath hQc hy with ⟨u, hu, rfl⟩ | ⟨u, hu, v, hv, huv, rfl⟩
    · simp only [hW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hyW
      rcases hyW with (h | h) | (h | h | h)
      · exact hdis _ hP0 (dbl_inj h ▸ hu)
      · rcases hPd (z := dbl u) (List.mem_cons_of_mem _ h) with ⟨x, hx, he⟩ | ⟨x, hx, x', hx', hxx, he⟩
        · exact hdis x hx (dbl_inj he ▸ hu)
        · exact dbl_ne_mid hxx he
      all_goals (unfold dbl at h; simp only [Prod.mk.injEq] at h; omega)
    · simp only [hW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hyW
      rcases hyW with (h | h) | (h | h | h)
      · exact dbl_ne_mid huv h.symm
      · rcases hPd (z := mid u v) (List.mem_cons_of_mem _ h) with ⟨x, hx, he⟩ | ⟨x, hx, x', hx', hxx, he⟩
        · exact dbl_ne_mid huv he.symm
        · rcases mid_inj huv hxx he with e | e
          · exact hdis x hx (e ▸ hu)
          · exact hdis x' hx' (e ▸ hu)
      · have hm : mid u v = mid (r + 1, c) (r + 1, c + 1) := by
          rw [h]; unfold mid; simp only [Prod.mk.injEq]; push_cast; constructor <;> ring
        rcases mid_pair huv (by unfold Adjacent; simp) hm with ⟨-, rfl⟩ | ⟨rfl, -⟩
        · exact hdis _ hP1 hv
        · exact hdis _ hP1 hu
      · obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v
        unfold Adjacent at huv; unfold mid at h; simp only [Prod.mk.injEq] at h huv; omega
      · have hm : mid u v = mid (r, c) (r, c + 1) := by
          rw [h]; unfold mid; simp only [Prod.mk.injEq]; push_cast; constructor <;> ring
        rcases mid_pair huv (by unfold Adjacent; simp) hm with ⟨rfl, -⟩ | ⟨-, rfl⟩
        · exact hdis _ hP0 hu
        · exact hdis _ hP0 hv
  -- the colour of the faces at the two ends of `Q`
  have m1 : dbl (r, c + 1) ∈ dpath Q := dbl_mem_dpath hq1
  have m2 : dbl (r + 1, c) ∈ dpath Q := dbl_mem_dpath hq2
  have eq := parP_chain closed (dpath Q) (dpath_chain Q hQc) avoid _ m1 _ m2
  obtain ⟨-, f1, -⟩ := faces_around closed (avoid _ m1)
  obtain ⟨f2, -, -⟩ := faces_around closed (avoid _ m2)
  have e1 : (dbl (r, c + 1)).2 - 1 = 2 * (c : ℤ) + 1 := by unfold dbl; push_cast; ring
  have e2 : (dbl (r + 1, c)).1 - 1 = 2 * (r : ℤ) + 1 := by unfold dbl; push_cast; ring
  have e3 : (dbl (r, c + 1)).1 = 2 * (r : ℤ) := by unfold dbl; rfl
  have e4 : (dbl (r + 1, c)).2 = 2 * (c : ℤ) := by unfold dbl; rfl
  rw [e1, e3] at f1
  rw [e2, e4] at f2
  rw [← f1, ← f2] at eq
  -- crossing between the two faces
  have centre_out : ∀ x ∈ (r, c) :: P0, ∀ x' ∈ (r, c) :: P0,
      (2 * (r : ℤ) + 1, 2 * (c : ℤ) + 1) ≠ dbl x ∧ (Adjacent x x' → (2 * (r : ℤ) + 1, 2 * (c : ℤ) + 1) ≠ mid x x') := by
    intro x _ x' _
    obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := x'
    refine ⟨?_, fun hxx => ?_⟩
    · unfold dbl; simp only [ne_eq, Prod.mk.injEq]; omega
    · unfold Adjacent at hxx; unfold mid; simp only [ne_eq, Prod.mk.injEq] at hxx ⊢; omega
  have d1 := par_down W (2 * (r : ℤ)) (2 * (c : ℤ) + 1)
  have hH : cnt (isH (2 * (r : ℤ) + 1) (2 * (c : ℤ) + 1)) (steps W) = 0 := by
    apply cnt_zero_of_not_mem (p := (2 * (r : ℤ) + 1, 2 * (c : ℤ) + 1 + 1))
    · intro hm
      simp only [hW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with (h | h) | (h | h | h)
      · unfold dbl at h; simp only [Prod.mk.injEq] at h; omega
      · rcases hPd (List.mem_cons_of_mem _ h) with ⟨x, hx, he⟩ | ⟨x, hx, x', hx', hxx, he⟩
        · obtain ⟨x1, x2⟩ := x; unfold dbl at he; simp only [Prod.mk.injEq] at he; omega
        · have hm : mid x x' = mid (r, c + 1) (r + 1, c + 1) := by
            rw [← he]; unfold mid; simp only [Prod.mk.injEq]; push_cast; constructor <;> ring
          rcases mid_pair hxx (by unfold Adjacent; simp) hm with ⟨rfl, -⟩ | ⟨-, rfl⟩
          · exact hdis _ hx hq1
          · exact hdis _ hx' hq1
      all_goals (simp only [Prod.mk.injEq] at h; omega)
    · intro st hst
      simp only [isH, decide_eq_true_eq] at hst
      rcases hst with rfl | rfl
      · right; ring_nf
      · left; ring_nf
  have r1 := par_right closed (2 * (r : ℤ) + 1) (2 * (c : ℤ))
  have hV : cnt (isV (2 * (r : ℤ) + 1) (2 * (c : ℤ) + 1)) (steps W) = 1 := by
    rw [hW, cnt_steps_append, hlast]
    have z : cnt (isV (2 * (r : ℤ) + 1) (2 * (c : ℤ) + 1)) (inner (dbl (r, c) :: T)) = 0 := by
      apply cnt_zero_all
      intro st hst
      obtain ⟨m1', m2'⟩ := mem_inner hst
      simp only [isV, decide_eq_false_iff_not, not_or]
      constructor <;> intro he <;> rw [he] at m1' m2' <;> simp only at m1' m2'
      · rcases hPd m1' with ⟨x, hx, hz⟩ | ⟨x, hx, x', hx', hxx, hz⟩
        · exact (centre_out x hx x hx).1 hz
        · exact (centre_out x hx x' hx').2 hxx hz
      · rcases hPd m2' with ⟨x, hx, hz⟩ | ⟨x, hx, x', hx', hxx, hz⟩
        · exact (centre_out x hx x hx).1 hz
        · exact (centre_out x hx x' hx').2 hxx hz
    rw [z]
    have j1 : isV (2 * (r : ℤ) + 1) (2 * (c : ℤ) + 1) (dbl (r + 1, c + 1), (2 * (r : ℤ) + 2, 2 * (c : ℤ) + 1)) = false := by
      unfold isV dbl; simp only [decide_eq_false_iff_not, Prod.mk.injEq, and_true]; push_cast; omega
    have j2 : isV (2 * (r : ℤ) + 1) (2 * (c : ℤ) + 1) ((2 * (r : ℤ) + 2, 2 * (c : ℤ) + 1), (2 * (r : ℤ) + 1, 2 * (c : ℤ) + 1)) = true := by
      unfold isV; simp only [decide_eq_true_eq, Prod.mk.injEq, and_true]; omega
    have j3 : isV (2 * (r : ℤ) + 1) (2 * (c : ℤ) + 1) ((2 * (r : ℤ) + 1, 2 * (c : ℤ) + 1), (2 * (r : ℤ), 2 * (c : ℤ) + 1)) = false := by
      unfold isV; simp only [decide_eq_false_iff_not, Prod.mk.injEq, and_true, true_and]; omega
    have j4 : isV (2 * (r : ℤ) + 1) (2 * (c : ℤ) + 1) ((2 * (r : ℤ), 2 * (c : ℤ) + 1), dbl (r, c)) = false := by
      unfold isV dbl; simp only [decide_eq_false_iff_not, Prod.mk.injEq, and_true]; omega
    simp only [inner, List.tail_cons, List.zip_cons_cons, List.zip_nil_right, List.getLastD_cons,
      List.getLastD_nil, cnt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, j1, j2, j3, j4]
    rfl
  rw [show (2 * (c : ℤ) + 1) = 2 * (c : ℤ) + 1 from rfl, hH] at d1
  rw [hV] at r1
  unfold par at d1 r1 eq
  omega

end ZZN.Planar

namespace ZZN

open Planar GridHam

theorem t2_facts {a b c e : ℕ × ℕ} (h : t2Fires [a, b, c, e] = true) :
    (a.1 + 1 = b.1 ∨ b.1 + 1 = a.1) ∧ (a.2 + 1 = b.2 ∨ b.2 + 1 = a.2) ∧
      (c.1 = a.1 ∨ c.1 = b.1) ∧ (c.2 = a.2 ∨ c.2 = b.2) ∧ (e.1 = a.1 ∨ e.1 = b.1) ∧
      (e.2 = a.2 ∨ e.2 = b.2) := by
  unfold t2Fires at h
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.headD_cons,
    List.getElem!_cons_zero, List.getElem!_cons_succ, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
    ne_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have m1 := Nat.le_max_left (max (max (max 0 a.1) b.1) c.1) e.1
  have m2 := Nat.le_max_right (max (max (max 0 a.1) b.1) c.1) e.1
  have m3 := Nat.le_max_right (max (max 0 a.1) b.1) c.1
  have m4 := Nat.le_max_right (max 0 a.1) b.1
  have m5 := Nat.le_max_right 0 a.1
  have m6 := Nat.le_max_left (max 0 a.1) b.1
  have m7 := Nat.le_max_left (max (max 0 a.1) b.1) c.1
  have n1 := Nat.min_le_left (min (min (min a.1 a.1) b.1) c.1) e.1
  have n2 := Nat.min_le_right (min (min (min a.1 a.1) b.1) c.1) e.1
  have n3 := Nat.min_le_right (min (min a.1 a.1) b.1) c.1
  have n4 := Nat.min_le_right (min a.1 a.1) b.1
  have n5 := Nat.min_le_left a.1 a.1
  have n6 := Nat.min_le_left (min a.1 a.1) b.1
  have n7 := Nat.min_le_left (min (min a.1 a.1) b.1) c.1
  have k1 := Nat.le_max_left (max (max (max 0 a.2) b.2) c.2) e.2
  have k2 := Nat.le_max_right (max (max (max 0 a.2) b.2) c.2) e.2
  have k3 := Nat.le_max_right (max (max 0 a.2) b.2) c.2
  have k4 := Nat.le_max_right (max 0 a.2) b.2
  have k5 := Nat.le_max_right 0 a.2
  have k6 := Nat.le_max_left (max 0 a.2) b.2
  have k7 := Nat.le_max_left (max (max 0 a.2) b.2) c.2
  have l1 := Nat.min_le_left (min (min (min a.2 a.2) b.2) c.2) e.2
  have l2 := Nat.min_le_right (min (min (min a.2 a.2) b.2) c.2) e.2
  have l3 := Nat.min_le_right (min (min a.2 a.2) b.2) c.2
  have l4 := Nat.min_le_right (min a.2 a.2) b.2
  have l5 := Nat.min_le_left a.2 a.2
  have l6 := Nat.min_le_left (min a.2 a.2) b.2
  have l7 := Nat.min_le_left (min (min a.2 a.2) b.2) c.2
  generalize max (max (max (max 0 a.1) b.1) c.1) e.1 = M at *
  generalize min (min (min (min a.1 a.1) b.1) c.1) e.1 = m at *
  generalize max (max (max (max 0 a.2) b.2) c.2) e.2 = M' at *
  generalize min (min (min (min a.2 a.2) b.2) c.2) e.2 = m' at *
  omega

/-- The arithmetic of moving the T2 square into canonical position. -/
theorem t2_coords {w h s01 s02 t01 t02 x1 x2 y1 y2 : ℕ}
    (f1 : s01 + 1 = t01 ∨ t01 + 1 = s01) (f2 : s02 + 1 = t02 ∨ t02 + 1 = s02)
    (f3 : x1 = s01 ∨ x1 = t01) (f4 : x2 = s02 ∨ x2 = t02) (f5 : y1 = s01 ∨ y1 = t01)
    (f6 : y2 = s02 ∨ y2 = t02) (bs1 : s01 < w) (bt1 : t01 < w) (bs2 : s02 < h) (bt2 : t02 < h)
    (dx1 : ¬ (s01 = x1 ∧ s02 = x2)) (dx2 : ¬ (t01 = x1 ∧ t02 = x2)) (dy1 : ¬ (s01 = y1 ∧ s02 = y2))
    (dy2 : ¬ (t01 = y1 ∧ t02 = y2)) (dxy : ¬ (x1 = y1 ∧ x2 = y2)) (A B : Bool)
    (hA : A = decide (t01 < s01)) (hB : B = decide (t02 < s02)) :
    ((if A then w - 1 - t01 else t01), (if B then h - 1 - t02 else t02)) =
        ((if A then w - 1 - s01 else s01) + 1, (if B then h - 1 - s02 else s02) + 1) ∧
      (((if A then w - 1 - s01 else s01), (if B then h - 1 - s02 else s02) + 1) =
          ((if A then w - 1 - x1 else x1), (if B then h - 1 - x2 else x2)) ∨
        ((if A then w - 1 - s01 else s01), (if B then h - 1 - s02 else s02) + 1) =
          ((if A then w - 1 - y1 else y1), (if B then h - 1 - y2 else y2))) ∧
      (((if A then w - 1 - s01 else s01) + 1, (if B then h - 1 - s02 else s02)) =
          ((if A then w - 1 - x1 else x1), (if B then h - 1 - x2 else x2)) ∨
        ((if A then w - 1 - s01 else s01) + 1, (if B then h - 1 - s02 else s02)) =
          ((if A then w - 1 - y1 else y1), (if B then h - 1 - y2 else y2))) := by
  subst hA hB
  rcases f1 with rfl | rfl <;> rcases f2 with rfl | rfl <;> rcases f3 with rfl | rfl <;>
    rcases f4 with rfl | rfl <;> rcases f5 with rfl | rfl <;> rcases f6 with rfl | rfl <;>
    simp (config := { decide := true }) only [Nat.lt_succ_self, decide_true, decide_false,
      Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq, show ∀ n : ℕ, ¬ (n + 1 < n) from fun n => by omega,
      true_and, and_true, not_true_eq_false, true_or, or_true] at * <;> omega

/-- **T2 is sound.** -/
theorem t2_sound {I : Inst} (hwf : I.WellFormed) (hS : Solvable I) :
    t2Fires [I.s0, I.t0, I.s1, I.t1] = false := by
  obtain ⟨w, h, ⟨s01, s02⟩, ⟨t01, t02⟩, ⟨s11, s12⟩, ⟨t11, t12⟩⟩ := I
  by_contra hf
  rw [Bool.not_eq_false] at hf
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := t2_facts hf
  obtain ⟨b0, b1, b2, b3, d1, d2, d3, d4, d5, d6⟩ := hwf
  set f : Frame := ⟨decide (t01 < s01), decide (t02 < s02), false⟩ with hf'
  obtain ⟨p, q, hp, hq, hd, -⟩ := solvable_frameMap f hS
  set J := (Inst.mk w h (s01, s02) (t01, t02) (s11, s12) (t11, t12)).frameMap f
  have hs0 : J.s0 = f.to w h (s01, s02) := rfl
  have ht0 : J.t0 = f.to w h (t01, t02) := rfl
  have hs1 : J.s1 = f.to w h (s11, s12) := rfl
  have ht1 : J.t1 = f.to w h (t11, t12) := rfl
  unfold InBounds at b0 b1 b2 b3
  simp only [ne_eq, Prod.mk.injEq] at f1 f2 f3 f4 f5 f6 b0 b1 b2 b3 d1 d2 d3 d4 d5 d6
  have hto : ∀ x : ℕ × ℕ, f.to w h x =
      ((if t01 < s01 then w - 1 - x.1 else x.1), (if t02 < s02 then h - 1 - x.2 else x.2)) := by
    intro x; simp [hf', Frame.to]
  obtain ⟨e1, e2, e3⟩ := t2_coords (w := w) (h := h) f1 f2 f3 f4 f5 f6 b0.1 b1.1 b0.2 b1.2 d2 d4 d3 d5 d6
    (decide (t01 < s01)) (decide (t02 < s02)) rfl rfl
  have hto' : ∀ x : ℕ × ℕ, f.to w h x =
      ((if decide (t01 < s01) then w - 1 - x.1 else x.1), (if decide (t02 < s02) then h - 1 - x.2 else x.2)) := by
    intro x; simp [hf', Frame.to]
  set r := (if decide (t01 < s01) then w - 1 - s01 else s01)
  set c := (if decide (t02 < s02) then h - 1 - s02 else s02)
  have es0 : J.s0 = (r, c) := by rw [hs0, hto']
  have et0 : J.t0 = (r + 1, c + 1) := by rw [ht0, hto']; exact e1
  have eq1 : (r, c + 1) = J.s1 ∨ (r, c + 1) = J.t1 := by rw [hs1, ht1, hto', hto']; exact e2
  have eq2 : (r + 1, c) = J.s1 ∨ (r + 1, c) = J.t1 := by rw [hs1, ht1, hto', hto']; exact e3
  rw [es0, et0] at hp
  have m1 : J.s1 ∈ q := List.mem_of_mem_head? hq.1
  have m2 : J.t1 ∈ q := List.mem_of_getLast? hq.2.1
  exact t2_core hp hq.2.2.2.2 hd (by rcases eq1 with e | e <;> rw [e] <;> assumption)
    (by rcases eq2 with e | e <;> rw [e] <;> assumption)

end ZZN

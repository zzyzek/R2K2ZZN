-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import Mathlib

/-!
# A discrete separation lemma

A closed walk `Γ` in `ℤ × ℤ` two-colours the unit squares
(faces) by the parity of crossings of an upward ray. Crossing an edge changes the colour by the
number of steps of `Γ` on that edge (`par_down`, `par_right`), so all faces around a path that
avoids `Γ` have one colour (`parP_chain`).
-/

namespace ZZN.Planar

abbrev Pz := ℤ × ℤ

/-- Unit distance. -/
def AdjZ (u v : Pz) : Prop :=
  (u.1 = v.1 ∧ (u.2 + 1 = v.2 ∨ v.2 + 1 = u.2)) ∨ (u.2 = v.2 ∧ (u.1 + 1 = v.1 ∨ v.1 + 1 = u.1))

/-- The steps of a closed walk, including the closing step. -/
def steps (W : List Pz) : List (Pz × Pz) := W.zip (W.rotate 1)

def Closed (W : List Pz) : Prop := ∀ s ∈ steps W, AdjZ s.1 s.2

/-- The step is the horizontal edge `(i, j)–(i, j+1)`, in either direction. -/
def isH (i j : ℤ) (s : Pz × Pz) : Bool :=
  decide (s = ((i, j), (i, j + 1)) ∨ s = ((i, j + 1), (i, j)))

/-- The step is the vertical edge `(i, j)–(i+1, j)`, in either direction. -/
def isV (i j : ℤ) (s : Pz × Pz) : Bool :=
  decide (s = ((i, j), (i + 1, j)) ∨ s = ((i + 1, j), (i, j)))

/-- The step crosses the upward ray from the centre of face `(i, j)`. -/
def ray (i j : ℤ) (s : Pz × Pz) : Bool :=
  decide (s.1.1 = s.2.1 ∧ s.1.1 ≤ i ∧ ((s.1.2 = j ∧ s.2.2 = j + 1) ∨ (s.1.2 = j + 1 ∧ s.2.2 = j)))

def cnt (p : Pz × Pz → Bool) (L : List (Pz × Pz)) : ℕ := (L.map fun s => (p s).toNat).sum

/-- The colour of face `(i, j)`: crossings of its upward ray, mod 2. -/
def par (W : List Pz) (i j : ℤ) : ℕ := cnt (ray i j) (steps W) % 2

theorem toNat_dec (p : Prop) [Decidable p] : (decide p).toNat = if p then 1 else 0 := by
  by_cases h : p <;> simp [h]

theorem cnt_add {p q r : Pz × Pz → Bool} (h : ∀ s, (p s).toNat = (q s).toNat + (r s).toNat)
    (L : List (Pz × Pz)) : cnt p L = cnt q L + cnt r L := by
  unfold cnt
  rw [← List.sum_map_add]
  congr 1
  exact List.map_congr_left (fun s _ => h s)

/-- **Crossing a horizontal edge.** -/
theorem par_down (W : List Pz) (i j : ℤ) :
    par W (i + 1) j = (cnt (ray i j) (steps W) + cnt (isH (i + 1) j) (steps W)) % 2 := by
  unfold par
  rw [cnt_add (q := ray i j) (r := isH (i + 1) j)]
  intro s
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := s
  simp only [ray, isH, Prod.mk.injEq, toNat_dec]
  split_ifs <;> omega

/-- The per-step identity behind `par_right`. -/
theorem step_identity {i j : ℤ} {u v : Pz} (h : AdjZ u v) :
    ((ray i j (u, v)).toNat + (ray i (j + 1) (u, v)).toNat + (isV i (j + 1) (u, v)).toNat +
      (decide (u.2 = j + 1 ∧ u.1 ≤ i)).toNat + (decide (v.2 = j + 1 ∧ v.1 ≤ i)).toNat) % 2 = 0 := by
  obtain ⟨a, b⟩ := u
  obtain ⟨c, d⟩ := v
  unfold AdjZ at h
  simp only [ray, isV, Prod.mk.injEq, toNat_dec] at h ⊢
  split_ifs <;> omega

theorem sum_even {L : List ℕ} (h : ∀ x ∈ L, x % 2 = 0) : L.sum % 2 = 0 := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    simp only [List.sum_cons]
    have := h x List.mem_cons_self
    have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

theorem steps_fst (W : List Pz) : (steps W).map Prod.fst = W := by
  unfold steps; rw [List.map_fst_zip]; simp

theorem steps_snd (W : List Pz) : (steps W).map Prod.snd = W.rotate 1 := by
  unfold steps; rw [List.map_snd_zip]; simp

/-- **Crossing a vertical edge.** -/
theorem par_right {W : List Pz} (hW : Closed W) (i j : ℤ) :
    par W i (j + 1) = (cnt (ray i j) (steps W) + cnt (isV i (j + 1)) (steps W)) % 2 := by
  unfold par
  let g : Pz → ℕ := fun p => (decide (p.2 = j + 1 ∧ p.1 ≤ i)).toNat
  have hsum : (cnt (ray i j) (steps W) + cnt (ray i (j + 1)) (steps W) + cnt (isV i (j + 1)) (steps W) +
      ((steps W).map fun s => g s.1).sum + ((steps W).map fun s => g s.2).sum) % 2 = 0 := by
    unfold cnt
    rw [← List.sum_map_add, ← List.sum_map_add, ← List.sum_map_add, ← List.sum_map_add]
    apply sum_even
    intro x hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    exact step_identity (hW s hs)
  have hg : ((steps W).map fun s => g s.1).sum = ((steps W).map fun s => g s.2).sum := by
    have e1 : ((steps W).map fun s => g s.1) = ((steps W).map Prod.fst).map g := by
      rw [List.map_map]; rfl
    have e2 : ((steps W).map fun s => g s.2) = ((steps W).map Prod.snd).map g := by
      rw [List.map_map]; rfl
    rw [e1, e2, steps_fst, steps_snd]
    exact ((List.rotate_perm W 1).map g).sum_eq.symm
  omega

/-! ### Faces around a point -/

/-- No step of `Γ` touches `p`. -/
theorem cnt_zero_of_not_mem {W : List Pz} {p : Pz} (hp : p ∉ W) (q : Pz × Pz → Bool)
    (hq : ∀ s, q s = true → s.1 = p ∨ s.2 = p) : cnt q (steps W) = 0 := by
  unfold cnt
  rw [List.sum_eq_zero_iff]
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
  cases hqs : q s
  · rfl
  · exfalso
    have h1 : s.1 ∈ W := by rw [← steps_fst W]; exact List.mem_map_of_mem hs
    have h2 : s.2 ∈ W := by
      rw [← List.mem_rotate (n := 1), ← steps_snd W]; exact List.mem_map_of_mem hs
    rcases hq s hqs with e | e
    · exact hp (e ▸ h1)
    · exact hp (e ▸ h2)

/-- The colour of a point off `Γ`: that of the face below-right of it. -/
def parP (W : List Pz) (p : Pz) : ℕ := par W p.1 p.2

/-- The four faces around a point off `Γ` have one colour. -/
theorem faces_around {W : List Pz} (hW : Closed W) {p : Pz} (hp : p ∉ W) :
    par W (p.1 - 1) p.2 = parP W p ∧ par W p.1 (p.2 - 1) = parP W p ∧
      par W (p.1 - 1) (p.2 - 1) = parP W p := by
  obtain ⟨i, j⟩ := p
  unfold parP
  simp only
  have hH : cnt (isH i j) (steps W) = 0 := cnt_zero_of_not_mem hp _ (by
    intro s h; simp only [isH, decide_eq_true_eq] at h; rcases h with rfl | rfl <;> simp)
  have hV : cnt (isV i j) (steps W) = 0 := cnt_zero_of_not_mem hp _ (by
    intro s h; simp only [isV, decide_eq_true_eq] at h; rcases h with rfl | rfl <;> simp)
  have hV' : cnt (isV (i - 1) j) (steps W) = 0 := cnt_zero_of_not_mem hp _ (by
    intro s h; simp only [isV, decide_eq_true_eq, sub_add_cancel] at h; rcases h with rfl | rfl <;> simp)
  have d1 := par_down W (i - 1) j
  rw [sub_add_cancel, hH] at d1
  have r1 := par_right hW i (j - 1)
  rw [sub_add_cancel, hV] at r1
  have r2 := par_right hW (i - 1) (j - 1)
  rw [sub_add_cancel, hV'] at r2
  unfold par at d1 r1 r2 ⊢
  omega

/-- Adjacent points off `Γ` have one colour. -/
theorem parP_adj {W : List Pz} (hW : Closed W) {p q : Pz} (hp : p ∉ W) (hq : q ∉ W) (h : AdjZ p q) :
    parP W p = parP W q := by
  obtain ⟨a1, a2, a3⟩ := faces_around hW hp
  obtain ⟨b1, b2, b3⟩ := faces_around hW hq
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  unfold AdjZ at h
  simp only at h a1 a2 a3 b1 b2 b3
  unfold parP at *
  rcases h with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩
  · rw [← b2]; simp
  · rw [← a2]; simp
  · rw [← b1]; simp
  · rw [← a1]; simp

/-- Consecutive points at unit distance. -/
def ChainZ : List Pz → Prop
  | [] => True
  | [_] => True
  | a :: b :: r => AdjZ a b ∧ ChainZ (b :: r)

/-- **A path off `Γ` has one colour.** -/
theorem parP_chain {W : List Pz} (hW : Closed W) : ∀ (Q : List Pz), ChainZ Q →
    (∀ p ∈ Q, p ∉ W) → ∀ p ∈ Q, ∀ q ∈ Q, parP W p = parP W q
  | [], _, _ => by simp
  | [x], _, _ => by simp
  | x :: y :: Q, hc, hn => by
    simp only [ChainZ] at hc
    have ih := parP_chain hW (y :: Q) hc.2 (fun p hp => hn p (List.mem_cons_of_mem _ hp))
    have hxy := parP_adj hW (hn x List.mem_cons_self) (hn y (by simp)) hc.1
    have hy : ∀ p ∈ x :: y :: Q, parP W p = parP W y := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hxy
      · exact ih p hp y List.mem_cons_self
    intro p hp q hq
    rw [hy p hp, hy q hq]

end ZZN.Planar

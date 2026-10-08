-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Catalogue
import ZZN.PathFacts

/-!
# Soundness of the parity entry P

Color cell `(x, y)` with `sgn = +1` if `x + y` is even, `-1` otherwise. Along a path the colors
alternate, so twice the color sum of a path is the sum of the colors of its two ends
(`path_sign_sum`). The grid's color sum is `(w * h) % 2` (`grid_sum`). A solution covers
each cell once, which gives the parity equation (`parity_of_solvable`).
-/

namespace ZZN

open GridHam

theorem sgn_adj {u v : Coord} (h : Adjacent u v) : sgn v = - sgn u := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  unfold Adjacent at h
  unfold sgn
  simp only at h ⊢
  by_cases hu : (u1 + u2) % 2 = 0
  · have hv : (v1 + v2) % 2 ≠ 0 := by omega
    simp [hu, hv]
  · have hv : (v1 + v2) % 2 = 0 := by omega
    simp [hu, hv]

/-- Twice the color sum of a chain is the sum of the colors of its ends. -/
theorem path_sign_sum : ∀ (a : Coord) (l : List Coord), chainAdjacent (a :: l) = true →
    2 * ((a :: l).map sgn).sum = sgn a + sgn ((a :: l).getLast (by simp))
  | a, [] => fun _ => by simp; ring
  | a, b :: l => by
    intro hc
    rw [chainAdjacent_cons_cons, Bool.and_eq_true] at hc
    have ih := path_sign_sum b l hc.2
    have hab := sgn_adj ((adjacentB_iff a b).mp hc.1)
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [List.getLast_cons (by simp)]
    linarith

theorem IsPath.sign_sum {w h : ℕ} {s t : Coord} {L : List Coord} (hp : IsPath w h s t L) :
    2 * (L.map sgn).sum = sgn s + sgn t := by
  obtain ⟨hh, hl, -, -, hc⟩ := hp
  cases L with
  | nil => simp at hh
  | cons a l =>
    simp at hh
    subst hh
    rw [path_sign_sum a l hc]
    rw [List.getLast?_eq_some_getLast (by simp)] at hl
    rw [Option.some.inj hl]

/-- The color sum of a column of `h` cells. -/
theorem col_sum (x : ℕ) : ∀ h, ((List.range h).map (fun y => sgn (x, y))).sum =
    if h % 2 = 0 then 0 else sgn (x, 0)
  | 0 => by simp
  | h + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, col_sum x h]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    unfold sgn
    by_cases hx : x % 2 = 0 <;> by_cases hh : h % 2 = 0 <;>
      simp only [hh, ↓reduceIte] <;> (split_ifs <;> simp_all <;> omega)

theorem row0_sum : ∀ w, ((List.range w).map (fun x => sgn (x, 0))).sum = ((w % 2 : ℕ) : ℤ)
  | 0 => by simp
  | w + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, row0_sum w]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    unfold sgn
    by_cases hw : w % 2 = 0
    · have : (w + 1) % 2 = 1 := by omega
      simp [hw, this]
    · have h1 : w % 2 = 1 := by omega
      have : (w + 1) % 2 = 0 := by omega
      simp [h1, this]

theorem sum_flatMap' {α : Type} (f : α → List ℤ) : ∀ (l : List α),
    (l.flatMap f).sum = (l.map (fun x => (f x).sum)).sum
  | [] => by simp
  | x :: l => by
    simp only [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons]
    rw [sum_flatMap' f l]

/-- The grid's color sum. -/
theorem grid_sum (w h : ℕ) :
    ((List.range w).flatMap (fun x => (List.range h).map (fun y => sgn (x, y)))).sum =
      (((w * h) % 2 : ℕ) : ℤ) := by
  have hsplit : ((List.range w).flatMap (fun x => (List.range h).map (fun y => sgn (x, y)))).sum =
      ((List.range w).map (fun x => if h % 2 = 0 then (0 : ℤ) else sgn (x, 0))).sum := by
    rw [sum_flatMap']
    congr 1
    exact List.map_congr_left (fun x _ => col_sum x h)
  rw [hsplit]
  have hm : (w * h) % 2 = (w % 2) * (h % 2) % 2 := Nat.mul_mod _ _ _
  by_cases hh : h % 2 = 0
  · simp [hh, hm]
  · have h1 : h % 2 = 1 := by omega
    rw [hm, h1, Nat.mul_one, Nat.mod_mod]
    simp only [one_ne_zero, ↓reduceIte]
    exact row0_sum w

/-- **Parity.** In a solution, twice the grid's color sum is the color sum of the endpoints. -/
theorem parity_of_solvable {I : Inst} (hS : Solvable I) :
    sgn I.s0 + sgn I.t0 + sgn I.s1 + sgn I.t1 = 2 * (((I.w * I.h) % 2 : ℕ) : ℤ) := by
  obtain ⟨p, q, hp, hq, hd, hc⟩ := hS
  have e1 := hp.sign_sum
  have e2 := hq.sign_sum
  -- p ++ q is a permutation of the grid's cells
  let G : List Coord := (List.range I.w).flatMap (fun x => (List.range I.h).map (fun y => (x, y)))
  have hG : G.Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun x _ => List.Nodup.map (fun a b h => by simpa using h) List.nodup_range, ?_⟩
    refine List.Pairwise.imp (fun {a b} hab => ?_) (List.nodup_range (n := I.w))
    simp only [Function.onFun]
    rw [List.disjoint_left]
    intro c hc hc'
    simp only [List.mem_map] at hc hc'
    obtain ⟨y, -, rfl⟩ := hc
    obtain ⟨y', -, he⟩ := hc'
    simp only [Prod.mk.injEq] at he
    exact hab he.1.symm
  have hmemG : ∀ v, v ∈ G ↔ InBounds I.w I.h v := by
    intro v
    simp only [G, List.mem_flatMap, List.mem_range, List.mem_map, InBounds]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨hx, hy⟩
    · rintro ⟨hx, hy⟩; exact ⟨v.1, hx, v.2, hy, rfl⟩
  have hpq : (p ++ q).Nodup := List.nodup_append.mpr ⟨hp.2.2.1, hq.2.2.1,
    fun x hx y hy hxy => hd x hx (hxy ▸ hy)⟩
  have hperm : (p ++ q).Perm G := by
    refine (List.perm_ext_iff_of_nodup hpq hG).mpr ?_
    intro v
    rw [List.mem_append, hmemG]
    constructor
    · rintro (h | h)
      · exact hp.2.2.2.1 v h
      · exact hq.2.2.2.1 v h
    · exact hc v
  have hsum : ((p ++ q).map sgn).sum = (G.map sgn).sum := (hperm.map sgn).sum_eq
  have hgrid : (G.map sgn).sum = (((I.w * I.h) % 2 : ℕ) : ℤ) := by
    rw [← grid_sum]
    simp only [G, List.map_flatMap, List.map_map]
    rfl
  rw [List.map_append, List.sum_append, hgrid] at hsum
  linarith

/-- The catalogue's parity check passes on every solvable instance. -/
theorem parityOk_of_solvable {I : Inst} (hS : Solvable I) :
    parityOk I.w I.h [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)] = true := by
  have := parity_of_solvable hS
  unfold parityOk
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, beq_iff_eq]
  linarith

end ZZN

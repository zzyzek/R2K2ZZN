-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.WinOut
import ZZN.Parity

/-!
# Window certificates: parity of the outside ends
-/

namespace ZZN.Win

open GridHam

theorem sgnW_eq (x : Coord) : Win.sgn x = ZZN.sgn x := by
  unfold Win.sgn ZZN.sgn; split_ifs <;> simp_all

theorem sgnW_adj {u v : Coord} (h : Adjacent u v) : Win.sgn v = - Win.sgn u := by
  rw [sgnW_eq, sgnW_eq]; exact ZZN.sgn_adj h

/-- The outside cell of a crossing. -/
def crossOut (k : ℕ) (L : List Coord) (j : ℕ) : Coord := (crossEdge k L j).2

/-- **Along a path**: twice the colour sum of its outside cells is the colour sum of its crossings'
outside cells, plus its first and last cells if they are outside. By induction on prefixes. -/
theorem prefix_parity {k : ℕ} {L : List Coord} (hc : chainAdjacent L = true) :
    ∀ n, 1 ≤ n → n ≤ L.length →
      2 * (((List.range n).filter (fun j => !inWb k (nth L j))).map (fun j => Win.sgn (nth L j))).sum =
        (((List.range (n - 1)).filter (fun j => inWb k (nth L j) != inWb k (nth L (j + 1)))).map
            (fun j => Win.sgn (crossOut k L j))).sum +
          (if inWb k (nth L 0) then 0 else Win.sgn (nth L 0)) +
          (if inWb k (nth L (n - 1)) then 0 else Win.sgn (nth L (n - 1))) := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    intro hlen
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp only [zero_add, List.range_one, List.filter_cons, List.filter_nil, Nat.sub_self, List.range_zero,
        List.map_nil, List.sum_nil, zero_add]
      split_ifs with h1 h2 <;> simp_all; ring
    have ih' := ih hpos (by omega)
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append]
    rw [show n + 1 - 1 = (n - 1) + 1 by omega, List.range_succ, List.filter_append, List.map_append,
      List.sum_append]
    have ad := chain_nth hc (j := n - 1) (by omega)
    rw [show n - 1 + 1 = n by omega] at ad
    have sg := sgnW_adj ad
    have co : crossOut k L (n - 1) = if inWb k (nth L (n - 1)) then nth L n else nth L (n - 1) := by
      unfold crossOut crossEdge; rw [show n - 1 + 1 = n by omega]; split_ifs <;> rfl
    simp only [List.filter_cons, List.filter_nil, show n - 1 + 1 = n by omega]
    cases ha : inWb k (nth L (n - 1)) <;> cases hb : inWb k (nth L n) <;>
      simp only [ha, Bool.not_true, Bool.not_false, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, add_zero, bne_iff_ne, ne_eq,
        not_false_eq_true, Bool.true_eq_false] at ih' ⊢ <;>
      (try rw [co, ha]) <;> (try simp only [Bool.false_eq_true, ↓reduceIte]) <;>
      linarith

theorem range_map_nth (L : List Coord) : (List.range L.length).map (nth L) = L := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [List.getElem_map, List.getElem_range, nth_eq h2]

/-- **Along a whole path.** -/
theorem path_parity {k : ℕ} {L : List Coord} (hc : chainAdjacent L = true) (hL : 0 < L.length) :
    2 * ((L.filter (fun y => !inWb k y)).map Win.sgn).sum =
      ((CI k L).map (fun j => Win.sgn (crossOut k L j))).sum +
        (if inWb k (nth L 0) then 0 else Win.sgn (nth L 0)) +
        (if inWb k (nth L (L.length - 1)) then 0 else Win.sgn (nth L (L.length - 1))) := by
  have := prefix_parity (k := k) hc L.length hL (le_refl _)
  unfold CI
  rw [← this]
  congr 2
  conv_lhs => rw [← range_map_nth L]
  rw [List.filter_map, List.map_map]
  rfl

/-- The solution's cells are the grid's cells. -/
theorem sol_perm {J : Inst} {p q : List Coord} (hS : IsSolution J p q) :
    (p ++ q).Perm ((List.range J.w).flatMap (fun x => (List.range J.h).map (fun y => (x, y)))) := by
  obtain ⟨hp, hq, hd, hc⟩ := hS
  have hG : ((List.range J.w).flatMap (fun x => (List.range J.h).map (fun y => ((x, y) : Coord)))).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun x _ => List.Nodup.map (fun a b h => by simpa using h) List.nodup_range, ?_⟩
    refine List.Pairwise.imp (fun {a b} hab => ?_) (List.nodup_range (n := J.w))
    simp only [Function.onFun]
    rw [List.disjoint_left]
    intro c hc hc'
    simp only [List.mem_map] at hc hc'
    obtain ⟨y, -, rfl⟩ := hc
    obtain ⟨y', -, he⟩ := hc'
    simp only [Prod.mk.injEq] at he
    exact hab he.1.symm
  have hpq : (p ++ q).Nodup := List.nodup_append.mpr ⟨hp.2.2.1, hq.2.2.1,
    fun x hx y hy hxy => hd x hx (hxy ▸ hy)⟩
  refine (List.perm_ext_iff_of_nodup hpq hG).mpr ?_
  intro v
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro (h | h)
    · exact ⟨v.1, (hp.2.2.2.1 v h).1, v.2, (hp.2.2.2.1 v h).2, rfl⟩
    · exact ⟨v.1, (hq.2.2.2.1 v h).1, v.2, (hq.2.2.2.1 v h).2, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact hc _ ⟨hx, hy⟩

theorem sum_filter_split {l : List Coord} (P : Coord → Bool) :
    (l.map Win.sgn).sum = ((l.filter P).map Win.sgn).sum + ((l.filter (fun y => !P y)).map Win.sgn).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.filter_cons]
    cases P a <;> simp [ih] <;> ring

/-- **The outside cells' colour sum** is that of the grid: the window's is zero. -/
theorem outside_sum {k : ℕ} (hk : k % 2 = 0) {J : Inst} {p q : List Coord} (hS : IsSolution J p q)
    (hkw : k ≤ J.w) (hkh : k ≤ J.h) :
    ((p.filter (fun y => !inWb k y)).map Win.sgn).sum + ((q.filter (fun y => !inWb k y)).map Win.sgn).sum =
      (((J.w * J.h) % 2 : ℕ) : ℤ) := by
  set G := (List.range J.w).flatMap (fun x => (List.range J.h).map (fun y => ((x, y) : Coord)))
  have hperm := sol_perm hS
  have total : (G.map Win.sgn).sum = (((J.w * J.h) % 2 : ℕ) : ℤ) := by
    rw [← grid_sum J.w J.h]
    simp only [G, List.map_flatMap, List.map_map]
    congr 1
    refine List.flatMap_congr (fun x _ => ?_)
    apply List.map_congr_left
    intro y _
    simp [sgnW_eq]
  -- the window part of the grid
  set Wg := (List.range k).flatMap (fun x => (List.range k).map (fun y => ((x, y) : Coord)))
  have win : ((G.filter (inWb k)).map Win.sgn).sum = 0 := by
    have hWg : ((G.filter (inWb k))).Perm Wg := by
      have nG : G.Nodup := (hperm.nodup_iff).mp (List.nodup_append.mpr ⟨hS.1.2.2.1, hS.2.1.2.2.1,
        fun x hx y hy hxy => hS.2.2.1 x hx (hxy ▸ hy)⟩)
      have nW : Wg.Nodup := by
        rw [List.nodup_flatMap]
        refine ⟨fun x _ => List.Nodup.map (fun a b h => by simpa using h) List.nodup_range, ?_⟩
        refine List.Pairwise.imp (fun {a b} hab => ?_) (List.nodup_range (n := k))
        simp only [Function.onFun]
        rw [List.disjoint_left]
        intro c hc hc'
        simp only [List.mem_map] at hc hc'
        obtain ⟨y, -, rfl⟩ := hc
        obtain ⟨y', -, he⟩ := hc'
        simp only [Prod.mk.injEq] at he
        exact hab he.1.symm
      refine (List.perm_ext_iff_of_nodup (nG.filter _) nW).mpr ?_
      intro v
      simp only [G, Wg, List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_map, inWb_iff]
      constructor
      · rintro ⟨⟨x, hx, y, hy, rfl⟩, h1, h2⟩; exact ⟨x, h1, y, h2, rfl⟩
      · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨⟨x, by omega, y, by omega, rfl⟩, hx, hy⟩
    rw [(hWg.map Win.sgn).sum_eq]
    have := grid_sum k k
    have hkk : (k * k) % 2 = 0 := by rw [Nat.mul_mod, hk]
    rw [hkk, Nat.cast_zero] at this
    simp only [Wg, List.map_flatMap, List.map_map]
    rw [← this]
    congr 1
    refine List.flatMap_congr (fun x _ => ?_)
    apply List.map_congr_left
    intro y _
    simp [sgnW_eq]
  have split := sum_filter_split (l := G) (inWb k)
  rw [win, zero_add, total] at split
  rw [split, ← List.sum_append, ← List.map_append, ← List.filter_append]
  exact ((hperm.filter _).map Win.sgn).sum_eq

/-- F's sign, or zero. -/
def fsOf (F : FSpec) : Int := match F with | some (_, fs, _) => fs | none => 0

theorem parOf_eq {k : ℕ} {F : FSpec} {s : St} :
    parOf k k F s = ((usedOf k k s).map fun sl => Win.sgn (exitCell k k sl)).sum + fsOf F := by
  unfold parOf fsOf; rfl

section ParW

variable {k : ℕ} {J : Inst} {p q : List Coord} {F : FSpec} {s : St}
  (W : WinSetup k J p q F) (hinv : Inv k k (k * k) p q s)
include W hinv

theorem cross_sum :
    ((CI k p).map (fun j => Win.sgn (crossOut k p j))).sum + ((CI k q).map (fun j => Win.sgn (crossOut k q j))).sum =
      ((usedOf k k s).map fun sl => Win.sgn (exitCell k k sl)).sum := by
  have Pp : PathC p q p 0 := Or.inl ⟨rfl, rfl⟩
  have Pq : PathC p q q 1 := Or.inr ⟨rfl, rfl⟩
  have inj : ∀ {L : List Coord} {col : ℕ}, PathC p q L col → ((CI k L).map (crossSlot k L)).Nodup := by
    intro L col hp
    refine (List.pairwise_map).mpr (CI_sorted.imp_of_mem ?_)
    intro a b ha hb hab e
    obtain ⟨-, -, e'⟩ := cross_unique W.sol hp hp (mem_CI.mp ha) (mem_CI.mp hb) e
    omega
  have hX : ((CI k p).map (crossSlot k p) ++ (CI k q).map (crossSlot k q)).Perm (usedOf k k s) := by
    refine (List.perm_ext_iff_of_nodup ?_ (used_nodup)).mpr ?_
    · refine List.nodup_append.mpr ⟨inj Pp, inj Pq, ?_⟩
      intro a ha b hb e
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hb
      obtain ⟨-, h, -⟩ := cross_unique W.sol Pp Pq (mem_CI.mp hj) (mem_CI.mp hj') e
      omega
    · intro sl
      rw [used_iff W.k8 W.sol hinv, List.mem_append, List.mem_map, List.mem_map]
      constructor
      · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
        · exact ⟨p, 0, j, Pp, mem_CI.mp hj, rfl⟩
        · exact ⟨q, 1, j, Pq, mem_CI.mp hj, rfl⟩
      · rintro ⟨L, col, j, hp, hc, rfl⟩
        rcases hp with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact Or.inl ⟨j, mem_CI.mpr hc, rfl⟩
        · exact Or.inr ⟨j, mem_CI.mpr hc, rfl⟩
  rw [← (hX.map _).sum_eq, List.map_append, List.sum_append, List.map_map, List.map_map]
  have go : ∀ {L : List Coord} {col : ℕ}, PathC p q L col →
      ((CI k L).map (fun j => Win.sgn (crossOut k L j))).sum =
        ((CI k L).map ((fun sl => Win.sgn (exitCell k k sl)) ∘ crossSlot k L)).sum := by
    intro L col hp
    obtain ⟨-, cL, -⟩ := pathC_facts W.sol hp
    congr 1
    apply List.map_congr_left
    intro j hj
    simp only [Function.comp, crossSlot, crossOut]
    rw [exitCell_slot (cross_exit cL (mem_CI.mp hj))]
  rw [go Pp, go Pq]

omit hinv in
theorem ends_sum :
    ((if inWb k (nth p 0) then 0 else Win.sgn (nth p 0)) +
      (if inWb k (nth p (p.length - 1)) then 0 else Win.sgn (nth p (p.length - 1)))) +
    ((if inWb k (nth q 0) then 0 else Win.sgn (nth q 0)) +
      (if inWb k (nth q (q.length - 1)) then 0 else Win.sgn (nth q (q.length - 1)))) =
      fsOf F := by
  obtain ⟨-, s0, t0, -, h0, h1, -, hc0⟩ := pathC_ends W (Or.inl ⟨rfl, rfl⟩ : PathC p q p 0)
  obtain ⟨-, s1, t1, -, h2, h3, -, hc1⟩ := pathC_ends W (Or.inr ⟨rfl, rfl⟩ : PathC p q q 1)
  rcases hc0 with ⟨-, rfl, rfl⟩ | ⟨h, -⟩
  swap; · omega
  rcases hc1 with ⟨h, -⟩ | ⟨-, rfl, rfl⟩
  · omega
  rw [h0, h1, h2, h3]
  obtain ⟨-, -, -, -, w1, w2, w3, w4, w5, w6⟩ := W.wf
  have T : ∀ x : Coord, x.1 < k ∧ x.2 < k → (if inWb k x then (0 : Int) else Win.sgn x) = 0 := fun x hx => by
    rw [ite_eq_left (inWb_iff.mpr hx)]
  have T' : ∀ x : Coord, ¬ (x.1 < k ∧ x.2 < k) → (if inWb k x then (0 : Int) else Win.sgn x) = Win.sgn x :=
    fun x hx => by rw [ite_eq_right (fun c => hx (inWb_iff.mp c))]
  rcases W.ends with ⟨hF, hin⟩ | ⟨E, fc, fs, fsl, hF, hE, hEo, hcol, hoth, -, hfs, -⟩
  · rw [hF, T _ (hin _ (by unfold IsEnd; simp)), T _ (hin _ (by unfold IsEnd; simp)),
      T _ (hin _ (by unfold IsEnd; simp)), T _ (hin _ (by unfold IsEnd; simp))]
    simp [fsOf]
  · rw [hF]
    simp only [fsOf]
    rw [hfs]
    have o : ∀ x, IsEnd J x → x ≠ E → (if inWb k x then (0 : Int) else Win.sgn x) = 0 :=
      fun x hx ne => T _ (hoth x hx ne)
    have i0 : IsEnd J J.s0 := by unfold IsEnd; simp
    have i1 : IsEnd J J.t0 := by unfold IsEnd; simp
    have i2 : IsEnd J J.s1 := by unfold IsEnd; simp
    have i3 : IsEnd J J.t1 := by unfold IsEnd; simp
    rcases hE with rfl | rfl | rfl | rfl
    · rw [T' _ hEo, o _ i1 (Ne.symm w1), o _ i2 (Ne.symm w2), o _ i3 (Ne.symm w3)]; ring
    · rw [o _ i0 w1, T' _ hEo, o _ i2 (Ne.symm w4), o _ i3 (Ne.symm w5)]; ring
    · rw [o _ i0 w2, o _ i1 w4, T' _ hEo, o _ i3 (Ne.symm w6)]; ring
    · rw [o _ i0 w3, o _ i1 w5, o _ i2 w6, T' _ hEo]; ring

/-- **Parity of the outside ends.** -/
theorem window_parity : parOf k k F s = 2 * (((J.w * J.h) % 2 : ℕ) : Int) := by
  obtain ⟨hp0, -⟩ := pathC_ends W (Or.inl ⟨rfl, rfl⟩ : PathC p q p 0)
  obtain ⟨hq0, -⟩ := pathC_ends W (Or.inr ⟨rfl, rfl⟩ : PathC p q q 1)
  have pp := path_parity (k := k) W.sol.1.2.2.2.2 hp0
  have pq := path_parity (k := k) W.sol.2.1.2.2.2.2 hq0
  have os := outside_sum W.keven W.sol W.kw.le W.kh.le
  have cs := cross_sum W hinv
  have es := ends_sum W
  rw [parOf_eq, ← cs, ← es, ← os]
  linarith

end ParW

end ZZN.Win

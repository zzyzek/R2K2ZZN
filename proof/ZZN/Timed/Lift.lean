/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.TimedStatement
public import ZZN.Constr.Solve
public import ZZN.Timed.BandCost

@[expose] public section

/-!
# The counted reduction search, lifting and checker

* `findRedT` (`findRed`): at most `40 (w + 1)²` steps.
* `liftET` (`liftE`): band extension after the reduction.
* `solBT` (`solB`): at most `3 (|p| + |q| + 1)² + 10` steps.
* `checkET` (`checkE`).
-/

namespace ZZN.T

open ZZN GridHam

/-! ### The reduction search -/


lemma freeLineBT_ret (I : Inst) (k : ℕ) : (freeLineBT I k).ret = freeLineB I k := by
  simp [freeLineBT, freeLineB, lallT]

lemma freeLineBT_time (I : Inst) (k : ℕ) : (freeLineBT I k).time ≤ 4 := by
  have := lallT_time_le (fun e : Coord => (pure (e.1 != k) : TimeM Bool)) I.ends 0 (fun _ _ => by simp)
  simpa [freeLineBT, Inst.ends] using this



lemma endBelowBT_time (I : Inst) (k : ℕ) : (endBelowBT I k).time ≤ 4 := by
  have := lanyT_time_le (fun e : Coord => (pure (decide (e.1 < k)) : TimeM Bool)) I.ends 0
    (fun _ _ => by simp)
  simpa [endBelowBT, Inst.ends] using this

lemma endAboveBT_time (I : Inst) (k : ℕ) : (endAboveBT I k).time ≤ 4 := by
  have := lanyT_time_le (fun e : Coord => (pure (decide (k < e.1)) : TimeM Bool)) I.ends 0
    (fun _ _ => by simp)
  simpa [endAboveBT, Inst.ends] using this




lemma redBT_ret (I : Inst) (d : ℕ) : (redBT I d).ret = redB I d := by
  simp [redBT, redB, winT, edgeKT, lallT, lanyT, rangeT, freeLineBT_ret, endBelowBT, endAboveBT,
    endBelowB, endAboveB]

lemma winT_time (I : Inst) (d lo : ℕ) : (winT I d lo).time ≤ 70 := by
  have := lallT_time_le (fun j => freeLineBT I (lo + j)) (List.range 10) 4
    (fun j _ => freeLineBT_time I (lo + j))
  have := endBelowBT_time I lo
  have := endAboveBT_time I (lo + 9)
  simp only [List.length_range] at *
  simp only [winT, time_bind, rangeT, time_pure]
  omega

lemma redBT_time (I : Inst) (d : ℕ) : (redBT I d).time ≤ 100 * (I.w + d + 2) := by
  have a1 := lallT_time_le (freeLineBT I) (List.range 4) 4 (fun k _ => freeLineBT_time I k)
  have a2 := lallT_time_le (edgeKT I) (List.range I.w) 4
    (fun k _ => by simp only [edgeKT, time_bind, time_pure]; have := freeLineBT_time I k; omega)
  have a3 := lanyT_time_le (winT I d) (List.range (d + 1)) 70 (fun lo _ => winT_time I d lo)
  have := freeLineBT_time I d; have := freeLineBT_time I (d + 1)
  have := freeLineBT_time I (d - 1); have := freeLineBT_time I (d + 2)
  have := endBelowBT_time I d; have := endAboveBT_time I (d + 1)
  simp only [List.length_range] at a1 a2 a3
  simp only [redBT, time_bind, rangeT, time_pure]
  omega


lemma findRedT_ret (I : Inst) : (findRedT I).ret = findRed I := by
  simp [findRedT, findRed, lfindT, rangeT, redBT_ret]

lemma findRedT_time (I : Inst) : (findRedT I).time ≤ 200 * (I.w + 1) ^ 2 := by
  have := lfindT_time_le (redBT I) (List.range I.w) (200 * (I.w + 1))
    (fun d hd => by have := redBT_time I d; have := List.mem_range.mp hd; omega)
  simp only [List.length_range] at this
  simp only [findRedT, time_bind, rangeT]
  nlinarith

/-! ### Lifting -/


lemma liftET_ret (I : Inst) (d : ℕ) (p q : List Coord) : (liftET I d p q).ret = liftE I d p q := by
  simp only [liftET, liftE, ret_bind, freeLineBT_ret]
  split_ifs <;> simp

lemma liftET_time (I : Inst) (d : ℕ) (p q : List Coord) :
    (liftET I d p q).time ≤ 210 * ((I.h + 1) * (p.length + q.length + I.h + 1)) := by
  have f := freeLineBT_time I (d + 2)
  have lx := @linX I.h (p.length + q.length)
  simp only [liftET, time_bind]
  split_ifs
  · have := bandExtET_time (I.deleteAt d) d p q
    rw [show (I.deleteAt d).h = I.h from rfl] at this; omega
  · have := bandExtET_time (I.deleteAt d) (d - 1) p q
    rw [show (I.deleteAt d).h = I.h from rfl] at this; omega

lemma liftE_len (I : Inst) (d : ℕ) (p q : List Coord) :
    (liftE I d p q).1.length + (liftE I d p q).2.length ≤ 3 * (p.length + q.length) + 4 * I.h + 4 := by
  unfold liftE
  split_ifs
  · exact bandExtE_len _ _ _ _
  · exact bandExtE_len _ _ _ _

/-! ### The checker -/


lemma chainT_ret : ∀ l : List Coord, (chainT l).ret = chainAdjacent l
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by simp [chainT, chainAdjacent, chainT_ret (b :: rest)]

lemma chainT_time : ∀ l : List Coord, (chainT l).time ≤ l.length
  | [] => by simp [chainT]
  | [_] => by simp [chainT]
  | a :: b :: rest => by
    have := chainT_time (b :: rest)
    simp only [chainT, time_bind, List.length_cons] at *
    omega


lemma isPathT_ret (w h : ℕ) (s t : Coord) (p : List Coord) :
    (isPathT w h s t p).ret = decide (IsPath w h s t p) := by
  simp only [isPathT, ret_bind, ret_pure, lgetLastT, lnodupT, lallT, chainT_ret]
  rw [Bool.eq_iff_iff]
  simp [IsPath, InBounds, and_assoc]

lemma isPathT_time (w h : ℕ) (s t : Coord) (p : List Coord) :
    (isPathT w h s t p).time ≤ (p.length + 1) ^ 2 + 2 * p.length + 2 := by
  have a := lallT_time_le (fun v : Coord => (pure (decide (v.1 < w) && decide (v.2 < h)) : TimeM Bool))
    p 0 (fun _ _ => by simp)
  have c := chainT_time p
  simp only [isPathT, time_bind, lgetLastT, lnodupT, time_pure]
  nlinarith


lemma solBT_ret (I : Inst) (p q : List Coord) : (solBT I p q).ret = solB I p q := by
  simp [solBT, solB, isPathT_ret, lappendT, lnodupT, lengthT]

lemma solBT_time (I : Inst) (p q : List Coord) :
    (solBT I p q).time ≤ 3 * (p.length + q.length + 1) ^ 2 + 10 := by
  have a := isPathT_time I.w I.h I.s0 I.t0 p
  have b := isPathT_time I.w I.h I.s1 I.t1 q
  simp only [solBT, time_bind, lappendT, lnodupT, lengthT, time_pure, List.length_append]
  nlinarith

lemma solB_len {I : Inst} {p q : List Coord} (h : solB I p q = true) :
    p.length + q.length = I.w * I.h := by
  simp only [solB, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2


lemma checkET_ret (I : Inst) (o : Option (List Coord × List Coord)) :
    (checkET I o).ret = checkE I o := by
  cases o <;> simp [checkET, checkE, solBT_ret]

lemma checkE_len {I : Inst} {o : Option (List Coord × List Coord)} {p q : List Coord}
    (h : checkE I o = some (p, q)) : p.length + q.length = I.w * I.h := by
  unfold checkE at h
  split at h
  · split_ifs at h with hc
    cases h
    exact solB_len hc
  · cases h

end ZZN.T

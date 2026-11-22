/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.TimedStatement
public import ZZN.Constr.Solve
public import ZZN.Timed.BandCost
public import ZZN.Timed.BandL
public import ZZN.Constr.Solve2

@[expose] public section

/-!
# The counted reduction search, lifting and checker

* `findRedT` (`findRed`): at most `200 (w + 1)²` steps.
* `liftET` (`liftL`, equal to `liftE` on solutions): one-pass band extension after the reduction.
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


lemma redBBT_ret (I : Inst) (d : ℕ) : (redBBT I d).ret = redBB I d := by
  simp [redBBT, redBB, freeLineBT_ret, endBelowBT, endAboveBT, endBelowB, endAboveB, lanyT]

lemma redBBT_time (I : Inst) (d : ℕ) : (redBBT I d).time ≤ 24 := by
  have := freeLineBT_time I d
  have := freeLineBT_time I (d + 1)
  have := freeLineBT_time I (d - 1)
  have := freeLineBT_time I (d + 2)
  have := endBelowBT_time I d
  have := endAboveBT_time I (d + 1)
  simp only [redBBT, time_bind, time_pure]
  omega

lemma findRed2T_ret (I : Inst) : (findRed2T I).ret = findRed2 I := by
  simp [findRed2T, findRed2, lfindT, rangeT, redBT_ret, redBBT_ret]
  rfl

lemma findRed2T_time (I : Inst) : (findRed2T I).time ≤ 300 * (I.w + 1) ^ 2 := by
  have := lfindT_time_le (fun d => do
      let x ← redBT I d
      let y ← redBBT I d
      pure (x || y)) (List.range I.w) (200 * (I.w + 1))
    (fun d hd => by
      have := redBT_time I d; have := redBBT_time I d; have := List.mem_range.mp hd
      simp only [time_bind, time_pure]; omega)
  simp only [List.length_range] at this
  simp only [findRed2T, time_bind, rangeT]
  nlinarith

/-! ### Lifting -/


lemma liftET_ret (I : Inst) (d : ℕ) (p q : List Coord) : (liftET I d p q).ret = liftL I d p q := by
  simp only [liftET, liftL, ret_bind, freeLineBT_ret]
  split_ifs <;> exact bandExtLT_ret (I.deleteAt d) _ p q

/-- A solution lists every cell once. -/
lemma sol_len {I : Inst} {p q : List Coord} (h : IsSolution I p q) :
    p.length + q.length = I.w * I.h := by
  have := solB_complete h
  simp only [solB, Bool.and_eq_true, beq_iff_eq] at this
  exact this.2

/-- **One lift**: linear in the paths plus `O(h²)`. -/
lemma liftET_time {I : Inst} {d : ℕ} {p q : List Coord} (hr : FreeShape I d)
    (hs : IsSolution (I.deleteAt d) p q) :
    (liftET I d p q).time ≤ 6 * (p.length + q.length) + 40 * (I.h + 1) ^ 2 + 5 := by
  have f := freeLineBT_time I (d + 2)
  have hL := liftL_eqF hr hs
  have hsol := liftE_solF hr hs
  have l1 := sol_len hs
  have l2 := sol_len hsol
  have hw : 13 ≤ I.w := hr.1
  have hdw : (I.deleteAt d).w = I.w - 2 := rfl
  have hdh : (I.deleteAt d).h = I.h := rfl
  have hp := hs.1.2.2.1
  have hq := hs.2.1.2.2.1
  have hbp : ∀ v ∈ p, v.2 < I.h := fun v hv => (hs.1.2.2.2.1 v hv).2
  have hbq : ∀ v ∈ q, v.2 < I.h := fun v hv => (hs.2.1.2.2.2.1 v hv).2
  have hout : (liftL I d p q).1.length + (liftL I d p q).2.length ≤ p.length + q.length + 2 * I.h := by
    rw [hL, l2, l1, hdw, hdh]
    have : (I.w - 2) * I.h + 2 * I.h = I.w * I.h := by
      rw [← Nat.add_mul]; congr 1; omega
    rw [this]
  simp only [liftET, time_bind, freeLineBT_ret]
  unfold liftL at hout
  split_ifs at hout ⊢
  · have := bandExtLT_time I.h d p q hp hq hbp hbq (by rw [bandExtLT_ret]; exact hout)
    omega
  · have := bandExtLT_time I.h (d - 1) p q hp hq hbp hbq (by rw [bandExtLT_ret]; exact hout)
    omega

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

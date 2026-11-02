-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Constr.Solve
import ZZN.Timed.BandCost

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

def freeLineBT (I : Inst) (k : ℕ) : TimeM Bool := lallT (fun e => pure (e.1 != k)) I.ends

lemma freeLineBT_ret (I : Inst) (k : ℕ) : (freeLineBT I k).ret = freeLineB I k := by
  simp [freeLineBT, freeLineB, lallT]

lemma freeLineBT_time (I : Inst) (k : ℕ) : (freeLineBT I k).time ≤ 4 := by
  have := lallT_time_le (fun e : Coord => (pure (e.1 != k) : TimeM Bool)) I.ends 0 (fun _ _ => by simp)
  simpa [freeLineBT, Inst.ends] using this

def endBelowBT (I : Inst) (k : ℕ) : TimeM Bool := lanyT (fun e => pure (decide (e.1 < k))) I.ends

def endAboveBT (I : Inst) (k : ℕ) : TimeM Bool := lanyT (fun e => pure (decide (k < e.1))) I.ends

lemma endBelowBT_time (I : Inst) (k : ℕ) : (endBelowBT I k).time ≤ 4 := by
  have := lanyT_time_le (fun e : Coord => (pure (decide (e.1 < k)) : TimeM Bool)) I.ends 0
    (fun _ _ => by simp)
  simpa [endBelowBT, Inst.ends] using this

lemma endAboveBT_time (I : Inst) (k : ℕ) : (endAboveBT I k).time ≤ 4 := by
  have := lanyT_time_le (fun e : Coord => (pure (decide (k < e.1)) : TimeM Bool)) I.ends 0
    (fun _ _ => by simp)
  simpa [endAboveBT, Inst.ends] using this

def winT (I : Inst) (d lo : ℕ) : TimeM Bool := do
  let js ← rangeT 10
  let f ← lallT (fun j => freeLineBT I (lo + j)) js
  let b ← endBelowBT I lo
  let a ← endAboveBT I (lo + 9)
  pure (decide (d + 1 ≤ lo + 9) && decide (lo + 10 ≤ I.w) && f && b && a)

def edgeKT (I : Inst) (k : ℕ) : TimeM Bool := do
  let f ← freeLineBT I k
  pure (!(decide (I.w ≤ k + 4)) || f)

def redBT (I : Inst) (d : ℕ) : TimeM Bool := do
  let r4 ← rangeT 4
  let s1 ← lallT (freeLineBT I) r4
  let rw ← rangeT I.w
  let s2 ← lallT (edgeKT I) rw
  let rd ← rangeT (d + 1)
  let s3 ← lanyT (winT I d) rd
  let f0 ← freeLineBT I d
  let f1 ← freeLineBT I (d + 1)
  let fm ← freeLineBT I (d - 1)
  let f2 ← freeLineBT I (d + 2)
  let b ← endBelowBT I d
  let a ← endAboveBT I (d + 1)
  pure (decide (13 ≤ I.w) &&
    ((d == 0 && s1) || (d + 2 == I.w && s2) || s3 ||
     (decide (8 ≤ d) && decide (d + 10 ≤ I.w) && f0 && f1 && ((decide (1 ≤ d) && fm) || f2) && b && a)))

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

def findRedT (I : Inst) : TimeM (Option ℕ) := do
  let rs ← rangeT I.w
  lfindT (redBT I) rs

lemma findRedT_ret (I : Inst) : (findRedT I).ret = findRed I := by
  simp [findRedT, findRed, lfindT, rangeT, redBT_ret]

lemma findRedT_time (I : Inst) : (findRedT I).time ≤ 200 * (I.w + 1) ^ 2 := by
  have := lfindT_time_le (redBT I) (List.range I.w) (200 * (I.w + 1))
    (fun d hd => by have := redBT_time I d; have := List.mem_range.mp hd; omega)
  simp only [List.length_range] at this
  simp only [findRedT, time_bind, rangeT]
  nlinarith

/-! ### Lifting -/

def liftET (I : Inst) (d : ℕ) (p q : List Coord) : TimeM (List Coord × List Coord) := do
  let f ← freeLineBT I (d + 2)
  if d + 3 ≤ I.w ∧ f = true then bandExtET (I.deleteAt d) d p q
  else bandExtET (I.deleteAt d) (d - 1) p q

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

def chainT : List Coord → TimeM Bool
  | [] => pure true
  | [_] => pure true
  | a :: b :: rest => do
    let r ← chainT (b :: rest)
    ⟨adjacentB a b && r, 1⟩

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

def isPathT (w h : ℕ) (s t : Coord) (p : List Coord) : TimeM Bool := do
  let l ← lgetLastT p
  let n ← lnodupT p
  let b ← lallT (fun v => pure (decide (v.1 < w) && decide (v.2 < h))) p
  let c ← chainT p
  pure (decide (p.head? = some s) && decide (l = some t) && n && b && c)

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

def solBT (I : Inst) (p q : List Coord) : TimeM Bool := do
  let a ← isPathT I.w I.h I.s0 I.t0 p
  let b ← isPathT I.w I.h I.s1 I.t1 q
  let pq ← lappendT p q
  let n ← lnodupT pq
  let lp ← lengthT p
  let lq ← lengthT q
  pure (a && b && n && (lp + lq == I.w * I.h))

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

def checkET (I : Inst) (o : Option (List Coord × List Coord)) : TimeM (Option (List Coord × List Coord)) :=
  match o with
  | some pq => do
    let b ← solBT I pq.1 pq.2
    pure (if b then some pq else none)
  | none => pure none

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

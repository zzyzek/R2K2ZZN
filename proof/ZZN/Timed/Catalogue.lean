/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.TimedStatement
public import ZZN.Catalogue
public import ZZN.Timed.TimeM

@[expose] public section

/-!
# The counted catalogue test

`fires3T` is `fires3` (`ZZN/Statement.lean`) written with the counted operations of
`ZZN/Timed/TimeM.lean`. Each counted definition has a lemma saying that its result is the
original one (`*_ret`). The time bounds are in `ZZN/Timed/CatalogueCost.lean`.

Constant-time helpers used directly (no list traversal): arithmetic and comparisons on numbers,
`sgn`, `perimIndex`, `Frame.to`, `Frame.back`, `Frame.H`, `Frame.W`, `alternating` (inspects at most
five list cells), `List.headD` (one cell), option and pair projections.
-/

namespace ZZN.T

open ZZN

/-! ### Views -/


@[simp] lemma atT_ret (v : View) (r c : ℕ) : (atT v r c).ret = v.at r c := by
  simp only [atT, View.at, ret_bind, ret_pure, lfindT]
  cases (List.find? (fun q => q.1 == (r, c)) v.pts) <;> rfl


@[simp] lemma emptyT_ret (v : View) (cells : List (ℕ × ℕ)) :
    (emptyT v cells).ret = v.empty cells := by
  simp [emptyT, View.empty, lallT]


@[simp] lemma makeViewT_ret (R C : ℕ) (f : Frame) (pts : List Pt) :
    (makeViewT R C f pts).ret = makeView R C f pts := by
  simp [makeViewT, makeView, lmapT]

/-! ### Global checks -/


@[simp] lemma parityOkT_ret (R C : ℕ) (pts : List Pt) :
    (parityOkT R C pts).ret = parityOk R C pts := by
  simp [parityOkT, parityOk, lmapT, lsumT]


@[simp] lemma sortByKeyT_ret (l : List (ℕ × ℕ)) : (sortByKeyT l).ret = sortByKey l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [sortByKeyT, sortByKey, ih, lfilterT, lappendT]

/-! ### T1, T2, L1, L6 -/


@[simp] lemma t1FiresT_ret (R C : ℕ) (pts : List Pt) :
    (t1FiresT R C pts).ret = t1Fires R C pts := by
  simp [t1FiresT, t1Fires, lmapT, lallT, lzipT, List.map_map, Function.comp_def]


@[simp] lemma t2FiresT_ret (cells : List (ℕ × ℕ)) : (t2FiresT cells).ret = t2Fires cells := by
  simp [t2FiresT, t2Fires, lmapT, lgetT]



@[simp] lemma l1FiresT_ret (R C : ℕ) (pts : List Pt) : (l1FiresT R C pts).ret = l1Fires R C pts := by
  simp [l1FiresT, l1Fires, nbrsT, lanyT, lallT, lfilterT]



@[simp] lemma l6ClosuresT_ret (R C : ℕ) (pts : List Pt) :
    (l6ClosuresT R C pts).ret = l6Closures R C pts := by
  simp only [l6ClosuresT, l6Closures, lfilterMapT, ret_bind, ret_pure, lanyT, lfindT, cornersL]
  rfl


@[simp] lemma l6FiresT_ret (R C : ℕ) (pts : List Pt) : (l6FiresT R C pts).ret = l6Fires R C pts := by
  simp [l6FiresT, l6Fires, lcontainsT]

/-! ### Corner patterns L2–L5, E1, B, C/D -/


@[simp] lemma testL2T_ret (v : View) : (testL2T v).ret = testL2 v := by
  simp only [testL2T, testL2, ret_bind, atT_ret]
  split <;> simp_all


@[simp] lemma testL3T_ret (v : View) : (testL3T v).ret = testL3 v := by
  simp only [testL3T, testL3, ret_bind, atT_ret]
  split <;> simp_all


@[simp] lemma testL4T_ret (v : View) : (testL4T v).ret = testL4 v := by
  simp only [testL4T, testL4, ret_bind, atT_ret]
  split <;> simp_all


@[simp] lemma testL5T_ret (v : View) : (testL5T v).ret = testL5 v := by
  simp only [testL5T, testL5, ret_bind, atT_ret]
  split <;> simp_all



@[simp] lemma edgeClosureT_ret (v : View) : (edgeClosureT v).ret = edgeClosure v := by
  simp only [edgeClosureT, edgeClosure, ret_bind, rangeT, lanyT]
  congr 1; funext k
  unfold edgeStepT
  by_cases hk : k + 3 < v.W
  · simp only [hk, ite_true, decide_true, Bool.true_and, ret_bind, atT_ret]
    split <;> simp_all
  · simp [hk]


@[simp] lemma sameSetT_ret (a b : List (ℕ × ℕ)) : (sameSetT a b).ret = sameSet a b := by
  simp [sameSetT, sameSet, lengthT, lallT, lcontainsT]


@[simp] lemma corner4T_ret (R C : ℕ) (f : Frame) (pts : List Pt) :
    (corner4T R C f pts).ret = corner4 R C f pts := by
  simp [corner4T, corner4, lfilterT, lmapT, lanyT]




@[simp] lemma boundaryOnlyT_ret (R C : ℕ) (f : Frame) (pts : List Pt) :
    (boundaryOnlyT R C f pts).ret = boundaryOnly R C f pts := by
  simp only [boundaryOnlyT, boundaryOnly, ret_bind, lmapT, lanyT, ret_pure]
  congr 1; funext t; congr 1; funext A
  simp only [boundaryStepT, isAT, ret_bind, lfindT, lanyT, ret_pure]
  cases List.find? (fun q => q.2 == 1 - A && q.1 == t.2.2)
    (List.map (fun q => (Frame.to R C f q.1, q.2)) pts) <;> rfl


@[simp] lemma frameFiresT_ret (R C : ℕ) (pts : List Pt) (f : Frame) :
    (frameFiresT R C pts f).ret = frameFires R C pts f := by
  simp [frameFiresT, frameFires]

/-! ### The R test -/


@[simp] lemma rewritesAtT_ret (v : View) : (rewritesAtT v).ret = rewritesAt v := by
  simp only [rewritesAtT, rewritesAt, ret_bind, ret_pure, atT_ret, emptyT_ret]
  rfl


@[simp] lemma moveFirstT_ret (e : List Pt) (m : (ℕ × ℕ) × (ℕ × ℕ)) :
    (moveFirstT e m).ret = moveFirst e m := by
  simp only [moveFirstT, moveFirst, ret_bind, lfindIdxT]
  cases List.findIdx? (fun q => q.1 == m.1) e <;> rfl



@[simp] lemma rwStepT_ret (R C : ℕ) (st : RWState) (f : Frame) :
    (rwStepT R C st f).ret = rwStep R C st f := by
  simp only [rwStepT, rwStep, ret_bind, makeViewT_ret, rewritesAtT_ret]
  cases rewritesAt (makeView R C f st.eff) with
  | none => rfl
  | some rw =>
    simp only [rwApplyT, ret_bind, lmapT, lanyT, lcontainsT, ret_pure, lappendT]
    have e1 : (fun x => Frame.back R C f x) = Frame.back R C f := rfl
    rw [e1]
    split_ifs <;> simp_all


@[simp] lemma rewriteAllT_ret (R C : ℕ) (pts : List Pt) :
    (rewriteAllT R C pts).ret = rewriteAll R C pts := by
  simp [rewriteAllT, rewriteAll]


@[simp] lemma notchLenT_ret (R C : ℕ) (f : Frame) (removed : List (ℕ × ℕ)) (i : ℕ) :
    (notchLenT R C f removed i).ret = notchLen R C f removed i := by
  simp [notchLenT, notchLen, rangeT, lfilterT, lengthT, lcontainsT]




lemma staircaseT_ret (lamT : ℕ → TimeM ℕ) :
    (staircaseT lamT).ret = staircase (fun i => (lamT i).ret) := by
  simp [staircaseT, stairBlockT, staircase, countPosT, rangeT, lreverseT, lflatMapT, lfilterT,
    lengthT, lappendT, lmapT]


@[simp] lemma stairOfT_ret (R C : ℕ) (f : Frame) (removed : List (ℕ × ℕ)) :
    (stairOfT R C f removed).ret = stairOf R C f removed := by
  simp only [stairOfT, stairOf, ret_bind, staircaseT_ret, notchLenT_ret, lmapT, ret_pure]







@[simp] lemma walk3T_ret (R C : ℕ) (removed : List (ℕ × ℕ)) :
    (walk3T R C removed).ret = walk3 R C removed := by
  simp [walk3T, walkStairsT, walkSidesT, sideMapT, walkJoinT, walk3, countPosT, sideT, rangeT, lfilterT,
    lengthT, lreverseT, lappendT, lmapT, List.append_assoc]


@[simp] lemma positionsT_ret (walk : List (ℕ × ℕ)) (x : ℕ × ℕ) :
    (positionsT walk x).ret = positions walk x := by
  simp [positionsT, positions, lzipIdxT, lfilterT, lmapT]


@[simp] lemma effAlt3T_ret (R C : ℕ) (pts : List Pt) : (effAlt3T R C pts).ret = effAlt3 R C pts := by
  simp [effAlt3T, effAlt3, lanyT, lcontainsT, lmapT, ldedupT, lengthT, List.map_map,
    Function.comp_def]

/-! ### The test -/


@[simp] lemma fires3T_ret (R C : ℕ) (s0 t0 s1 t1 : ℕ × ℕ) :
    (fires3T R C s0 t0 s1 t1).ret = fires3 R C s0 t0 s1 t1 := by
  simp [fires3T, fires3, lanyT]

end ZZN.T

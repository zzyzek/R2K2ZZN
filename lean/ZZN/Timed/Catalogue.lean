-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Catalogue
import ZZN.Timed.TimeM

/-!
# The counted catalogue test

`fires3T` is `fires3` (`ZZN/Catalogue.lean`) written with the counted operations of
`ZZN/Timed/TimeM.lean`. Each counted definition has a lemma saying that its result is the
original one (`*_ret`). The time bounds are in `ZZN/Timed/CatalogueCost.lean`.

Constant-time helpers used directly (no list traversal): arithmetic and comparisons on numbers,
`sgn`, `perimIndex`, `Frame.to`, `Frame.back`, `Frame.H`, `Frame.W`, `alternating` (inspects at most
five list cells), `List.headD` (one cell), option and pair projections.
-/

namespace ZZN.T

open ZZN

/-! ### Views -/

def atT (v : View) (r c : ℕ) : TimeM (Option ℕ) := do
  let o ← lfindT (fun q => pure (q.1 == (r, c))) v.pts
  pure (match o with | some q => some q.2 | none => none)

@[simp] lemma atT_ret (v : View) (r c : ℕ) : (atT v r c).ret = v.at r c := by
  simp only [atT, View.at, ret_bind, ret_pure, lfindT]
  cases (List.find? (fun q => q.1 == (r, c)) v.pts) <;> rfl

def emptyT (v : View) (cells : List (ℕ × ℕ)) : TimeM Bool :=
  lallT (fun x => do let o ← atT v x.1 x.2; pure o.isNone) cells

@[simp] lemma emptyT_ret (v : View) (cells : List (ℕ × ℕ)) :
    (emptyT v cells).ret = v.empty cells := by
  simp [emptyT, View.empty, lallT]

def makeViewT (R C : ℕ) (f : Frame) (pts : List Pt) : TimeM View := do
  let ps ← lmapT (fun q => pure (f.to R C q.1, q.2)) pts
  pure ⟨f.H R C, f.W R C, ps⟩

@[simp] lemma makeViewT_ret (R C : ℕ) (f : Frame) (pts : List Pt) :
    (makeViewT R C f pts).ret = makeView R C f pts := by
  simp [makeViewT, makeView, lmapT]

/-! ### Global checks -/

def parityOkT (R C : ℕ) (pts : List Pt) : TimeM Bool := do
  let l ← lmapT (fun q => pure (sgn q.1)) pts
  let s ← lsumT l
  pure (s == 2 * (((R * C) % 2 : ℕ) : ℤ))

@[simp] lemma parityOkT_ret (R C : ℕ) (pts : List Pt) :
    (parityOkT R C pts).ret = parityOk R C pts := by
  simp [parityOkT, parityOk, lmapT, lsumT]

def sortByKeyT : List (ℕ × ℕ) → TimeM (List (ℕ × ℕ))
  | [] => pure []
  | x :: xs => do
    let s ← sortByKeyT xs
    let a ← lfilterT (fun y => pure (decide (y.1 < x.1))) s
    let b ← lfilterT (fun y => pure (decide (¬ (y.1 < x.1)))) s
    let ab ← lappendT a [x]
    lappendT ab b

@[simp] lemma sortByKeyT_ret (l : List (ℕ × ℕ)) : (sortByKeyT l).ret = sortByKey l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [sortByKeyT, sortByKey, ih, lfilterT, lappendT]

/-! ### T1, T2, L1, L6 -/

def t1FiresT (R C : ℕ) (pts : List Pt) : TimeM Bool := do
  let idx ← lmapT (fun q => pure (perimIndex R C q.1)) pts
  let ok ← lallT (fun o => pure o.isSome) idx
  let keys ← lmapT (fun o => pure (o.getD 0)) idx
  let cols ← lmapT (fun q => pure q.2) pts
  let z ← lzipT keys cols
  let s ← sortByKeyT z
  let c ← lmapT (fun y => pure y.2) s
  pure (ok && alternating c)

@[simp] lemma t1FiresT_ret (R C : ℕ) (pts : List Pt) :
    (t1FiresT R C pts).ret = t1Fires R C pts := by
  simp [t1FiresT, t1Fires, lmapT, lallT, lzipT, List.map_map, Function.comp_def]

def t2FiresT (cells : List (ℕ × ℕ)) : TimeM Bool := do
  let rs ← lmapT (fun x => pure x.1) cells
  let cs ← lmapT (fun x => pure x.2) cells
  let mxr ← lfoldlT (fun a x => pure (max a x)) 0 rs
  let mxc ← lfoldlT (fun a x => pure (max a x)) 0 cs
  let mnr ← lfoldlT (fun a x => pure (min a x)) (rs.headD 0) rs
  let mnc ← lfoldlT (fun a x => pure (min a x)) (cs.headD 0) cs
  let r0 ← lgetT rs 0
  let r1 ← lgetT rs 1
  let c0 ← lgetT cs 0
  let c1 ← lgetT cs 1
  pure (mxr - mnr == 1 && mxc - mnc == 1 && mnr + 1 == mxr && mnc + 1 == mxc && r0 != r1 &&
    c0 != c1)

@[simp] lemma t2FiresT_ret (cells : List (ℕ × ℕ)) : (t2FiresT cells).ret = t2Fires cells := by
  simp [t2FiresT, t2Fires, lmapT, lgetT]

def nbrsT (R C : ℕ) (p : ℕ × ℕ) : TimeM (List (ℤ × ℤ)) :=
  let pr : ℤ := p.1
  let pc : ℤ := p.2
  lfilterT (fun q => pure (decide (0 ≤ q.1) && decide (q.1 < (R : ℤ)) && decide (0 ≤ q.2) &&
      decide (q.2 < (C : ℤ))))
    ([(pr - 1, pc), (pr + 1, pc), (pr, pc - 1), (pr, pc + 1)] : List (ℤ × ℤ))

def l1FiresT (R C : ℕ) (pts : List Pt) : TimeM Bool :=
  lanyT (fun pc => do
    let nb ← nbrsT R C pc.1
    lallT (fun q => lanyT (fun pc' => pure (pc'.1 == (q.1.toNat, q.2.toNat) && pc'.2 != pc.2)) pts)
      nb) pts

@[simp] lemma l1FiresT_ret (R C : ℕ) (pts : List Pt) : (l1FiresT R C pts).ret = l1Fires R C pts := by
  simp [l1FiresT, l1Fires, nbrsT, lanyT, lallT, lfilterT]

def cornersL (R C : ℕ) : List (ℤ × ℤ × ℤ × ℤ) :=
  [(0, 0, 1, 1), (0, (C : ℤ) - 1, 1, -1), ((R : ℤ) - 1, 0, -1, 1), ((R : ℤ) - 1, (C : ℤ) - 1, -1, -1)]

def l6ClosuresT (R C : ℕ) (pts : List Pt) : TimeM (List ℕ) :=
  lfilterMapT (fun (x : ℤ × ℤ × ℤ × ℤ) => do
    let n1 : ℕ × ℕ := (x.1.toNat, (x.2.1 + x.2.2.2).toNat)
    let n2 : ℕ × ℕ := ((x.1 + x.2.2.1).toNat, x.2.1.toNat)
    let occ ← lanyT (fun q => pure (q.1 == (x.1.toNat, x.2.1.toNat))) pts
    let e1 ← lfindT (fun q => pure (q.1 == n1)) pts
    let e2 ← lfindT (fun q => pure (q.1 == n2)) pts
    pure (match e1, e2 with
      | some a, some b => if a.2 == b.2 && !occ then some a.2 else none
      | _, _ => none)) (cornersL R C)

@[simp] lemma l6ClosuresT_ret (R C : ℕ) (pts : List Pt) :
    (l6ClosuresT R C pts).ret = l6Closures R C pts := by
  simp only [l6ClosuresT, l6Closures, lfilterMapT, ret_bind, ret_pure, lanyT, lfindT, cornersL]
  rfl

def l6FiresT (R C : ℕ) (pts : List Pt) : TimeM Bool := do
  let cl ← l6ClosuresT R C pts
  let c0 ← lcontainsT cl 0
  let c1 ← lcontainsT cl 1
  pure (c0 && c1 && decide (R * C > 6))

@[simp] lemma l6FiresT_ret (R C : ℕ) (pts : List Pt) : (l6FiresT R C pts).ret = l6Fires R C pts := by
  simp [l6FiresT, l6Fires, lcontainsT]

/-! ### Corner patterns L2–L5, E1, B, C/D -/

def testL2T (v : View) : TimeM Bool := do
  let x ← atT v 0 1
  let y ← atT v 1 0
  match x, y with
  | some a, some b => do let e ← emptyT v [(0, 0)]; pure (a != b && e)
  | _, _ => pure false

@[simp] lemma testL2T_ret (v : View) : (testL2T v).ret = testL2 v := by
  simp only [testL2T, testL2, ret_bind, atT_ret]
  split <;> simp_all

def testL3T (v : View) : TimeM Bool := do
  let x ← atT v 0 2
  match x with
  | some a => do
    let y ← atT v 1 1
    let z ← atT v 1 0
    let e ← emptyT v [(0, 0), (0, 1)]
    pure (y == some a && z == some (1 - a) && e)
  | none => pure false

@[simp] lemma testL3T_ret (v : View) : (testL3T v).ret = testL3 v := by
  simp only [testL3T, testL3, ret_bind, atT_ret]
  split <;> simp_all

def testL4T (v : View) : TimeM Bool := do
  let x ← atT v 0 0
  match x with
  | some a => do
    let y ← atT v 1 1
    let z ← atT v 0 2
    let e ← emptyT v [(0, 1), (1, 0)]
    pure (y == some a && z == some (1 - a) && decide (v.H ≥ 3) && e)
  | none => pure false

@[simp] lemma testL4T_ret (v : View) : (testL4T v).ret = testL4 v := by
  simp only [testL4T, testL4, ret_bind, atT_ret]
  split <;> simp_all

def testL5T (v : View) : TimeM Bool := do
  let x ← atT v 0 0
  match x with
  | some b => do
    let y ← atT v 0 2
    let z ← atT v 2 0
    let e ← emptyT v [(0, 1), (1, 0), (1, 1)]
    pure (y == some (1 - b) && z == some (1 - b) && e)
  | none => pure false

@[simp] lemma testL5T_ret (v : View) : (testL5T v).ret = testL5 v := by
  simp only [testL5T, testL5, ret_bind, atT_ret]
  split <;> simp_all

def edgeStepT (v : View) (k : ℕ) : TimeM Bool :=
  if k + 3 < v.W then do
    let x ← atT v 0 k
    match x with
    | some a => do
      let y1 ← atT v 1 (k + 1)
      let y2 ← atT v 0 (k + 3)
      let y3 ← atT v 1 (k + 2)
      pure (y1 == some a && y2 == some (1 - a) && y3 == some (1 - a))
    | none => pure false
  else pure false

def edgeClosureT (v : View) : TimeM Bool := do
  let ks ← rangeT v.W
  lanyT (edgeStepT v) ks

@[simp] lemma edgeClosureT_ret (v : View) : (edgeClosureT v).ret = edgeClosure v := by
  simp only [edgeClosureT, edgeClosure, ret_bind, rangeT, lanyT]
  congr 1; funext k
  unfold edgeStepT
  by_cases hk : k + 3 < v.W
  · simp only [hk, ite_true, decide_true, Bool.true_and, ret_bind, atT_ret]
    split <;> simp_all
  · simp [hk]

def sameSetT (a b : List (ℕ × ℕ)) : TimeM Bool := do
  let la ← lengthT a
  let lb ← lengthT b
  let al ← lallT (fun x => lcontainsT b x) a
  pure (la == lb && al)

@[simp] lemma sameSetT_ret (a b : List (ℕ × ℕ)) : (sameSetT a b).ret = sameSet a b := by
  simp [sameSetT, sameSet, lengthT, lallT, lcontainsT]

def corner4T (R C : ℕ) (f : Frame) (pts : List Pt) : TimeM Bool := do
  let F0 ← lfilterT (fun q => pure (q.2 == 0)) pts
  let A0 ← lmapT (fun q => pure (f.to R C q.1)) F0
  let F1 ← lfilterT (fun q => pure (q.2 == 1)) pts
  let A1 ← lmapT (fun q => pure (f.to R C q.1)) F1
  lanyT (fun (AB : List (ℕ × ℕ) × List (ℕ × ℕ)) => do
    let x1 ← sameSetT AB.1 A0
    let x2 ← sameSetT AB.2 A1
    let x3 ← sameSetT AB.1 A1
    let x4 ← sameSetT AB.2 A0
    pure ((x1 && x2) || (x3 && x4))) (if (R * C) % 2 == 0 then CORNER4 else CORNER4_ODD)

@[simp] lemma corner4T_ret (R C : ℕ) (f : Frame) (pts : List Pt) :
    (corner4T R C f pts).ret = corner4 R C f pts := by
  simp [corner4T, corner4, lfilterT, lmapT, lanyT]

def isAT (fp : List Pt) (A : ℕ) (x : ℕ × ℕ) : TimeM Bool :=
  lanyT (fun q => pure (q.2 == A && q.1 == x)) fp

def boundaryStepT (H W : ℕ) (fp : List Pt) (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) (A : ℕ) :
    TimeM Bool := do
  let o ← lfindT (fun q => pure (q.2 == 1 - A && q.1 == t.2.2)) fp
  match o with
  | none => pure false
  | some _ => do
    let i1 ← isAT fp A t.1
    let i2 ← isAT fp A t.2.1
    let o2 ← lfindT (fun q => pure (q.2 == 1 - A && q.1 != t.2.2)) fp
    pure (i1 && i2 && match o2 with
      | none => false
      | some (fourth, _) =>
        let onPerim := fourth.1 == 0 || fourth.2 == 0 || fourth.1 == H - 1 || fourth.2 == W - 1
        let inWin := decide (fourth.1 < 6) && decide (fourth.2 < 6)
        onPerim && !inWin)

def boundaryOnlyT (R C : ℕ) (f : Frame) (pts : List Pt) : TimeM Bool := do
  let fp ← lmapT (fun q => pure (f.to R C q.1, q.2)) pts
  lanyT (fun t => lanyT (boundaryStepT (f.H R C) (f.W R C) fp t) [0, 1])
    (if R % 2 == 1 && C % 2 == 1 then BOUNDARY3_ODD else BOUNDARY3_EVEN)

@[simp] lemma boundaryOnlyT_ret (R C : ℕ) (f : Frame) (pts : List Pt) :
    (boundaryOnlyT R C f pts).ret = boundaryOnly R C f pts := by
  simp only [boundaryOnlyT, boundaryOnly, ret_bind, lmapT, lanyT, ret_pure]
  congr 1; funext t; congr 1; funext A
  simp only [boundaryStepT, isAT, ret_bind, lfindT, lanyT, ret_pure]
  cases List.find? (fun q => q.2 == 1 - A && q.1 == t.2.2)
    (List.map (fun q => (Frame.to R C f q.1, q.2)) pts) <;> rfl

def frameFiresT (R C : ℕ) (pts : List Pt) (f : Frame) : TimeM Bool := do
  let v ← makeViewT R C f pts
  let a ← testL2T v
  let b ← testL3T v
  let c ← testL4T v
  let d ← testL5T v
  let e ← edgeClosureT v
  let g ← boundaryOnlyT R C f pts
  let k ← corner4T R C f pts
  pure (a || b || c || d || e || g || (decide (R ≥ 10) && decide (C ≥ 10) && k))

@[simp] lemma frameFiresT_ret (R C : ℕ) (pts : List Pt) (f : Frame) :
    (frameFiresT R C pts f).ret = frameFires R C pts f := by
  simp [frameFiresT, frameFires]

/-! ### The R test -/

def rewritesAtT (v : View) : TimeM (Option Rewrite) := do
  let e12 ← atT v 1 2
  let e21 ← atT v 2 1
  let w3 ← emptyT v [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (2, 0), (3, 0)]
  let e00 ← atT v 0 0
  let e11 ← atT v 1 1
  let w2 ← emptyT v [(0, 1), (1, 0), (0, 2), (2, 0)]
  let e01 ← atT v 0 1
  let w1 ← emptyT v [(0, 0), (1, 0)]
  pure (
    if (match e12, e21 with | some x, some y => x != y | _, _ => false) && decide (v.H ≥ 4) &&
        decide (v.W ≥ 4) && w3
    then some ⟨[(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0), (1, 2), (2, 1)],
      [((1, 2), (0, 3)), ((2, 1), (3, 0))]⟩
    else if (match e00 with | some a => e11 == some a | none => false) && decide (v.H ≥ 3) &&
        decide (v.W ≥ 3) && w2
    then some ⟨[(0, 0), (0, 1), (1, 0), (1, 1)], [((0, 0), (0, 2)), ((1, 1), (2, 0))]⟩
    else if e01.isSome && w1 && decide (v.H ≥ 2)
    then some ⟨[(0, 0), (0, 1)], [((0, 1), (1, 0))]⟩
    else none)

@[simp] lemma rewritesAtT_ret (v : View) : (rewritesAtT v).ret = rewritesAt v := by
  simp only [rewritesAtT, rewritesAt, ret_bind, ret_pure, atT_ret, emptyT_ret]
  rfl

def moveFirstT (e : List Pt) (m : (ℕ × ℕ) × (ℕ × ℕ)) : TimeM (List Pt) := do
  let i ← lfindIdxT (fun q => q.1 == m.1) e
  match i with
  | some i => lmodifyT e i (fun q => (m.2, q.2))
  | none => pure e

@[simp] lemma moveFirstT_ret (e : List Pt) (m : (ℕ × ℕ) × (ℕ × ℕ)) :
    (moveFirstT e m).ret = moveFirst e m := by
  simp only [moveFirstT, moveFirst, ret_bind, lfindIdxT]
  cases List.findIdx? (fun q => q.1 == m.1) e <;> rfl

def rwApplyT (R C : ℕ) (st : RWState) (f : Frame) (rw : Rewrite) : TimeM RWState := do
  let cells ← lmapT (fun x => pure (f.back R C x)) rw.removed
  let moves ← lmapT (fun m => pure (f.back R C m.1, f.back R C m.2)) rw.moves
  let b1 ← lanyT (fun x => lcontainsT st.removed x) cells
  let b2 ← lanyT (fun m => lcontainsT st.removed m.2) moves
  if b1 then pure st
  else if b2 then pure st
  else do
    let eff ← lfoldlT moveFirstT st.eff moves
    let rem ← lappendT st.removed cells
    pure ⟨eff, rem, true⟩

def rwStepT (R C : ℕ) (st : RWState) (f : Frame) : TimeM RWState := do
  let v ← makeViewT R C f st.eff
  let o ← rewritesAtT v
  match o with
  | none => pure st
  | some rw => rwApplyT R C st f rw

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

def rewriteAllT (R C : ℕ) (pts : List Pt) : TimeM RWState :=
  lfoldlT (rwStepT R C) ⟨pts, [], false⟩ frames

@[simp] lemma rewriteAllT_ret (R C : ℕ) (pts : List Pt) :
    (rewriteAllT R C pts).ret = rewriteAll R C pts := by
  simp [rewriteAllT, rewriteAll]

def notchLenT (R C : ℕ) (f : Frame) (removed : List (ℕ × ℕ)) (i : ℕ) : TimeM ℕ := do
  let js ← rangeT 4
  let l ← lfilterT (fun j => lcontainsT removed (f.back R C (i, j))) js
  lengthT l

@[simp] lemma notchLenT_ret (R C : ℕ) (f : Frame) (removed : List (ℕ × ℕ)) (i : ℕ) :
    (notchLenT R C f removed i).ret = notchLen R C f removed i := by
  simp [notchLenT, notchLen, rangeT, lfilterT, lengthT, lcontainsT]

def countPosT (lamT : ℕ → TimeM ℕ) : TimeM ℕ := do
  let is ← rangeT 4
  let l ← lfilterT (fun i => do let x ← lamT i; pure (decide (x > 0))) is
  lengthT l

def stairBlockT (lamT : ℕ → TimeM ℕ) (i : ℕ) : TimeM (List (ℕ × ℕ)) := do
  let li ← lamT i
  let li1 ← lamT (i + 1)
  let js ← rangeT (li - li1)
  let m ← lmapT (fun j => pure (i + 1, li1 + 1 + j)) js
  lappendT m [(i, li)]

def staircaseT (lamT : ℕ → TimeM ℕ) : TimeM (List (ℕ × ℕ)) := do
  let k ← countPosT lamT
  let rk ← rangeT k
  let rr ← lreverseT rk
  let body ← lflatMapT (stairBlockT lamT) rr
  lappendT [(k, 0)] body

lemma staircaseT_ret (lamT : ℕ → TimeM ℕ) :
    (staircaseT lamT).ret = staircase (fun i => (lamT i).ret) := by
  simp [staircaseT, stairBlockT, staircase, countPosT, rangeT, lreverseT, lflatMapT, lfilterT,
    lengthT, lappendT, lmapT]

def stairOfT (R C : ℕ) (f : Frame) (removed : List (ℕ × ℕ)) : TimeM (List (ℕ × ℕ)) := do
  let s ← staircaseT (notchLenT R C f removed)
  lmapT (fun x => pure (f.back R C x)) s

@[simp] lemma stairOfT_ret (R C : ℕ) (f : Frame) (removed : List (ℕ × ℕ)) :
    (stairOfT R C f removed).ret = stairOf R C f removed := by
  simp only [stairOfT, stairOf, ret_bind, staircaseT_ret, notchLenT_ret, lmapT, ret_pure]

def sideT (n lo hi : ℕ) : TimeM (List ℕ) := do
  let r ← rangeT n
  lfilterT (fun y => pure (decide (lo < y ∧ y + 1 + hi < n))) r

def walkStairsT (R C : ℕ) (removed : List (ℕ × ℕ)) :
    TimeM (List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ)) := do
  let tl ← stairOfT R C frameTL removed
  let tr0 ← stairOfT R C frameTR removed
  let tr ← lreverseT tr0
  let br ← stairOfT R C frameBR removed
  let bl0 ← stairOfT R C frameBL removed
  let bl ← lreverseT bl0
  pure (tl, tr, br, bl)

def sideMapT (n lo hi : ℕ) (mk : ℕ → ℕ × ℕ) : TimeM (List (ℕ × ℕ)) := do
  let l ← sideT n lo hi
  lmapT (fun y => pure (mk y)) l

def walkSidesT (R C : ℕ) (removed : List (ℕ × ℕ)) :
    TimeM (List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ)) := do
  let lTL ← notchLenT R C frameTL removed 0
  let lTR ← notchLenT R C frameTR removed 0
  let lBR ← notchLenT R C frameBR removed 0
  let lBL ← notchLenT R C frameBL removed 0
  let kTL ← countPosT (notchLenT R C frameTL removed)
  let kTR ← countPosT (notchLenT R C frameTR removed)
  let kBR ← countPosT (notchLenT R C frameBR removed)
  let kBL ← countPosT (notchLenT R C frameBL removed)
  let top ← sideMapT C lTL lTR (fun y => (0, y))
  let right ← sideMapT R kTR kBR (fun x => (x, C - 1))
  let bot1 ← sideMapT C lBL lBR (fun y => (R - 1, y))
  let bot ← lreverseT bot1
  let left1 ← sideMapT R kTL kBL (fun x => (x, 0))
  let left ← lreverseT left1
  pure (top, right, bot, left)

def walkJoinT (a b : List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ)) :
    TimeM (List (ℕ × ℕ)) := do
  let w1 ← lappendT a.1 b.1
  let w2 ← lappendT w1 a.2.1
  let w3 ← lappendT w2 b.2.1
  let w4 ← lappendT w3 a.2.2.1
  let w5 ← lappendT w4 b.2.2.1
  let w6 ← lappendT w5 a.2.2.2
  lappendT w6 b.2.2.2

def walk3T (R C : ℕ) (removed : List (ℕ × ℕ)) : TimeM (List (ℕ × ℕ)) := do
  let a ← walkStairsT R C removed
  let b ← walkSidesT R C removed
  walkJoinT a b

@[simp] lemma walk3T_ret (R C : ℕ) (removed : List (ℕ × ℕ)) :
    (walk3T R C removed).ret = walk3 R C removed := by
  simp [walk3T, walkStairsT, walkSidesT, sideMapT, walkJoinT, walk3, countPosT, sideT, rangeT, lfilterT,
    lengthT, lreverseT, lappendT, lmapT, List.append_assoc]

def positionsT (walk : List (ℕ × ℕ)) (x : ℕ × ℕ) : TimeM (List ℕ) := do
  let z ← lzipIdxT walk
  let f ← lfilterT (fun q => pure (q.1 == x)) z
  lmapT (fun q => pure q.2) f

@[simp] lemma positionsT_ret (walk : List (ℕ × ℕ)) (x : ℕ × ℕ) :
    (positionsT walk x).ret = positions walk x := by
  simp [positionsT, positions, lzipIdxT, lfilterT, lmapT]

def effAlt3T (R C : ℕ) (pts : List Pt) : TimeM Bool := do
  let st ← rewriteAllT R C pts
  let bad ← lanyT (fun q => lcontainsT st.removed q.1) st.eff
  let cs ← lmapT (fun q => pure q.1) st.eff
  let d ← ldedupT cs
  let n ← lengthT d
  let walk ← walk3T R C st.removed
  let places ← lmapT (fun q => do let p ← positionsT walk q.1; pure (p, q.2)) st.eff
  let bad2 ← lanyT (fun pl => do let m ← lengthT pl.1; pure (m != 1)) places
  let keys ← lmapT (fun pl => pure (pl.1.headD 0, pl.2)) places
  let s ← sortByKeyT keys
  let cols ← lmapT (fun y => pure y.2) s
  pure (if !st.any then false else if bad then false else if n != 4 then false
    else if bad2 then false else alternating cols)

@[simp] lemma effAlt3T_ret (R C : ℕ) (pts : List Pt) : (effAlt3T R C pts).ret = effAlt3 R C pts := by
  simp [effAlt3T, effAlt3, lanyT, lcontainsT, lmapT, ldedupT, lengthT, List.map_map,
    Function.comp_def]

/-! ### The test -/

def fires3T (R C : ℕ) (s0 t0 s1 t1 : ℕ × ℕ) : TimeM Bool := do
  let pts : List Pt := [(s0, 0), (t0, 0), (s1, 1), (t1, 1)]
  let p ← parityOkT R C pts
  let a ← t1FiresT R C pts
  let b ← t2FiresT [s0, t0, s1, t1]
  let c ← l1FiresT R C pts
  let d ← l6FiresT R C pts
  let e ← lanyT (frameFiresT R C pts) frames
  let g ← effAlt3T R C pts
  pure (!p || a || b || c || d || e || g)

@[simp] lemma fires3T_ret (R C : ℕ) (s0 t0 s1 t1 : ℕ × ℕ) :
    (fires3T R C s0 t0 s1 t1).ret = fires3 R C s0 t0 s1 t1 := by
  simp [fires3T, fires3, lanyT]

end ZZN.T

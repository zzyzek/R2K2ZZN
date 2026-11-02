-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Statement

/-!
# The step bounds: definitions

The definitions the step bounds mention beyond `ZZN.Statement`, in one module (Palomar's
`Challenge.lean` is the part of `ZZN.Statement` they use, this file, and the theorems): the
step-counting monad `TimeM`, the counted decision procedure `solvableBT` with its constant `Cdec`,
and the counted construction `solveZZNT`. Each block names the module it was moved from, where its
lemmas remain.
-/

-- ZZN.Timed.TimeM
namespace ZZN.T
structure TimeM (α : Type) where
  ret : α
  time : ℕ
instance : Monad TimeM where
  pure a := ⟨a, 0⟩
  bind m f := let r := f m.ret; ⟨r.ret, m.time + r.time⟩
end ZZN.T

-- ZZN.Timed.TimeM
namespace ZZN.T
variable {α β : Type}
def lmapT (f : α → TimeM β) (l : List α) : TimeM (List β) :=
  ⟨l.map (fun x => (f x).ret), (l.map (fun x => (f x).time + 1)).sum⟩
def lfilterT (p : α → TimeM Bool) (l : List α) : TimeM (List α) :=
  ⟨l.filter (fun x => (p x).ret), (l.map (fun x => (p x).time + 1)).sum⟩
def lallT (p : α → TimeM Bool) (l : List α) : TimeM Bool :=
  ⟨l.all (fun x => (p x).ret), (l.map (fun x => (p x).time + 1)).sum⟩
def lanyT (p : α → TimeM Bool) (l : List α) : TimeM Bool :=
  ⟨l.any (fun x => (p x).ret), (l.map (fun x => (p x).time + 1)).sum⟩
def lfindT (p : α → TimeM Bool) (l : List α) : TimeM (Option α) :=
  ⟨l.find? (fun x => (p x).ret), (l.map (fun x => (p x).time + 1)).sum⟩
def lfilterMapT (f : α → TimeM (Option β)) (l : List α) : TimeM (List β) :=
  ⟨l.filterMap (fun x => (f x).ret), (l.map (fun x => (f x).time + 1)).sum⟩
def lflatMapT (f : α → TimeM (List β)) (l : List α) : TimeM (List β) :=
  ⟨l.flatMap (fun x => (f x).ret), (l.map (fun x => let r := f x; r.time + r.ret.length + 1)).sum⟩
def lfoldlT (f : β → α → TimeM β) : β → List α → TimeM β
  | b, [] => ⟨b, 0⟩
  | b, x :: l => let r := f b x; let s := lfoldlT f r.ret l; ⟨s.ret, r.time + 1 + s.time⟩
def lengthT (l : List α) : TimeM ℕ := ⟨l.length, l.length + 1⟩
def lcontainsT [BEq α] (l : List α) (x : α) : TimeM Bool := ⟨l.contains x, l.length + 1⟩
def leraseT [BEq α] (l : List α) (x : α) : TimeM (List α) := ⟨l.erase x, l.length + 1⟩
def lappendT (l m : List α) : TimeM (List α) := ⟨l ++ m, l.length + 1⟩
def lreverseT (l : List α) : TimeM (List α) := ⟨l.reverse, l.length + 1⟩
def lsumT (l : List ℤ) : TimeM ℤ := ⟨l.sum, l.length + 1⟩
def lzipIdxT (l : List α) : TimeM (List (α × ℕ)) := ⟨l.zipIdx, l.length + 1⟩
def lzipT (l : List α) (m : List β) : TimeM (List (α × β)) := ⟨l.zip m, l.length + 1⟩
def lfindIdxT (p : α → Bool) (l : List α) : TimeM (Option ℕ) := ⟨l.findIdx? p, l.length + 1⟩
def lmodifyT (l : List α) (i : ℕ) (f : α → α) : TimeM (List α) := ⟨l.modify i f, l.length + 1⟩
def lgetT [Inhabited α] (l : List α) (i : ℕ) : TimeM α := ⟨l[i]!, l.length + 1⟩
def rangeT (n : ℕ) : TimeM (List ℕ) := ⟨List.range n, n + 1⟩
def ldedupT [DecidableEq α] (l : List α) : TimeM (List α) := ⟨l.dedup, l.length ^ 2 + 1⟩
def lnodupT [DecidableEq α] (l : List α) : TimeM Bool := ⟨decide l.Nodup, l.length ^ 2 + 1⟩
def infix2T [DecidableEq α] (a b : α) (l : List α) : TimeM Bool :=
  ⟨decide ([a, b] <:+: l), l.length + 1⟩
def lgetLastT (l : List α) : TimeM (Option α) := ⟨l.getLast?, l.length + 1⟩
def fmemT (x : ℕ) (s : Finset ℕ) : TimeM Bool := ⟨decide (x ∈ s), s.card + 1⟩
def feraseT (s : Finset ℕ) (x : ℕ) : TimeM (Finset ℕ) := ⟨s.erase x, s.card + 1⟩
def ffilterT (p : ℕ → Bool) (s : Finset ℕ) : TimeM (Finset ℕ) := ⟨s.filter (fun x => p x = true), s.card + 1⟩
def frangeFilterT (n : ℕ) (p : ℕ → TimeM Bool) : TimeM (Finset ℕ) :=
  ⟨(Finset.range n).filter (fun y => (p y).ret = true), ((List.range n).map (fun y => (p y).time + 1)).sum⟩
end ZZN.T

-- ZZN.Timed.Band
namespace ZZN.T
open ZZN GridHam
def stretchT (r : ℕ) : List Coord → TimeM (List Coord)
  | [] => pure []
  | [a] => ⟨[shiftAt r a], 1⟩
  | a :: b :: l => do
    let s ← stretchT r (b :: l)
    ⟨shiftAt r a :: (gap r a b ++ s), 3⟩
def insBT (a b : Coord) (X : List Coord) : List Coord → TimeM (List Coord)
  | x :: y :: l =>
    if x = a ∧ y = b then ⟨x :: (X ++ y :: l), X.length + 1⟩ else do
      let s ← insBT a b X (y :: l)
      ⟨x :: s, 1⟩
  | [x] => pure [x]
  | [] => pure []
def spliceET (P Q : List Coord) (a b : Coord) (X : List Coord) : TimeM (List Coord × List Coord) := do
  let t ← infix2T a b P
  if t then do
    let l ← insBT a b X P
    pure (l, Q)
  else do
    let l ← insBT a b X Q
    pure (P, l)
def absorbET (r y y' : ℕ) (P Q : List Coord) : TimeM (List Coord × List Coord) := do
  let t1 ← infix2T (r + 1, y') (r + 2, y') P
  let t2 ← infix2T (r + 1, y') (r + 2, y') Q
  if t1 || t2 then spliceET P Q (r + 1, y') (r + 2, y') [(r + 1, y), (r + 2, y)]
  else spliceET P Q (r + 2, y') (r + 1, y') [(r + 2, y), (r + 1, y)]
def flipET (r y : ℕ) (P Q : List Coord) : TimeM (List Coord × List Coord) := do
  let t1 ← infix2T (r, y) (r, y + 1) P
  let t2 ← infix2T (r, y) (r, y + 1) Q
  if t1 || t2 then
    spliceET P Q (r, y) (r, y + 1) [(r + 1, y), (r + 2, y), (r + 2, y + 1), (r + 1, y + 1)]
  else spliceET P Q (r, y + 1) (r, y) [(r + 1, y + 1), (r + 2, y + 1), (r + 2, y), (r + 1, y)]
def sweepLeftET (r : ℕ) : ℕ → Finset ℕ → List Coord → List Coord → TimeM (List Coord × List Coord)
  | 0, _, P, Q => pure (P, Q)
  | L + 1, U, P, Q => do
    let m ← fmemT L U
    if m then do
      let PQ ← absorbET r L (L + 1) P Q
      let U' ← feraseT U L
      sweepLeftET r L U' PQ.1 PQ.2
    else sweepLeftET r L U P Q
def sweepRightET (r h : ℕ) : ℕ → ℕ → Finset ℕ → List Coord → List Coord →
    TimeM (List Coord × List Coord)
  | 0, _, _, P, Q => pure (P, Q)
  | n + 1, R, U, P, Q => do
    let m ← fmemT (R + 1) U
    if m then do
      let PQ ← absorbET r (R + 1) R P Q
      let U' ← feraseT U (R + 1)
      sweepRightET r h n (R + 1) U' PQ.1 PQ.2
    else if R + 1 < h then sweepRightET r h n (R + 1) U P Q
    else pure (P, Q)
def usedT (l : List Coord) (u v : Coord) : TimeM Bool := do
  let a ← infix2T u v l
  let b ← infix2T v u l
  pure (a || b)
def crossT (p q : List Coord) (r y : ℕ) : TimeM Bool := do
  let a ← usedT p (r, y) (r + 1, y)
  let b ← usedT q (r, y) (r + 1, y)
  pure (a || b)
def seedAtT (h : ℕ) (p q : List Coord) (r R : ℕ) : TimeM Bool := do
  let c0 ← crossT p q r (R - 1)
  let c1 ← crossT p q r R
  let u0 ← usedT p (r, R - 1) (r, R)
  let u1 ← usedT q (r, R - 1) (r, R)
  pure (((decide (R = 0) || c0) && (decide (R = h) || c1)) ||
    (decide (1 ≤ R) && decide (R < h) && !c0 && !c1 && (u0 || u1)))
def cond1T (h : ℕ) (p q : List Coord) (r R : ℕ) : TimeM Bool := do
  let c0 ← crossT p q r (R - 1)
  let c1 ← crossT p q r R
  pure ((decide (R = 0) || c0) && (decide (R = h) || c1))
/-- The counted band extension, given the starting state. -/
def bandFromT (I : Inst) (r : ℕ) (p q : List Coord) (U0 : Finset ℕ) (P0 Q0 : List Coord) (R : ℕ) :
    TimeM (List Coord × List Coord) := do
  let c1 ← cond1T I.h p q r R
  if c1 then
    if R = 0 then sweepRightET r I.h (I.h - 0) 0 U0 P0 Q0
    else if R = I.h then sweepLeftET r (R - 1) U0 P0 Q0
    else do
      let A ← sweepLeftET r (R - 1) U0 P0 Q0
      let U1 ← ffilterT (fun z => decide (R - 1 < z)) U0
      sweepRightET r I.h (I.h - R) R U1 A.1 A.2
  else do
    let B ← flipET r (R - 1) P0 Q0
    let U1 ← feraseT U0 (R - 1)
    let U2 ← feraseT U1 (R - 1 + 1)
    let C ← sweepLeftET r (R - 1) U2 B.1 B.2
    let U3 ← ffilterT (fun z => decide (R - 1 < z)) U2
    sweepRightET r I.h (I.h - (R - 1 + 1)) (R - 1 + 1) U3 C.1 C.2
def bandExtET (I : Inst) (r : ℕ) (p q : List Coord) : TimeM (List Coord × List Coord) := do
  let P0 ← stretchT r p
  let Q0 ← stretchT r q
  let U0 ← frangeFilterT I.h (fun y => do let c ← crossT p q r y; pure !c)
  let rs ← rangeT (I.h + 1)
  let o ← lfindT (seedAtT I.h p q r) rs
  match o with
  | none => pure (P0, Q0)
  | some R => bandFromT I r p q U0 P0 Q0 R
end ZZN.T

-- ZZN.Timed.Catalogue
namespace ZZN.T
open ZZN
def atT (v : View) (r c : ℕ) : TimeM (Option ℕ) := do
  let o ← lfindT (fun q => pure (q.1 == (r, c))) v.pts
  pure (match o with | some q => some q.2 | none => none)
def emptyT (v : View) (cells : List (ℕ × ℕ)) : TimeM Bool :=
  lallT (fun x => do let o ← atT v x.1 x.2; pure o.isNone) cells
def makeViewT (R C : ℕ) (f : Frame) (pts : List Pt) : TimeM View := do
  let ps ← lmapT (fun q => pure (f.to R C q.1, q.2)) pts
  pure ⟨f.H R C, f.W R C, ps⟩
def parityOkT (R C : ℕ) (pts : List Pt) : TimeM Bool := do
  let l ← lmapT (fun q => pure (sgn q.1)) pts
  let s ← lsumT l
  pure (s == 2 * (((R * C) % 2 : ℕ) : ℤ))
def sortByKeyT : List (ℕ × ℕ) → TimeM (List (ℕ × ℕ))
  | [] => pure []
  | x :: xs => do
    let s ← sortByKeyT xs
    let a ← lfilterT (fun y => pure (decide (y.1 < x.1))) s
    let b ← lfilterT (fun y => pure (decide (¬ (y.1 < x.1)))) s
    let ab ← lappendT a [x]
    lappendT ab b
def t1FiresT (R C : ℕ) (pts : List Pt) : TimeM Bool := do
  let idx ← lmapT (fun q => pure (perimIndex R C q.1)) pts
  let ok ← lallT (fun o => pure o.isSome) idx
  let keys ← lmapT (fun o => pure (o.getD 0)) idx
  let cols ← lmapT (fun q => pure q.2) pts
  let z ← lzipT keys cols
  let s ← sortByKeyT z
  let c ← lmapT (fun y => pure y.2) s
  pure (ok && alternating c)
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
def l6FiresT (R C : ℕ) (pts : List Pt) : TimeM Bool := do
  let cl ← l6ClosuresT R C pts
  let c0 ← lcontainsT cl 0
  let c1 ← lcontainsT cl 1
  pure (c0 && c1 && decide (R * C > 6))
def testL2T (v : View) : TimeM Bool := do
  let x ← atT v 0 1
  let y ← atT v 1 0
  match x, y with
  | some a, some b => do let e ← emptyT v [(0, 0)]; pure (a != b && e)
  | _, _ => pure false
def testL3T (v : View) : TimeM Bool := do
  let x ← atT v 0 2
  match x with
  | some a => do
    let y ← atT v 1 1
    let z ← atT v 1 0
    let e ← emptyT v [(0, 0), (0, 1)]
    pure (y == some a && z == some (1 - a) && e)
  | none => pure false
def testL4T (v : View) : TimeM Bool := do
  let x ← atT v 0 0
  match x with
  | some a => do
    let y ← atT v 1 1
    let z ← atT v 0 2
    let e ← emptyT v [(0, 1), (1, 0)]
    pure (y == some a && z == some (1 - a) && decide (v.H ≥ 3) && e)
  | none => pure false
def testL5T (v : View) : TimeM Bool := do
  let x ← atT v 0 0
  match x with
  | some b => do
    let y ← atT v 0 2
    let z ← atT v 2 0
    let e ← emptyT v [(0, 1), (1, 0), (1, 1)]
    pure (y == some (1 - b) && z == some (1 - b) && e)
  | none => pure false
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
def sameSetT (a b : List (ℕ × ℕ)) : TimeM Bool := do
  let la ← lengthT a
  let lb ← lengthT b
  let al ← lallT (fun x => lcontainsT b x) a
  pure (la == lb && al)
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
def moveFirstT (e : List Pt) (m : (ℕ × ℕ) × (ℕ × ℕ)) : TimeM (List Pt) := do
  let i ← lfindIdxT (fun q => q.1 == m.1) e
  match i with
  | some i => lmodifyT e i (fun q => (m.2, q.2))
  | none => pure e
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
def rewriteAllT (R C : ℕ) (pts : List Pt) : TimeM RWState :=
  lfoldlT (rwStepT R C) ⟨pts, [], false⟩ frames
def notchLenT (R C : ℕ) (f : Frame) (removed : List (ℕ × ℕ)) (i : ℕ) : TimeM ℕ := do
  let js ← rangeT 4
  let l ← lfilterT (fun j => lcontainsT removed (f.back R C (i, j))) js
  lengthT l
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
def stairOfT (R C : ℕ) (f : Frame) (removed : List (ℕ × ℕ)) : TimeM (List (ℕ × ℕ)) := do
  let s ← staircaseT (notchLenT R C f removed)
  lmapT (fun x => pure (f.back R C x)) s
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
def positionsT (walk : List (ℕ × ℕ)) (x : ℕ × ℕ) : TimeM (List ℕ) := do
  let z ← lzipIdxT walk
  let f ← lfilterT (fun q => pure (q.1 == x)) z
  lmapT (fun q => pure q.2) f
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
end ZZN.T

-- ZZN.Timed.Lift
namespace ZZN.T
open ZZN GridHam
def freeLineBT (I : Inst) (k : ℕ) : TimeM Bool := lallT (fun e => pure (e.1 != k)) I.ends
def endBelowBT (I : Inst) (k : ℕ) : TimeM Bool := lanyT (fun e => pure (decide (e.1 < k))) I.ends
def endAboveBT (I : Inst) (k : ℕ) : TimeM Bool := lanyT (fun e => pure (decide (k < e.1))) I.ends
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
def findRedT (I : Inst) : TimeM (Option ℕ) := do
  let rs ← rangeT I.w
  lfindT (redBT I) rs
def liftET (I : Inst) (d : ℕ) (p q : List Coord) : TimeM (List Coord × List Coord) := do
  let f ← freeLineBT I (d + 2)
  if d + 3 ≤ I.w ∧ f = true then bandExtET (I.deleteAt d) d p q
  else bandExtET (I.deleteAt d) (d - 1) p q
def chainT : List Coord → TimeM Bool
  | [] => pure true
  | [_] => pure true
  | a :: b :: rest => do
    let r ← chainT (b :: rest)
    ⟨adjacentB a b && r, 1⟩
def isPathT (w h : ℕ) (s t : Coord) (p : List Coord) : TimeM Bool := do
  let l ← lgetLastT p
  let n ← lnodupT p
  let b ← lallT (fun v => pure (decide (v.1 < w) && decide (v.2 < h))) p
  let c ← chainT p
  pure (decide (p.head? = some s) && decide (l = some t) && n && b && c)
def solBT (I : Inst) (p q : List Coord) : TimeM Bool := do
  let a ← isPathT I.w I.h I.s0 I.t0 p
  let b ← isPathT I.w I.h I.s1 I.t1 q
  let pq ← lappendT p q
  let n ← lnodupT pq
  let lp ← lengthT p
  let lq ← lengthT q
  pure (a && b && n && (lp + lq == I.w * I.h))
def checkET (I : Inst) (o : Option (List Coord × List Coord)) : TimeM (Option (List Coord × List Coord)) :=
  match o with
  | some pq => do
    let b ← solBT I pq.1 pq.2
    pure (if b then some pq else none)
  | none => pure none
end ZZN.T

-- ZZN.Timed.Solve
namespace ZZN.T
open ZZN GridHam
abbrev Sol := Option (List Coord × List Coord)
def swapT (l : List Coord) : TimeM (List Coord) := lmapT (fun x => pure x.swap) l
/-- Lift a solution of `I.deleteAt d` and check it. -/
def stepT (I : Inst) (d : ℕ) : Sol → TimeM Sol
  | some pq => do
    let l ← liftET I d pq.1 pq.2
    checkET I (some l)
  | none => pure none
/-- Lift a solution of `I.transpose.deleteAt d`, transpose it back and check it. -/
def stepTT (I : Inst) (d : ℕ) : Sol → TimeM Sol
  | some pq => do
    let l ← liftET I.transpose d pq.1 pq.2
    let a ← swapT l.1
    let b ← swapT l.2
    checkET I (some (a, b))
  | none => pure none
def solveRecT (thinT : Inst → TimeM Sol) : ℕ → Inst → TimeM Sol
  | 0, _ => pure none
  | n + 1, I =>
    if I.w ≤ 10 ∨ I.h ≤ 10 then thinT I >>= checkET I else do
    let f ← findRedT I
    match f with
    | some d => solveRecT thinT n (I.deleteAt d) >>= stepT I d
    | none => do
      let g ← findRedT I.transpose
      match g with
      | some d => solveRecT thinT n (I.transpose.deleteAt d) >>= stepTT I d
      | none => thinT I >>= checkET I
def solveZT (thinT : Inst → TimeM Sol) (I : Inst) : TimeM Sol :=
  solveRecT thinT (I.w + I.h) I >>= checkET I
end ZZN.T

-- ZZN.Timed.Thin
namespace ZZN.T
open ZZN ZZN.Thin GridHam
def insSortedT (x : ℕ) : List ℕ → TimeM (List ℕ)
  | [] => pure [x]
  | y :: l => if x ≤ y then ⟨x :: y :: l, 1⟩ else do
      let r ← insSortedT x l
      ⟨y :: r, 1⟩
def closePT (a b x y : ℕ) (rest : List ℕ) (dn : ℕ) : TimeM (Option St) :=
  if isTerm a b x && isTerm a b y then
    pure (if colE a b x != colE a b y then none
      else if (dn / 2 ^ colE a b x) % 2 == 1 then none
      else some (rest, dn + 2 ^ colE a b x))
  else do
    let l ← insSortedT (mkP x y) rest
    pure (some (l, dn))
/-- The pieces left after removing the incoming plugs (at most two `erase`s). -/
def restT (ps : List ℕ) (pu pl : Option ℕ) : TimeM (List ℕ) :=
  match pu, pl with
  | some u, some l => do let r ← leraseT ps u; leraseT r l
  | some u, none => leraseT ps u
  | none, some l => leraseT ps l
  | none, none => pure ps
/-- The (at most three) incoming and endpoint ends, then the (at most two) outgoing ones. -/
def endsL (a b c : ℕ) (e pu pl : Option ℕ) : List ℕ :=
  (match pu with | some z => [other c z] | none => []) ++
    (match pl with | some z => [other b z] | none => []) ++
    (match e with | some col => [termE a b col] | none => [])
def closeOptT (a b : ℕ) (ins outs : List ℕ) (rest : List ℕ) (dn : ℕ) : TimeM (Option St) := do
  let l ← lappendT ins outs
  match l with
  | [x, y] => closePT a b x y rest dn
  | [] => pure none
  | [_] => pure none
  | _ :: _ :: _ :: _ => pure none
def optsL (k : ℕ) (down right : ℕ) : List (List ℕ) :=
  match k with
  | 0 => [[]]
  | 1 => [[down], [right]]
  | _ => [[down, right]]
def stepTailT (a b : ℕ) (e : Option ℕ) (r c : ℕ) (s : St) (pu pl : Option ℕ) : TimeM (List St) :=
  let down := if r + 1 < a then c else exitE b (a + (b - 1 - c))
  let right := if c + 1 < b then b else exitE b r
  let nin := (if pu.isSome then 1 else 0) + (if pl.isSome then 1 else 0)
  let deg := if e.isSome then 1 else 2
  if deg < nin then pure [] else
  if pu.isSome && pu == pl then pure [] else do
  let rest ← restT s.1 pu pl
  lfilterMapT (fun outs => closeOptT a b (endsL a b c e pu pl) outs rest s.2) (optsL (deg - nin) down right)
/-- The piece with an end at code `k`, unless `skip` (border cell). -/
def lookT (skip : Bool) (k : ℕ) (ps : List ℕ) : TimeM (Option ℕ) :=
  if skip then pure none else lfindT (fun z => pure (hasEnd k z)) ps
def stepCellT (a b : ℕ) (e : Option ℕ) (r c : ℕ) (s : St) : TimeM (List St) := do
  let pu ← lookT (r == 0) c s.1
  let pl ← lookT (c == 0) b s.1
  stepTailT a b e r c s pu pl
def noExitT (a b : ℕ) (s : St) : TimeM Bool :=
  lallT (fun z => pure (okEnd a b (lo z) && okEnd a b (hi z))) s.1
/-- The colour of a found endpoint record. -/
def optSnd (o : Option ((ℕ × ℕ) × ℕ)) : Option ℕ := match o with | some q => some q.2 | none => none
def stageT (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (S : List St) (i : ℕ) : TimeM (List St) := do
  let o ← lfindT (fun q => pure (q.1 == cell b i)) tm
  let e := optSnd o
  let l ← lflatMapT (stepCellT a b e (cell b i).1 (cell b i).2) S
  let d ← ldedupT l
  lfilterT (noExitT a b) d
def insideT (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) : TimeM (List St) := do
  let is ← rangeT (a * b)
  lfoldlT (stageT a b tm) [([], 0)] is
def dpAcceptT (J : Inst) : TimeM Bool := do
  let S ← insideT J.w J.h (tmOf J)
  lcontainsT S ([], 3)
def thinBFT (J : Inst) : TimeM Bool :=
  if J.h ≤ J.w then dpAcceptT J else dpAcceptT J.transpose
end ZZN.T

-- ZZN.Timed.ThinCount
namespace ZZN.T
open ZZN ZZN.Thin GridHam
def Q (b : ℕ) : ℕ := (b + 3) ^ 2
def Nst (b : ℕ) : ℕ := 4 * (Q b + 1) ^ Q b
end ZZN.T

-- ZZN.Timed.ThinCost
namespace ZZN.T
open ZZN ZZN.Thin GridHam
variable {a b : ℕ} {J : Inst}
def Kst (b : ℕ) : ℕ := 5 + Nst b * (6 * Q b + 19) + 4 * Nst b ^ 2 + 1 + 2 * Nst b * (Q b + 2)
end ZZN.T

-- ZZN.Timed.ThinWit
namespace ZZN.T
open ZZN ZZN.Thin GridHam
/-- Equality of two lists of numbers, one step per matching entry. -/
def lbeqT : List ℕ → List ℕ → TimeM Bool
  | [], [] => pure true
  | x :: l, y :: m => if x = y then do
      let r ← lbeqT l m
      ⟨r, 1⟩
    else pure false
  | [], _ :: _ => pure false
  | _ :: _, [] => pure false
/-- Equality of two states. -/
def stEqT (s t : St) : TimeM Bool := do
  let r ← lbeqT s.1 t.1
  pure (r && decide (s.2 = t.2))
/-- Keep the first entry of each state not among `seen`. -/
def dedupKeyAuxT : List St → List (St × Wit) → TimeM (List (St × Wit))
  | _, [] => pure []
  | seen, x :: l => do
      let m ← lanyT (fun t => stEqT t x.1) seen
      if m then dedupKeyAuxT seen l else do
        let r ← dedupKeyAuxT (x.1 :: seen) l
        pure (x :: r)
def dedupKeyT (l : List (St × Wit)) : TimeM (List (St × Wit)) := dedupKeyAuxT [] l
/-- The stored segment of piece `z` (`[]` if none). -/
def lookDT (l : List (ℕ × List Coord)) (z : ℕ) : TimeM (List Coord) := do
  let o ← lfindT (fun q => pure (q.1 == z)) l
  pure (match o with | some q => q.2 | none => [])
def orientST (e z : ℕ) (L : List Coord) : TimeM (List Coord) :=
  if lo z = e then lreverseT L else pure L
def orientNT (x y : ℕ) (L : List Coord) : TimeM (List Coord) :=
  if x ≤ y then pure L else lreverseT L
def orientPT (J : Inst) (col : ℕ) (L : List Coord) : TimeM (List Coord) :=
  if L.head? = some (ends2 J col).1 then pure L else lreverseT L
/-- The new segment through cell `(r, c)`. -/
def segNewT (b r c : ℕ) (w : List (ℕ × List Coord)) (pu pl : Option ℕ) : TimeM (List Coord) :=
  match pu, pl with
  | some zu, some zl => do
    let Lu0 ← lookDT w zu
    let Lu ← orientST c zu Lu0
    let Ll0 ← lookDT w zl
    let Ll ← orientST b zl Ll0
    let t ← lappendT Lu [(r, c)]
    let rl ← lreverseT Ll
    lappendT t rl
  | some zu, none => do
    let Lu0 ← lookDT w zu
    let Lu ← orientST c zu Lu0
    lappendT Lu [(r, c)]
  | none, some zl => do
    let Ll0 ← lookDT w zl
    let Ll ← orientST b zl Ll0
    lappendT Ll [(r, c)]
  | none, none => pure [(r, c)]
def closeWitT (J : Inst) (a b x y : ℕ) (Ln : List Coord) (sgR : List (ℕ × List Coord))
    (d : List Coord × List Coord) : TimeM Wit :=
  if isTerm a b x && isTerm a b y then do
    let P ← orientPT J (colE a b x) Ln
    pure (sgR, setDp d (colE a b x) P)
  else do
    let L ← orientNT x y Ln
    pure ((mkP x y, L) :: sgR, d)
def closeOptGT (a b : ℕ) (ins outs rest : List ℕ) (dn : ℕ) : TimeM (Option ((ℕ × ℕ) × St)) := do
  let l ← lappendT ins outs
  match l with
  | [x, y] => do
    let o ← closePT a b x y rest dn
    pure (o.map fun s' => ((x, y), s'))
  | [] => pure none
  | [_] => pure none
  | _ :: _ :: _ :: _ => pure none
/-- `stepCellG` after the two lookups. -/
def stepTailGT (a b : ℕ) (e : Option ℕ) (r c : ℕ) (s : St) (pu pl : Option ℕ) :
    TimeM (List ((ℕ × ℕ) × St)) :=
  if degOf e < ninOf pu pl then pure [] else
  if pu.isSome && pu == pl then pure [] else do
  let rest ← restT s.1 pu pl
  lfilterMapT (fun outs => closeOptGT a b (endsL a b c e pu pl) outs rest s.2) (optsOf a b r c e pu pl)
def stepCellWT (J : Inst) (a b : ℕ) (e : Option ℕ) (r c : ℕ) (sw : St × Wit) :
    TimeM (List (St × Wit)) := do
  let pu ← lookT (r == 0) c sw.1.1
  let pl ← lookT (c == 0) b sw.1.1
  let Ln ← segNewT b r c sw.2.1 pu pl
  let sgR ← lfilterT (fun q => pure (pu != some q.1 && pl != some q.1)) sw.2.1
  let G ← stepTailGT a b e r c sw.1 pu pl
  lmapT (fun g => do
    let w ← closeWitT J a b g.1.1 g.1.2 Ln sgR sw.2.2
    pure (g.2, w)) G
def stageWT (J : Inst) (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (S : List (St × Wit)) (i : ℕ) :
    TimeM (List (St × Wit)) := do
  let o ← lfindT (fun q => pure (q.1 == cell b i)) tm
  let e := optSnd o
  let l ← lflatMapT (stepCellWT J a b e (cell b i).1 (cell b i).2) S
  let f ← lfilterT (fun sw => noExitT a b sw.1) l
  dedupKeyT f
def insideWT (J : Inst) (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) : TimeM (List (St × Wit)) := do
  let is ← rangeT (a * b)
  lfoldlT (stageWT J a b tm) [(([], 0), ([], ([], [])))] is
def solveDPT (J : Inst) : TimeM (Option (List Coord × List Coord)) := do
  let S ← insideWT J J.w J.h (tmOf J)
  let o ← lfindT (fun sw => stEqT sw.1 ([], 3)) S
  pure (match o with | some sw => some sw.2.2 | none => none)
def swapPairT (pq : List Coord × List Coord) : TimeM (List Coord × List Coord) := do
  let p ← lmapT (fun x => pure x.swap) pq.1
  let q ← lmapT (fun x => pure x.swap) pq.2
  pure (p, q)
/-- **The counted solver.** -/
def thinSolveWT (J : Inst) : TimeM (Option (List Coord × List Coord)) :=
  if J.h ≤ J.w then solveDPT J else do
    let o ← solveDPT J.transpose
    match o with
    | some pq => do
      let r ← swapPairT pq
      pure (some r)
    | none => pure none
end ZZN.T

-- ZZN.Timed.ThinWitCost
namespace ZZN.T
open ZZN ZZN.Thin GridHam
/-- The per-cell constant: a stage costs at most `(a b + 1) Ks b` steps. -/
def Ks (b : ℕ) : ℕ :=
  4 + Nst b * (9 * Q b + 31) + 2 * Nst b * (Q b + 2) + 2 * Nst b * (2 * Nst b * (Q b + 2) + 1) + 9 * Nst b
/-- The constant of the time bound, a function of the short side only. -/
def Kw (b : ℕ) : ℕ := Ks b + Nst b + 4
end ZZN.T

-- ZZN.Timed.Construct
namespace ZZN.T
open ZZN GridHam
def solveZZNT (I : Inst) : TimeM Sol := solveZT thinSolveWT I
end ZZN.T

-- ZZN.Timed.Main
namespace ZZN.T
open ZZN ZZN.Thin
def solvableBT (J : Inst) : TimeM Bool :=
  if 11 ≤ J.w ∧ 11 ≤ J.h then do
    let f ← fires3T J.w J.h J.s0 J.t0 J.s1 J.t1
    pure !f
  else thinBFT J
/-- The constant of the time bound. -/
def Cdec : ℕ := Kst 10 + Nst 10 + 300003
end ZZN.T

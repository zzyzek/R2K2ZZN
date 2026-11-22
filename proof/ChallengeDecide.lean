/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import Mathlib

@[expose] public section

-- Undocumented copies (1 000-line limit) of the definitions the statements use, from
-- ZZN.Statement
-- ZZN.TimedStatement
-- ZZN.Timed.SortKeyG
-- ZZN.Timed.ThinRope
-- ZZN.Timed.ThinWord
-- ZZN.Timed.ThinRopeCost
-- ZZN.Timed.DecideR
namespace GridHam
abbrev Coord := ℕ × ℕ
def InBounds (width height : ℕ) (v : Coord) : Prop :=
  v.1 < width ∧ v.2 < height
def Adjacent (v w : Coord) : Prop :=
  (v.1 = w.1 ∧ (v.2 + 1 = w.2 ∨ w.2 + 1 = v.2)) ∨
  (v.2 = w.2 ∧ (v.1 + 1 = w.1 ∨ w.1 + 1 = v.1))
instance : DecidableRel Adjacent := fun v w => by unfold Adjacent; infer_instance
def adjacentB (v w : Coord) : Bool := decide (Adjacent v w)
def chainAdjacent : List Coord → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => adjacentB a b && chainAdjacent (b :: rest)
end GridHam
namespace ZZN
open GridHam
def IsPath (w h : ℕ) (s t : Coord) (p : List Coord) : Prop :=
  p.head? = some s ∧
  p.getLast? = some t ∧
  p.Nodup ∧
  (∀ v ∈ p, InBounds w h v) ∧
  chainAdjacent p = true
structure Inst where
  w  : ℕ
  h  : ℕ
  s0 : Coord
  t0 : Coord
  s1 : Coord
  t1 : Coord
def Inst.WellFormed (I : Inst) : Prop :=
  InBounds I.w I.h I.s0 ∧ InBounds I.w I.h I.t0 ∧
  InBounds I.w I.h I.s1 ∧ InBounds I.w I.h I.t1 ∧
  I.s0 ≠ I.t0 ∧ I.s0 ≠ I.s1 ∧ I.s0 ≠ I.t1 ∧
  I.t0 ≠ I.s1 ∧ I.t0 ≠ I.t1 ∧ I.s1 ≠ I.t1
def IsSolution (I : Inst) (p q : List Coord) : Prop :=
  IsPath I.w I.h I.s0 I.t0 p ∧
  IsPath I.w I.h I.s1 I.t1 q ∧
  (∀ v ∈ p, v ∉ q) ∧
  (∀ v, InBounds I.w I.h v → v ∈ p ∨ v ∈ q)
def Solvable (I : Inst) : Prop :=
  ∃ p q, IsSolution I p q
end ZZN
namespace ZZN
abbrev Pt := (ℕ × ℕ) × ℕ
structure Frame where
  fr : Bool
  fc : Bool
  tr : Bool
def Frame.H (R C : ℕ) (f : Frame) : ℕ := if f.tr then C else R
def Frame.W (R C : ℕ) (f : Frame) : ℕ := if f.tr then R else C
def Frame.to (R C : ℕ) (f : Frame) (p : ℕ × ℕ) : ℕ × ℕ :=
  let a := if f.fr then R - 1 - p.1 else p.1
  let b := if f.fc then C - 1 - p.2 else p.2
  if f.tr then (b, a) else (a, b)
def Frame.back (R C : ℕ) (f : Frame) (q : ℕ × ℕ) : ℕ × ℕ :=
  let r := if f.tr then q.2 else q.1
  let c := if f.tr then q.1 else q.2
  ((if f.fr then R - 1 - r else r), (if f.fc then C - 1 - c else c))
def frames : List Frame :=
  [false, true].flatMap fun fr => [false, true].flatMap fun fc => [false, true].map fun tr =>
    ⟨fr, fc, tr⟩
structure View where
  H : ℕ
  W : ℕ
  pts : List Pt
def sgn (p : ℕ × ℕ) : ℤ := if (p.1 + p.2) % 2 == 0 then 1 else -1
def perimIndex (R C : ℕ) (p : ℕ × ℕ) : Option ℕ :=
  if p.1 == 0 then some p.2
  else if p.2 == C - 1 then some ((C - 1) + p.1)
  else if p.1 == R - 1 then some ((C - 1) + (R - 1) + (C - 1 - p.2))
  else if p.2 == 0 then some (2 * (C - 1) + (R - 1) + (R - 1 - p.1))
  else none
def alternating (cols : List ℕ) : Bool :=
  match cols with
  | [a, b, c, d] => a != b && b != c && c != d
  | _ => false
def CORNER4 : List (List (ℕ × ℕ) × List (ℕ × ℕ)) := [
  ([(0, 1), (0, 3)], [(1, 1), (1, 3)]), ([(0, 1), (0, 6)], [(0, 7), (1, 1)]),
  ([(0, 1), (0, 6)], [(1, 1), (7, 0)]), ([(0, 1), (0, 6)], [(1, 2), (6, 0)]),
  ([(0, 1), (0, 7)], [(1, 1), (6, 0)]), ([(0, 1), (1, 3)], [(1, 1), (1, 2)]),
  ([(0, 1), (1, 3)], [(1, 2), (2, 2)]), ([(0, 1), (1, 3)], [(1, 2), (3, 1)]),
  ([(0, 1), (2, 2)], [(1, 1), (1, 2)]), ([(0, 1), (2, 2)], [(1, 2), (3, 1)]),
  ([(0, 1), (2, 2)], [(1, 3), (3, 0)]), ([(0, 1), (7, 0)], [(1, 1), (6, 0)]),
  ([(0, 2), (1, 1)], [(2, 1), (3, 0)]), ([(0, 2), (2, 0)], [(1, 2), (2, 1)]),
  ([(0, 3), (2, 1)], [(3, 1), (4, 0)]), ([(0, 6), (2, 1)], [(1, 2), (6, 0)]),
  ([(1, 2), (2, 2)], [(1, 3), (2, 1)]), ([(1, 2), (3, 1)], [(1, 3), (2, 1)]),
  ([(0, 1), (1, 2)], [(0, 4), (2, 2)]), ([(0, 1), (1, 2)], [(0, 4), (3, 1)]),
  ([(0, 1), (1, 2)], [(1, 3), (2, 0)]), ([(0, 1), (1, 2)], [(1, 3), (4, 0)]),
  ([(0, 1), (1, 2)], [(2, 0), (2, 2)]), ([(0, 1), (1, 2)], [(2, 2), (4, 0)]),
  ([(0, 1), (1, 2)], [(3, 1), (4, 0)]), ([(0, 1), (1, 3)], [(0, 3), (0, 4)]),
  ([(0, 1), (1, 3)], [(0, 3), (2, 0)]), ([(0, 1), (1, 3)], [(0, 3), (4, 0)]),
  ([(0, 1), (2, 1)], [(0, 2), (2, 2)]), ([(0, 1), (2, 1)], [(0, 2), (3, 1)]),
  ([(0, 1), (2, 1)], [(0, 4), (1, 3)]), ([(0, 1), (2, 1)], [(0, 4), (2, 2)]),
  ([(0, 1), (2, 1)], [(0, 4), (3, 1)]), ([(0, 1), (2, 1)], [(1, 3), (4, 0)]),
  ([(0, 1), (2, 1)], [(2, 2), (4, 0)]), ([(0, 1), (2, 1)], [(3, 1), (4, 0)]) ]
def CORNER4_ODD : List (List (ℕ × ℕ) × List (ℕ × ℕ)) := [
  ([(0, 0), (0, 1)], [(1, 1), (2, 0)]), ([(0, 0), (1, 4)], [(0, 2), (1, 3)]),
  ([(0, 0), (2, 3)], [(0, 2), (1, 3)]) ]
def BOUNDARY3_EVEN : List ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) := [
  ((0, 0), (1, 1), (1, 2)), ((0, 1), (0, 2), (1, 1)), ((0, 1), (0, 2), (1, 2)),
  ((0, 1), (0, 3), (1, 1)), ((0, 1), (0, 4), (1, 1)), ((0, 1), (0, 4), (1, 2)),
  ((0, 1), (0, 5), (1, 1)), ((0, 1), (1, 2), (1, 1)), ((0, 1), (1, 2), (1, 3)),
  ((0, 1), (1, 2), (2, 2)), ((0, 1), (1, 2), (3, 1)), ((0, 1), (1, 3), (0, 3)),
  ((0, 1), (2, 1), (1, 3)), ((0, 1), (2, 1), (2, 2)), ((0, 1), (2, 1), (3, 1)),
  ((0, 2), (2, 1), (1, 0)), ((0, 3), (1, 1), (1, 0)), ((0, 4), (1, 1), (1, 0)),
  ((0, 4), (2, 1), (1, 0)), ((0, 4), (2, 1), (1, 2)), ((0, 5), (1, 1), (1, 0)) ]
def BOUNDARY3_ODD : List ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) := [
  ((0, 0), (1, 1), (1, 2)), ((0, 0), (1, 1), (2, 2)), ((0, 1), (0, 2), (1, 1)),
  ((0, 1), (0, 4), (1, 1)), ((0, 4), (1, 1), (1, 0)) ]
structure Rewrite where
  removed : List (ℕ × ℕ)
  moves   : List ((ℕ × ℕ) × (ℕ × ℕ))
structure RWState where
  eff     : List Pt
  removed : List (ℕ × ℕ)
  any     : Bool
def frameTL : Frame := ⟨false, false, false⟩
def frameTR : Frame := ⟨false, true, false⟩
def frameBR : Frame := ⟨true, true, false⟩
def frameBL : Frame := ⟨true, false, false⟩
end ZZN
namespace ZZN
open GridHam
def Inst.transpose (I : Inst) : Inst where
  w  := I.h
  h  := I.w
  s0 := I.s0.swap
  t0 := I.t0.swap
  s1 := I.s1.swap
  t1 := I.t1.swap
end ZZN
namespace ZZN.Thin
abbrev St := List ℕ × ℕ
def mkP (x y : ℕ) : ℕ := if x ≤ y then Nat.pair x y else Nat.pair y x
def lo (p : ℕ) : ℕ := (Nat.unpair p).1
def hi (p : ℕ) : ℕ := (Nat.unpair p).2
def hasEnd (e p : ℕ) : Bool := lo p == e || hi p == e
def other (e p : ℕ) : ℕ := if lo p == e then hi p else lo p
def termE (a b col : ℕ) : ℕ := a + 2 * b + 1 + col
def isTerm (a b e : ℕ) : Bool := decide (a + 2 * b + 1 ≤ e)
def colE (a b e : ℕ) : ℕ := e - (a + 2 * b + 1)
def exitE (b s : ℕ) : ℕ := b + 1 + s
def insSorted (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: l => if x ≤ y then x :: y :: l else y :: insSorted x l
def closeP (a b : ℕ) (x y : ℕ) (rest : List ℕ) (dn : ℕ) : Option St :=
  if isTerm a b x && isTerm a b y then
    if colE a b x != colE a b y then none
    else if (dn / 2 ^ colE a b x) % 2 == 1 then none
    else some (rest, dn + 2 ^ colE a b x)
  else some (insSorted (mkP x y) rest, dn)
def stepCell (a b : ℕ) (e : Option ℕ) (r c : ℕ) (s : St) : List St :=
  let ps := s.1
  let pu := if r = 0 then none else ps.find? (hasEnd c)
  let pl := if c = 0 then none else ps.find? (hasEnd b)
  let down := if r + 1 < a then c else exitE b (a + (b - 1 - c))
  let right := if c + 1 < b then b else exitE b r
  let nin := (if pu.isSome then 1 else 0) + (if pl.isSome then 1 else 0)
  let deg := if e.isSome then 1 else 2
  if deg < nin then [] else
  if pu.isSome && pu == pl then [] else
  let rest := if pu.isSome then (if pl.isSome then (ps.erase (pu.getD 0)).erase (pl.getD 0)
    else ps.erase (pu.getD 0)) else (if pl.isSome then ps.erase (pl.getD 0) else ps)
  let ins := (pu.map (other c)).toList ++ (pl.map (other b)).toList ++ (e.map (termE a b)).toList
  let opts : List (List ℕ) := match deg - nin with
    | 0 => [[]]
    | 1 => [[down], [right]]
    | _ => [[down, right]]
  opts.filterMap fun outs =>
    match ins ++ outs with
    | [x, y] => closeP a b x y rest s.2
    | _ => none
def cell (b i : ℕ) : ℕ × ℕ := (i / b, i % b)
end ZZN.Thin
namespace ZZN.Thin
open GridHam
variable (a b : ℕ) (J : Inst)
def ends2 (col : ℕ) : Coord × Coord := if col = 0 then (J.s0, J.t0) else (J.s1, J.t1)
end ZZN.Thin
namespace ZZN.Thin
open GridHam
def tmOf (J : Inst) : List ((ℕ × ℕ) × ℕ) := [(J.s0, 0), (J.t0, 0), (J.s1, 1), (J.t1, 1)]
def okEnd (a b e : ℕ) : Bool := decide (e ≤ b) || isTerm a b e
def ninOf (pu pl : Option ℕ) : ℕ := (if pu.isSome then 1 else 0) + (if pl.isSome then 1 else 0)
def degOf (e : Option ℕ) : ℕ := if e.isSome then 1 else 2
def optsOf (a b r c : ℕ) (e pu pl : Option ℕ) : List (List ℕ) :=
  match degOf e - ninOf pu pl with
  | 0 => [[]]
  | 1 => [[if r + 1 < a then c else exitE b (a + (b - 1 - c))], [if c + 1 < b then b else exitE b r]]
  | _ => [[if r + 1 < a then c else exitE b (a + (b - 1 - c)), if c + 1 < b then b else exitE b r]]
end ZZN.Thin
namespace ZZN.T
structure TimeM (α : Type) where
  ret : α
  time : ℕ
instance : Monad TimeM where
  pure a := ⟨a, 0⟩
  bind m f := let r := f m.ret; ⟨r.ret, m.time + r.time⟩
end ZZN.T
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
end ZZN.T
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
namespace ZZN.T
open ZZN ZZN.Thin GridHam
set_option bootstrap.genMatcherCode false in
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
def restT (ps : List ℕ) (pu pl : Option ℕ) : TimeM (List ℕ) :=
  match pu, pl with
  | some u, some l => do let r ← leraseT ps u; leraseT r l
  | some u, none => leraseT ps u
  | none, some l => leraseT ps l
  | none, none => pure ps
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
def lookT (skip : Bool) (k : ℕ) (ps : List ℕ) : TimeM (Option ℕ) :=
  if skip then pure none else lfindT (fun z => pure (hasEnd k z)) ps
def noExitT (a b : ℕ) (s : St) : TimeM Bool :=
  lallT (fun z => pure (okEnd a b (lo z) && okEnd a b (hi z))) s.1
def optSnd (o : Option ((ℕ × ℕ) × ℕ)) : Option ℕ := match o with | some q => some q.2 | none => none
def lbeqT : List ℕ → List ℕ → TimeM Bool
  | [], [] => pure true
  | x :: l, y :: m => if x = y then do
      let r ← lbeqT l m
      ⟨r, 1⟩
    else pure false
  | [], _ :: _ => pure false
  | _ :: _, [] => pure false
def stEqT (s t : St) : TimeM Bool := do
  let r ← lbeqT s.1 t.1
  pure (r && decide (s.2 = t.2))
def ltLT : List ℕ → List ℕ → TimeM Bool
  | [], [] => pure false
  | [], _ :: _ => pure true
  | _ :: _, [] => pure false
  | x :: l, y :: m =>
    if x < y then pure true
    else if x = y then do
      let r ← ltLT l m
      ⟨r, 1⟩
    else pure false
def ltST (s t : St) : TimeM Bool := do
  let r ← ltLT s.1 t.1
  pure (decide (s.2 < t.2) || (s.2 == t.2 && r))
def orientPT (J : Inst) (col : ℕ) (L : List Coord) : TimeM (List Coord) :=
  if L.head? = some (ends2 J col).1 then pure L else lreverseT L
def closeOptGT (a b : ℕ) (ins outs rest : List ℕ) (dn : ℕ) : TimeM (Option ((ℕ × ℕ) × St)) := do
  let l ← lappendT ins outs
  match l with
  | [x, y] => do
    let o ← closePT a b x y rest dn
    pure (o.map fun s' => ((x, y), s'))
  | [] => pure none
  | [_] => pure none
  | _ :: _ :: _ :: _ => pure none
def stepTailGT (a b : ℕ) (e : Option ℕ) (r c : ℕ) (s : St) (pu pl : Option ℕ) :
    TimeM (List ((ℕ × ℕ) × St)) :=
  if degOf e < ninOf pu pl then pure [] else
  if pu.isSome && pu == pl then pure [] else do
  let rest ← restT s.1 pu pl
  lfilterMapT (fun outs => closeOptGT a b (endsL a b c e pu pl) outs rest s.2) (optsOf a b r c e pu pl)
def swapPairT (pq : List Coord × List Coord) : TimeM (List Coord × List Coord) := do
  let p ← lmapT (fun x => pure x.swap) pq.1
  let q ← lmapT (fun x => pure x.swap) pq.2
  pure (p, q)
end ZZN.T
namespace ZZN.T
open ZZN ZZN.Thin GridHam
variable {β : Type}
def mergeGT : List (St × β) → List (St × β) → TimeM (List (St × β))
  | [], ys => pure ys
  | xs, [] => pure xs
  | x :: xs, y :: ys => do
    let c ← ltST y.1 x.1
    if !c then do
      let r ← mergeGT xs (y :: ys)
      pure (x :: r)
    else do
      let r ← mergeGT (x :: xs) ys
      pure (y :: r)
termination_by xs ys => xs.length + ys.length
def splitGT : List (St × β) → TimeM (List (St × β) × List (St × β))
  | [] => pure ([], [])
  | [x] => pure ([x], [])
  | x :: y :: l => do
    let p ← splitGT l
    ⟨(x :: p.1, y :: p.2), 1⟩
def msortGT : ℕ → List (St × β) → TimeM (List (St × β))
  | 0, l => pure l
  | f + 1, l => do
    let n ← lengthT l
    if n ≤ 1 then pure l else do
      let p ← splitGT l
      let a ← msortGT f p.1
      let b ← msortGT f p.2
      mergeGT a b
def dedupAdjGT : List (St × β) → TimeM (List (St × β))
  | [] => pure []
  | [x] => pure [x]
  | x :: y :: l => do
    let e ← stEqT x.1 y.1
    if e then dedupAdjGT (x :: l) else do
      let r ← dedupAdjGT (y :: l)
      pure (x :: r)
termination_by l => l.length
def dedupGT (l : List (St × β)) : TimeM (List (St × β)) := do
  let n ← lengthT l
  let s ← msortGT n l
  dedupAdjGT s
end ZZN.T
namespace ZZN.T
open ZZN ZZN.Thin GridHam
inductive Rp where
  | nil : Rp
  | leaf : Coord → Rp
  | app : Rp → Rp → Rp
  | rev : Rp → Rp
abbrev WitR := List (ℕ × Rp) × (Rp × Rp)
def lookDRT (l : List (ℕ × Rp)) (z : ℕ) : TimeM Rp := do
  let o ← lfindT (fun q => pure (q.1 == z)) l
  pure (match o with | some q => q.2 | none => Rp.nil)
def orientSR (e z : ℕ) (R : Rp) : Rp := if lo z = e then Rp.rev R else R
def orientNR (x y : ℕ) (R : Rp) : Rp := if x ≤ y then R else Rp.rev R
def setDpR (d : Rp × Rp) (col : ℕ) (P : Rp) : Rp × Rp := if col = 0 then (P, d.2) else (d.1, P)
set_option bootstrap.genMatcherCode false in
def segNewRT (b r c : ℕ) (w : List (ℕ × Rp)) (pu pl : Option ℕ) : TimeM Rp :=
  match pu, pl with
  | some zu, some zl => do
    let Lu ← lookDRT w zu
    let Ll ← lookDRT w zl
    pure (Rp.app (Rp.app (orientSR c zu Lu) (Rp.leaf (r, c))) (Rp.rev (orientSR b zl Ll)))
  | some zu, none => do
    let Lu ← lookDRT w zu
    pure (Rp.app (Rp.app (orientSR c zu Lu) (Rp.leaf (r, c))) (Rp.rev Rp.nil))
  | none, some zl => do
    let Ll ← lookDRT w zl
    pure (Rp.app (orientSR b zl Ll) (Rp.leaf (r, c)))
  | none, none => pure (Rp.app Rp.nil (Rp.leaf (r, c)))
def closeWitR (a b x y : ℕ) (Ln : Rp) (sgR : List (ℕ × Rp)) (d : Rp × Rp) : WitR :=
  if isTerm a b x && isTerm a b y then (sgR, setDpR d (colE a b x) Ln)
  else ((mkP x y, orientNR x y Ln) :: sgR, d)
def stepCellWRT (a b : ℕ) (e : Option ℕ) (r c : ℕ) (sw : St × WitR) : TimeM (List (St × WitR)) := do
  let pu ← lookT (r == 0) c sw.1.1
  let pl ← lookT (c == 0) b sw.1.1
  let Ln ← segNewRT b r c sw.2.1 pu pl
  let sgR ← lfilterT (fun q => pure (pu != some q.1 && pl != some q.1)) sw.2.1
  let G ← stepTailGT a b e r c sw.1 pu pl
  lmapT (fun g => pure (g.2, closeWitR a b g.1.1 g.1.2 Ln sgR sw.2.2)) G
def stageWRT (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (S : List (St × WitR)) (i : ℕ) :
    TimeM (List (St × WitR)) := do
  let o ← lfindT (fun q => pure (q.1 == cell b i)) tm
  let e := optSnd o
  let l ← lflatMapT (stepCellWRT a b e (cell b i).1 (cell b i).2) S
  let f ← lfilterT (fun sw => noExitT a b sw.1) l
  dedupGT f
def insideWRT (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) : TimeM (List (St × WitR)) := do
  let is ← rangeT (a * b)
  lfoldlT (stageWRT a b tm) [(([], 0), ([], (Rp.nil, Rp.nil)))] is
def flatAccT : Rp → Bool → List Coord → TimeM (List Coord)
  | Rp.nil, _, acc => ⟨acc, 1⟩
  | Rp.leaf x, _, acc => ⟨x :: acc, 1⟩
  | Rp.app l r, rv, acc => do
    let t ← (if rv then flatAccT l true acc else flatAccT r false acc)
    let u ← (if rv then flatAccT r true t else flatAccT l false t)
    ⟨u, 1⟩
  | Rp.rev r, rv, acc => do
    let t ← flatAccT r (!rv) acc
    ⟨t, 1⟩
def flatT (R : Rp) : TimeM (List Coord) := flatAccT R false []
def solveDPRT (J : Inst) : TimeM (Option (List Coord × List Coord)) := do
  let S ← insideWRT J.w J.h (tmOf J)
  let o ← lfindT (fun sw => stEqT sw.1 ([], 3)) S
  match o with
  | some sw => do
    let p0 ← flatT sw.2.2.1
    let p ← orientPT J 0 p0
    let q0 ← flatT sw.2.2.2
    let q ← orientPT J 1 q0
    pure (some (p, q))
  | none => pure none
set_option bootstrap.genMatcherCode false in
def thinSolveWRT (J : Inst) : TimeM (Option (List Coord × List Coord)) :=
  if J.h ≤ J.w then solveDPRT J else do
    let o ← solveDPRT J.transpose
    match o with
    | some pq => do
      let r ← swapPairT pq
      pure (some r)
    | none => pure none
def wcnt : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, d, u, v => if d = 0 then (if u = 0 then 2 else 1) * (if v = 0 then 2 else 1) else 0
  | m + 1, d, u, v => wcnt m d u v + wcnt m (d + 1) u v + (if 0 < d then wcnt m (d - 1) u v else 0) +
      (if u < 2 then wcnt m d (u + 1) v else 0) + (if v < 2 then wcnt m d u (v + 1) else 0)
def Nw (b : ℕ) : ℕ := wcnt (b + 1) 0 0 0
def LgW (b : ℕ) : ℕ := Nat.log2 (2 * Nw b) + 1
def KsR (b : ℕ) : ℕ := 4 + Nw b * (9 * (b + 1) + 31) + 2 * Nw b * (b + 3) +
    (2 * Nw b + 1 + ((b + 8) * (2 * Nw b) * (LgW b + 1) + 1) + 2 * Nw b * (b + 3))
def KwR (b : ℕ) : ℕ := KsR b + 2 * Nw b + 30
end ZZN.T
namespace ZZN.T
open ZZN ZZN.Thin
def solvableBRT (J : Inst) : TimeM Bool :=
  if 11 ≤ J.w ∧ 11 ≤ J.h then do
    let f ← fires3T J.w J.h J.s0 J.t0 J.s1 J.t1
    pure !f
  else do
    let o ← thinSolveWRT J
    pure o.isSome
def CdecR : ℕ := KwR 10 + 300000
end ZZN.T
namespace ZZN.T
open GridHam
/-- **Feasibility, counted.** For a well-formed instance the counted decision procedure answers
`true` exactly when the instance is solvable, within `CdecR · (w h + w + h + 1)` steps. -/
theorem solvableBRT_main {J : Inst} (hwf : J.WellFormed) :
    ((solvableBRT J).ret = true ↔ Solvable J) ∧
      (solvableBRT J).time ≤ CdecR * (J.w * J.h + J.w + J.h + 1) := by
  sorry
/-- **The characterization, counted.** On rectangles with both sides at least 11, a well-formed
instance is solvable exactly when the counted forbidden-pattern catalogue `fires3T` finds no
pattern. -/
theorem fires3T_iff_solvable {J : Inst} (hwf : J.WellFormed) (hw : 11 ≤ J.w) (hh : 11 ≤ J.h) :
    (fires3T J.w J.h J.s0 J.t0 J.s1 J.t1).ret = false ↔ Solvable J := by
  sorry
end ZZN.T

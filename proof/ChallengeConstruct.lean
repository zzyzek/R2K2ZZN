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
-- ZZN.Symmetry
-- ZZN.Timed.SortKeyG
-- ZZN.Timed.ThinRope
-- ZZN.Timed.ThinWord
-- ZZN.Timed.ThinRopeCost
-- ZZN.Constr.EdgeBlock
-- ZZN.Constr.WideBand
-- ZZN.Constr.Round
-- ZZN.Timed.RoundT
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
def shiftAt (r : ℕ) (v : Coord) : Coord := if v.1 ≤ r then v else (v.1 + 2, v.2)
def gap (r : ℕ) (a b : Coord) : List Coord :=
  if a.1 = r ∧ b.1 = r + 1 ∧ a.2 = b.2 then [(r + 1, a.2), (r + 2, a.2)]
  else if a.1 = r + 1 ∧ b.1 = r ∧ a.2 = b.2 then [(r + 2, a.2), (r + 1, a.2)]
  else []
end ZZN
namespace ZZN
abbrev Pt := (ℕ × ℕ) × ℕ
structure View where
  H : ℕ
  W : ℕ
  pts : List Pt
def alternating (cols : List ℕ) : Bool :=
  match cols with
  | [a, b, c, d] => a != b && b != c && c != d
  | _ => false
end ZZN
namespace ZZN
open GridHam
def delAt (d : ℕ) (v : Coord) : Coord := if v.1 < d then v else (v.1 - 2, v.2)
def Inst.deleteAt (I : Inst) (d : ℕ) : Inst where
  w  := I.w - 2
  h  := I.h
  s0 := delAt d I.s0
  t0 := delAt d I.t0
  s1 := delAt d I.s1
  t1 := delAt d I.t1
def Inst.ends (I : Inst) : List Coord := [I.s0, I.t0, I.s1, I.t1]
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
def lmodifyT (l : List α) (i : ℕ) (f : α → α) : TimeM (List α) := ⟨l.modify i f, l.length + 1⟩
def lgetT [Inhabited α] (l : List α) (i : ℕ) : TimeM α := ⟨l[i]!, l.length + 1⟩
def rangeT (n : ℕ) : TimeM (List ℕ) := ⟨List.range n, n + 1⟩
def lnodupT [DecidableEq α] (l : List α) : TimeM Bool := ⟨decide l.Nodup, l.length ^ 2 + 1⟩
def lgetLastT (l : List α) : TimeM (Option α) := ⟨l.getLast?, l.length + 1⟩
def fmemT (x : ℕ) (s : Finset ℕ) : TimeM Bool := ⟨decide (x ∈ s), s.card + 1⟩
def feraseT (s : Finset ℕ) (x : ℕ) : TimeM (Finset ℕ) := ⟨s.erase x, s.card + 1⟩
def ffilterT (p : ℕ → Bool) (s : Finset ℕ) : TimeM (Finset ℕ) := ⟨s.filter (fun x => p x = true), s.card + 1⟩
def frangeFilterT (n : ℕ) (p : ℕ → TimeM Bool) : TimeM (Finset ℕ) :=
  ⟨(Finset.range n).filter (fun y => (p y).ret = true), ((List.range n).map (fun y => (p y).time + 1)).sum⟩
end ZZN.T
namespace ZZN.T
open ZZN GridHam
set_option bootstrap.genMatcherCode false in
def stretchT (r : ℕ) : List Coord → TimeM (List Coord)
  | [] => pure []
  | [a] => ⟨[shiftAt r a], 1⟩
  | a :: b :: l => do
    let s ← stretchT r (b :: l)
    ⟨shiftAt r a :: (gap r a b ++ s), 3⟩
end ZZN.T
namespace ZZN.T
open ZZN
def atT (v : View) (r c : ℕ) : TimeM (Option ℕ) := do
  let o ← lfindT (fun q => pure (q.1 == (r, c))) v.pts
  pure (match o with | some q => some q.2 | none => none)
def emptyT (v : View) (cells : List (ℕ × ℕ)) : TimeM Bool :=
  lallT (fun x => do let o ← atT v x.1 x.2; pure o.isNone) cells
def testL3T (v : View) : TimeM Bool := do
  let x ← atT v 0 2
  match x with
  | some a => do
    let y ← atT v 1 1
    let z ← atT v 1 0
    let e ← emptyT v [(0, 0), (0, 1)]
    pure (y == some a && z == some (1 - a) && e)
  | none => pure false
end ZZN.T
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
set_option bootstrap.genMatcherCode false in
def crossRowsT (r : ℕ) : List Coord → TimeM (List ℕ)
  | [] => pure []
  | [_] => pure []
  | a :: b :: l => do
    let rest ← crossRowsT r (b :: l)
    ⟨if ((a.1 = r ∧ b.1 = r + 1) ∨ (a.1 = r + 1 ∧ b.1 = r)) ∧ a.2 = b.2 then a.2 :: rest else rest, 1⟩
set_option bootstrap.genMatcherCode false in
def flipRowsT (r : ℕ) : List Coord → TimeM (List ℕ)
  | [] => pure []
  | [_] => pure []
  | a :: b :: l => do
    let rest ← flipRowsT r (b :: l)
    ⟨if a.1 = r ∧ b.1 = r ∧ b.2 = a.2 + 1 then a.2 :: rest
      else if a.1 = r ∧ b.1 = r ∧ a.2 = b.2 + 1 then b.2 :: rest else rest, 1⟩
def seedT (h : ℕ) (cr fr : List ℕ) (R : ℕ) : TimeM Bool := do
  let c0 ← lcontainsT cr (R - 1)
  let c1 ← lcontainsT cr R
  let f ← lcontainsT fr (R - 1)
  pure (((R == 0 || c0) && (R == h || c1)) || (decide (1 ≤ R) && decide (R < h) && !c0 && !c1 && f))
def planLeftT : ℕ → Finset ℕ → List ℕ → ℕ → TimeM (List ℕ)
  | 0, _, K, _ => pure K
  | L + 1, U, K, c => do
    let b ← fmemT L U
    if b then do
      let U' ← feraseT U L
      let K' ← lmodifyT K c (· + 1)
      planLeftT L U' K' c
    else planLeftT L U K L
def planRightT (h : ℕ) : ℕ → ℕ → Finset ℕ → List ℕ → ℕ → TimeM (List ℕ)
  | 0, _, _, K, _ => pure K
  | n + 1, R0, U, K, c => do
    let b ← fmemT (R0 + 1) U
    if b then do
      let U' ← feraseT U (R0 + 1)
      let K' ← lmodifyT K c (· + 1)
      planRightT h n (R0 + 1) U' K' c
    else if R0 + 1 < h then planRightT h n (R0 + 1) U K (R0 + 1)
    else pure K
def detT (r a k : ℕ) (up : Bool) (c : ℕ) : TimeM (List Coord) := do
  let is ← rangeT (k + 1)
  let A ← lmapT (fun i => pure (r + c, if up then a + i else a - i)) is
  let ri ← lreverseT is
  let B ← lmapT (fun i => pure (r + (3 - c), if up then a + i else a - i)) ri
  lappendT A B
def insKT (r : ℕ) (K : List ℕ) (R : ℕ) (fl : Bool) (x y : Coord) : TimeM (List Coord) :=
  if x.1 = r ∧ y.1 = r + 1 ∧ x.2 = y.2 then do
    let k ← lgetT K x.2
    detT r x.2 k (decide (R ≤ x.2)) 1
  else if x.1 = r + 1 ∧ y.1 = r ∧ x.2 = y.2 then do
    let k ← lgetT K x.2
    detT r x.2 k (decide (R ≤ x.2)) 2
  else if fl = true ∧ x = (r, R - 1) ∧ y = (r, R) then do
    let k1 ← lgetT K (R - 1)
    let k2 ← lgetT K R
    let A ← detT r (R - 1) k1 false 1
    let B ← detT r R k2 true 2
    lappendT A B
  else if fl = true ∧ x = (r, R) ∧ y = (r, R - 1) then do
    let k1 ← lgetT K R
    let k2 ← lgetT K (R - 1)
    let A ← detT r R k1 true 1
    let B ← detT r (R - 1) k2 false 2
    lappendT A B
  else pure []
set_option bootstrap.genMatcherCode false in
def extLT (r : ℕ) (K : List ℕ) (R : ℕ) (fl : Bool) : List Coord → TimeM (List Coord)
  | [] => pure []
  | [a] => pure [shiftAt r a]
  | a :: b :: l => do
    let i ← insKT r K R fl a b
    let rest ← extLT r K R fl (b :: l)
    let m ← lappendT i rest
    pure (shiftAt r a :: m)
def extPT (r : ℕ) (K : List ℕ) (R : ℕ) (fl : Bool) (p q : List Coord) :
    TimeM (List Coord × List Coord) := do
  let a ← extLT r K R fl p
  let b ← extLT r K R fl q
  pure (a, b)
def bandExtLT (h r : ℕ) (p q : List Coord) : TimeM (List Coord × List Coord) := do
  let cp ← crossRowsT r p
  let cq ← crossRowsT r q
  let cr ← lappendT cp cq
  let fp ← flipRowsT r p
  let fq ← flipRowsT r q
  let fr ← lappendT fp fq
  let rs ← rangeT (h + 1)
  let o ← lfindT (seedT h cr fr) rs
  match o with
  | none => do
    let a ← stretchT r p
    let b ← stretchT r q
    pure (a, b)
  | some R => do
    let U0 ← frangeFilterT h (fun y => do let c ← lcontainsT cr y; pure !c)
    let hs ← rangeT (h + 1)
    let K0 ← lmapT (fun _ => pure 0) hs
    let c0 ← lcontainsT cr (R - 1)
    let c1 ← lcontainsT cr R
    if (R == 0 || c0) && (R == h || c1) then
      if R = 0 then do
        let K ← planRightT h (h - 0) 0 U0 K0 0
        extPT r K R false p q
      else if R = h then do
        let K ← planLeftT (R - 1) U0 K0 (R - 1)
        extPT r K R false p q
      else do
        let K1 ← planLeftT (R - 1) U0 K0 (R - 1)
        let U' ← ffilterT (fun z => decide (R - 1 < z)) U0
        let K ← planRightT h (h - R) R U' K1 R
        extPT r K R false p q
    else do
      let U1a ← feraseT U0 (R - 1)
      let U1 ← feraseT U1a (R - 1 + 1)
      let K1 ← planLeftT (R - 1) U1 K0 (R - 1)
      let U' ← ffilterT (fun z => decide (R - 1 < z)) U1
      let K ← planRightT h (h - (R - 1 + 1)) (R - 1 + 1) U' K1 (R - 1 + 1)
      extPT r K R true p q
def redBBT (I : Inst) (d : ℕ) : TimeM Bool := do
  let f0 ← freeLineBT I d
  let f1 ← freeLineBT I (d + 1)
  let fm ← freeLineBT I (d - 1)
  let fp ← freeLineBT I (d + 2)
  let b ← endBelowBT I d
  let a ← endAboveBT I (d + 1)
  pure (decide (13 ≤ I.w) && decide (5 ≤ d) && decide (d + 7 ≤ I.w) && f0 && f1 &&
    ((decide (1 ≤ d) && fm) || fp) && b && a)
def findRed2T (I : Inst) : TimeM (Option ℕ) := do
  let rs ← rangeT I.w
  lfindT (fun d => do
    let x ← redBT I d
    let y ← redBBT I d
    pure (x || y)) rs
def wfB (I : Inst) : Bool :=
  decide (I.s0.1 < I.w ∧ I.s0.2 < I.h ∧ I.t0.1 < I.w ∧ I.t0.2 < I.h ∧ I.s1.1 < I.w ∧ I.s1.2 < I.h ∧
    I.t1.1 < I.w ∧ I.t1.2 < I.h ∧ I.s0 ≠ I.t0 ∧ I.s0 ≠ I.s1 ∧ I.s0 ≠ I.t1 ∧ I.t0 ≠ I.s1 ∧
    I.t0 ≠ I.t1 ∧ I.s1 ≠ I.t1)
def liftET (I : Inst) (d : ℕ) (p q : List Coord) : TimeM (List Coord × List Coord) := do
  let f ← freeLineBT I (d + 2)
  if d + 3 ≤ I.w ∧ f = true then bandExtLT I.h d p q
  else bandExtLT I.h (d - 1) p q
set_option bootstrap.genMatcherCode false in
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
abbrev Sol := Option (List Coord × List Coord)
def swapT (l : List Coord) : TimeM (List Coord) := lmapT (fun x => pure x.swap) l
def stepT (I : Inst) (d : ℕ) : Sol → TimeM Sol
  | some pq => do
    let l ← liftET I d pq.1 pq.2
    pure (some l)
  | none => pure none
def stepTT (I : Inst) (d : ℕ) : Sol → TimeM Sol
  | some pq => do
    let l ← liftET I.transpose d pq.1 pq.2
    let a ← swapT l.1
    let b ← swapT l.2
    pure (some (a, b))
  | none => pure none
def solveRecT (thinT : Inst → TimeM Sol) : ℕ → Inst → TimeM Sol
  | 0, _ => pure none
  | n + 1, I =>
    if I.w ≤ 10 ∨ I.h ≤ 10 then thinT I >>= checkET I else do
    let f ← findRed2T I
    match f with
    | some d => solveRecT thinT n (I.deleteAt d) >>= stepT I d
    | none => do
      let g ← findRed2T I.transpose
      match g with
      | some d => solveRecT thinT n (I.transpose.deleteAt d) >>= stepTT I d
      | none => thinT I >>= checkET I
def solveZT (thinT : Inst → TimeM Sol) (I : Inst) : TimeM Sol :=
  if wfB I then solveRecT thinT (I.w + I.h) I else pure none
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
namespace ZZN
open GridHam
def reflX (w : ℕ) (v : Coord) : Coord := (w - 1 - v.1, v.2)
end ZZN
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
namespace ZZN
open GridHam
def vertAt (r : ℕ) (u v : Coord) : Bool := u.1 = r ∧ v.1 = r ∧ (u.2 + 1 = v.2 ∨ v.2 + 1 = u.2)
def shW (r W : ℕ) (v : Coord) : Coord := if v.1 ≤ r then v else (v.1 + W, v.2)
def Inst.mapE (I : Inst) (w : ℕ) (f : Coord → Coord) : Inst := ⟨w, I.h, f I.s0, f I.t0, f I.s1, f I.t1⟩
def Inst.dropL (I : Inst) (m : ℕ) : Inst := I.mapE (I.w - m) (fun v => (v.1 - m, v.2))
def Inst.dropR (I : Inst) (m : ℕ) : Inst := I.mapE (I.w - m) id
def Inst.dropIn (I : Inst) (r m : ℕ) : Inst :=
  I.mapE (I.w - m) (fun v => if v.1 ≤ r then v else (v.1 - m, v.2))
inductive Blk
  | left (k : ℕ)
  | right (k : ℕ)
  | inner (r k : ℕ)
def Blk.del : Blk → Inst → Inst
  | .left k, I => I.dropL (2 * k)
  | .right k, I => I.dropR (2 * k)
  | .inner r k, I => I.dropIn r (2 * k)
def xmin (I : Inst) : ℕ := min (min I.s0.1 I.t0.1) (min I.s1.1 I.t1.1)
def xmax (I : Inst) : ℕ := max (max I.s0.1 I.t0.1) (max I.s1.1 I.t1.1)
def leftK (I : Inst) : ℕ := min ((xmin I - 2) / 2) ((I.w - 11) / 2)
def rightK (I : Inst) : ℕ := min ((I.w - 3 - xmax I) / 2) ((I.w - 11) / 2)
def innerK (I : Inst) (a b : ℕ) : ℕ := min ((b - a - 9) / 2) ((I.w - 11) / 2)
end ZZN
namespace ZZN.T
open ZZN GridHam
def cvT (cr : List ℕ) (R : ℕ) (fl : Bool) (y : ℕ) : TimeM Bool := do
  let c ← lcontainsT cr y
  pure (c || (fl && (y + 1 == R || y == R)))
def runDnT (cv : ℕ → TimeM Bool) : ℕ → TimeM (List ℕ)
  | 0 => pure []
  | n + 1 => do
    let c ← cv n
    if c then pure [] else do
      let rest ← runDnT cv n
      ⟨n :: rest, 1⟩
def runUpFT (cv : ℕ → TimeM Bool) : ℕ → ℕ → TimeM (List ℕ)
  | 0, _ => pure []
  | k + 1, y => do
    let c ← cv y
    if c then pure [] else do
      let rest ← runUpFT cv k (y + 1)
      ⟨y :: rest, 1⟩
def attWT (cv : ℕ → TimeM Bool) (h R a : ℕ) : TimeM (List ℕ) :=
  if a < R then runDnT cv a else runUpFT cv (h - (a + 1)) (a + 1)
def tblT (cv : ℕ → TimeM Bool) (h R : ℕ) : TimeM (List (ℕ × List ℕ)) := do
  let rs ← rangeT h
  lfilterMapT (fun a => do
    let c ← cv a
    if c then do
      let l ← attWT cv h R a
      pure (some (a, l))
    else pure none) rs
def grpT (tbl : List (ℕ × List ℕ)) (y : ℕ) : TimeM (List ℕ) := do
  let o ← lfindT (fun e => pure (e.1 == y)) tbl
  match o with
  | some e => pure (y :: e.2)
  | none => pure [y]
def colSnakeT (x : ℕ) (A : List ℕ) (k : ℕ) : TimeM (List Coord) := do
  let is ← rangeT k
  let ra ← lreverseT A
  lflatMapT (fun i => do
    let a ← lmapT (fun y => pure (x + 2 * i, y)) A
    let b ← lmapT (fun y => pure (x + 2 * i + 1, y)) ra
    lappendT a b) is
def snWT (r k : ℕ) (tbl : List (ℕ × List ℕ)) (a : ℕ) : TimeM (List Coord) := do
  let g ← grpT tbl a
  colSnakeT (r + 1) g k
def GWT (r k R : ℕ) (fl : Bool) (tbl : List (ℕ × List ℕ)) (u v : Coord) : TimeM (List Coord) :=
  if u.1 = r ∧ v.1 = r + 2 * k + 1 ∧ u.2 = v.2 then snWT r k tbl u.2
  else if u.1 = r + 2 * k + 1 ∧ v.1 = r ∧ u.2 = v.2 then do
    let s ← snWT r k tbl u.2
    lreverseT s
  else if fl = true ∧ u = (r, R - 1) ∧ v = (r, R) then do
    let a ← snWT r k tbl (R - 1)
    let b ← snWT r k tbl R
    let rb ← lreverseT b
    lappendT a rb
  else if fl = true ∧ u = (r, R) ∧ v = (r, R - 1) then do
    let a ← snWT r k tbl (R - 1)
    let b ← snWT r k tbl R
    let rb ← lreverseT b
    let f ← lappendT a rb
    lreverseT f
  else pure []
def insManyT (G : Coord → Coord → TimeM (List Coord)) : List Coord → TimeM (List Coord)
  | a :: b :: l => do
    let i ← G a b
    let rest ← insManyT G (b :: l)
    let m ← lappendT i rest
    pure (a :: m)
  | [a] => pure [a]
  | [] => pure []
def shWT (r W : ℕ) (L : List Coord) : TimeM (List Coord) := lmapT (fun v => pure (shW r W v)) L
def wideTailT (h r k : ℕ) (cr : List ℕ) (R : ℕ) (fl : Bool) (p q : List Coord) :
    TimeM (List Coord × List Coord) := do
  let tbl ← tblT (cvT cr R fl) h R
  let sp ← shWT r (2 * k) p
  let sq ← shWT r (2 * k) q
  let P ← insManyT (GWT r k R fl tbl) sp
  let Q ← insManyT (GWT r k R fl tbl) sq
  pure (P, Q)
def wideBandT (h r k : ℕ) (p q : List Coord) : TimeM (List Coord × List Coord) := do
  let cp ← crossRowsT r p
  let cq ← crossRowsT r q
  let cr ← lappendT cp cq
  let fp ← flipRowsT r p
  let fq ← flipRowsT r q
  let fr ← lappendT fp fq
  let rs ← rangeT (h + 1)
  let o ← lfindT (seedT h cr fr) rs
  let c0 ← lcontainsT cr (o.getD 0 - 1)
  let c1 ← lcontainsT cr (o.getD 0)
  wideTailT h r k cr (o.getD 0) (o.isSome && !((o.getD 0 == 0 || c0) && (o.getD 0 == h || c1))) p q
def findVT (r : ℕ) : List Coord → TimeM (Option (Coord × Coord))
  | u :: v :: l => if vertAt r u v then ⟨some (u, v), 1⟩ else do
      let o ← findVT r (v :: l)
      ⟨o, 1⟩
  | [_] => pure none
  | [] => pure none
def edgeBlockT (w h y k : ℕ) : TimeM (List Coord) := do
  let d ← rangeT (y + 1)
  let dr ← lreverseT d
  let u0 ← rangeT (h - (y + 1))
  let u ← lmapT (fun i => pure (i + (y + 1))) u0
  let A ← colSnakeT w dr k
  let B ← colSnakeT w u k
  let rB ← lreverseT B
  lappendT A rB
def blkET (w h k : ℕ) (a b : Coord) : TimeM (List Coord) :=
  if a.2 < b.2 then edgeBlockT w h a.2 k else do
    let e ← edgeBlockT w h b.2 k
    lreverseT e
def insBT (a b : Coord) (X : List Coord) : List Coord → TimeM (List Coord)
  | x :: y :: l => if x = a ∧ y = b then do
      let m ← lappendT X (y :: l)
      ⟨x :: m, 1⟩
    else do
      let r ← insBT a b X (y :: l)
      ⟨x :: r, 1⟩
  | [x] => pure [x]
  | [] => pure []
def edgeLiftT (w h k : ℕ) (p q : List Coord) : TimeM (List Coord × List Coord) := do
  let o ← findVT (w - 1) p
  match o with
  | some (a, b) => do
    let X ← blkET w h k a b
    let P ← insBT a b X p
    pure (P, q)
  | none => do
    let o' ← findVT (w - 1) q
    match o' with
    | some (a, b) => do
      let X ← blkET w h k a b
      let Q ← insBT a b X q
      pure (p, Q)
    | none => pure (p, q)
def reflT (w : ℕ) (L : List Coord) : TimeM (List Coord) := lmapT (fun v => pure (reflX w v)) L
def edgeLiftLT (w h k : ℕ) (p q : List Coord) : TimeM (List Coord × List Coord) := do
  let p' ← reflT w p
  let q' ← reflT w q
  let e ← edgeLiftT w h k p' q'
  let P ← reflT (w + 2 * k) e.1
  let Q ← reflT (w + 2 * k) e.2
  pure (P, Q)
def innerPairT (I : Inst) : TimeM (Option (ℕ × ℕ)) := do
  let xs ← lmapT (fun e => pure e.1) I.ends
  let ps ← lflatMapT (fun a => lmapT (fun b => pure (a, b)) xs) xs
  lfindT (fun ab => do
    let c ← lallT (fun x => pure (!(decide (ab.1 < x) && decide (x < ab.2)))) xs
    pure (decide (ab.1 < ab.2) && c && decide (1 ≤ innerK I ab.1 ab.2))) ps
def blkXT (I : Inst) : TimeM (Option Blk) :=
  if 1 ≤ leftK I then pure (some (.left (leftK I)))
  else if 1 ≤ rightK I then pure (some (.right (rightK I)))
  else do
    let o ← innerPairT I
    match o with
    | some ab => pure (some (.inner (ab.1 + 1) (innerK I ab.1 ab.2)))
    | none => pure none
def _root_.ZZN.Blk.liftT : Blk → Inst → List Coord → List Coord → TimeM (List Coord × List Coord)
  | .left k, J, p, q => edgeLiftLT J.w J.h k p q
  | .right k, J, p, q => edgeLiftT J.w J.h k p q
  | .inner r k, J, p, q => wideBandT J.h r k p q
set_option bootstrap.genMatcherCode false in
def liftBT (b : Blk) (J : Inst) : Sol → TimeM Sol
  | some pq => do
    let l ← b.liftT J pq.1 pq.2
    pure (some l)
  | none => pure none
set_option bootstrap.genMatcherCode false in
def liftBTT (b : Blk) (J : Inst) : Sol → TimeM Sol
  | some pq => do
    let l ← b.liftT J pq.1 pq.2
    let a ← swapT l.1
    let c ← swapT l.2
    pure (some (a, c))
  | none => pure none
def solveRT (thinT : Inst → TimeM Sol) : ℕ → Inst → TimeM Sol
  | n + 1, I =>
    if I.w ≤ 10 ∨ I.h ≤ 10 then solveZT thinT I else do
    let o ← blkXT I
    match o with
    | none => do
      let o' ← blkXT I.transpose
      match o' with
      | some b => solveRT thinT n (b.del I.transpose) >>= liftBTT b (b.del I.transpose)
      | none => solveZT thinT I
    | some b => solveRT thinT n (b.del I) >>= liftBT b (b.del I)
  | 0, _ => pure none
def solveZ3T (thinT : Inst → TimeM Sol) (I : Inst) : TimeM Sol :=
  if wfB I then solveRT thinT (I.w + I.h) I else pure none
end ZZN.T
namespace ZZN.T
open GridHam
/-- **The block construction with the tree-segment plug DP, counted.** Every answer is a
solution, it returns one for every well-formed solvable instance, and on a `w × h` instance with
`M = max w h` it takes `O(M²)` steps. -/
theorem solveZ3RT_main (I : Inst) :
    (∀ p q, (solveZ3T thinSolveWRT I).ret = some (p, q) → IsSolution I p q) ∧
    (I.WellFormed → Solvable I → ∃ p q, (solveZ3T thinSolveWRT I).ret = some (p, q)) ∧
    (solveZ3T thinSolveWRT I).time ≤ 37 * (80 * (max I.w I.h + 1) ^ 2 + 400) +
      ((10 * max I.w I.h + 1) * KwR 10 + 3 * (10 * max I.w I.h + 1) ^ 2 + 10) +
      (74 * (700 * (37 + 1) ^ 2) + ((16 * 37 + 1) * KwR 16 + 3 * (16 * 37 + 1) ^ 2 + 10)) := by
  sorry
end ZZN.T

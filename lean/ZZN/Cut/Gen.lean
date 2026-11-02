-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Cut.Template

/-!
# The cut-tree checker over an arithmetic interface

`Alg V B`: values `V` with constants, `+`, `-`, and tests `<`, `=`, odd giving `B`, with Boolean
connectives on `B`. The checker `checkG` is written once against `Alg`. Instances:

* `ℤ`, `Bool`: the concrete checker (exact arithmetic, no truncation);
* linear forms and formulas (`Cut/Sym.lean`): one formula per template.

`Hom`: maps `V → ℤ`, `B → Bool` commuting with the operations. `checkG_hom`: a hom carries
`checkG` to the concrete checker. `accG_int`: on naturals, the concrete `accG` is `Lane.accB`.
-/

namespace ZZN.Cut

open GridHam

class Alg (V B : Type) where
  k : ℤ → V
  add : V → V → V
  sub : V → V → V
  lt : V → V → B
  eq : V → V → B
  odd : V → B
  tt : B
  ff : B
  and : B → B → B
  or : B → B → B
  not : B → B

instance : Alg ℤ Bool where
  k c := c
  add := (· + ·)
  sub := (· - ·)
  lt a b := decide (a < b)
  eq a b := decide (a = b)
  odd a := decide (a % 2 = 1)
  tt := true
  ff := false
  and := (· && ·)
  or := (· || ·)
  not := (! ·)

section
variable {V B : Type} [A : Alg V B]

def ne (a b : V) : B := A.not (A.eq a b)
def le (a b : V) : B := A.not (A.lt b a)

/-- IPS acceptability (`Lane.accB`) as a formula over linear tests only. -/
def accG (w h : V) (s t : V × V) : B :=
  let one := A.k 1
  let zero := A.k 0
  let ps := A.odd (A.add s.1 s.2)
  let pt := A.odd (A.add t.1 t.2)
  let ow := A.odd w
  let oh := A.odd h
  let pne := A.or (A.and ps (A.not pt)) (A.and (A.not ps) pt)
  let cc := A.or (A.and (A.and ow oh) (A.and (A.not ps) (A.not pt))) (A.and (A.not (A.and ow oh)) pne)
  let w1 := A.sub w one
  let h1 := A.sub h one
  let corner := fun v : V × V =>
    A.and (A.or (A.eq v.1 zero) (A.eq v.1 w1)) (A.or (A.eq v.2 zero) (A.eq v.2 h1))
  let isW1 := A.eq w one
  let atZero := fun v : V × V => A.and (A.eq v.1 zero) (A.eq v.2 zero)
  let atFar := fun v : V × V =>
    A.or (A.and isW1 (A.and (A.eq v.1 zero) (A.eq v.2 h1)))
      (A.and (A.not isW1) (A.and (A.eq v.1 w1) (A.eq v.2 zero)))
  let f1 := A.not (A.or (A.and (atZero s) (atFar t)) (A.and (atFar s) (atZero t)))
  let f2 := A.and (A.and (A.not (corner s)) (A.not (corner t)))
    (A.or (A.and (A.eq w (A.k 2)) (A.eq s.2 t.2)) (A.and (A.eq h (A.k 2)) (A.eq s.1 t.1)))
  let isW3 := A.eq w (A.k 3)
  let oppOdd := A.or (A.and isW3 oh) (A.and (A.not isW3) ow)
  let F3 := fun c0 c1 oc : V =>
    let gr := A.lt c1 c0
    let dsat := A.or (A.and (A.eq oc one) (ne c0 c1))
      (A.and (ne oc one) (A.or (le (A.k 2) (A.sub c0 c1)) (le (A.k 2) (A.sub c1 c0))))
    A.and (A.and (A.and (A.not oppOdd) pne) dsat)
      (A.or (A.and gr (A.not ps)) (A.and (A.not gr) ps))
  let f3 := A.or (A.and isW3 (F3 s.2 t.2 s.1)) (A.and (A.not isW3) (F3 s.1 t.1 s.2))
  let c1 := A.or (A.eq w one) (A.eq h one)
  let c2 := A.or (A.eq w (A.k 2)) (A.eq h (A.k 2))
  let c3 := A.or (A.eq w (A.k 3)) (A.eq h (A.k 3))
  let forb := A.or (A.and c1 f1)
    (A.or (A.and (A.not c1) (A.and c2 f2)) (A.and (A.not c1) (A.and (A.not c2) (A.and c3 f3))))
  A.and cc (A.not forb)

end

set_option maxHeartbeats 8000000 in
/-- On naturals, the concrete `accG` is `Lane.accB`. -/
theorem accG_int (w h : ℕ) (s t : Coord) :
    accG (V := ℤ) (B := Bool) (w : ℤ) (h : ℤ) ((s.1 : ℤ), (s.2 : ℤ)) ((t.1 : ℤ), (t.2 : ℤ)) =
      Lane.accB w h s t := by
  obtain ⟨s1, s2⟩ := s
  obtain ⟨t1, t2⟩ := t
  simp only [accG, Lane.accB, ne, le, Alg.k, Alg.add, Alg.sub, Alg.lt, Alg.eq, Alg.odd, Alg.and,
    Alg.or, Alg.not]
  rw [Bool.eq_iff_iff]
  by_cases hw1 : w = 1 <;> by_cases hh1 : h = 1 <;> by_cases hw2 : w = 2 <;> by_cases hh2 : h = 2 <;>
    by_cases hw3 : w = 3 <;> by_cases hh3 : h = 3 <;> simp [hw1, hh1, hw2, hh2, hw3, hh3] <;>
    (try split_ifs) <;> omega

/-! ### The generic checker -/

structure PieceG (V : Type) where
  ox : V
  oy : V
  pw : V
  ph : V
  segs : List ((V × V) × (V × V))

section
variable {V B : Type} [A : Alg V B]

def cutcG (vert : Bool) (pos : V) (s : Bool) (y : V) : V × V :=
  let x := if s then pos else A.sub pos (A.k 1)
  if vert then (y, x) else (x, y)

def putG {E : Type} (s : Bool) (e : E) (LR : List E × List E) : List E × List E :=
  if s then (LR.1, LR.2 ++ [e]) else (LR.1 ++ [e], LR.2)

def splitG (vert : Bool) (pos : V) :
    List (Kind V) → List ((V × V) × (V × V)) → List ((V × V) × (V × V)) × List ((V × V) × (V × V)) →
      Option (List ((V × V) × (V × V)) × List ((V × V) × (V × V)))
  | [], [], acc => some acc
  | Kind.stay s :: ks, (a, b) :: ss, acc => splitG vert pos ks ss (putG s (a, b) acc)
  | Kind.cross s y :: ks, (a, b) :: ss, acc =>
    splitG vert pos ks ss
      (putG (!s) (cutcG (A := A) vert pos (!s) y, b) (putG s (a, cutcG (A := A) vert pos s y) acc))
  | Kind.exc s y z :: ks, (a, b) :: ss, acc =>
    splitG vert pos ks ss
      (putG (!s) (cutcG (A := A) vert pos (!s) y, cutcG (A := A) vert pos (!s) z)
        (putG s (cutcG (A := A) vert pos s z, b) (putG s (a, cutcG (A := A) vert pos s y) acc)))
  | _, _, _ => none

def PieceG.lo (P : PieceG V) (vert : Bool) (pos : V) (L : List ((V × V) × (V × V))) : PieceG V :=
  if vert then ⟨P.ox, P.oy, P.pw, A.sub pos P.oy, L⟩ else ⟨P.ox, P.oy, A.sub pos P.ox, P.ph, L⟩

def PieceG.hi (P : PieceG V) (vert : Bool) (pos : V) (R : List ((V × V) × (V × V))) : PieceG V :=
  if vert then ⟨P.ox, pos, P.pw, A.sub (A.add P.oy P.ph) pos, R⟩
  else ⟨pos, P.oy, A.sub (A.add P.ox P.pw) pos, P.ph, R⟩

def insideG (vert : Bool) (pos : V) (P : PieceG V) : B :=
  if vert then A.and (A.lt P.oy pos) (A.lt pos (A.add P.oy P.ph))
  else A.and (A.lt P.ox pos) (A.lt pos (A.add P.ox P.pw))

def regionG (P : PieceG V) (v : V × V) : B :=
  A.and (A.and (le P.ox v.1) (A.lt v.1 (A.add P.ox P.pw)))
    (A.and (le P.oy v.2) (A.lt v.2 (A.add P.oy P.ph)))

def eqCG (a b : V × V) : B := A.and (A.eq a.1 b.1) (A.eq a.2 b.2)

def leafG (P : PieceG V) : B :=
  match P.segs with
  | [(a, b)] =>
    A.or (A.and (eqCG a b) (A.and (A.and (A.eq P.pw (A.k 1)) (A.eq P.ph (A.k 1))) (eqCG a (P.ox, P.oy))))
      (A.and (A.not (eqCG a b)) (A.and (A.and (regionG P a) (regionG P b))
        (accG P.pw P.ph (A.sub a.1 P.ox, A.sub a.2 P.oy) (A.sub b.1 P.ox, A.sub b.2 P.oy))))
  | _ => A.ff

def checkG : CTree V → PieceG V → B
  | CTree.leaf, P => leafG P
  | CTree.cut vert pos ks l r, P =>
    A.and (insideG vert pos P)
      (match splitG (A := A) vert pos ks P.segs ([], []) with
       | some (L, R) => A.and (checkG l (P.lo (A := A) vert pos L) : B) (checkG r (P.hi (A := A) vert pos R) : B)
       | none => A.ff)

end

/-! ### Homomorphisms to the concrete instance -/

structure Hom (V B : Type) [A : Alg V B] where
  eV : V → ℤ
  eB : B → Bool
  k : ∀ c, eV (A.k c) = c
  add : ∀ a b, eV (A.add a b) = eV a + eV b
  sub : ∀ a b, eV (A.sub a b) = eV a - eV b
  lt : ∀ a b, eB (A.lt a b) = decide (eV a < eV b)
  eq : ∀ a b, eB (A.eq a b) = decide (eV a = eV b)
  odd : ∀ a, eB (A.odd a) = decide (eV a % 2 = 1)
  tt : eB A.tt = true
  ff : eB A.ff = false
  and : ∀ x y, eB (A.and x y) = (eB x && eB y)
  or : ∀ x y, eB (A.or x y) = (eB x || eB y)
  not : ∀ x, eB (A.not x) = !eB x

section
variable {V B : Type} [A : Alg V B] (H : Hom V B)

def Hom.c (v : V × V) : ℤ × ℤ := (H.eV v.1, H.eV v.2)
def Hom.s (e : (V × V) × (V × V)) : (ℤ × ℤ) × (ℤ × ℤ) := (H.c e.1, H.c e.2)
def Hom.p (P : PieceG V) : PieceG ℤ := ⟨H.eV P.ox, H.eV P.oy, H.eV P.pw, H.eV P.ph, P.segs.map H.s⟩

theorem Hom.acc_h (w h : V) (s t : V × V) :
    H.eB (accG w h s t) = accG (V := ℤ) (B := Bool) (H.eV w) (H.eV h) (H.c s) (H.c t) := by
  simp only [accG, ne, le, H.k, H.add, H.sub, H.lt, H.eq, H.odd, H.and, H.or, H.not, Hom.c]
  rfl

theorem Hom.cutc_h (vert : Bool) (pos : V) (s : Bool) (y : V) :
    H.c (cutcG (A := A) vert pos s y) = cutcG (V := ℤ) (B := Bool) vert (H.eV pos) s (H.eV y) := by
  cases vert <;> cases s <;> simp [cutcG, Hom.c, H.sub, H.k] <;> rfl

theorem Hom.put_h (s : Bool) (e : (V × V) × (V × V)) (LR : List ((V × V) × (V × V)) × List ((V × V) × (V × V))) :
    ((putG s e LR).1.map H.s, (putG s e LR).2.map H.s) = putG s (H.s e) (LR.1.map H.s, LR.2.map H.s) := by
  cases s <;> simp [putG]

theorem Hom.split_h (vert : Bool) (pos : V) : ∀ (ks : List (Kind V)) (ss : List ((V × V) × (V × V)))
    (acc : List ((V × V) × (V × V)) × List ((V × V) × (V × V))),
    (splitG (A := A) vert pos ks ss acc).map (fun LR => (LR.1.map H.s, LR.2.map H.s)) =
      splitG (V := ℤ) (B := Bool) vert (H.eV pos) (ks.map (Kind.map H.eV)) (ss.map H.s)
        (acc.1.map H.s, acc.2.map H.s)
  | [], [], acc => by simp [splitG]
  | [], _ :: _, acc => by simp [splitG]
  | k :: ks, [], acc => by cases k <;> simp [splitG, Kind.map]
  | Kind.stay s :: ks, (a, b) :: ss, acc => by
    simp only [splitG, List.map_cons, Kind.map]
    rw [Hom.split_h vert pos ks ss, H.put_h]
  | Kind.cross s y :: ks, (a, b) :: ss, acc => by
    simp only [splitG, List.map_cons, Kind.map]
    rw [Hom.split_h vert pos ks ss, H.put_h, H.put_h]
    simp only [Hom.s, H.cutc_h]
  | Kind.exc s y z :: ks, (a, b) :: ss, acc => by
    simp only [splitG, List.map_cons, Kind.map]
    rw [Hom.split_h vert pos ks ss, H.put_h, H.put_h, H.put_h]
    simp only [Hom.s, H.cutc_h]

theorem Hom.lo_h (P : PieceG V) (vert : Bool) (pos : V) (L : List ((V × V) × (V × V))) :
    H.p (P.lo (A := A) vert pos L) = PieceG.lo (V := ℤ) (B := Bool) (A := inferInstance) (H.p P) vert (H.eV pos) (L.map H.s) := by
  cases vert <;> simp [PieceG.lo, Hom.p, H.sub] <;> rfl

theorem Hom.hi_h (P : PieceG V) (vert : Bool) (pos : V) (R : List ((V × V) × (V × V))) :
    H.p (P.hi (A := A) vert pos R) = PieceG.hi (V := ℤ) (B := Bool) (A := inferInstance) (H.p P) vert (H.eV pos) (R.map H.s) := by
  cases vert <;> simp [PieceG.hi, Hom.p, H.sub, H.add] <;> rfl

theorem Hom.inside_h (vert : Bool) (pos : V) (P : PieceG V) :
    H.eB (insideG vert pos P) = insideG (V := ℤ) (B := Bool) vert (H.eV pos) (H.p P) := by
  cases vert <;> simp [insideG, Hom.p, H.and, H.lt, H.add] <;> rfl

theorem Hom.leaf_h (P : PieceG V) : H.eB (leafG P) = leafG (V := ℤ) (B := Bool) (H.p P) := by
  obtain ⟨ox, oy, pw, ph, segs⟩ := P
  match segs with
  | [] => simp [leafG, Hom.p, H.ff]; rfl
  | [(a, b)] =>
    simp only [leafG, Hom.p, List.map_cons, List.map_nil, Hom.s, H.or, H.and, H.not, H.eq, H.k,
      eqCG, regionG, le, H.lt, H.add, H.acc_h, H.sub, Hom.c]
    rfl
  | _ :: _ :: _ => simp [leafG, Hom.p, H.ff]; rfl

theorem Hom.check_h : ∀ (T : CTree V) (P : PieceG V),
    H.eB (checkG T P) = checkG (V := ℤ) (B := Bool) (T.map H.eV) (H.p P)
  | CTree.leaf, P => H.leaf_h P
  | CTree.cut vert pos ks l r, P => by
    have hs := H.split_h vert pos ks P.segs ([], [])
    simp only [checkG, CTree.map, H.and, H.inside_h]
    congr 1
    have hseg : (H.p P).segs = P.segs.map H.s := rfl
    rw [hseg]
    simp only [List.map_nil] at hs
    rw [← hs]
    match h : splitG (A := A) vert pos ks P.segs ([], []) with
    | some (L, R) =>
      simp only [Option.map_some, H.and, Hom.check_h l, Hom.check_h r, H.lo_h, H.hi_h]
      rfl
    | none => simp [H.ff]; rfl

end

end ZZN.Cut

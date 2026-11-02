/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.BoxK.Slice

@[expose] public section

/-!
# The lane checks with direct `Nat` operations

The kernel evaluates `a &&& b` on numbers by unfolding `HAnd.hAnd`, `AndOp.and` and the instance
before reaching `Nat.land`, which it computes natively; the same holds for the other operators.
These copies of the lane primitives, `accS` and the cut-tree checker call `Nat.land`, `Nat.lor`,
`Nat.xor`, `Nat.shiftRight`, `Nat.add`, `Nat.sub`, `Nat.mul` and `Nat.div` directly, which the
kernel checks about 30% faster on template pairs. Each copy is equal to its original
(`coverFD_eq`), so the soundness proofs carry over unchanged.
-/

namespace ZZN.Cut

open ZZN ZZN.Lane GridHam ZZN.BoxK

local infixl:58 " ∧ₙ " => Nat.land
local infixl:58 " ⊕ₙ " => Nat.xor
local infixl:55 " ∨ₙ " => Nat.lor
local infixl:75 " ≫ₙ " => Nat.shiftRight
local infixl:65 " +ₙ " => Nat.add
local infixl:65 " -ₙ " => Nat.sub
local infixl:70 " *ₙ " => Nat.mul
local infixl:70 " /ₙ " => Nat.div

def oneSD (N : ℕ) : ℕ := (Bs ^ N -ₙ 1) /ₙ (Bs -ₙ 1)

def GSD (N : ℕ) : ℕ := oneSD N *ₙ 128

def MSD (N : ℕ) : ℕ := oneSD N *ₙ 127

def subSD (N a b : ℕ) : ℕ :=
  let r := a +ₙ GSD N -ₙ b
  let gm := r ∧ₙ GSD N
  r ∧ₙ (gm /ₙ 128 *ₙ 127)

def ltSD (N a b : ℕ) : ℕ := GSD N ⊕ₙ ((a +ₙ GSD N -ₙ b) ∧ₙ GSD N)

def ltBD (N a b : ℕ) : ℕ := ltSD N a b ≫ₙ 7

def eqBD (N a b : ℕ) : ℕ := (GSD N ⊕ₙ (((a ⊕ₙ b) +ₙ MSD N) ∧ₙ GSD N)) ≫ₙ 7

def iteSD (N c a b : ℕ) : ℕ :=
  let sp := (c ∧ₙ oneSD N) *ₙ 127
  (a ∧ₙ sp) ∨ₙ (b ∧ₙ (MSD N ⊕ₙ sp))

def kSD (N c : ℕ) : ℕ := c *ₙ oneSD N

def notSD (N x : ℕ) : ℕ := x ⊕ₙ oneSD N

def accSD (N W H S1 S2 T1 T2 : ℕ) : ℕ :=
  let o := oneSD N
  let z := kSD N 0
  let one := kSD N 1
  let ps := S1 ⊕ₙ S2
  let pt := T1 ⊕ₙ T2
  let ow := W
  let oh := H
  let cc := ((ow ∧ₙ oh) ∧ₙ (notSD N ps ∧ₙ notSD N pt)) ∨ₙ (notSD N (ow ∧ₙ oh) ∧ₙ (ps ⊕ₙ pt))
  let w1 := subSD N W one
  let h1 := subSD N H one
  let corner := fun (v1 v2 : ℕ) => (eqBD N v1 z ∨ₙ eqBD N v1 w1) ∧ₙ (eqBD N v2 z ∨ₙ eqBD N v2 h1)
  let isW1 := eqBD N W one
  let fx := iteSD N isW1 z w1
  let fy := iteSD N isW1 h1 z
  let f1 := notSD N ((eqBD N S1 z ∧ₙ eqBD N S2 z ∧ₙ eqBD N T1 fx ∧ₙ eqBD N T2 fy) ∨ₙ
    (eqBD N S1 fx ∧ₙ eqBD N S2 fy ∧ₙ eqBD N T1 z ∧ₙ eqBD N T2 z))
  let f2 := notSD N (corner S1 S2) ∧ₙ notSD N (corner T1 T2) ∧ₙ
    ((eqBD N W (kSD N 2) ∧ₙ eqBD N S2 T2) ∨ₙ (eqBD N H (kSD N 2) ∧ₙ eqBD N S1 T1))
  let isW3 := eqBD N W (kSD N 3)
  let oppOdd := (isW3 ∧ₙ oh) ∨ₙ (notSD N isW3 ∧ₙ ow)
  let c0 := iteSD N isW3 S2 S1
  let c1 := iteSD N isW3 T2 T1
  let oc := iteSD N isW3 S1 S2
  let gr := ltBD N c1 c0
  let dist := iteSD N gr (subSD N c0 c1) (subSD N c1 c0)
  let e1 := eqBD N oc one
  let dsat := (e1 ∧ₙ ltBD N z dist) ∨ₙ (notSD N e1 ∧ₙ ltBD N one dist)
  let f3 := notSD N oppOdd ∧ₙ (ps ⊕ₙ pt) ∧ₙ dsat ∧ₙ ((gr ∧ₙ notSD N ps) ∨ₙ (notSD N gr ∧ₙ ps))
  let c1w := eqBD N W one ∨ₙ eqBD N H one
  let c2w := eqBD N W (kSD N 2) ∨ₙ eqBD N H (kSD N 2)
  let c3w := eqBD N W (kSD N 3) ∨ₙ eqBD N H (kSD N 3)
  let forb := (c1w ∧ₙ f1) ∨ₙ (notSD N c1w ∧ₙ ((c2w ∧ₙ f2) ∨ₙ (notSD N c2w ∧ₙ (c3w ∧ₙ f3))))
  (cc ∧ₙ notSD N forb) ∧ₙ o

section ops
variable (N : ℕ)

def maxSD (a b : ℕ) : ℕ := iteSD N (ltBD N a b) b a

def bSD (b : Bool) : ℕ := if b then oneSD N else 0

def cutcFD (vert : Bool) (pos : ℕ) (s : Bool) (y : ℕ) : FC :=
  if vert then (y, if s then pos else subSD N pos (kSD N 1)) else (if s then pos else pos -ₙ 1, y)

def putFD (s : Bool) (e : FC × FC) (LR : List (FC × FC) × List (FC × FC)) :
    List (FC × FC) × List (FC × FC) :=
  if s then (LR.1, LR.2 ++ [e]) else (LR.1 ++ [e], LR.2)

def splitFD (vert : Bool) (pos : ℕ) :
    List (Kind ℕ) → List (FC × FC) → List (FC × FC) × List (FC × FC) →
      Option (List (FC × FC) × List (FC × FC))
  | [], [], acc => some acc
  | Kind.stay s :: ks, (a, b) :: ss, acc => splitFD vert pos ks ss (putFD s (a, b) acc)
  | Kind.cross s y :: ks, (a, b) :: ss, acc =>
    splitFD vert pos ks ss
      (putFD (!s) (cutcFD N vert pos (!s) y, b) (putFD s (a, cutcFD N vert pos s y) acc))
  | Kind.exc s y z :: ks, (a, b) :: ss, acc =>
    splitFD vert pos ks ss
      (putFD (!s) (cutcFD N vert pos (!s) y, cutcFD N vert pos (!s) z)
        (putFD s (cutcFD N vert pos s z, b) (putFD s (a, cutcFD N vert pos s y) acc)))
  | _, _, _ => none

def PieceF.loD (P : PieceF) (vert : Bool) (pos : ℕ) (L : List (FC × FC)) : PieceF :=
  if vert then ⟨P.ox, P.pw, P.oy, maxSD N P.oy pos, L⟩ else ⟨P.ox, pos -ₙ P.ox, P.oy, P.ey, L⟩

def PieceF.hiD (P : PieceF) (vert : Bool) (pos : ℕ) (R : List (FC × FC)) : PieceF :=
  if vert then ⟨P.ox, P.pw, pos, maxSD N pos P.ey, R⟩ else ⟨pos, P.ox +ₙ P.pw -ₙ pos, P.oy, P.ey, R⟩

def insideFD (vert : Bool) (pos : ℕ) (P : PieceF) : ℕ :=
  if vert then ltBD N P.oy pos ∧ₙ ltBD N pos P.ey
  else bSD N (decide (P.ox < pos) && decide (pos < P.ox +ₙ P.pw))

def regionFD (P : PieceF) (v : FC) : ℕ :=
  bSD N (decide (P.ox ≤ v.1) && decide (v.1 < P.ox +ₙ P.pw)) ∧ₙ (notSD N (ltBD N v.2 P.oy) ∧ₙ ltBD N v.2 P.ey)

def eqFD (a b : FC) : ℕ := bSD N (decide (a.1 = b.1)) ∧ₙ eqBD N a.2 b.2

def leafFD (P : PieceF) : ℕ :=
  match P.segs with
  | [(a, b)] =>
    let e := eqFD N a b
    let one := bSD N (decide (P.pw = 1) && decide (a.1 = P.ox)) ∧ₙ
      (eqBD N (subSD N P.ey P.oy) (kSD N 1) ∧ₙ eqBD N a.2 P.oy)
    let acc := (regionFD N P a ∧ₙ regionFD N P b) ∧ₙ
      accSD N (kSD N P.pw) (subSD N P.ey P.oy) (kSD N (a.1 -ₙ P.ox)) (subSD N a.2 P.oy) (kSD N (b.1 -ₙ P.ox))
        (subSD N b.2 P.oy)
    (e ∧ₙ one) ∨ₙ (notSD N e ∧ₙ acc)
  | _ => 0

def checkFD : CTree ℕ → PieceF → ℕ
  | CTree.leaf, P => leafFD N P
  | CTree.cut vert pos ks l r, P =>
    insideFD N vert pos P ∧ₙ
      match splitFD N vert pos ks P.segs ([], []) with
      | some (L, R) => checkFD l (PieceF.loD N P vert pos L) ∧ₙ checkFD r (PieceF.hiD N P vert pos R)
      | none => 0

end ops

def offFD (N a : ℕ) (o : ℤ) : ℕ := if 0 ≤ o then a +ₙ kSD N o.toNat else subSD N a (kSD N (-o).toNat)

def posFD (N y0 y1 y2 y3 h : ℕ) (p : TPos) : ℕ := offFD N (anchors y0 y1 y2 y3 (kSD N h) p.1) p.2

def rootFD (N w h : ℕ) (x Y : Fin 4 → ℕ) : PieceF :=
  ⟨0, w, 0, kSD N h, [((x 0, Y 0), (x 1, Y 1)), ((x 2, Y 2), (x 3, Y 3))]⟩

def tcheckFD (N w h : ℕ) (x Y : Fin 4 → ℕ) (T : CTree TPos) : ℕ :=
  checkFD N (inst (posN (x 0) (x 1) (x 2) (x 3) w) (posFD N (Y 0) (Y 1) (Y 2) (Y 3) h) T) (rootFD N w h x Y)

def coverFD (N w h : ℕ) (x Y : Fin 4 → ℕ) : List (CTree TPos × Sym) → ℕ
  | [] => 0
  | (T, σ) :: ps => (if σ.tr || σ.ry || !tsmall T then 0
      else tcheckFD N w h (xS σ w x) (fun i => Y (lperm σ i)) T) ∨ₙ coverFD N w h x Y ps

/-! ### Each copy equals its original -/

theorem subSD_eq (N a b : ℕ) : subSD N a b = subS N a b := rfl
theorem ltBD_eq (N a b : ℕ) : ltBD N a b = ltB N a b := rfl
theorem eqBD_eq (N a b : ℕ) : eqBD N a b = eqB N a b := rfl
theorem iteSD_eq (N c a b : ℕ) : iteSD N c a b = iteS N c a b := rfl
theorem kSD_eq (N c : ℕ) : kSD N c = ZZN.Lane.kS N c := rfl
theorem accSD_eq (N W H S1 S2 T1 T2 : ℕ) : accSD N W H S1 S2 T1 T2 = accS N W H S1 S2 T1 T2 := rfl

theorem cutcFD_eq (N : ℕ) (vert : Bool) (pos : ℕ) (s : Bool) (y : ℕ) :
    cutcFD N vert pos s y = cutcF N vert pos s y := rfl

theorem splitFD_eq (N : ℕ) (vert : Bool) (pos : ℕ) : ∀ (ks : List (Kind ℕ)) (ss : List (FC × FC))
    (acc : List (FC × FC) × List (FC × FC)), splitFD N vert pos ks ss acc = splitF N vert pos ks ss acc
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | Kind.stay _ :: _, [], _ => rfl
  | Kind.cross _ _ :: _, [], _ => rfl
  | Kind.exc _ _ _ :: _, [], _ => rfl
  | Kind.stay s :: ks, (a, b) :: ss, acc => by
    simp only [splitFD, splitF]; exact splitFD_eq N vert pos ks ss _
  | Kind.cross s y :: ks, (a, b) :: ss, acc => by
    simp only [splitFD, splitF, cutcFD_eq]; exact splitFD_eq N vert pos ks ss _
  | Kind.exc s y z :: ks, (a, b) :: ss, acc => by
    simp only [splitFD, splitF, cutcFD_eq]; exact splitFD_eq N vert pos ks ss _

theorem leafFD_eq (N : ℕ) (P : PieceF) : leafFD N P = leafF N P := rfl
theorem insideFD_eq (N : ℕ) (vert : Bool) (pos : ℕ) (P : PieceF) :
    insideFD N vert pos P = insideF N vert pos P := rfl
theorem loD_eq (N : ℕ) (P : PieceF) (vert : Bool) (pos : ℕ) (L : List (FC × FC)) :
    PieceF.loD N P vert pos L = P.lo N vert pos L := rfl
theorem hiD_eq (N : ℕ) (P : PieceF) (vert : Bool) (pos : ℕ) (R : List (FC × FC)) :
    PieceF.hiD N P vert pos R = P.hi N vert pos R := rfl

theorem checkFD_eq (N : ℕ) : ∀ (T : CTree ℕ) (P : PieceF), checkFD N T P = checkF N T P
  | CTree.leaf, P => leafFD_eq N P
  | CTree.cut vert pos ks l r, P => by
    simp only [checkFD, checkF, splitFD_eq, insideFD_eq, loD_eq, hiD_eq, checkFD_eq N l,
      checkFD_eq N r]
    rfl

theorem tcheckFD_eq (N w h : ℕ) (x Y : Fin 4 → ℕ) (T : CTree TPos) :
    tcheckFD N w h x Y T = tcheckF N w h x Y T := by
  simp only [tcheckFD, tcheckF, checkFD_eq]; rfl

theorem coverFD_eq (N w h : ℕ) (x Y : Fin 4 → ℕ) : ∀ ps : List (CTree TPos × Sym),
    coverFD N w h x Y ps = coverF N w h x Y ps
  | [] => rfl
  | (T, σ) :: ps => by simp only [coverFD, coverF, tcheckFD_eq, coverFD_eq N w h x Y ps]; rfl

end ZZN.Cut

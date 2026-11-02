-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Cut.Tree
import ZZN.Cut.AccS

/-!
# The cut-tree checker on lanes

`checkV N T P` runs `check` on every lane at once: positions and piece coordinates are lane
values (`LV`), the result is a lane Boolean (`LB`). `checkV_get`: lane `j` of the result is
`check` on lane `j` of the tree and the piece.
-/

namespace ZZN.Cut

open GridHam ZZN.Lane

abbrev VC := LV × LV

def VC.get (v : VC) (j : ℕ) : Coord := (v.1.get j, v.2.get j)

structure PieceV where
  ox : LV
  oy : LV
  pw : LV
  ph : LV
  segs : List (VC × VC)

def segGet (j : ℕ) (e : VC × VC) : Coord × Coord := (e.1.get j, e.2.get j)

def PieceV.get (P : PieceV) (j : ℕ) : Piece :=
  ⟨P.ox.get j, P.oy.get j, P.pw.get j, P.ph.get j, P.segs.map (segGet j)⟩

def cutcV (N : ℕ) (vert : Bool) (pos : LV) (s : Bool) (y : LV) : VC :=
  let x := if s then pos else LV.sub N pos (LV.k 1)
  if vert then (y, x) else (x, y)

def putV (s : Bool) (e : VC × VC) (LR : List (VC × VC) × List (VC × VC)) :
    List (VC × VC) × List (VC × VC) :=
  if s then (LR.1, LR.2 ++ [e]) else (LR.1 ++ [e], LR.2)

def splitV (N : ℕ) (vert : Bool) (pos : LV) :
    List (Kind LV) → List (VC × VC) → List (VC × VC) × List (VC × VC) →
      Option (List (VC × VC) × List (VC × VC))
  | [], [], acc => some acc
  | Kind.stay s :: ks, (a, b) :: ss, acc => splitV N vert pos ks ss (putV s (a, b) acc)
  | Kind.cross s y :: ks, (a, b) :: ss, acc =>
    splitV N vert pos ks ss
      (putV (!s) (cutcV N vert pos (!s) y, b) (putV s (a, cutcV N vert pos s y) acc))
  | Kind.exc s y z :: ks, (a, b) :: ss, acc =>
    splitV N vert pos ks ss
      (putV (!s) (cutcV N vert pos (!s) y, cutcV N vert pos (!s) z)
        (putV s (cutcV N vert pos s z, b) (putV s (a, cutcV N vert pos s y) acc)))
  | _, _, _ => none

def PieceV.lo (N : ℕ) (P : PieceV) (vert : Bool) (pos : LV) (L : List (VC × VC)) : PieceV :=
  if vert then ⟨P.ox, P.oy, P.pw, LV.sub N pos P.oy, L⟩ else ⟨P.ox, P.oy, LV.sub N pos P.ox, P.ph, L⟩

def PieceV.hi (N : ℕ) (P : PieceV) (vert : Bool) (pos : LV) (R : List (VC × VC)) : PieceV :=
  if vert then ⟨P.ox, pos, P.pw, LV.sub N (LV.add N P.oy P.ph) pos, R⟩
  else ⟨pos, P.oy, LV.sub N (LV.add N P.ox P.pw) pos, P.ph, R⟩

def insideV (N : ℕ) (vert : Bool) (pos : LV) (P : PieceV) : LB :=
  if vert then LB.and (LV.lt N P.oy pos) (LV.lt N pos (LV.add N P.oy P.ph))
  else LB.and (LV.lt N P.ox pos) (LV.lt N pos (LV.add N P.ox P.pw))

def regionV (N : ℕ) (P : PieceV) (v : VC) : LB :=
  LB.and (LB.and (LV.le N P.ox v.1) (LV.lt N v.1 (LV.add N P.ox P.pw)))
    (LB.and (LV.le N P.oy v.2) (LV.lt N v.2 (LV.add N P.oy P.ph)))

def eqVC (N : ℕ) (a b : VC) : LB := LB.and (LV.eq N a.1 b.1) (LV.eq N a.2 b.2)

def leafV (N : ℕ) (P : PieceV) : LB :=
  match P.segs with
  | [(a, b)] =>
    LB.ite N (eqVC N a b)
      (LB.and (LB.and (LV.eq N P.pw (LV.k 1)) (LV.eq N P.ph (LV.k 1))) (eqVC N a (P.ox, P.oy)))
      (LB.and (LB.and (regionV N P a) (regionV N P b))
        (accV2 N P.pw P.ph (LV.sub N a.1 P.ox, LV.sub N a.2 P.oy) (LV.sub N b.1 P.ox, LV.sub N b.2 P.oy)))
  | _ => LB.b false

def checkV (N : ℕ) : CTree LV → PieceV → LB
  | CTree.leaf, P => leafV N P
  | CTree.cut vert pos ks l r, P =>
    LB.and (insideV N vert pos P)
      (match splitV N vert pos ks P.segs ([], []) with
       | some (L, R) => LB.and (checkV N l (P.lo N vert pos L)) (checkV N r (P.hi N vert pos R))
       | none => LB.b false)

/-! ### Lane lemmas -/

section
variable {N j : ℕ} (hj : j < N)
include hj

theorem cutcV_get (vert : Bool) (pos : LV) (s : Bool) (y : LV) :
    (cutcV N vert pos s y).get j = cutc vert (pos.get j) s (y.get j) := by
  cases vert <;> cases s <;> simp [cutcV, cutc, VC.get, LV.at_sub hj]

theorem cutcV_get1 (vert : Bool) (pos : LV) (s : Bool) (y : LV) :
    (cutcV N vert pos s y).1.get j = (cutc vert (pos.get j) s (y.get j)).1 :=
  congrArg Prod.fst (cutcV_get hj vert pos s y)

theorem cutcV_get2 (vert : Bool) (pos : LV) (s : Bool) (y : LV) :
    (cutcV N vert pos s y).2.get j = (cutc vert (pos.get j) s (y.get j)).2 :=
  congrArg Prod.snd (cutcV_get hj vert pos s y)

omit hj in
theorem putV_get (s : Bool) (e : VC × VC) (LR : List (VC × VC) × List (VC × VC)) :
    ((putV s e LR).1.map (segGet j), (putV s e LR).2.map (segGet j)) =
      put s (segGet j e) (LR.1.map (segGet j), LR.2.map (segGet j)) := by
  cases s <;> simp [putV, put]

theorem splitV_get (vert : Bool) (pos : LV) : ∀ (ks : List (Kind LV)) (ss : List (VC × VC))
    (acc : List (VC × VC) × List (VC × VC)),
    (splitV N vert pos ks ss acc).map (fun LR => (LR.1.map (segGet j), LR.2.map (segGet j))) =
      split vert (pos.get j) (ks.map (Kind.map (·.get j))) (ss.map (segGet j))
        (acc.1.map (segGet j), acc.2.map (segGet j))
  | [], [], acc => by simp [splitV, split]
  | [], _ :: _, acc => by simp [splitV, split]
  | k :: ks, [], acc => by cases k <;> simp [splitV, split, Kind.map]
  | Kind.stay s :: ks, (a, b) :: ss, acc => by
    simp only [splitV, split, List.map_cons, Kind.map]
    rw [splitV_get vert pos ks ss, putV_get]
  | Kind.cross s y :: ks, (a, b) :: ss, acc => by
    simp only [splitV, split, List.map_cons, Kind.map]
    rw [splitV_get vert pos ks ss, putV_get, putV_get]
    simp only [segGet, cutcV_get hj]
  | Kind.exc s y z :: ks, (a, b) :: ss, acc => by
    simp only [splitV, split, List.map_cons, Kind.map]
    rw [splitV_get vert pos ks ss, putV_get, putV_get, putV_get]
    simp only [segGet, cutcV_get hj]

theorem lo_get (P : PieceV) (vert : Bool) (pos : LV) (L : List (VC × VC)) :
    (P.lo N vert pos L).get j = (P.get j).lo vert (pos.get j) (L.map (segGet j)) := by
  cases vert <;> simp [PieceV.lo, Piece.lo, PieceV.get, LV.at_sub hj]

theorem hi_get (P : PieceV) (vert : Bool) (pos : LV) (R : List (VC × VC)) :
    (P.hi N vert pos R).get j = (P.get j).hi vert (pos.get j) (R.map (segGet j)) := by
  cases vert <;> simp [PieceV.hi, Piece.hi, PieceV.get, LV.at_sub hj, LV.at_add hj]

theorem insideV_get (vert : Bool) (pos : LV) (P : PieceV) :
    (insideV N vert pos P).get j = inside vert (pos.get j) (P.get j) := by
  cases vert <;> simp only [insideV, inside, LB.at_and, LV.at_lt hj, LV.at_add hj, PieceV.get,
    Bool.false_eq_true, ite_false, ite_true] <;> rfl

theorem regionV_get (P : PieceV) (v : VC) :
    (regionV N P v).get j = (P.get j).regionB (v.get j) := by
  simp only [regionV, Piece.regionB, LB.at_and, LV.at_lt hj, LV.at_le hj, LV.at_add hj, PieceV.get,
    VC.get]
  rfl

theorem eqVC_get (a b : VC) : (eqVC N a b).get j = eqC (a.get j) (b.get j) := by
  simp only [eqVC, eqC, LB.at_and, LV.at_eq hj, VC.get]
  rfl

theorem leafV_get (P : PieceV) : (leafV N P).get j = leafOK (P.get j) := by
  obtain ⟨ox, oy, pw, ph, segs⟩ := P
  match segs with
  | [] => rfl
  | [(a, b)] =>
    simp only [leafV, leafOK, PieceV.get, List.map_cons, List.map_nil, segGet, LB.at_ite hj,
      eqVC_get hj, LB.at_and, LV.at_eq hj, LV.get_k, regionV_get hj, accV2_get hj, LV.at_sub hj]
    rfl
  | _ :: _ :: _ => rfl

end

/-- **Lane lemma.** Lane `j` of `checkV` is `check` on lane `j`. -/
theorem checkV_get {N j : ℕ} (hj : j < N) : ∀ (T : CTree LV) (P : PieceV),
    (checkV N T P).get j = check (T.map (·.get j)) (P.get j)
  | CTree.leaf, P => leafV_get hj P
  | CTree.cut vert pos ks l r, P => by
    have hs := splitV_get hj vert pos ks P.segs ([], [])
    simp only [checkV, check, CTree.map, LB.at_and, insideV_get hj]
    congr 1
    have hseg : (P.get j).segs = P.segs.map (segGet j) := rfl
    rw [hseg]
    simp only [List.map_nil] at hs
    rw [← hs]
    match h : splitV N vert pos ks P.segs ([], []) with
    | some (L, R) =>
      simp only [Option.map_some, LB.at_and, checkV_get hj l, checkV_get hj r, lo_get hj, hi_get hj]
    | none => rfl

end ZZN.Cut

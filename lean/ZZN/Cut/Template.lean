-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Cut.CheckV

/-!
# Templates

A template is a cut tree whose positions are `(anchor, offset)`. On the axis of a position the
anchors are: 0–3 the coordinate of `s0 t0 s1 t1`, 4 the low boundary `0`, 5 the side length.
A cut position lies on the cut's own axis (rows if `vert = false`); crossing cells lie on the other
axis.

`tcheck T I`: the instantiated tree checks on `I`; `solvable_of_tcheck`. `tcheckV`: the lane
version for one row tuple, all column tuples at once; `tcheckV_get`.
-/

namespace ZZN.Cut

open GridHam ZZN.Lane

abbrev TPos := ℕ × ℤ

/-- Add a signed offset (truncated at 0). -/
def offN (a : ℕ) (o : ℤ) : ℕ := if 0 ≤ o then a + o.toNat else a - (-o).toNat

def offV (N : ℕ) (a : LV) (o : ℤ) : LV :=
  if 0 ≤ o then LV.add N a (LV.k o.toNat) else LV.sub N a (LV.k (-o).toNat)

theorem offV_get {N j : ℕ} (hj : j < N) (a : LV) (o : ℤ) : (offV N a o).get j = offN (a.get j) o := by
  unfold offV offN; split_ifs <;> simp [LV.at_add hj, LV.at_sub hj]

def instK {α : Type} (f : TPos → α) : Kind TPos → Kind α
  | Kind.stay s => Kind.stay s
  | Kind.cross s y => Kind.cross s (f y)
  | Kind.exc s y z => Kind.exc s (f y) (f z)

/-- Instantiate positions: `fR` on rows, `fC` on columns. -/
def inst {α : Type} (fR fC : TPos → α) : CTree TPos → CTree α
  | CTree.leaf => CTree.leaf
  | CTree.cut vert pos ks l r =>
    CTree.cut vert (if vert then fC pos else fR pos)
      (ks.map (instK (if vert then fR else fC))) (inst fR fC l) (inst fR fC r)

theorem instK_map {α β : Type} (f : TPos → α) (g : α → β) (k : Kind TPos) :
    (instK f k).map g = instK (g ∘ f) k := by
  cases k <;> rfl

theorem inst_map {α β : Type} (fR fC : TPos → α) (g : α → β) : ∀ T : CTree TPos,
    (inst fR fC T).map g = inst (g ∘ fR) (g ∘ fC) T
  | CTree.leaf => rfl
  | CTree.cut vert pos ks l r => by
    simp only [inst, CTree.map, inst_map fR fC g l, inst_map fR fC g r, List.map_map]
    cases vert <;> simp [instK_map, Function.comp_def]

/-- Anchor values of an instance on one axis. -/
def anchors (e0 e1 e2 e3 n : ℕ) (a : ℕ) : ℕ :=
  match a with
  | 0 => e0 | 1 => e1 | 2 => e2 | 3 => e3 | 4 => 0 | _ => n

def posN (e0 e1 e2 e3 n : ℕ) (p : TPos) : ℕ := offN (anchors e0 e1 e2 e3 n p.1) p.2

def tcheck (T : CTree TPos) (I : Inst) : Bool :=
  check (inst (posN I.s0.1 I.t0.1 I.s1.1 I.t1.1 I.w) (posN I.s0.2 I.t0.2 I.s1.2 I.t1.2 I.h) T)
    (rootPiece I)

theorem solvable_of_tcheck {I : Inst} (T : CTree TPos) (h : tcheck T I = true) : Solvable I :=
  solvable_of_check _ h

/-! ### Lanes: one row tuple, column values as lane vectors -/

def anchorsV (e0 e1 e2 e3 n : LV) (a : ℕ) : LV :=
  match a with
  | 0 => e0 | 1 => e1 | 2 => e2 | 3 => e3 | 4 => LV.k 0 | _ => n

def posV (N : ℕ) (e0 e1 e2 e3 n : LV) (p : TPos) : LV := offV N (anchorsV e0 e1 e2 e3 n p.1) p.2

/-- Row tuple `x`, column lanes `y`, box `w × h`. -/
def rootV (w h : ℕ) (x : Fin 4 → ℕ) (y : Fin 4 → LV) : PieceV :=
  ⟨LV.k 0, LV.k 0, LV.k w, LV.k h, [((LV.k (x 0), y 0), (LV.k (x 1), y 1)),
    ((LV.k (x 2), y 2), (LV.k (x 3), y 3))]⟩

def tcheckV (N w h : ℕ) (x : Fin 4 → ℕ) (y : Fin 4 → LV) (T : CTree TPos) : LB :=
  checkV N (inst (posV N (LV.k (x 0)) (LV.k (x 1)) (LV.k (x 2)) (LV.k (x 3)) (LV.k w))
    (posV N (y 0) (y 1) (y 2) (y 3) (LV.k h)) T) (rootV w h x y)

/-- The instance in lane `j`. -/
def laneInst (w h : ℕ) (x : Fin 4 → ℕ) (y : Fin 4 → LV) (j : ℕ) : Inst :=
  ⟨w, h, (x 0, (y 0).get j), (x 1, (y 1).get j), (x 2, (y 2).get j), (x 3, (y 3).get j)⟩

theorem tcheckV_get {N j : ℕ} (hj : j < N) (w h : ℕ) (x : Fin 4 → ℕ) (y : Fin 4 → LV)
    (T : CTree TPos) : (tcheckV N w h x y T).get j = tcheck T (laneInst w h x y j) := by
  unfold tcheckV tcheck
  rw [checkV_get hj, inst_map]
  congr 1
  · congr 1 <;> funext p <;> obtain ⟨a, o⟩ := p <;>
      simp only [Function.comp, posV, posN, offV_get hj, laneInst] <;>
      rcases a with _ | _ | _ | _ | _ | a <;> rfl

end ZZN.Cut

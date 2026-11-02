-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Cut.AccS
import ZZN.Cut.Template

/-!
# Cut trees on 8-bit lanes, rows as scalars

The kernel spends most of a lane check on the dispatch of `LV` (constant, field and plane forms).
Here every value has a fixed form, chosen by axis: rows are scalars (the row tuple is fixed in a
slice), columns are 8-bit lane words. A piece keeps its column end `ey = oy + ph` in place of its
height, so lane values are positions, maxima and truncated differences, never sums; with column
inputs below 32 and template offsets in `[-63, 63]` every lane stays below 128 (`Sm`), which the
lane comparisons need. Lane `j` of `checkF` is `check` on lane `j` (`checkF_get`).
-/

namespace ZZN.Cut

open GridHam ZZN.Lane

/-- A cell: scalar row, column lanes. -/
abbrev FC := ℕ × ℕ

def FC.get (j : ℕ) (v : FC) : Coord := (v.1, fld v.2 j)

def segF (j : ℕ) (e : FC × FC) : Coord × Coord := (e.1.get j, e.2.get j)

structure PieceF where
  ox : ℕ
  pw : ℕ
  oy : ℕ
  ey : ℕ
  segs : List (FC × FC)

def PieceF.get (j : ℕ) (P : PieceF) : Piece :=
  ⟨P.ox, fld P.oy j, P.pw, fld P.ey j - fld P.oy j, P.segs.map (segF j)⟩

/-- Lane `j` of a position: lanes on column positions, the scalar itself on row positions. -/
def lget (lane : Bool) (j v : ℕ) : ℕ := if lane then fld v j else v

def CTree.getF (j : ℕ) : CTree ℕ → CTree ℕ
  | CTree.leaf => CTree.leaf
  | CTree.cut vert pos ks l r =>
    CTree.cut vert (lget vert j pos) (ks.map (Kind.map (lget (!vert) j))) (l.getF j) (r.getF j)

section ops
variable (N : ℕ)

/-- Lane-wise maximum. -/
def maxS (a b : ℕ) : ℕ := iteS N (ltB N a b) b a

/-- All lanes set where `b` holds. -/
def bS (b : Bool) : ℕ := if b then oneS N else 0

def cutcF (vert : Bool) (pos : ℕ) (s : Bool) (y : ℕ) : FC :=
  if vert then (y, if s then pos else subS N pos (kS N 1)) else (if s then pos else pos - 1, y)

def putF (s : Bool) (e : FC × FC) (LR : List (FC × FC) × List (FC × FC)) :
    List (FC × FC) × List (FC × FC) :=
  if s then (LR.1, LR.2 ++ [e]) else (LR.1 ++ [e], LR.2)

def splitF (vert : Bool) (pos : ℕ) :
    List (Kind ℕ) → List (FC × FC) → List (FC × FC) × List (FC × FC) →
      Option (List (FC × FC) × List (FC × FC))
  | [], [], acc => some acc
  | Kind.stay s :: ks, (a, b) :: ss, acc => splitF vert pos ks ss (putF s (a, b) acc)
  | Kind.cross s y :: ks, (a, b) :: ss, acc =>
    splitF vert pos ks ss
      (putF (!s) (cutcF N vert pos (!s) y, b) (putF s (a, cutcF N vert pos s y) acc))
  | Kind.exc s y z :: ks, (a, b) :: ss, acc =>
    splitF vert pos ks ss
      (putF (!s) (cutcF N vert pos (!s) y, cutcF N vert pos (!s) z)
        (putF s (cutcF N vert pos s z, b) (putF s (a, cutcF N vert pos s y) acc)))
  | _, _, _ => none

def PieceF.lo (P : PieceF) (vert : Bool) (pos : ℕ) (L : List (FC × FC)) : PieceF :=
  if vert then ⟨P.ox, P.pw, P.oy, maxS N P.oy pos, L⟩ else ⟨P.ox, pos - P.ox, P.oy, P.ey, L⟩

def PieceF.hi (P : PieceF) (vert : Bool) (pos : ℕ) (R : List (FC × FC)) : PieceF :=
  if vert then ⟨P.ox, P.pw, pos, maxS N pos P.ey, R⟩ else ⟨pos, P.ox + P.pw - pos, P.oy, P.ey, R⟩

def insideF (vert : Bool) (pos : ℕ) (P : PieceF) : ℕ :=
  if vert then ltB N P.oy pos &&& ltB N pos P.ey
  else bS N (decide (P.ox < pos) && decide (pos < P.ox + P.pw))

def regionF (P : PieceF) (v : FC) : ℕ :=
  bS N (decide (P.ox ≤ v.1) && decide (v.1 < P.ox + P.pw)) &&& (notS N (ltB N v.2 P.oy) &&& ltB N v.2 P.ey)

def eqF (a b : FC) : ℕ := bS N (decide (a.1 = b.1)) &&& eqB N a.2 b.2

def leafF (P : PieceF) : ℕ :=
  match P.segs with
  | [(a, b)] =>
    let e := eqF N a b
    let one := bS N (decide (P.pw = 1) && decide (a.1 = P.ox)) &&&
      (eqB N (subS N P.ey P.oy) (kS N 1) &&& eqB N a.2 P.oy)
    let acc := (regionF N P a &&& regionF N P b) &&&
      accS N (kS N P.pw) (subS N P.ey P.oy) (kS N (a.1 - P.ox)) (subS N a.2 P.oy) (kS N (b.1 - P.ox))
        (subS N b.2 P.oy)
    (e &&& one) ||| (notS N e &&& acc)
  | _ => 0

def checkF : CTree ℕ → PieceF → ℕ
  | CTree.leaf, P => leafF N P
  | CTree.cut vert pos ks l r, P =>
    insideF N vert pos P &&&
      match splitF N vert pos ks P.segs ([], []) with
      | some (L, R) => checkF l (P.lo N vert pos L) &&& checkF r (P.hi N vert pos R)
      | none => 0

end ops

/-! ### Smallness -/

/-- A position: below 128 as a scalar, or every lane below 128. -/
def PosOK (N : ℕ) (lane : Bool) (v : ℕ) : Prop := if lane then Sm N v else v < 128

def CellOK (N : ℕ) (v : FC) : Prop := v.1 < 128 ∧ Sm N v.2

def SegsOK (N : ℕ) (ss : List (FC × FC)) : Prop := ∀ e ∈ ss, CellOK N e.1 ∧ CellOK N e.2

def PieceF.OK (N : ℕ) (P : PieceF) : Prop :=
  P.ox + P.pw < 128 ∧ Sm N P.oy ∧ Sm N P.ey ∧ (∀ j, fld P.oy j ≤ fld P.ey j) ∧ SegsOK N P.segs

def KindOK (N : ℕ) (lane : Bool) : Kind ℕ → Prop
  | Kind.stay _ => True
  | Kind.cross _ y => PosOK N lane y
  | Kind.exc _ y z => PosOK N lane y ∧ PosOK N lane z

def TOK (N : ℕ) : CTree ℕ → Prop
  | CTree.leaf => True
  | CTree.cut vert pos ks l r => PosOK N vert pos ∧ (∀ k ∈ ks, KindOK N (!vert) k) ∧ TOK N l ∧ TOK N r

theorem Sm_maxS {N a b : ℕ} (ha : Sm N a) (hb : Sm N b) : Sm N (maxS N a b) := Sm_iteS hb ha

theorem fld_maxS {N a b j : ℕ} (hj : j < N) (ha : Sm N a) (hb : Sm N b) :
    fld (maxS N a b) j = max (fld a j) (fld b j) := by
  unfold maxS
  rw [fld_iteS hb.2 ha.2 hj, testBit_ltB ha hb hj]
  by_cases h : fld a j < fld b j
  · simp [h]; omega
  · simp [h]; omega

theorem testBit_bS {N j : ℕ} (hj : j < N) (b : Bool) : (bS N b).testBit (8 * j) = b := by
  cases b <;> simp [bS, testBit_oneS, hj]

theorem cutcF_ok {N : ℕ} (vert : Bool) {pos y : ℕ} (hp : PosOK N vert pos) (hy : PosOK N (!vert) y)
    (s : Bool) : CellOK N (cutcF N vert pos s y) := by
  cases vert <;> cases s <;> simp only [PosOK, Bool.not_false, Bool.not_true, ite_true,
    ite_false, Bool.false_eq_true] at hp hy <;> simp only [cutcF, CellOK, Bool.false_eq_true,
    ite_false, ite_true]
  · exact ⟨by omega, hy⟩
  · exact ⟨hp, hy⟩
  · exact ⟨hy, Sm_subS hp (Sm_kS (by norm_num))⟩
  · exact ⟨hy, hp⟩

section
variable {N j : ℕ} (hj : j < N)
include hj

theorem cutcF_get (vert : Bool) {pos y : ℕ} (hp : PosOK N vert pos) (s : Bool) :
    (cutcF N vert pos s y).get j = cutc vert (lget vert j pos) s (lget (!vert) j y) := by
  cases vert <;> cases s <;> simp only [PosOK, ite_true, ite_false, Bool.false_eq_true] at hp <;>
    simp [cutcF, cutc, FC.get, lget]
  rw [fld_subS hp (Sm_kS (by norm_num)), fld_kS (by norm_num) hj]

omit hj in
theorem putF_map (s : Bool) (e : FC × FC) (LR : List (FC × FC) × List (FC × FC)) :
    ((putF s e LR).1.map (segF j), (putF s e LR).2.map (segF j)) =
      put s (segF j e) (LR.1.map (segF j), LR.2.map (segF j)) := by
  cases s <;> simp [putF, put]

theorem splitF_get (vert : Bool) {pos : ℕ} (hp : PosOK N vert pos) :
    ∀ (ks : List (Kind ℕ)) (ss : List (FC × FC)) (acc : List (FC × FC) × List (FC × FC)),
    (splitF N vert pos ks ss acc).map (fun LR => (LR.1.map (segF j), LR.2.map (segF j))) =
      split vert (lget vert j pos) (ks.map (Kind.map (lget (!vert) j))) (ss.map (segF j))
        (acc.1.map (segF j), acc.2.map (segF j))
  | [], [], acc => by simp [splitF, split]
  | [], _ :: _, acc => by simp [splitF, split]
  | k :: ks, [], acc => by cases k <;> simp [splitF, split, Kind.map]
  | Kind.stay s :: ks, (a, b) :: ss, acc => by
    simp only [splitF, split, List.map_cons, Kind.map]
    rw [splitF_get vert hp ks ss, putF_map (j := j)]
  | Kind.cross s y :: ks, (a, b) :: ss, acc => by
    simp only [splitF, split, List.map_cons, Kind.map]
    rw [splitF_get vert hp ks ss, putF_map (j := j), putF_map (j := j)]
    simp only [segF, cutcF_get hj vert hp]
  | Kind.exc s y z :: ks, (a, b) :: ss, acc => by
    simp only [splitF, split, List.map_cons, Kind.map]
    rw [splitF_get vert hp ks ss, putF_map (j := j), putF_map (j := j), putF_map (j := j)]
    simp only [segF, cutcF_get hj vert hp]

end

theorem putF_ok {N : ℕ} {s : Bool} {e : FC × FC} {LR : List (FC × FC) × List (FC × FC)}
    (he : CellOK N e.1 ∧ CellOK N e.2) (h1 : SegsOK N LR.1) (h2 : SegsOK N LR.2) :
    SegsOK N (putF s e LR).1 ∧ SegsOK N (putF s e LR).2 := by
  cases s <;> refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;>
    simp only [putF, Bool.false_eq_true, ite_false, ite_true, List.mem_append,
      List.mem_singleton] at hx
  · rcases hx with hx | rfl
    exacts [h1 x hx, he]
  · exact h2 x hx
  · exact h1 x hx
  · rcases hx with hx | rfl
    exacts [h2 x hx, he]

theorem splitF_ok {N : ℕ} (vert : Bool) {pos : ℕ} (hp : PosOK N vert pos) :
    ∀ (ks : List (Kind ℕ)) (ss : List (FC × FC)) (acc : List (FC × FC) × List (FC × FC)),
    (∀ k ∈ ks, KindOK N (!vert) k) → SegsOK N ss → SegsOK N acc.1 → SegsOK N acc.2 →
    ∀ L R, splitF N vert pos ks ss acc = some (L, R) → SegsOK N L ∧ SegsOK N R
  | [], [], acc, _, _, h1, h2, L, R, h => by
    simp only [splitF, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨h1, h2⟩
  | [], _ :: _, _, _, _, _, _, _, _, h => by simp [splitF] at h
  | k :: ks, [], _, _, _, _, _, _, _, h => by cases k <;> simp [splitF] at h
  | Kind.stay s :: ks, (a, b) :: ss, acc, hk, hs, h1, h2, L, R, h => by
    simp only [splitF] at h
    have hab := hs (a, b) (by simp)
    have := putF_ok (s := s) hab h1 h2
    exact splitF_ok vert hp ks ss _ (fun k hk' => hk k (by simp [hk'])) (fun e he => hs e (by simp [he]))
      this.1 this.2 L R h
  | Kind.cross s y :: ks, (a, b) :: ss, acc, hk, hs, h1, h2, L, R, h => by
    simp only [splitF] at h
    have hab := hs (a, b) (by simp)
    have hy : PosOK N (!vert) y := by simpa [KindOK] using hk (Kind.cross s y) (by simp)
    have c1 := cutcF_ok vert hp hy s
    have c2 := cutcF_ok vert hp hy (!s)
    have p1 := putF_ok (s := s) (e := (a, cutcF N vert pos s y)) ⟨hab.1, c1⟩ h1 h2
    have p2 := putF_ok (s := !s) (e := (cutcF N vert pos (!s) y, b)) ⟨c2, hab.2⟩ p1.1 p1.2
    exact splitF_ok vert hp ks ss _ (fun k hk' => hk k (by simp [hk'])) (fun e he => hs e (by simp [he]))
      p2.1 p2.2 L R h
  | Kind.exc s y z :: ks, (a, b) :: ss, acc, hk, hs, h1, h2, L, R, h => by
    simp only [splitF] at h
    have hab := hs (a, b) (by simp)
    have hyz : PosOK N (!vert) y ∧ PosOK N (!vert) z := by simpa [KindOK] using hk (Kind.exc s y z) (by simp)
    have p1 := putF_ok (s := s) (e := (a, cutcF N vert pos s y)) ⟨hab.1, cutcF_ok vert hp hyz.1 s⟩ h1 h2
    have p2 := putF_ok (s := s) (e := (cutcF N vert pos s z, b)) ⟨cutcF_ok vert hp hyz.2 s, hab.2⟩
      p1.1 p1.2
    have p3 := putF_ok (s := !s) (e := (cutcF N vert pos (!s) y, cutcF N vert pos (!s) z))
      ⟨cutcF_ok vert hp hyz.1 (!s), cutcF_ok vert hp hyz.2 (!s)⟩ p2.1 p2.2
    exact splitF_ok vert hp ks ss _ (fun k hk' => hk k (by simp [hk'])) (fun e he => hs e (by simp [he]))
      p3.1 p3.2 L R h

theorem lo_ok {N : ℕ} {P : PieceF} (hP : P.OK N) (vert : Bool) {pos : ℕ} (hp : PosOK N vert pos)
    {L : List (FC × FC)} (hL : SegsOK N L) : (P.lo N vert pos L).OK N := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hP
  cases vert <;> simp only [PosOK, ite_true, ite_false, Bool.false_eq_true] at hp <;>
    simp only [PieceF.lo, PieceF.OK, ite_true, ite_false, Bool.false_eq_true]
  · exact ⟨by omega, h2, h3, h4, hL⟩
  · refine ⟨h1, h2, Sm_maxS h2 hp, fun j => ?_, hL⟩
    by_cases hj : j < N
    · rw [fld_maxS hj h2 hp]; omega
    · rw [fld_of_lt h2.1 (by omega)]; omega

theorem hi_ok {N : ℕ} {P : PieceF} (hP : P.OK N) (vert : Bool) {pos : ℕ} (hp : PosOK N vert pos)
    {R : List (FC × FC)} (hR : SegsOK N R) : (P.hi N vert pos R).OK N := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hP
  cases vert <;> simp only [PosOK, ite_true, ite_false, Bool.false_eq_true] at hp <;>
    simp only [PieceF.hi, PieceF.OK, ite_true, ite_false, Bool.false_eq_true]
  · exact ⟨by omega, h2, h3, h4, hR⟩
  · refine ⟨h1, hp, Sm_maxS hp h3, fun j => ?_, hR⟩
    by_cases hj : j < N
    · rw [fld_maxS hj hp h3]; omega
    · rw [fld_of_lt hp.1 (by omega)]; omega

section
variable {N j : ℕ} (hj : j < N)
include hj

theorem lo_getF {P : PieceF} (hP : P.OK N) (vert : Bool) {pos : ℕ} (hp : PosOK N vert pos)
    (L : List (FC × FC)) :
    (P.lo N vert pos L).get j = (P.get j).lo vert (lget vert j pos) (L.map (segF j)) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hP
  cases vert <;> simp only [PosOK, ite_true, ite_false, Bool.false_eq_true] at hp <;>
    simp only [PieceF.lo, Piece.lo, PieceF.get, lget, ite_true, ite_false, Bool.false_eq_true]
  rw [fld_maxS hj h2 hp]
  congr 1; omega

theorem hi_getF {P : PieceF} (hP : P.OK N) (vert : Bool) {pos : ℕ} (hp : PosOK N vert pos)
    (R : List (FC × FC)) :
    (P.hi N vert pos R).get j = (P.get j).hi vert (lget vert j pos) (R.map (segF j)) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hP
  cases vert <;> simp only [PosOK, ite_true, ite_false, Bool.false_eq_true] at hp <;>
    simp only [PieceF.hi, Piece.hi, PieceF.get, lget, ite_true, ite_false, Bool.false_eq_true]
  rw [fld_maxS hj hp h3]
  have := h4 j
  congr 1; omega

theorem insideF_get {P : PieceF} (hP : P.OK N) (vert : Bool) {pos : ℕ} (hp : PosOK N vert pos) :
    (insideF N vert pos P).testBit (8 * j) = inside vert (lget vert j pos) (P.get j) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hP
  cases vert <;> simp only [PosOK, ite_true, ite_false, Bool.false_eq_true] at hp
  · simp [insideF, inside, testBit_bS hj, PieceF.get, lget]
  · have := h4 j
    simp only [insideF, inside, ite_true, Nat.testBit_and, testBit_ltB h2 hp hj, testBit_ltB hp h3 hj,
      PieceF.get, lget, Nat.add_sub_cancel' this]

theorem regionF_get {P : PieceF} (hP : P.OK N) {v : FC} (hv : CellOK N v) :
    (regionF N P v).testBit (8 * j) = (P.get j).regionB (v.get j) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hP
  have := h4 j
  simp only [regionF, Piece.regionB, Nat.testBit_and, testBit_bS hj, tb_not hj,
    testBit_ltB hv.2 h2 hj, testBit_ltB hv.2 h3 hj, PieceF.get, FC.get, Nat.add_sub_cancel' this]
  have key : (!decide (fld v.2 j < fld P.oy j)) = decide (fld P.oy j ≤ fld v.2 j) := by
    rw [← decide_not]; simp only [Nat.not_lt]
  rw [key]; simp only [Bool.and_assoc]
  try rfl

theorem eqF_get {a b : FC} (ha : CellOK N a) (hb : CellOK N b) :
    (eqF N a b).testBit (8 * j) = eqC (a.get j) (b.get j) := by
  simp only [eqF, eqC, Nat.testBit_and, testBit_bS hj, testBit_eqB ha.2 hb.2 hj, FC.get]
  rfl

theorem leafF_get {P : PieceF} (hP : P.OK N) : (leafF N P).testBit (8 * j) = leafOK (P.get j) := by
  obtain ⟨ox, pw, oy, ey, segs⟩ := P
  match segs, hP with
  | [], _ => simp [leafF, leafOK, PieceF.get]
  | [(a, b)], hP =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := hP
    have ha : CellOK N a := (h5 (a, b) (by simp)).1
    have hb : CellOK N b := (h5 (a, b) (by simp)).2
    have hw : pw < 128 := by simp at h1; omega
    have ha1 : a.1 - ox < 128 := by have := ha.1; omega
    have hb1 : b.1 - ox < 128 := by have := hb.1; omega
    have hP' : PieceF.OK N ⟨ox, pw, oy, ey, [(a, b)]⟩ := ⟨h1, h2, h3, h4, h5⟩
    have he := h4 j
    simp only [leafF, leafOK, PieceF.get, List.map_cons, List.map_nil, segF]
    simp only [Nat.testBit_or, Nat.testBit_and, tb_not hj, eqF_get hj ha hb, testBit_bS hj,
      testBit_eqB (Sm_subS h3 h2) (Sm_kS (c := 1) (by norm_num)) hj, testBit_eqB ha.2 h2 hj,
      fl_sub h3 h2, fld_kS (by norm_num : 1 < 128) hj, regionF_get hj hP' ha, regionF_get hj hP' hb,
      accS_get hj (Sm_kS hw) (Sm_subS h3 h2) (Sm_kS ha1) (Sm_subS ha.2 h2) (Sm_kS hb1) (Sm_subS hb.2 h2),
      fld_kS hw hj, fld_kS ha1 hj, fld_kS hb1 hj, fl_sub ha.2 h2, fl_sub hb.2 h2]
    cases h : eqC (FC.get j a) (FC.get j b)
    · simp only [Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_or, Bool.false_eq_true,
        ite_false]
      rfl
    · simp only [Bool.true_and, Bool.not_true, Bool.false_and, Bool.or_false, ite_true]
      unfold eqC FC.get
      simp only [Bool.and_assoc, Bool.and_left_comm]
  | _ :: _ :: _, _ => simp [leafF, leafOK, PieceF.get]

end

/-- **Lane lemma.** Lane `j` of `checkF` is `check` on lane `j`. -/
theorem checkF_get {N j : ℕ} (hj : j < N) : ∀ (T : CTree ℕ) (P : PieceF), TOK N T → P.OK N →
    (checkF N T P).testBit (8 * j) = check (T.getF j) (P.get j)
  | CTree.leaf, P, _, hP => leafF_get hj hP
  | CTree.cut vert pos ks l r, P, hT, hP => by
    obtain ⟨hp, hk, hl, hr⟩ := hT
    have hs := splitF_get hj vert hp ks P.segs ([], [])
    simp only [checkF, check, CTree.getF, Nat.testBit_and, insideF_get hj hP vert hp]
    congr 1
    have hseg : (P.get j).segs = P.segs.map (segF j) := rfl
    rw [hseg]
    simp only [List.map_nil] at hs
    rw [← hs]
    match h : splitF N vert pos ks P.segs ([], []) with
    | some (L, R) =>
      have hLR := splitF_ok vert hp ks P.segs ([], []) hk hP.2.2.2.2 (by simp [SegsOK])
        (by simp [SegsOK]) L R h
      simp only [Option.map_some, Nat.testBit_and,
        checkF_get hj l _ hl (lo_ok hP vert hp hLR.1), checkF_get hj r _ hr (hi_ok hP vert hp hLR.2),
        lo_getF hj hP vert hp, hi_getF hj hP vert hp]
    | none => simp

end ZZN.Cut

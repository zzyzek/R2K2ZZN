/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Cut.FastD
public import ZZN.Cut.AccW

@[expose] public section

/-!
# Template checks with the scalar-width leaf test

`leafFW`, `checkFW`, `tcheckFW` and `coverFW` are `leafF`, `checkF`, `tcheckF` and `coverF` with the
leaf test `accSW` (ZZN/Cut/AccW.lean), which decides the tests on the width and the rows of the
piece once instead of in every lane. Their lane lemmas are those of the originals, with
`accSW_get` in place of `accS_get`. The `…D` copies call the `Nat` operations directly (as in
`FastD`) and equal the standard ones (`coverFWD_eq`).
-/

namespace ZZN.Cut

open ZZN ZZN.Lane GridHam ZZN.BoxK

section ops
variable (N : ℕ)

def leafFW (P : PieceF) : ℕ :=
  match P.segs with
  | [(a, b)] =>
    let e := eqF N a b
    let one := bS N (decide (P.pw = 1) && decide (a.1 = P.ox)) &&&
      (eqB N (subS N P.ey P.oy) (ZZN.Lane.kS N 1) &&& eqB N a.2 P.oy)
    let acc := (regionF N P a &&& regionF N P b) &&&
      accSW N P.pw (subS N P.ey P.oy) (a.1 - P.ox) (subS N a.2 P.oy) (b.1 - P.ox) (subS N b.2 P.oy)
    (e &&& one) ||| (notS N e &&& acc)
  | _ => 0

def checkFW : CTree ℕ → PieceF → ℕ
  | CTree.leaf, P => leafFW N P
  | CTree.cut vert pos ks l r, P =>
    insideF N vert pos P &&&
      match splitF N vert pos ks P.segs ([], []) with
      | some (L, R) => checkFW l (P.lo N vert pos L) &&& checkFW r (P.hi N vert pos R)
      | none => 0

end ops

def tcheckFW (N w h : ℕ) (x Y : Fin 4 → ℕ) (T : CTree TPos) : ℕ :=
  checkFW N (inst (posN (x 0) (x 1) (x 2) (x 3) w) (posF N (Y 0) (Y 1) (Y 2) (Y 3) h) T) (rootF N w h x Y)

def coverFW (N w h : ℕ) (x Y : Fin 4 → ℕ) : List (CTree TPos × Sym) → ℕ
  | [] => 0
  | (T, σ) :: ps => (if σ.tr || σ.ry || !tsmall T then 0
      else tcheckFW N w h (xS σ w x) (fun i => Y (lperm σ i)) T) ||| coverFW N w h x Y ps

section
variable {N j : ℕ} (hj : j < N)
include hj

theorem leafFW_get {P : PieceF} (hP : P.OK N) : (leafFW N P).testBit (8 * j) = leafOK (P.get j) := by
  obtain ⟨ox, pw, oy, ey, segs⟩ := P
  match segs, hP with
  | [], _ => simp [leafFW, leafOK, PieceF.get]
  | [(a, b)], hP =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := hP
    have ha : CellOK N a := (h5 (a, b) (by simp)).1
    have hb : CellOK N b := (h5 (a, b) (by simp)).2
    have hw : pw < 128 := by simp at h1; omega
    have ha1 : a.1 - ox < 128 := by have := ha.1; omega
    have hb1 : b.1 - ox < 128 := by have := hb.1; omega
    have hP' : PieceF.OK N ⟨ox, pw, oy, ey, [(a, b)]⟩ := ⟨h1, h2, h3, h4, h5⟩
    have he := h4 j
    simp only [leafFW, leafOK, PieceF.get, List.map_cons, List.map_nil, segF]
    simp only [Nat.testBit_or, Nat.testBit_and, tb_not hj, eqF_get hj ha hb, testBit_bS hj,
      testBit_eqB (Sm_subS h3 h2) (ZZN.Lane.Sm_kS (c := 1) (by norm_num)) hj, testBit_eqB ha.2 h2 hj,
      fl_sub h3 h2, fld_kS (by norm_num : 1 < 128) hj, regionF_get hj hP' ha, regionF_get hj hP' hb,
      accSW_get hj (Sm_subS h3 h2) (Sm_subS ha.2 h2) (Sm_subS hb.2 h2), fl_sub ha.2 h2, fl_sub hb.2 h2]
    cases h : eqC (FC.get j a) (FC.get j b)
    · simp only [Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_or, Bool.false_eq_true,
        ite_false]
      rfl
    · simp only [Bool.true_and, Bool.not_true, Bool.false_and, Bool.or_false, ite_true]
      unfold eqC FC.get
      simp only [Bool.and_assoc, Bool.and_left_comm]
  | _ :: _ :: _, _ => simp [leafFW, leafOK, PieceF.get]

end

theorem checkFW_get {N j : ℕ} (hj : j < N) : ∀ (T : CTree ℕ) (P : PieceF), TOK N T → P.OK N →
    (checkFW N T P).testBit (8 * j) = check (T.getF j) (P.get j)
  | CTree.leaf, P, _, hP => leafFW_get hj hP
  | CTree.cut vert pos ks l r, P, hT, hP => by
    obtain ⟨hp, hk, hl, hr⟩ := hT
    have hs := splitF_get hj vert hp ks P.segs ([], [])
    simp only [checkFW, check, CTree.getF, Nat.testBit_and, insideF_get hj hP vert hp]
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
        checkFW_get hj l _ hl (lo_ok hP vert hp hLR.1), checkFW_get hj r _ hr (hi_ok hP vert hp hLR.2),
        lo_getF hj hP vert hp, hi_getF hj hP vert hp]
    | none => simp

theorem tcheckFW_get {N j w h : ℕ} (hj : j < N) {x Y : Fin 4 → ℕ} (hx : ∀ i, x i < 64) (hw : w < 64)
    (hY : ∀ i, Sm64 N (Y i)) (hh : h < 64) {T : CTree TPos} (hT : tsmall T = true) :
    (tcheckFW N w h x Y T).testBit (8 * j) = tcheck T (laneF w h x Y j) := by
  have hroot : (rootF N w h x Y).OK N := by
    refine ⟨by simp [rootF]; omega, ⟨by simp [rootF, Bs], fun i => by simp [rootF, fld]⟩,
      ZZN.Lane.Sm_kS (by omega), fun i => by simp [rootF, fld], ?_⟩
    intro e he
    simp only [rootF, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl
    · exact ⟨⟨hx 0 |>.trans (by norm_num), (hY 0).sm⟩, ⟨hx 1 |>.trans (by norm_num), (hY 1).sm⟩⟩
    · exact ⟨⟨hx 2 |>.trans (by norm_num), (hY 2).sm⟩, ⟨hx 3 |>.trans (by norm_num), (hY 3).sm⟩⟩
  unfold tcheckFW tcheck
  rw [checkFW_get hj _ _ (tok_inst ⟨hx 0, hx 1, hx 2, hx 3⟩ hw hY hh T hT) hroot, inst_getF,
    inst_posF hj hY hh T hT]
  have hk : fld (ZZN.Lane.kS N h) j = h := fld_kS (by omega) hj
  have h0 : fld 0 j = 0 := by simp [fld]
  congr 1
  simp only [rootF, PieceF.get, rootPiece, laneF, segF, FC.get, hk, h0, Nat.sub_zero, List.map_cons,
    List.map_nil]

theorem coverFW_sound {N w h j : ℕ} (hh : 0 < h) (h32 : h ≤ 32) (hw : w ≤ 32) (hN : N = h ^ 4)
    (hj : j < N) (x : Fin 4 → ℕ) (hx : ∀ i, x i < 32) {Y : Fin 4 → ℕ} (hY : ∀ i, Y i = YS h i.val) :
    ∀ (ps : List (CTree TPos × Sym)),
    (coverFW N w h x Y ps).testBit (8 * j) = true → (laneI w h x j).WellFormed → Solvable (laneI w h x j)
  | [], h1, _ => by simp [coverFW] at h1
  | (T, σ) :: ps, h1, hwf => by
    simp only [coverFW, Nat.testBit_or, Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · split_ifs at h1 with hs
      · simp at h1
      · simp only [Bool.not_eq_true', not_or, Bool.not_eq_false] at hs
        obtain ⟨⟨htr, hry⟩, hT⟩ := hs
        have htr' : σ.tr = false := by simpa using htr
        have hry' : σ.ry = false := by simpa using hry
        subst hN
        rw [tcheckFW_get hj (fun i => by unfold xS; have := hx (lperm σ i); split_ifs <;> omega)
          (by omega) (fun i => by rw [hY]; exact YS_sm64 hh h32 (by omega)) (by omega) hT] at h1
        have e : laneF w h (xS σ w x) (fun i => Y (lperm σ i)) j =
            σ.apply (laneI w h x j) := by
          rw [apply_laneI htr' hh h32 rfl hj]
          simp [laneF, laneInst, yS, hry', Ycols, LV.get, hY]
        rw [e] at h1
        exact Sym.solvable hwf (solvable_of_tcheck T h1)
    · exact coverFW_sound hh h32 hw hN hj x hx hY ps h1 hwf

local infixl:58 " ∧ₙ " => Nat.land
local infixl:58 " ⊕ₙ " => Nat.xor
local infixl:55 " ∨ₙ " => Nat.lor
local infixl:65 " -ₙ " => Nat.sub
local infixl:65 " +ₙ " => Nat.add

def accSWD (N w H s1 S2 t1 T2 : ℕ) : ℕ :=
  let o := oneSD N
  let z := kSD N 0
  let one := kSD N 1
  let ps := if s1 % 2 = 1 then notSD N S2 else S2
  let pt := if t1 % 2 = 1 then notSD N T2 else T2
  let cc := if w % 2 = 1 then (H ∧ₙ (notSD N ps ∧ₙ notSD N pt)) ∨ₙ (notSD N H ∧ₙ (ps ⊕ₙ pt))
    else ps ⊕ₙ pt
  let h1 := subSD N H one
  let hc := fun (v1 v2 : ℕ) => if v1 = 0 ∨ v1 = w - 1 then eqBD N v2 z ∨ₙ eqBD N v2 h1 else 0
  let f1 :=
    if w = 1 then
      notSD N ((if s1 = 0 ∧ t1 = 0 then eqBD N S2 z ∧ₙ eqBD N T2 h1 else 0) ∨ₙ
        (if s1 = 0 ∧ t1 = 0 then eqBD N S2 h1 ∧ₙ eqBD N T2 z else 0))
    else
      notSD N ((if s1 = 0 ∧ t1 = w - 1 then eqBD N S2 z ∧ₙ eqBD N T2 z else 0) ∨ₙ
        (if s1 = w - 1 ∧ t1 = 0 then eqBD N S2 z ∧ₙ eqBD N T2 z else 0))
  let f2 := notSD N (hc s1 S2) ∧ₙ notSD N (hc t1 T2) ∧ₙ
    ((if w = 2 then eqBD N S2 T2 else 0) ∨ₙ (if s1 = t1 then eqBD N H (kSD N 2) else 0))
  let f3 :=
    if w = 3 then
      let gr := ltBD N T2 S2
      let dist := iteSD N gr (subSD N S2 T2) (subSD N T2 S2)
      let dsat := if s1 = 1 then ltBD N z dist else ltBD N one dist
      notSD N H ∧ₙ (ps ⊕ₙ pt) ∧ₙ dsat ∧ₙ ((gr ∧ₙ notSD N ps) ∨ₙ (notSD N gr ∧ₙ ps))
    else if w % 2 = 1 then 0
    else
      let dist := if t1 < s1 then s1 - t1 else t1 - s1
      let e1 := eqBD N S2 one
      let dsat := if 1 < dist then o else if 0 < dist then e1 else 0
      (ps ⊕ₙ pt) ∧ₙ dsat ∧ₙ (if t1 < s1 then notSD N ps else ps)
  let hh1 := eqBD N H one
  let hh2 := eqBD N H (kSD N 2)
  let hh3 := eqBD N H (kSD N 3)
  let forb :=
    if w = 1 then f1
    else if w = 2 then (hh1 ∧ₙ f1) ∨ₙ (notSD N hh1 ∧ₙ f2)
    else if w = 3 then (hh1 ∧ₙ f1) ∨ₙ (notSD N hh1 ∧ₙ ((hh2 ∧ₙ f2) ∨ₙ (notSD N hh2 ∧ₙ f3)))
    else (hh1 ∧ₙ f1) ∨ₙ (notSD N hh1 ∧ₙ ((hh2 ∧ₙ f2) ∨ₙ (notSD N hh2 ∧ₙ (hh3 ∧ₙ f3))))
  (cc ∧ₙ notSD N forb) ∧ₙ o

section opsD
variable (N : ℕ)

def leafFWD (P : PieceF) : ℕ :=
  match P.segs with
  | [(a, b)] =>
    let e := eqFD N a b
    let one := bSD N (decide (P.pw = 1) && decide (a.1 = P.ox)) ∧ₙ
      (eqBD N (subSD N P.ey P.oy) (kSD N 1) ∧ₙ eqBD N a.2 P.oy)
    let acc := (regionFD N P a ∧ₙ regionFD N P b) ∧ₙ
      accSWD N P.pw (subSD N P.ey P.oy) (a.1 -ₙ P.ox) (subSD N a.2 P.oy) (b.1 -ₙ P.ox) (subSD N b.2 P.oy)
    (e ∧ₙ one) ∨ₙ (notSD N e ∧ₙ acc)
  | _ => 0

def checkFWD : CTree ℕ → PieceF → ℕ
  | CTree.leaf, P => leafFWD N P
  | CTree.cut vert pos ks l r, P =>
    insideFD N vert pos P ∧ₙ
      match splitFD N vert pos ks P.segs ([], []) with
      | some (L, R) => checkFWD l (PieceF.loD N P vert pos L) ∧ₙ checkFWD r (PieceF.hiD N P vert pos R)
      | none => 0

end opsD

def tcheckFWD (N w h : ℕ) (x Y : Fin 4 → ℕ) (T : CTree TPos) : ℕ :=
  checkFWD N (inst (posN (x 0) (x 1) (x 2) (x 3) w) (posFD N (Y 0) (Y 1) (Y 2) (Y 3) h) T) (rootFD N w h x Y)

def coverFWD (N w h : ℕ) (x Y : Fin 4 → ℕ) : List (CTree TPos × Sym) → ℕ
  | [] => 0
  | (T, σ) :: ps => (if σ.tr || σ.ry || !tsmall T then 0
      else tcheckFWD N w h (xS σ w x) (fun i => Y (lperm σ i)) T) ∨ₙ coverFWD N w h x Y ps

theorem accSWD_eq (N w H s1 S2 t1 T2 : ℕ) : accSWD N w H s1 S2 t1 T2 = accSW N w H s1 S2 t1 T2 := rfl

theorem leafFWD_eq (N : ℕ) (P : PieceF) : leafFWD N P = leafFW N P := rfl

theorem checkFWD_eq (N : ℕ) : ∀ (T : CTree ℕ) (P : PieceF), checkFWD N T P = checkFW N T P
  | CTree.leaf, P => leafFWD_eq N P
  | CTree.cut vert pos ks l r, P => by
    simp only [checkFWD, checkFW, splitFD_eq, insideFD_eq, loD_eq, hiD_eq, checkFWD_eq N l,
      checkFWD_eq N r]
    rfl

theorem tcheckFWD_eq (N w h : ℕ) (x Y : Fin 4 → ℕ) (T : CTree TPos) :
    tcheckFWD N w h x Y T = tcheckFW N w h x Y T := by
  simp only [tcheckFWD, tcheckFW, checkFWD_eq]; rfl

theorem coverFWD_eq (N w h : ℕ) (x Y : Fin 4 → ℕ) : ∀ ps : List (CTree TPos × Sym),
    coverFWD N w h x Y ps = coverFW N w h x Y ps
  | [] => rfl
  | (T, σ) :: ps => by simp only [coverFWD, coverFW, tcheckFWD_eq, coverFWD_eq N w h x Y ps]; rfl

end ZZN.Cut

-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Cut.Gen

/-!
# The exact integer checker

`checkG` at `ℤ`/`Bool` agrees with the natural-number checker `check` on cast inputs
(`checkZ_cast`): wherever the two differ by truncated subtraction, a cut-inside or region test
fails on both sides. `zcheck T I`: template positions as integers (anchor + offset), all of them
non-negative, and the integer checker accepts; `solvable_of_zcheck`.
-/

namespace ZZN.Cut

open GridHam

@[simp] theorem algZ_k (c : ℤ) : Alg.k (B := Bool) c = c := rfl
@[simp] theorem algZ_add (a b : ℤ) : Alg.add (B := Bool) a b = a + b := rfl
@[simp] theorem algZ_sub (a b : ℤ) : Alg.sub (B := Bool) a b = a - b := rfl
@[simp] theorem algZ_lt (a b : ℤ) : Alg.lt (V := ℤ) a b = decide (a < b) := rfl
@[simp] theorem algZ_eq (a b : ℤ) : Alg.eq (V := ℤ) a b = decide (a = b) := rfl
@[simp] theorem algZ_odd (a : ℤ) : Alg.odd (V := ℤ) a = decide (a % 2 = 1) := rfl
@[simp] theorem algZ_and (x y : Bool) : Alg.and (V := ℤ) x y = (x && y) := rfl
@[simp] theorem algZ_or (x y : Bool) : Alg.or (V := ℤ) x y = (x || y) := rfl
@[simp] theorem algZ_not (x : Bool) : Alg.not (V := ℤ) x = !x := rfl
@[simp] theorem algZ_ff : Alg.ff (V := ℤ) = false := rfl

def castC (v : Coord) : ℤ × ℤ := ((v.1 : ℤ), (v.2 : ℤ))
def castS (e : Coord × Coord) : (ℤ × ℤ) × (ℤ × ℤ) := (castC e.1, castC e.2)
def castP (P : Piece) : PieceG ℤ := ⟨P.ox, P.oy, P.pw, P.ph, P.segs.map castS⟩

theorem cutc_cast (vert : Bool) (pos : ℕ) (s : Bool) (y : ℕ) (hp : 1 ≤ pos) :
    castC (cutc vert pos s y) = cutcG (V := ℤ) (B := Bool) vert (pos : ℤ) s (y : ℤ) := by
  cases vert <;> cases s <;> simp [cutc, cutcG, castC, Alg.sub, Alg.k] <;> omega

theorem put_cast (s : Bool) (e : Coord × Coord) (LR : List (Coord × Coord) × List (Coord × Coord)) :
    ((put s e LR).1.map castS, (put s e LR).2.map castS) =
      putG s (castS e) (LR.1.map castS, LR.2.map castS) := by
  cases s <;> simp [put, putG]

theorem split_cast (vert : Bool) (pos : ℕ) (hp : 1 ≤ pos) : ∀ (ks : List (Kind ℕ))
    (ss : List (Coord × Coord)) (acc : List (Coord × Coord) × List (Coord × Coord)),
    (split vert pos ks ss acc).map (fun LR => (LR.1.map castS, LR.2.map castS)) =
      splitG (V := ℤ) (B := Bool) vert (pos : ℤ) (ks.map (Kind.map (fun n : ℕ => (n : ℤ))))
        (ss.map castS) (acc.1.map castS, acc.2.map castS)
  | [], [], acc => by simp [split, splitG]
  | [], _ :: _, acc => by simp [split, splitG]
  | k :: ks, [], acc => by cases k <;> simp [split, splitG, Kind.map]
  | Kind.stay s :: ks, (a, b) :: ss, acc => by
    simp only [split, splitG, List.map_cons, Kind.map]
    rw [split_cast vert pos hp ks ss, put_cast]
  | Kind.cross s y :: ks, (a, b) :: ss, acc => by
    simp only [split, splitG, List.map_cons, Kind.map]
    rw [split_cast vert pos hp ks ss, put_cast, put_cast]
    simp only [castS, cutc_cast vert pos _ _ hp]
  | Kind.exc s y z :: ks, (a, b) :: ss, acc => by
    simp only [split, splitG, List.map_cons, Kind.map]
    rw [split_cast vert pos hp ks ss, put_cast, put_cast, put_cast]
    simp only [castS, cutc_cast vert pos _ _ hp]

theorem inside_cast (vert : Bool) (pos : ℕ) (P : Piece) :
    insideG (V := ℤ) (B := Bool) vert (pos : ℤ) (castP P) = inside vert pos P := by
  cases vert <;> simp [insideG, inside, castP] <;> norm_cast

theorem lo_cast (P : Piece) (vert : Bool) (pos : ℕ) (L : List (Coord × Coord))
    (h : inside vert pos P = true) :
    PieceG.lo (V := ℤ) (B := Bool) (castP P) vert (pos : ℤ) (L.map castS) = castP (P.lo vert pos L) := by
  cases vert <;> simp [inside] at h <;> simp [PieceG.lo, Piece.lo, castP, Alg.sub] <;> omega

theorem hi_cast (P : Piece) (vert : Bool) (pos : ℕ) (R : List (Coord × Coord))
    (h : inside vert pos P = true) :
    PieceG.hi (V := ℤ) (B := Bool) (castP P) vert (pos : ℤ) (R.map castS) = castP (P.hi vert pos R) := by
  cases vert <;> simp [inside] at h <;> simp [PieceG.hi, Piece.hi, castP, Alg.sub, Alg.add] <;> omega

theorem region_cast (P : Piece) (v : Coord) :
    regionG (V := ℤ) (B := Bool) (castP P) (castC v) = P.regionB v := by
  simp only [regionG, le, castP, castC, Piece.regionB, algZ_and, algZ_not, algZ_lt, algZ_add]
  rw [Bool.eq_iff_iff]
  simp
  omega

theorem leaf_cast (P : Piece) : leafG (V := ℤ) (B := Bool) (castP P) = leafOK P := by
  obtain ⟨ox, oy, pw, ph, segs⟩ := P
  match segs with
  | [] => rfl
  | [(a, b)] =>
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    simp only [leafG, leafOK, castP, List.map_cons, List.map_nil, castS, castC]
    by_cases hab : a1 = b1 ∧ a2 = b2
    · obtain ⟨rfl, rfl⟩ := hab
      simp [eqCG, eqC, Alg.and, Alg.or, Alg.eq, Alg.not, Alg.k]
    · have h1 : eqC (a1, a2) (b1, b2) = false := by simp [eqC]; omega
      have h2 : eqCG (V := ℤ) (B := Bool) ((a1 : ℤ), (a2 : ℤ)) ((b1 : ℤ), (b2 : ℤ)) = false := by
        simp [eqCG]; omega
      rw [h1, h2]
      have ra := region_cast ⟨ox, oy, pw, ph, [((a1, a2), (b1, b2))]⟩ (a1, a2)
      have rb := region_cast ⟨ox, oy, pw, ph, [((a1, a2), (b1, b2))]⟩ (b1, b2)
      simp only [castP, castC, List.map_cons, List.map_nil, castS] at ra rb
      simp only [algZ_or, algZ_and, algZ_not, Bool.false_and, Bool.not_false, Bool.true_and,
        Bool.false_or, Bool.false_eq_true, ite_false, ra, rb]
      cases hr : (Piece.regionB ⟨ox, oy, pw, ph, [((a1, a2), (b1, b2))]⟩ (a1, a2) &&
          Piece.regionB ⟨ox, oy, pw, ph, [((a1, a2), (b1, b2))]⟩ (b1, b2))
      · simp
      · simp only [Piece.regionB, Bool.and_eq_true, decide_eq_true_eq] at hr
        have e1 : ((a1 : ℤ) - ox) = ((a1 - ox : ℕ) : ℤ) := by omega
        have e2 : ((a2 : ℤ) - oy) = ((a2 - oy : ℕ) : ℤ) := by omega
        have e3 : ((b1 : ℤ) - ox) = ((b1 - ox : ℕ) : ℤ) := by omega
        have e4 : ((b2 : ℤ) - oy) = ((b2 - oy : ℕ) : ℤ) := by omega
        have := accG_int pw ph (a1 - ox, a2 - oy) (b1 - ox, b2 - oy)
        simp only at this
        simp only [Bool.true_and, algZ_sub, e1, e2, e3, e4, this]
  | _ :: _ :: _ => rfl

theorem checkZ_cast : ∀ (T : CTree ℕ) (P : Piece),
    checkG (V := ℤ) (B := Bool) (T.map (fun n : ℕ => (n : ℤ))) (castP P) = check T P
  | CTree.leaf, P => leaf_cast P
  | CTree.cut vert pos ks l r, P => by
    simp only [checkG, check, CTree.map]
    rw [inside_cast]
    by_cases hin : inside vert pos P = true
    · have hp : 1 ≤ pos := by
        cases vert <;> simp [inside] at hin <;> omega
      have hs := split_cast vert pos hp ks P.segs ([], [])
      simp only [List.map_nil] at hs
      have hseg : (castP P).segs = P.segs.map castS := rfl
      rw [hseg, ← hs]
      match h : split vert pos ks P.segs ([], []) with
      | some (L, R) =>
        simp only [Option.map_some, lo_cast P vert pos L hin, hi_cast P vert pos R hin,
          checkZ_cast l, checkZ_cast r]
        rfl
      | none => rfl
    · simp [hin, Alg.and]

/-! ### Templates with exact integer positions -/

section
variable {V B : Type} [A : Alg V B]

def posG (anch : ℕ → V) (p : TPos) : V := A.add (anch p.1) (A.k p.2)

def nonnegK : Kind V → B
  | Kind.stay _ => A.tt
  | Kind.cross _ y => le (A.k 0) y
  | Kind.exc _ y z => A.and (le (A.k 0) y) (le (A.k 0) z)

def nonnegG : CTree V → B
  | CTree.leaf => A.tt
  | CTree.cut _ pos ks l r =>
    A.and (A.and (le (A.k 0) pos) (ks.foldr (fun k acc => A.and (nonnegK k) acc) A.tt))
      (A.and (nonnegG l) (nonnegG r))

/-- Template `T` on the instance whose row anchors are `rA`, column anchors `cA`. -/
def zcheckG (rA cA : ℕ → V) (root : PieceG V) (T : CTree TPos) : B :=
  let TV := inst (posG (A := A) rA) (posG (A := A) cA) T
  A.and (nonnegG TV) (checkG TV root)

end

def anchZ (e0 e1 e2 e3 n : ℕ) (a : ℕ) : ℤ := (anchors e0 e1 e2 e3 n a : ℕ)

def zcheck (T : CTree TPos) (I : Inst) : Bool :=
  zcheckG (V := ℤ) (B := Bool) (anchZ I.s0.1 I.t0.1 I.s1.1 I.t1.1 I.w)
    (anchZ I.s0.2 I.t0.2 I.s1.2 I.t1.2 I.h) (castP (rootPiece I)) T

theorem nonnegK_cast (k : Kind ℤ) (h : nonnegK (V := ℤ) (B := Bool) k = true) :
    Kind.map (fun n : ℕ => (n : ℤ)) (Kind.map Int.toNat k) = k := by
  cases k <;> simp [nonnegK, le, Kind.map] at h ⊢ <;> omega

theorem nonneg_cast : ∀ T : CTree ℤ, nonnegG (V := ℤ) (B := Bool) T = true →
    (T.map Int.toNat).map (fun n : ℕ => (n : ℤ)) = T
  | CTree.leaf, _ => rfl
  | CTree.cut v pos ks l r, h => by
    simp only [nonnegG, algZ_and, Bool.and_eq_true] at h
    obtain ⟨⟨hp, hks⟩, hl, hr⟩ := h
    simp only [CTree.map, nonneg_cast l hl, nonneg_cast r hr, List.map_map]
    simp only [le, algZ_not, algZ_lt, algZ_k, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not, not_lt] at hp
    congr 1
    · omega
    · induction ks with
      | nil => rfl
      | cons k ks ih =>
        simp only [List.foldr_cons, algZ_and, Bool.and_eq_true] at hks
        simp only [List.map_cons]
        congr 1
        · simpa [Function.comp] using nonnegK_cast k hks.1
        · exact ih hks.2

/-- **Soundness of the integer template check.** -/
theorem solvable_of_zcheck {I : Inst} (T : CTree TPos) (h : zcheck T I = true) : Solvable I := by
  simp only [zcheck, zcheckG, algZ_and, Bool.and_eq_true] at h
  obtain ⟨hn, hc⟩ := h
  rw [← nonneg_cast _ hn, checkZ_cast] at hc
  exact solvable_of_check _ hc

end ZZN.Cut

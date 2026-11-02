-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Cut.ZCheck

/-!
# Templates as formulas over linear atoms

Variables: `r 0..3` the rows of `s0 t0 s1 t1`, `r 4` the width; `q 0..3` their columns, `q 4` the
height. A linear form is a constant plus integer coefficients on the ten variables. A formula is a
Boolean combination of atoms `L < 0`, `L = 0`, `L` odd.

`tform T`: the formula of template `T` (`zcheckG` at linear forms). `tform_eval`: evaluating
`tform T` at an instance gives `zcheck T`.
-/

namespace ZZN.Cut

structure Lin where
  c : ℤ
  r0 : ℤ
  r1 : ℤ
  r2 : ℤ
  r3 : ℤ
  r4 : ℤ
  q0 : ℤ
  q1 : ℤ
  q2 : ℤ
  q3 : ℤ
  q4 : ℤ

inductive Form where
  | tt
  | ff
  | and (x y : Form)
  | or (x y : Form)
  | not (x : Form)
  | lt (L : Lin)
  | eq (L : Lin)
  | odd (L : Lin)

namespace Lin

def k (c : ℤ) : Lin := ⟨c, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
def add (a b : Lin) : Lin :=
  ⟨a.c + b.c, a.r0 + b.r0, a.r1 + b.r1, a.r2 + b.r2, a.r3 + b.r3, a.r4 + b.r4,
    a.q0 + b.q0, a.q1 + b.q1, a.q2 + b.q2, a.q3 + b.q3, a.q4 + b.q4⟩
def sub (a b : Lin) : Lin :=
  ⟨a.c - b.c, a.r0 - b.r0, a.r1 - b.r1, a.r2 - b.r2, a.r3 - b.r3, a.r4 - b.r4,
    a.q0 - b.q0, a.q1 - b.q1, a.q2 - b.q2, a.q3 - b.q3, a.q4 - b.q4⟩
def rv (i : ℕ) : Lin :=
  ⟨0, if i = 0 then 1 else 0, if i = 1 then 1 else 0, if i = 2 then 1 else 0, if i = 3 then 1 else 0,
    if i = 4 then 1 else 0, 0, 0, 0, 0, 0⟩
def qv (i : ℕ) : Lin :=
  ⟨0, 0, 0, 0, 0, 0, if i = 0 then 1 else 0, if i = 1 then 1 else 0, if i = 2 then 1 else 0,
    if i = 3 then 1 else 0, if i = 4 then 1 else 0⟩

/-- Value at rows `x`, columns `y`. -/
def eval (x y : Fin 5 → ℤ) (L : Lin) : ℤ :=
  L.c + (L.r0 * x 0 + L.r1 * x 1 + L.r2 * x 2 + L.r3 * x 3 + L.r4 * x 4) +
    (L.q0 * y 0 + L.q1 * y 1 + L.q2 * y 2 + L.q3 * y 3 + L.q4 * y 4)

end Lin

/-- Smart constructors fold constants. -/
def Form.and' : Form → Form → Form
  | Form.ff, _ => Form.ff
  | _, Form.ff => Form.ff
  | Form.tt, y => y
  | x, Form.tt => x
  | x, y => Form.and x y

def Form.or' : Form → Form → Form
  | Form.tt, _ => Form.tt
  | _, Form.tt => Form.tt
  | Form.ff, y => y
  | x, Form.ff => x
  | x, y => Form.or x y

def Form.not' : Form → Form
  | Form.tt => Form.ff
  | Form.ff => Form.tt
  | x => Form.not x

def Form.eval (x y : Fin 5 → ℤ) : Form → Bool
  | Form.tt => true
  | Form.ff => false
  | Form.and a b => a.eval x y && b.eval x y
  | Form.or a b => a.eval x y || b.eval x y
  | Form.not a => !a.eval x y
  | Form.lt L => decide (L.eval x y < 0)
  | Form.eq L => decide (L.eval x y = 0)
  | Form.odd L => decide (L.eval x y % 2 = 1)

theorem Form.eval_and' (x y : Fin 5 → ℤ) (a b : Form) :
    (Form.and' a b).eval x y = (a.eval x y && b.eval x y) := by
  unfold Form.and'; split <;> simp_all [Form.eval]

theorem Form.eval_or' (x y : Fin 5 → ℤ) (a b : Form) :
    (Form.or' a b).eval x y = (a.eval x y || b.eval x y) := by
  unfold Form.or'; split <;> simp_all [Form.eval]

theorem Form.eval_not' (x y : Fin 5 → ℤ) (a : Form) : (Form.not' a).eval x y = !a.eval x y := by
  unfold Form.not'; split <;> simp_all [Form.eval]

/-- The form has no variables. -/
def Lin.isK (L : Lin) : Bool :=
  L.r0 == 0 && L.r1 == 0 && L.r2 == 0 && L.r3 == 0 && L.r4 == 0 &&
    L.q0 == 0 && L.q1 == 0 && L.q2 == 0 && L.q3 == 0 && L.q4 == 0

theorem Lin.eval_isK {L : Lin} (h : L.isK = true) (x y : Fin 5 → ℤ) : L.eval x y = L.c := by
  simp only [Lin.isK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  simp [Lin.eval, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- Atoms with constant forms fold to `tt`/`ff`. -/
def mkLt (L : Lin) : Form := if L.isK then (if L.c < 0 then Form.tt else Form.ff) else Form.lt L
def mkEq (L : Lin) : Form := if L.isK then (if L.c = 0 then Form.tt else Form.ff) else Form.eq L
def mkOdd (L : Lin) : Form := if L.isK then (if L.c % 2 = 1 then Form.tt else Form.ff) else Form.odd L

theorem eval_mkLt (x y : Fin 5 → ℤ) (L : Lin) : (mkLt L).eval x y = decide (L.eval x y < 0) := by
  unfold mkLt
  by_cases h1 : L.isK = true
  · rw [if_pos h1, Lin.eval_isK h1]; split_ifs <;> simp_all [Form.eval]
  · rw [if_neg h1]; rfl

theorem eval_mkEq (x y : Fin 5 → ℤ) (L : Lin) : (mkEq L).eval x y = decide (L.eval x y = 0) := by
  unfold mkEq
  by_cases h1 : L.isK = true
  · rw [if_pos h1, Lin.eval_isK h1]; split_ifs <;> simp_all [Form.eval]
  · rw [if_neg h1]; rfl

theorem eval_mkOdd (x y : Fin 5 → ℤ) (L : Lin) : (mkOdd L).eval x y = decide (L.eval x y % 2 = 1) := by
  unfold mkOdd
  by_cases h1 : L.isK = true
  · rw [if_pos h1, Lin.eval_isK h1]; split_ifs <;> simp_all [Form.eval]
  · rw [if_neg h1]; rfl

instance : Alg Lin Form where
  k := Lin.k
  add := Lin.add
  sub := Lin.sub
  lt a b := mkLt (Lin.sub a b)
  eq a b := mkEq (Lin.sub a b)
  odd a := mkOdd a
  tt := Form.tt
  ff := Form.ff
  and := Form.and'
  or := Form.or'
  not := Form.not'

/-- Evaluation at rows `x`, columns `y` is a homomorphism. -/
def evalHom (x y : Fin 5 → ℤ) : Hom Lin Form where
  eV := Lin.eval x y
  eB := Form.eval x y
  k c := by simp [Alg.k, Lin.k, Lin.eval]
  add a b := by simp [Alg.add, Lin.add, Lin.eval]; ring
  sub a b := by simp [Alg.sub, Lin.sub, Lin.eval]; ring
  lt a b := by
    simp only [Alg.lt, eval_mkLt, Lin.sub, Lin.eval]
    congr 1; apply propext; constructor <;> intro h <;> linarith
  eq a b := by
    simp only [Alg.eq, eval_mkEq, Lin.sub, Lin.eval]
    congr 1; apply propext; constructor <;> intro h <;> linarith
  odd a := eval_mkOdd x y a
  tt := rfl
  ff := rfl
  and a b := Form.eval_and' x y a b
  or a b := Form.eval_or' x y a b
  not a := Form.eval_not' x y a

/-- Anchors as linear forms: `0..3` an endpoint coordinate, `4` zero, `5` the side. -/
def anchR (a : ℕ) : Lin := match a with
  | 0 => Lin.rv 0 | 1 => Lin.rv 1 | 2 => Lin.rv 2 | 3 => Lin.rv 3 | 4 => Lin.k 0 | _ => Lin.rv 4

def anchQ (a : ℕ) : Lin := match a with
  | 0 => Lin.qv 0 | 1 => Lin.qv 1 | 2 => Lin.qv 2 | 3 => Lin.qv 3 | 4 => Lin.k 0 | _ => Lin.qv 4

def rootL : PieceG Lin :=
  ⟨Lin.k 0, Lin.k 0, Lin.rv 4, Lin.qv 4,
    [((Lin.rv 0, Lin.qv 0), (Lin.rv 1, Lin.qv 1)), ((Lin.rv 2, Lin.qv 2), (Lin.rv 3, Lin.qv 3))]⟩

/-- The formula of a template. -/
def tform (T : CTree TPos) : Form := zcheckG (V := Lin) (B := Form) anchR anchQ rootL T

/-- Row and column values of an instance. -/
def rowsOf (I : Inst) : Fin 5 → ℤ := ![I.s0.1, I.t0.1, I.s1.1, I.t1.1, I.w]
def colsOf (I : Inst) : Fin 5 → ℤ := ![I.s0.2, I.t0.2, I.s1.2, I.t1.2, I.h]

section
variable {V B : Type} [A : Alg V B] (H : Hom V B)

theorem Hom.nonnegK_h (k : Kind V) :
    H.eB (nonnegK k) = nonnegK (V := ℤ) (B := Bool) (k.map H.eV) := by
  cases k <;> simp [nonnegK, Kind.map, le, H.tt, H.and, H.not, H.lt, H.k] <;> rfl

theorem Hom.nonneg_h : ∀ T : CTree V, H.eB (nonnegG T) = nonnegG (V := ℤ) (B := Bool) (T.map H.eV)
  | CTree.leaf => by simp [nonnegG, H.tt]; rfl
  | CTree.cut v pos ks l r => by
    simp only [nonnegG, CTree.map, H.and, Hom.nonneg_h l, Hom.nonneg_h r, le, H.not, H.lt, H.k]
    congr 2
    induction ks with
    | nil => simp [H.tt]; rfl
    | cons k ks ih => simp only [List.foldr_cons, List.map_cons, H.and, ih, H.nonnegK_h]; rfl

theorem Hom.zcheck_h (rA cA : ℕ → V) (root : PieceG V) (T : CTree TPos) :
    H.eB (zcheckG rA cA root T) =
      zcheckG (V := ℤ) (B := Bool) (H.eV ∘ rA) (H.eV ∘ cA) (H.p root) T := by
  simp only [zcheckG, H.and, H.nonneg_h, H.check_h, inst_map]
  have e : ∀ f : ℕ → V, H.eV ∘ posG (A := A) f = posG (V := ℤ) (B := Bool) (H.eV ∘ f) := by
    intro f; funext p; simp [posG, H.add, H.k]
  rw [e rA, e cA]
  rfl

end

theorem tform_eval (T : CTree TPos) (I : Inst) : (tform T).eval (rowsOf I) (colsOf I) = zcheck T I := by
  have h := (evalHom (rowsOf I) (colsOf I)).zcheck_h anchR anchQ rootL T
  have eR : (evalHom (rowsOf I) (colsOf I)).eV ∘ anchR = anchZ I.s0.1 I.t0.1 I.s1.1 I.t1.1 I.w := by
    funext a
    rcases a with _ | _ | _ | _ | _ | a <;>
      simp [evalHom, anchR, anchZ, anchors, Lin.rv, Lin.k, Lin.eval, rowsOf]
  have eQ : (evalHom (rowsOf I) (colsOf I)).eV ∘ anchQ = anchZ I.s0.2 I.t0.2 I.s1.2 I.t1.2 I.h := by
    funext a
    rcases a with _ | _ | _ | _ | _ | a <;>
      simp [evalHom, anchQ, anchZ, anchors, Lin.qv, Lin.k, Lin.eval, colsOf]
  have eP : Hom.p (evalHom (rowsOf I) (colsOf I)) rootL = castP (rootPiece I) := by
    simp [Hom.p, evalHom, rootL, castP, rootPiece, Hom.s, Hom.c, castS, castC, Lin.eval, Lin.rv,
      Lin.qv, Lin.k, rowsOf, colsOf]
  rw [eR, eQ, eP] at h
  exact h

/-! ### Per-box formulas: width and height as constants -/

def anchRB (w : ℕ) (a : ℕ) : Lin := match a with
  | 0 => Lin.rv 0 | 1 => Lin.rv 1 | 2 => Lin.rv 2 | 3 => Lin.rv 3 | 4 => Lin.k 0 | _ => Lin.k w

def anchQB (h : ℕ) (a : ℕ) : Lin := match a with
  | 0 => Lin.qv 0 | 1 => Lin.qv 1 | 2 => Lin.qv 2 | 3 => Lin.qv 3 | 4 => Lin.k 0 | _ => Lin.k h

def rootLB (w h : ℕ) : PieceG Lin :=
  ⟨Lin.k 0, Lin.k 0, Lin.k w, Lin.k h,
    [((Lin.rv 0, Lin.qv 0), (Lin.rv 1, Lin.qv 1)), ((Lin.rv 2, Lin.qv 2), (Lin.rv 3, Lin.qv 3))]⟩

def tformB (w h : ℕ) (T : CTree TPos) : Form :=
  zcheckG (V := Lin) (B := Form) (anchRB w) (anchQB h) (rootLB w h) T

theorem tformB_eval (T : CTree TPos) (I : Inst) :
    (tformB I.w I.h T).eval (rowsOf I) (colsOf I) = zcheck T I := by
  have h := (evalHom (rowsOf I) (colsOf I)).zcheck_h (anchRB I.w) (anchQB I.h) (rootLB I.w I.h) T
  have eR : (evalHom (rowsOf I) (colsOf I)).eV ∘ anchRB I.w = anchZ I.s0.1 I.t0.1 I.s1.1 I.t1.1 I.w := by
    funext a
    rcases a with _ | _ | _ | _ | _ | a <;>
      simp [evalHom, anchRB, anchZ, anchors, Lin.rv, Lin.k, Lin.eval, rowsOf]
  have eQ : (evalHom (rowsOf I) (colsOf I)).eV ∘ anchQB I.h = anchZ I.s0.2 I.t0.2 I.s1.2 I.t1.2 I.h := by
    funext a
    rcases a with _ | _ | _ | _ | _ | a <;>
      simp [evalHom, anchQB, anchZ, anchors, Lin.qv, Lin.k, Lin.eval, colsOf]
  have eP : Hom.p (evalHom (rowsOf I) (colsOf I)) (rootLB I.w I.h) = castP (rootPiece I) := by
    simp [Hom.p, evalHom, rootLB, castP, rootPiece, Hom.s, Hom.c, castS, castC, Lin.eval, Lin.rv,
      Lin.qv, Lin.k, rowsOf, colsOf]
  rw [eR, eQ, eP] at h
  exact h

end ZZN.Cut

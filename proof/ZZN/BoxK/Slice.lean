/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.BoxK.Masks
public import ZZN.Cut.Template
public import ZZN.Cut.TemplateF
public import ZZN.Cut.SolF
public import ZZN.Moves

@[expose] public section

/-!
# One row slice of a box

The rows `x` of the four endpoints are fixed; lane `j < h^4` carries the columns
`digit h i j`. `laneI w h x j` is the instance in lane `j`. For a symmetry `σ` without
transposition, `σ.apply (laneI w h x j)` is the lane instance of the transformed rows `xS σ w x`
and transformed column lanes `yS σ N h (Ycols h)` (`apply_laneI`).
-/

namespace ZZN.BoxK

open ZZN ZZN.Lane ZZN.Cut GridHam

def Ycols (h : ℕ) : Cols := fun i => LV.s (YS h i.val)

theorem Ycols_get {h j : ℕ} (hh : 0 < h) (h32 : h ≤ 32) (hj : j < h ^ 4) (i : Fin 4) :
    (Ycols h i).get j = digit h i j := by
  show fld (YS h i.val) j = _
  rw [fld_YS hh (by simp [Bs]; omega) (by omega) hj]; rfl

def laneI (w h : ℕ) (x : Fin 4 → ℕ) (j : ℕ) : Inst :=
  ⟨w, h, (x 0, digit h 0 j), (x 1, digit h 1 j), (x 2, digit h 2 j), (x 3, digit h 3 j)⟩

/-- Entry `i` of the image under the label part of `σ` comes from entry `lperm σ i`. -/
def lperm (σ : Sym) (i : Fin 4) : Fin 4 :=
  let k := if σ.sw then (i.val + 2) % 4 else i.val
  let k := if σ.r0 && k < 2 then 1 - k else if σ.r1 && 2 ≤ k then 5 - k else k
  ⟨k % 4, Nat.mod_lt _ (by norm_num)⟩

def xS (σ : Sym) (w : ℕ) (x : Fin 4 → ℕ) : Fin 4 → ℕ := fun i =>
  if σ.rx then w - 1 - x (lperm σ i) else x (lperm σ i)

def yS (σ : Sym) (N h : ℕ) (Y : Cols) : Cols := fun i =>
  if σ.ry then LV.sub N (LV.k (h - 1)) (Y (lperm σ i)) else Y (lperm σ i)

theorem digit_lt {h i j : ℕ} (hh : 0 < h) : digit h i j < h := Nat.mod_lt _ hh

theorem apply_laneI {σ : Sym} (htr : σ.tr = false) {w h N j : ℕ} (hh : 0 < h) (h32 : h ≤ 32)
    (hN : N = h ^ 4) (hj : j < N) (x : Fin 4 → ℕ) :
    σ.apply (laneI w h x j) = laneInst w h (xS σ w x) (yS σ N h (Ycols h)) j := by
  subst hN
  have g : ∀ i : Fin 4, (Ycols h i).get j = digit h i j := Ycols_get hh h32 hj
  have gs : ∀ i : Fin 4, (LV.sub (h ^ 4) (LV.k (h - 1)) (Ycols h i)).get j = h - 1 - digit h i j := by
    intro i; rw [LV.at_sub hj, g]; rfl
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  simp only at htr
  subst htr
  cases rx <;> cases ry <;> cases r0 <;> cases r1 <;> cases sw <;>
    simp [Sym.apply, Sym.geo, Sym.lab, laneI, laneInst, xS, yS, lperm, Inst.reflectX, reflX,
      Inst.reflectY, Inst.transpose, Inst.rev0, Inst.rev1, Inst.swapColors, g, gs, Fin.isValue]

/-! ### Distinct endpoints and parity on lanes -/

def pairsIdx : List (Fin 4 × Fin 4) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

def distinctV (N : ℕ) (x : Fin 4 → ℕ) (Y : Cols) : LB :=
  pairsIdx.foldr (fun ab acc => LB.and (if x ab.1 = x ab.2 then LB.not N (LV.eq N (Y ab.1) (Y ab.2))
    else LB.b true) acc) (LB.b true)

def cellAt (x : Fin 4 → ℕ) (Y : Cols) (j : ℕ) (i : Fin 4) : Coord := (x i, (Y i).get j)

theorem distinctV_get {N j : ℕ} (hj : j < N) (x : Fin 4 → ℕ) (Y : Cols) :
    (distinctV N x Y).get j = pairsIdx.all (fun ab => decide (cellAt x Y j ab.1 ≠ cellAt x Y j ab.2)) := by
  simp only [distinctV, pairsIdx, List.foldr_cons, List.foldr_nil, List.all_cons, List.all_nil,
    LB.at_and, LB.get_b, Bool.and_true]
  congr 1 <;> (try congr 1) <;> (try congr 1) <;> (try congr 1) <;> (try congr 1) <;>
    · split_ifs with h <;> simp [LB.at_not hj, LV.at_eq hj, cellAt, h, Prod.ext_iff]

/-- Exactly `k` of the lane Booleans are true. -/
def cntEq (N : ℕ) : List LB → ℕ → LB
  | [], k => LB.b (k == 0)
  | b :: bs, k => LB.or (if k = 0 then LB.b false else LB.and b (cntEq N bs (k - 1)))
      (LB.and (LB.not N b) (cntEq N bs k))

theorem cntEq_get {N j : ℕ} (hj : j < N) : ∀ (bs : List LB) (k : ℕ),
    (cntEq N bs k).get j = decide ((bs.map (·.get j)).count true = k)
  | [], k => by cases k <;> simp [cntEq]
  | b :: bs, k => by
    simp only [cntEq, LB.at_or, LB.at_and, LB.at_not hj, cntEq_get hj bs, List.map_cons,
      List.count_cons]
    cases hb : b.get j <;> cases k <;> simp [LB.at_and, cntEq_get hj bs, hb]

/-- The lanes whose instance passes the parity test. -/
def parityV (N w h : ℕ) (x : Fin 4 → ℕ) (Y : Cols) : LB :=
  cntEq N ((List.finRange 4).map fun i => if x i % 2 = 0 then LB.not N (LV.odd (Y i)) else LV.odd (Y i))
    (2 + (w * h) % 2)

theorem sgn_eq (v : Coord) : sgn v = if (v.1 + v.2) % 2 = 0 then 1 else -1 := by
  unfold sgn; simp

theorem parityV_get {N w h j : ℕ} (hj : j < N) (x : Fin 4 → ℕ) (Y : Cols) :
    (parityV N w h x Y).get j = parityOk w h [((x 0, (Y 0).get j), 0), ((x 1, (Y 1).get j), 0),
      ((x 2, (Y 2).get j), 1), ((x 3, (Y 3).get j), 1)] := by
  have he : ∀ i : Fin 4, (if x i % 2 = 0 then LB.not N (LV.odd (Y i)) else LV.odd (Y i)).get j =
      decide ((x i + (Y i).get j) % 2 = 0) := by
    intro i; split_ifs with h <;> simp only [LB.at_not hj, LV.at_odd] <;>
      (rw [Bool.eq_iff_iff]; simp; omega)
  simp only [parityV, cntEq_get hj, List.map_map, Function.comp_def, he]
  simp only [List.finRange, List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil]
  unfold parityOk
  simp only [sgn_eq, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rcases Nat.mod_two_eq_zero_or_one (x 0 + (Y 0).get j) with a | a <;>
  rcases Nat.mod_two_eq_zero_or_one (x 1 + (Y 1).get j) with b | b <;>
  rcases Nat.mod_two_eq_zero_or_one (x 2 + (Y 2).get j) with c | c <;>
  rcases Nat.mod_two_eq_zero_or_one (x 3 + (Y 3).get j) with d | d <;>
  rcases Nat.mod_two_eq_zero_or_one (w * h) with e | e <;>
  simp [a, b, c, d, e]

def ptsOf' (J : Inst) : List Pt := [(J.s0, 0), (J.t0, 0), (J.s1, 1), (J.t1, 1)]

theorem sgn_reflX {w : ℕ} {v : Coord} (hv : v.1 < w) :
    sgn (reflX w v) = if w % 2 = 1 then sgn v else -sgn v := by
  obtain ⟨a, b⟩ := v
  simp only [reflX, sgn_eq] at *
  split_ifs <;> omega

theorem sgn_reflY {h : ℕ} {v : Coord} (hv : v.2 < h) :
    sgn (v.1, h - 1 - v.2) = if h % 2 = 1 then sgn v else -sgn v := by
  obtain ⟨a, b⟩ := v
  simp only [sgn_eq] at *
  split_ifs <;> omega

theorem parityOk_reflectX {J : Inst} (hwf : J.WellFormed) :
    parityOk J.reflectX.w J.reflectX.h (ptsOf' J.reflectX) = parityOk J.w J.h (ptsOf' J) := by
  obtain ⟨b0, b1, b2, b3, -⟩ := hwf
  simp only [Inst.reflectX, ptsOf', parityOk, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [sgn_reflX b0.1, sgn_reflX b1.1, sgn_reflX b2.1, sgn_reflX b3.1]
  rcases Nat.mod_two_eq_zero_or_one J.w with e | e
  · have : (J.w * J.h) % 2 = 0 := by rw [Nat.mul_mod, e]; simp
    simp only [e, this]; simp; constructor <;> intro h <;> linarith
  · simp [e]

theorem parityOk_reflectY {J : Inst} (hwf : J.WellFormed) :
    parityOk J.reflectY.w J.reflectY.h (ptsOf' J.reflectY) = parityOk J.w J.h (ptsOf' J) := by
  obtain ⟨b0, b1, b2, b3, -⟩ := hwf
  simp only [Inst.reflectY, Inst.transpose, Inst.reflectX, reflX, Prod.swap, ptsOf', parityOk,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [sgn_reflY b0.2, sgn_reflY b1.2, sgn_reflY b2.2, sgn_reflY b3.2]
  rcases Nat.mod_two_eq_zero_or_one J.h with e | e
  · have : (J.w * J.h) % 2 = 0 := by rw [Nat.mul_mod, e]; simp
    simp only [e, this]; simp; constructor <;> intro h <;> linarith
  · simp [e]

theorem not_passes_of_parity {J : Inst} (h : parityOk J.w J.h (ptsOf' J) = false) : ¬ Passes J := by
  unfold Passes fires3; simp [ptsOf'] at h ⊢; simp [h]

theorem passImgB_of_parity {J : Inst} (hwf : J.WellFormed) (h : parityOk J.w J.h (ptsOf' J) = false) :
    passImgB J = false := by
  have h1 := not_passes_of_parity h
  have h2 := not_passes_of_parity (J := J.reflectX) (by rw [parityOk_reflectX hwf]; exact h)
  have h3 := not_passes_of_parity (J := J.reflectY) (by rw [parityOk_reflectY hwf]; exact h)
  have h4 := not_passes_of_parity (J := J.reflectX.reflectY)
    (by rw [parityOk_reflectY (wf_reflectX hwf), parityOk_reflectX hwf]; exact h)
  simp [passImgB, h1, h2, h3, h4]

/-! ### The slice check -/

/-- Lanes solved by one of the (template, symmetry) pairs. -/
def coverV (N w h : ℕ) (x : Fin 4 → ℕ) : List (CTree TPos × Sym) → LB
  | [] => LB.b false
  | (T, σ) :: ps => LB.or (if σ.tr then LB.b false else tcheckV N w h (xS σ w x) (yS σ N h (Ycols h)) T)
      (coverV N w h x ps)

/-- Lanes listed as not passing (each checked: neither the instance nor a reflection passes). -/
def firesM (N w h : ℕ) (x : Fin 4 → ℕ) : List ℕ → ℕ
  | [] => 0
  | j :: js => (if j < N ∧ passImgB (laneI w h x j) = false then 2 ^ (8 * j) else 0) ||| firesM N w h x js

/-- Lanes solved one at a time: lane `j`, a symmetry `σ`, a template that checks on `σ` of the
instance. -/
def instM (N w h : ℕ) (x : Fin 4 → ℕ) : List (ℕ × Sym × CTree TPos) → ℕ
  | [] => 0
  | (j, σ, T) :: js =>
    (if j < N ∧ tcheck T (σ.apply (laneI w h x j)) = true then 2 ^ (8 * j) else 0) |||
      instM N w h x js

def keyR (x : Fin 4 → ℕ) : ℕ := ((x 0 * 32 + x 1) * 32 + x 2) * 32 + x 3

/-- Lexicographic `≤` of two 4-tuples of lane values. -/
def lexLeV (N : ℕ) (X Z : Cols) : LB :=
  LB.or (LV.lt N (X 0) (Z 0)) (LB.and (LV.eq N (X 0) (Z 0))
    (LB.or (LV.lt N (X 1) (Z 1)) (LB.and (LV.eq N (X 1) (Z 1))
      (LB.or (LV.lt N (X 2) (Z 2)) (LB.and (LV.eq N (X 2) (Z 2)) (LV.le N (X 3) (Z 3)))))))

/-- With entries below 32, the key order is the lexicographic order. -/
theorem keyR_le_iff {a b : Fin 4 → ℕ} (ha : ∀ i, a i < 32) (hb : ∀ i, b i < 32) :
    keyR a ≤ keyR b ↔ (a 0 < b 0 ∨ (a 0 = b 0 ∧ (a 1 < b 1 ∨ (a 1 = b 1 ∧
      (a 2 < b 2 ∨ (a 2 = b 2 ∧ a 3 ≤ b 3)))))) := by
  have := ha 0; have := ha 1; have := ha 2; have := ha 3
  have := hb 0; have := hb 1; have := hb 2; have := hb 3
  unfold keyR; omega

theorem lexLeV_get {N j : ℕ} (hj : j < N) (X Z : Cols) (hX : ∀ i, (X i).get j < 32)
    (hZ : ∀ i, (Z i).get j < 32) :
    (lexLeV N X Z).get j = decide (keyR (fun i => (X i).get j) ≤ keyR (fun i => (Z i).get j)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, keyR_le_iff hX hZ]
  simp [lexLeV, LB.at_or, LB.at_and, LV.at_lt hj, LV.at_eq hj, LV.at_le hj]

/-- The column part of a symmetry without transposition, on one column tuple. -/
def yS0 (σ : Sym) (h : ℕ) (y : Fin 4 → ℕ) : Fin 4 → ℕ := fun i =>
  if σ.ry then h - 1 - y (lperm σ i) else y (lperm σ i)

theorem yS_get {σ : Sym} {N h j : ℕ} (hj : j < N) (Y : Cols) (i : Fin 4) :
    (yS σ N h Y i).get j = yS0 σ h (fun i => (Y i).get j) i := by
  unfold yS yS0; split_ifs
  · rw [LV.at_sub hj]; rfl
  · rfl

/-- The symmetries without transposition that fix the row tuple. -/
def stabL (w : ℕ) (x : Fin 4 → ℕ) : List Sym :=
  allSym.filter fun σ => !σ.tr && decide (xS σ w x = x)

/-- Lanes whose column key is least over the row tuple's stabiliser. -/
def stabV (N w h : ℕ) (x : Fin 4 → ℕ) (Y : Cols) : LB :=
  (stabL w x).foldr (fun σ acc => LB.and (lexLeV N Y (yS σ N h Y)) acc) (LB.b true)

theorem stabV_get {N w h j : ℕ} (hj : j < N) (h32 : h ≤ 32) (x : Fin 4 → ℕ) (Y : Cols)
    (hY : ∀ i, (Y i).get j < h) :
    (stabV N w h x Y).get j = (stabL w x).all fun σ =>
      decide (keyR (fun i => (Y i).get j) ≤ keyR (yS0 σ h (fun i => (Y i).get j))) := by
  unfold stabV
  induction stabL w x with
  | nil => rfl
  | cons σ l ih =>
    have hs : ∀ i, (yS σ N h Y i).get j < 32 := by
      intro i; rw [yS_get hj]; unfold yS0; dsimp only; have := hY (lperm σ i); split_ifs <;> omega
    simp only [List.foldr_cons, LB.at_and, lexLeV_get hj Y (yS σ N h Y)
      (fun i => by have := hY i; omega) hs, List.all_cons, ih]
    rw [show (fun i => (yS σ N h Y i).get j) = yS0 σ h (fun i => (Y i).get j) from
      funext fun i => yS_get hj Y i]

/-- On a square box, lanes whose column key is not below the row key (transposition). -/
def trV (N w h : ℕ) (x : Fin 4 → ℕ) (Y : Cols) : LB :=
  if w = h then lexLeV N (fun i => LV.k (x i)) Y else LB.b true

theorem trV_get {N w h j : ℕ} (hj : j < N) (x : Fin 4 → ℕ) (Y : Cols) (hx : ∀ i, x i < 32)
    (hY : ∀ i, (Y i).get j < 32) :
    (trV N w h x Y).get j = (!(decide (w = h)) || decide (keyR x ≤ keyR (fun i => (Y i).get j))) := by
  unfold trV
  split_ifs with hwh
  · rw [lexLeV_get hj _ _ (fun i => by simpa using hx i) hY]
    simp only [hwh, decide_true, Bool.not_true, Bool.false_or, LV.get_k]
    rfl
  · simp [hwh, LB.get]

/-- Lanes solved by one of the (template, symmetry) pairs, on 8-bit lanes with rows as scalars
(`tcheckF`). Pairs whose symmetry transposes or reflects the columns, or whose template has an
offset outside `[-63, 63]`, contribute nothing. -/
def coverF (N w h : ℕ) (x Y : Fin 4 → ℕ) : List (CTree TPos × Sym) → ℕ
  | [] => 0
  | (T, σ) :: ps => (if σ.tr || σ.ry || !tsmall T then 0
      else tcheckF N w h (xS σ w x) (fun i => Y (lperm σ i)) T) ||| coverF N w h x Y ps

/-- One of four values; `sel4 a b c d i` is literally `a`, `b`, `c` or `d`, so the kernel shares
the column lanes between the pairs of a slice. -/
def sel4 (a b c d : ℕ) (i : Fin 4) : ℕ :=
  match i with
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d

theorem sel4_YS (h : ℕ) (i : Fin 4) : sel4 (YS h 0) (YS h 1) (YS h 2) (YS h 3) i = YS h i.val := by
  fin_cases i <;> rfl

theorem fld_YS_lt {h c : ℕ} (hh : 0 < h) (h32 : h ≤ 32) (hc : c ≤ 3) (j : ℕ) : fld (YS h c) j < h := by
  by_cases hj : j < h ^ 4
  · rw [fld_YS hh (by simp [Bs]; omega) hc hj]; exact Nat.mod_lt _ hh
  · have hL : 0 < h ^ (3 - c) := by positivity
    obtain ⟨b1, -⟩ := blockS_spec hL h (by simp [Bs]; omega)
    have e1 : h * h ^ (3 - c) = h ^ (4 - c) := by
      rw [show 4 - c = 3 - c + 1 by omega, pow_succ, mul_comm]
    have e2 : h ^ c * h ^ (4 - c) = h ^ 4 := by rw [← pow_add]; congr 1; omega
    rw [e1] at b1
    unfold YS
    rw [fld_mul_repS (by positivity) b1, e2]; simp only [hj, ↓reduceIte]; exact hh

theorem YS_sm64 {h c : ℕ} (hh : 0 < h) (h32 : h ≤ 32) (hc : c ≤ 3) : Sm64 (h ^ 4) (YS h c) := by
  refine ⟨?_, fun j => by have := fld_YS_lt hh h32 hc j; omega⟩
  have hle : YS h c ≤ ZZN.Lane.kS (h ^ 4) (h - 1) := le_of_fld _ _ fun i => by
    rw [fld_kS_all (by omega)]
    split_ifs with hi
    · have := fld_YS_lt hh h32 hc i; omega
    · have hL : 0 < h ^ (3 - c) := by positivity
      obtain ⟨b1, -⟩ := blockS_spec hL h (by simp [Bs]; omega)
      have e1 : h * h ^ (3 - c) = h ^ (4 - c) := by
        rw [show 4 - c = 3 - c + 1 by omega, pow_succ, mul_comm]
      have e2 : h ^ c * h ^ (4 - c) = h ^ 4 := by rw [← pow_add]; congr 1; omega
      rw [e1] at b1
      unfold YS
      rw [fld_mul_repS (by positivity) b1, e2]; simp only [hi, ↓reduceIte, le_refl]
  exact lt_of_le_of_lt hle (kS_lt (by omega))

theorem coverF_sound {N w h j : ℕ} (hh : 0 < h) (h32 : h ≤ 32) (hw : w ≤ 32) (hN : N = h ^ 4)
    (hj : j < N) (x : Fin 4 → ℕ) (hx : ∀ i, x i < 32) {Y : Fin 4 → ℕ} (hY : ∀ i, Y i = YS h i.val) :
    ∀ (ps : List (CTree TPos × Sym)),
    (coverF N w h x Y ps).testBit (8 * j) = true → (laneI w h x j).WellFormed → Solvable (laneI w h x j)
  | [], h1, _ => by simp [coverF] at h1
  | (T, σ) :: ps, h1, hwf => by
    simp only [coverF, Nat.testBit_or, Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · split_ifs at h1 with hs
      · simp at h1
      · simp only [Bool.not_eq_true', not_or, Bool.not_eq_false] at hs
        obtain ⟨⟨htr, hry⟩, hT⟩ := hs
        have htr' : σ.tr = false := by simpa using htr
        have hry' : σ.ry = false := by simpa using hry
        subst hN
        rw [tcheckF_get hj (fun i => by unfold xS; have := hx (lperm σ i); split_ifs <;> omega)
          (by omega) (fun i => by rw [hY]; exact YS_sm64 hh h32 (by omega)) (by omega) hT] at h1
        have e : laneF w h (xS σ w x) (fun i => Y (lperm σ i)) j =
            σ.apply (laneI w h x j) := by
          rw [apply_laneI htr' hh h32 rfl hj]
          simp [laneF, laneInst, yS, hry', Ycols, LV.get, hY]
        rw [e] at h1
        exact Sym.solvable hwf (solvable_of_tcheck T h1)
    · exact coverF_sound hh h32 hw hN hj x hx hY ps h1 hwf

/-- Lanes solved by an explicit pair of paths (`solF`), each path packed by `decPath`:
`(lane, cells, code, cells, code)`. -/
def solsM (N w h : ℕ) (x : Fin 4 → ℕ) : List (ℕ × ℕ × ℕ × ℕ × ℕ) → ℕ
  | [] => 0
  | (j, np, cp, nq, cq) :: js =>
    (if j < N ∧ solF (laneI w h x j) (decPath np cp) (decPath nq cq) = true then 2 ^ (8 * j) else 0) |||
      solsM N w h x js

theorem solsM_sound {N w h j : ℕ} (x : Fin 4 → ℕ) : ∀ (js : List (ℕ × ℕ × ℕ × ℕ × ℕ)),
    (solsM N w h x js).testBit (8 * j) = true → Solvable (laneI w h x j)
  | [], h1 => by simp [solsM] at h1
  | (k, np, cp, nq, cq) :: js, h1 => by
    simp only [solsM, Nat.testBit_or, Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · split_ifs at h1 with hk
      · rw [Nat.testBit_two_pow] at h1
        have : k = j := by simp at h1; omega
        subst this
        exact solvable_of_solF hk.2
      · simp at h1
    · exact solsM_sound x js h1

def sliceOK (w h : ℕ) (x : Fin 4 → ℕ) (pairs : List (CTree TPos × Sym)) (fires : List ℕ)
    (insts : List (ℕ × Sym × CTree TPos)) (sols : List (ℕ × ℕ × ℕ × ℕ × ℕ)) : Bool :=
  let N := h ^ 4
  let Y := Ycols h
  let valid := LB.and (LB.and (LB.and (axBBV N h Y) (stabV N w h x Y)) (trV N w h x Y))
    (LB.and (distinctV N x Y) (parityV N w h x Y))
  ((valid.mkG N) &&& (oneS N ^^^ (coverF N w h x (sel4 (YS h 0) (YS h 1) (YS h 2) (YS h 3)) pairs |||
    firesM N w h x fires ||| instM N w h x insts ||| solsM N w h x sols))) == 0

theorem coverV_sound {N w h j : ℕ} (hh : 0 < h) (h32 : h ≤ 32) (hN : N = h ^ 4) (hj : j < N)
    (x : Fin 4 → ℕ) : ∀ (ps : List (CTree TPos × Sym)), (coverV N w h x ps).get j = true →
      (laneI w h x j).WellFormed → Solvable (laneI w h x j)
  | [], h1, _ => by simp [coverV] at h1
  | (T, σ) :: ps, h1, hwf => by
    simp only [coverV, LB.at_or, Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · split_ifs at h1 with htr
      · simp at h1
      · have htr' : σ.tr = false := by simpa using htr
        rw [tcheckV_get hj] at h1
        rw [← apply_laneI htr' hh h32 hN hj] at h1
        exact Sym.solvable hwf (solvable_of_tcheck T h1)
    · exact coverV_sound hh h32 hN hj x ps h1 hwf

theorem firesM_sound {N w h j : ℕ} (x : Fin 4 → ℕ) : ∀ (js : List ℕ), (firesM N w h x js).testBit (8 * j) = true →
    passImgB (laneI w h x j) = false
  | [], h1 => by simp [firesM] at h1
  | k :: js, h1 => by
    simp only [firesM, Nat.testBit_or, Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · split_ifs at h1 with hk
      · rw [Nat.testBit_two_pow] at h1
        have : k = j := by simp at h1; omega
        subst this; exact hk.2
      · simp at h1
    · exact firesM_sound x js h1

theorem instM_sound {N w h j : ℕ} (x : Fin 4 → ℕ) : ∀ (js : List (ℕ × Sym × CTree TPos)),
    (instM N w h x js).testBit (8 * j) = true → (laneI w h x j).WellFormed → Solvable (laneI w h x j)
  | [], h1, _ => by simp [instM] at h1
  | (k, σ, T) :: js, h1, hwf => by
    simp only [instM, Nat.testBit_or, Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · split_ifs at h1 with hk
      · rw [Nat.testBit_two_pow] at h1
        have : k = j := by simp at h1; omega
        subst this
        exact Sym.solvable hwf (solvable_of_tcheck T hk.2)
      · simp at h1
    · exact instM_sound x js h1 hwf

theorem slice_sound {w h : ℕ} (hh : 0 < h) (h32 : h ≤ 32) (hw32 : w ≤ 32) {x : Fin 4 → ℕ}
    {pairs : List (CTree TPos × Sym)} {fires : List ℕ} {insts : List (ℕ × Sym × CTree TPos)}
    {sols : List (ℕ × ℕ × ℕ × ℕ × ℕ)} (hok : sliceOK w h x pairs fires insts sols = true)
    {j : ℕ} (hj : j < h ^ 4) (hax : axBB h [digit h 0 j, digit h 1 j, digit h 2 j, digit h 3 j] = true)
    (hst : ∀ σ ∈ stabL w x, keyR (fun i => digit h i j) ≤ keyR (yS0 σ h (fun i => digit h i j)))
    (htc : w = h → keyR x ≤ keyR (fun i => digit h i j))
    (hx32 : ∀ i, x i < 32) (hwf : (laneI w h x j).WellFormed) :
    Solvable (laneI w h x j) ∨ passImgB (laneI w h x j) = false := by
  have g : ∀ i : Fin 4, (Ycols h i).get j = digit h i j := Ycols_get hh h32 hj
  by_cases hp : parityOk w h (ptsOf' (laneI w h x j)) = true
  · unfold sliceOK at hok
    simp only [beq_iff_eq] at hok
    have hb := congrArg (fun n => n.testBit (8 * j)) hok
    simp only [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_xor, testBit_oneS, hj, decide_true,
      Nat.testBit_or, LB.testBit_mkG hj, LB.at_and] at hb
    have gl : ∀ i, (Ycols h i).get j < h := fun i => by rw [g]; exact digit_lt hh
    have v1 : (axBBV (h ^ 4) h (Ycols h)).get j = true := by
      rw [axBBV_get hj]; simpa [colsAt, g] using hax
    have v2 : (distinctV (h ^ 4) x (Ycols h)).get j = true := by
      rw [distinctV_get hj]
      obtain ⟨-, -, -, -, n01, n02, n03, n12, n13, n23⟩ := hwf
      simp [pairsIdx, cellAt, g, laneI] at n01 n02 n03 n12 n13 n23 ⊢
      exact ⟨imp_iff_not_or.mp n01, imp_iff_not_or.mp n02, imp_iff_not_or.mp n03,
        imp_iff_not_or.mp n12, imp_iff_not_or.mp n13, imp_iff_not_or.mp n23⟩
    have v3 : (parityV (h ^ 4) w h x (Ycols h)).get j = true := by
      rw [parityV_get hj]; simpa [ptsOf', laneI, g] using hp
    have v4 : (stabV (h ^ 4) w h x (Ycols h)).get j = true := by
      rw [stabV_get hj h32 _ _ gl]
      refine List.all_eq_true.mpr fun σ hσ => ?_
      simpa [g] using hst σ hσ
    have v5 : (trV (h ^ 4) w h x (Ycols h)).get j = true := by
      rw [trV_get hj _ _ hx32 (fun i => by have := gl i; omega)]
      by_cases hwh : w = h
      · simp only [hwh, decide_true, Bool.not_true, Bool.false_or, decide_eq_true_eq]
        simpa [g] using htc hwh
      · simp [hwh]
    rw [v1, v4, v5, v2, v3] at hb
    have hb' : ((coverF (h ^ 4) w h x (sel4 (YS h 0) (YS h 1) (YS h 2) (YS h 3)) pairs).testBit (8 * j) ||
        (firesM (h ^ 4) w h x fires).testBit (8 * j)) || (instM (h ^ 4) w h x insts).testBit (8 * j) ||
        (solsM (h ^ 4) w h x sols).testBit (8 * j) = true := by
      by_contra hc
      simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hc
      obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hc
      simp [c1, c2, c3] at hb
      simp [hb] at c4
    simp only [Bool.or_eq_true] at hb'
    rcases hb' with ((hb | hb) | hb) | hb
    · exact Or.inl (coverF_sound hh h32 hw32 rfl hj x hx32 (sel4_YS h) pairs hb hwf)
    · exact Or.inr (firesM_sound x fires hb)
    · exact Or.inl (instM_sound x insts hb hwf)
    · exact Or.inl (solsM_sound x sols hb)
  · right
    exact passImgB_of_parity hwf (by simp only [Bool.not_eq_true] at hp; exact hp)

end ZZN.BoxK

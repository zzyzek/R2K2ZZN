-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.BoxK.Masks
import ZZN.Cut.Template
import ZZN.Moves

/-!
# One row slice of a box

The rows `x` of the four endpoints are fixed; lane `j < h^4` carries the columns
`digit h i j`. `laneI w h x j` is the instance in lane `j`. For a symmetry `σ` without
transposition, `σ.apply (laneI w h x j)` is the lane instance of the transformed rows `xS σ w x`
and transformed column lanes `yS σ N h (Ycols h)` (`apply_laneI`).
-/

namespace ZZN.BoxK

open ZZN ZZN.Lane ZZN.Cut GridHam

def Ycols (h : ℕ) : Cols := fun i => LV.v (colPlanes h i.val)

theorem Ycols_get {h j : ℕ} (hh : 0 < h) (h32 : h ≤ 32) (hj : j < h ^ 4) (i : Fin 4) :
    (Ycols h i).get j = digit h i j :=
  val_colPlanes hh h32 (by omega) hj

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
    cases hb : b.get j <;> cases k <;> simp [LB.at_and, cntEq_get hj bs, hb] <;> omega

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
  | j :: js => (if j < N ∧ passImgB (laneI w h x j) = false then 2 ^ j else 0) ||| firesM N w h x js

def sliceOK (w h : ℕ) (x : Fin 4 → ℕ) (pairs : List (CTree TPos × Sym)) (fires : List ℕ) : Bool :=
  let N := h ^ 4
  let Y := Ycols h
  let valid := LB.and (axBV N h Y) (LB.and (distinctV N x Y) (parityV N w h x Y))
  ((valid.mk N) &&& nt N ((coverV N w h x pairs).mk N ||| firesM N w h x fires)) == 0

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

theorem firesM_sound {N w h j : ℕ} (x : Fin 4 → ℕ) : ∀ (js : List ℕ), (firesM N w h x js).testBit j = true →
    passImgB (laneI w h x j) = false
  | [], h1 => by simp [firesM] at h1
  | k :: js, h1 => by
    simp only [firesM, Nat.testBit_or, Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · split_ifs at h1 with hk
      · rw [Nat.testBit_two_pow] at h1
        have : k = j := by simpa using h1
        subst this; exact hk.2
      · simp at h1
    · exact firesM_sound x js h1

theorem slice_sound {w h : ℕ} (hh : 0 < h) (h32 : h ≤ 32) {x : Fin 4 → ℕ}
    {pairs : List (CTree TPos × Sym)} {fires : List ℕ} (hok : sliceOK w h x pairs fires = true)
    {j : ℕ} (hj : j < h ^ 4) (hax : axB h [digit h 0 j, digit h 1 j, digit h 2 j, digit h 3 j] = true)
    (hwf : (laneI w h x j).WellFormed) :
    Solvable (laneI w h x j) ∨ passImgB (laneI w h x j) = false := by
  have g : ∀ i : Fin 4, (Ycols h i).get j = digit h i j := Ycols_get hh h32 hj
  by_cases hp : parityOk w h (ptsOf' (laneI w h x j)) = true
  · unfold sliceOK at hok
    simp only [beq_iff_eq] at hok
    have hb := congrArg (fun n => n.testBit j) hok
    simp only [Nat.testBit_and, Nat.zero_testBit, testBit_nt hj, Nat.testBit_or, LB.testBit_mk hj,
      LB.at_and] at hb
    have v1 : (axBV (h ^ 4) h (Ycols h)).get j = true := by
      rw [axBV_get hj]; simpa [colsAt, g] using hax
    have v2 : (distinctV (h ^ 4) x (Ycols h)).get j = true := by
      rw [distinctV_get hj]
      obtain ⟨-, -, -, -, n01, n02, n03, n12, n13, n23⟩ := hwf
      simp [pairsIdx, cellAt, g, laneI] at n01 n02 n03 n12 n13 n23 ⊢
      exact ⟨imp_iff_not_or.mp n01, imp_iff_not_or.mp n02, imp_iff_not_or.mp n03,
        imp_iff_not_or.mp n12, imp_iff_not_or.mp n13, imp_iff_not_or.mp n23⟩
    have v3 : (parityV (h ^ 4) w h x (Ycols h)).get j = true := by
      rw [parityV_get hj]; simpa [ptsOf', laneI, g] using hp
    rw [v1, v2, v3] at hb
    simp only [Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.or_eq_false_iff] at hb
    simp only [Bool.not_false, Bool.or_eq_true] at hb
    rcases hb with hb | hb
    · exact Or.inl (coverV_sound hh h32 rfl hj x pairs hb hwf)
    · exact Or.inr (firesM_sound x fires hb)
  · right
    exact passImgB_of_parity hwf (by simp only [Bool.not_eq_true] at hp; exact hp)

end ZZN.BoxK

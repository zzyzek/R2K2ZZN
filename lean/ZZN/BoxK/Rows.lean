-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.BoxK.Slice
import ZZN.Orbit

/-!
# Row tuples of a box

`G16`: the symmetries without transposition or column reflection. A row 4-tuple is a
representative if its key (`keyR`, base 32) is least over its `G16` images. Lanes `j < w^4` are the
row tuples; `rowsOK w reps` checks that every irreducible representative lane is in the list
`reps` (`rowsOK_sound`).
-/

namespace ZZN.BoxK

open ZZN ZZN.Lane ZZN.Cut GridHam

def G16 : List Sym := allSym.filter fun σ => !σ.tr && !σ.ry

/-- Lane version of `xS` with lane rows. -/
def xSV (σ : Sym) (N w : ℕ) (X : Cols) : Cols := fun i =>
  if σ.rx then LV.sub N (LV.k (w - 1)) (X (lperm σ i)) else X (lperm σ i)

theorem xSV_get {σ : Sym} {N w j : ℕ} (hj : j < N) (X : Cols) (i : Fin 4) :
    (xSV σ N w X i).get j = xS σ w (fun i => (X i).get j) i := by
  unfold xSV xS; split_ifs <;> simp [LV.at_sub hj]

def isRepV (N w : ℕ) (X : Cols) : LB :=
  G16.foldr (fun σ acc => LB.and (lexLeV N X (xSV σ N w X)) acc) (LB.b true)

theorem isRepV_get {N w j : ℕ} (hj : j < N) (hw : w ≤ 32) (X : Cols) (hX : ∀ i, (X i).get j < w) :
    (isRepV N w X).get j = G16.all fun σ =>
      decide (keyR (fun i => (X i).get j) ≤ keyR (xS σ w (fun i => (X i).get j))) := by
  unfold isRepV
  induction G16 with
  | nil => rfl
  | cons σ l ih =>
    have hs : ∀ i, (xSV σ N w X i).get j < 32 := by
      intro i; rw [xSV_get hj]; unfold xS; dsimp only; have := hX (lperm σ i); split_ifs <;> omega
    simp only [List.foldr_cons, LB.at_and, lexLeV_get hj X (xSV σ N w X)
      (fun i => by have := hX i; omega) hs, List.all_cons, ih]
    rw [show (fun i => (xSV σ N w X i).get j) = xS σ w (fun i => (X i).get j) from
      funext fun i => xSV_get hj X i]

/-- Lane index of a row tuple (base `w`). -/
def idx (w : ℕ) (x : Fin 4 → ℕ) : ℕ := ((x 0 * w + x 1) * w + x 2) * w + x 3

def repsMask (w : ℕ) : List (Fin 4 → ℕ) → ℕ
  | [] => 0
  | x :: xs => (if (List.finRange 4).all (fun i => x i < w) then 2 ^ (8 * idx w x) else 0) |||
    repsMask w xs

def rowsOK (w : ℕ) (reps : List (Fin 4 → ℕ)) : Bool :=
  let N := w ^ 4
  let X := Ycols w
  ((LB.and (axBBV N w X) (isRepV N w X)).mkG N &&& (oneS N ^^^ repsMask w reps)) == 0

theorem qr_div {q r w : ℕ} (hr : r < w) : (q * w + r) / w = q := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr, Nat.zero_add]

theorem qr_mod {q r w : ℕ} (hr : r < w) : (q * w + r) % w = r := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

theorem digit_idx {w : ℕ} {x : Fin 4 → ℕ} (hx : ∀ i, x i < w) (i : Fin 4) :
    digit w i (idx w x) = x i := by
  have h0 := hx 0; have h1 := hx 1; have h2 := hx 2; have h3 := hx 3
  have a1 : (idx w x) / w = (x 0 * w + x 1) * w + x 2 := qr_div h3
  have a2 : (idx w x) / w / w = x 0 * w + x 1 := by rw [a1, qr_div h2]
  have a3 : (idx w x) / w / w / w = x 0 := by rw [a2, qr_div h1]
  fin_cases i
  · show idx w x / w ^ 3 % w = x 0
    rw [pow_succ, pow_succ, pow_one, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, a3,
      Nat.mod_eq_of_lt h0]
  · show idx w x / w ^ 2 % w = x 1
    rw [pow_succ, pow_one, ← Nat.div_div_eq_div_mul, a2, qr_mod h1]
  · show idx w x / w ^ 1 % w = x 2
    rw [pow_one, a1, qr_mod h2]
  · show idx w x / w ^ 0 % w = x 3
    rw [pow_zero, Nat.div_one]; exact qr_mod h3

theorem idx_lt {w : ℕ} {x : Fin 4 → ℕ} (hx : ∀ i, x i < w) : idx w x < w ^ 4 := by
  have h0 := hx 0; have h1 := hx 1; have h2 := hx 2; have h3 := hx 3
  unfold idx
  have e1 : x 0 * w + x 1 < (x 0 + 1) * w := by nlinarith
  have e2 : (x 0 * w + x 1) * w + x 2 < ((x 0 + 1) * w) * w := by
    have : (x 0 * w + x 1 + 1) * w ≤ ((x 0 + 1) * w) * w := Nat.mul_le_mul_right _ e1
    nlinarith
  have : ((x 0 * w + x 1) * w + x 2) * w + x 3 < (((x 0 + 1) * w) * w) * w := by
    have : ((x 0 * w + x 1) * w + x 2 + 1) * w ≤ (((x 0 + 1) * w) * w) * w := Nat.mul_le_mul_right _ e2
    nlinarith
  calc _ < (((x 0 + 1) * w) * w) * w := this
    _ ≤ ((w * w) * w) * w := by gcongr; omega
    _ = w ^ 4 := by ring

theorem repsMask_sound {w j : ℕ} : ∀ (reps : List (Fin 4 → ℕ)), (repsMask w reps).testBit (8 * j) = true →
    ∃ x ∈ reps, (∀ i, x i < w) ∧ idx w x = j
  | [], h => by simp [repsMask] at h
  | x :: xs, h => by
    simp only [repsMask, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · split_ifs at h with hb
      · rw [Nat.testBit_two_pow] at h
        refine ⟨x, List.mem_cons_self .., ?_, by simp at h; omega⟩
        simpa using hb
      · simp at h
    · obtain ⟨y, hy, h1, h2⟩ := repsMask_sound xs h
      exact ⟨y, List.mem_cons_of_mem _ hy, h1, h2⟩

/-- Every irreducible representative row tuple is in `reps`. -/
theorem rowsOK_sound {w : ℕ} (hw : 0 < w) (hw32 : w ≤ 32) {reps : List (Fin 4 → ℕ)}
    (hok : rowsOK w reps = true) {x : Fin 4 → ℕ} (hx : ∀ i, x i < w)
    (hax : axBB w [x 0, x 1, x 2, x 3] = true)
    (hrep : ∀ σ ∈ G16, keyR x ≤ keyR (xS σ w x)) : x ∈ reps := by
  have hj := idx_lt hx
  have g : ∀ i : Fin 4, (Ycols w i).get (idx w x) = x i := fun i => by
    rw [Ycols_get hw hw32 hj, digit_idx hx]
  unfold rowsOK at hok
  simp only [beq_iff_eq] at hok
  have hb := congrArg (fun n => n.testBit (8 * idx w x)) hok
  simp only [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_xor, testBit_oneS, hj, decide_true,
    LB.testBit_mkG hj, LB.at_and] at hb
  rw [axBBV_get hj, isRepV_get hj hw32 _ (fun i => by rw [g]; exact hx i)] at hb
  have e : (fun i => (Ycols w i).get (idx w x)) = x := funext g
  simp only [colsAt, g, hax, Bool.true_and] at hb
  have hall : (G16.all fun σ => decide (keyR x ≤ keyR (xS σ w x))) = true :=
    List.all_eq_true.mpr fun σ hσ => decide_eq_true (hrep σ hσ)
  rw [hall] at hb
  obtain ⟨y, hy, hyw, hyi⟩ := repsMask_sound reps (by simpa using hb)
  have : y = x := by
    funext i; rw [← digit_idx hyw i, hyi, digit_idx hx i]
  exact this ▸ hy

/-- No tuple of side `n` is irreducible. -/
def noneOK (n : ℕ) : Bool := (axBBV (n ^ 4) n (Ycols n)).mkG (n ^ 4) == 0

theorem noneOK_sound {n : ℕ} (hn : 0 < n) (h32 : n ≤ 32) (hok : noneOK n = true) {x : Fin 4 → ℕ}
    (hx : ∀ i, x i < n) : axBB n [x 0, x 1, x 2, x 3] = false := by
  have hj := idx_lt hx
  have g : ∀ i : Fin 4, (Ycols n i).get (idx n x) = x i := fun i => by
    rw [Ycols_get hn h32 hj, digit_idx hx]
  unfold noneOK at hok
  simp only [beq_iff_eq] at hok
  have hb := congrArg (fun m => m.testBit (8 * idx n x)) hok
  simp only [Nat.zero_testBit, LB.testBit_mkG hj] at hb
  rw [axBBV_get hj] at hb
  simpa [colsAt, g] using hb

end ZZN.BoxK

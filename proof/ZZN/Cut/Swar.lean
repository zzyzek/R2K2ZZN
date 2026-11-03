/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Cut.Lane

@[expose] public section

/-!
# Lane values in 8-bit fields

A number `a` holds one small value per lane: lane `j` is the base-256 digit `fld a j`. Addition,
subtraction and bitwise operations act field by field when no field carries or borrows
(`fld_add`, `fld_sub`, `fld_land`, `fld_mulc`). With every field below 128 (bit 7 free), the
truncated difference and the comparison take a handful of operations on whole numbers.
-/

namespace ZZN.Lane

/-- The field base. -/
def Bs : ℕ := 256

/-- Lane `j` of `a`. -/
def fld (a j : ℕ) : ℕ := a / Bs ^ j % Bs

theorem fld_lt (a j : ℕ) : fld a j < Bs := Nat.mod_lt _ (by simp [Bs])

theorem fld_zero (a : ℕ) : fld a 0 = a % Bs := by simp [fld]

theorem fld_succ (a j : ℕ) : fld a (j + 1) = fld (a / Bs) j := by
  simp [fld, pow_succ, Nat.div_div_eq_div_mul, mul_comm]

/-- Fieldwise addition without carries. -/
theorem fld_add : ∀ (j a b : ℕ), (∀ i, fld a i + fld b i < Bs) → fld (a + b) j = fld a j + fld b j
  | 0, a, b, h => by
    have h0 := h 0
    simp only [fld_zero] at h0 ⊢
    simp only [Bs] at *
    omega
  | j + 1, a, b, h => by
    have h0 := h 0
    simp only [fld_zero] at h0
    have e : (a + b) / Bs = a / Bs + b / Bs := by simp only [Bs] at *; omega
    rw [fld_succ, fld_succ, fld_succ, e]
    exact fld_add j _ _ fun i => by
      have := h (i + 1); rwa [fld_succ, fld_succ] at this

/-- Fieldwise domination gives domination. -/
theorem le_of_fld : ∀ (b a : ℕ), (∀ i, fld b i ≤ fld a i) → b ≤ a
  | b, a, h => by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · exact Nat.zero_le _
    have hq : b / Bs < b := Nat.div_lt_self hb (by simp [Bs])
    have ih := le_of_fld (b / Bs) (a / Bs) fun i => by
      have := h (i + 1); rwa [fld_succ, fld_succ] at this
    have h0 := h 0
    simp only [fld_zero] at h0
    have e1 := Nat.mod_add_div a Bs
    have e2 := Nat.mod_add_div b Bs
    simp only [Bs] at *
    omega
termination_by b => b

/-- Fieldwise subtraction without borrows. -/
theorem fld_sub : ∀ (j a b : ℕ), (∀ i, fld b i ≤ fld a i) → fld (a - b) j = fld a j - fld b j
  | 0, a, b, h => by
    have h0 := h 0
    have hle := le_of_fld b a h
    simp only [fld_zero] at h0 ⊢
    have e1 := Nat.mod_add_div a Bs
    have e2 := Nat.mod_add_div b Bs
    have hq := le_of_fld (b / Bs) (a / Bs) fun i => by
      have := h (i + 1); rwa [fld_succ, fld_succ] at this
    simp only [Bs] at *
    omega
  | j + 1, a, b, h => by
    have h0 := h 0
    simp only [fld_zero] at h0
    have hq := le_of_fld (b / Bs) (a / Bs) fun i => by
      have := h (i + 1); rwa [fld_succ, fld_succ] at this
    have e1 := Nat.mod_add_div a Bs
    have e2 := Nat.mod_add_div b Bs
    have e : (a - b) / Bs = a / Bs - b / Bs := by simp only [Bs] at *; omega
    rw [fld_succ, fld_succ, fld_succ, e]
    exact fld_sub j _ _ fun i => by
      have := h (i + 1); rwa [fld_succ, fld_succ] at this

/-- The number with lane `j` equal to `f j` for `j < N`. -/
def ofFun : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | N + 1, f => f 0 + Bs * ofFun N (fun j => f (j + 1))

theorem fld_ofFun : ∀ (N : ℕ) (f : ℕ → ℕ), (∀ j, f j < Bs) → ∀ j,
    fld (ofFun N f) j = if j < N then f j else 0
  | 0, f, _, j => by simp [ofFun, fld]
  | N + 1, f, hf, j => by
    have h0 := hf 0
    have q : (f 0 + Bs * ofFun N (fun j => f (j + 1))) / Bs = ofFun N (fun j => f (j + 1)) := by
      rw [Nat.add_mul_div_left _ _ (by simp [Bs]), Nat.div_eq_of_lt h0, zero_add]
    cases j with
    | zero =>
      simp only [ofFun, fld_zero, Nat.zero_lt_succ, ↓reduceIte]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
    | succ j =>
      simp only [ofFun, fld_succ, q, fld_ofFun N _ (fun j => hf (j + 1)) j, Nat.add_lt_add_iff_right]

theorem ofFun_lt : ∀ (N : ℕ) (f : ℕ → ℕ), (∀ j, f j < Bs) → ofFun N f < Bs ^ N
  | 0, _, _ => by simp [ofFun]
  | N + 1, f, hf => by
    have := ofFun_lt N (fun j => f (j + 1)) (fun j => hf (j + 1))
    have h0 := hf 0
    simp only [ofFun, pow_succ]
    simp only [Bs] at *
    nlinarith

/-- Lane `j` of a number below `Bs ^ N` is zero from `N` on. -/
theorem fld_of_lt {a N j : ℕ} (ha : a < Bs ^ N) (hj : N ≤ j) : fld a j = 0 := by
  unfold fld
  rw [Nat.div_eq_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by simp [Bs]) hj))]
  rfl

theorem ofFun_mulc : ∀ (N : ℕ) (f : ℕ → ℕ) (c : ℕ), ofFun N f * c = ofFun N (fun j => f j * c)
  | 0, _, _ => by simp [ofFun]
  | N + 1, f, c => by
    simp only [ofFun]
    rw [add_mul, mul_assoc, ofFun_mulc N _ c]

/-- One in every lane below `N`. -/
def oneS (N : ℕ) : ℕ := (Bs ^ N - 1) / (Bs - 1)

theorem oneS_eq : ∀ N, oneS N = ofFun N (fun _ => 1)
  | 0 => by simp [oneS, ofFun]
  | N + 1 => by
    have ih := oneS_eq N
    unfold oneS at ih ⊢
    simp only [ofFun]
    rw [← ih]
    have hd : (Bs - 1) ∣ (Bs ^ N - 1) := by
      simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow Bs 1 N
    obtain ⟨k, hk⟩ := hd
    have hp : 1 ≤ Bs ^ N := Nat.one_le_pow _ _ (by simp [Bs])
    have e1 : Bs ^ (N + 1) - 1 = (Bs - 1) * (1 + Bs * k) := by
      rw [pow_succ]
      have : Bs ^ N = (Bs - 1) * k + 1 := by omega
      rw [this]; simp only [Bs]; ring_nf; omega
    rw [e1, hk, Nat.mul_div_cancel_left _ (by simp [Bs]), Nat.mul_div_cancel_left _ (by simp [Bs])]

/-- Bit `b` of lane `j`. -/
theorem testBit_fld (a j b : ℕ) : (fld a j).testBit b = (decide (b < 8) && a.testBit (8 * j + b)) := by
  have e : fld a j = (a >>> (8 * j)) % 2 ^ 8 := by
    simp only [fld, Bs, Nat.shiftRight_eq_div_pow, pow_mul]; rfl
  rw [e, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

theorem fld_land (a c j : ℕ) : fld (a &&& c) j = fld a j &&& fld c j := by
  apply Nat.eq_of_testBit_eq; intro b
  simp only [testBit_fld, Nat.testBit_and]; cases decide (b < 8) <;> simp

theorem fld_lor (a c j : ℕ) : fld (a ||| c) j = fld a j ||| fld c j := by
  apply Nat.eq_of_testBit_eq; intro b
  simp only [testBit_fld, Nat.testBit_or]; cases decide (b < 8) <;> simp

theorem fld_xor (a c j : ℕ) : fld (a ^^^ c) j = fld a j ^^^ fld c j := by
  apply Nat.eq_of_testBit_eq; intro b
  simp only [testBit_fld, Nat.testBit_xor]; cases decide (b < 8) <;> simp

/-- Fieldwise multiplication by a constant without carries. -/
theorem fld_mulc : ∀ (j a k : ℕ), (∀ i, fld a i * k < Bs) → fld (a * k) j = fld a j * k
  | 0, a, k, h => by
    have h0 := h 0
    simp only [fld_zero] at h0 ⊢
    have e := Nat.mod_add_div a Bs
    have : a * k = a % Bs * k + Bs * (a / Bs * k) := by
      conv_lhs => rw [← e]
      ring
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
  | j + 1, a, k, h => by
    have h0 := h 0
    simp only [fld_zero] at h0
    have e := Nat.mod_add_div a Bs
    have : a * k = a % Bs * k + Bs * (a / Bs * k) := by
      conv_lhs => rw [← e]
      ring
    have q : a * k / Bs = a / Bs * k := by
      rw [this, Nat.add_mul_div_left _ _ (by simp [Bs]), Nat.div_eq_of_lt h0, zero_add]
    rw [fld_succ, fld_succ, q]
    exact fld_mulc j _ k fun i => by
      have := h (i + 1); rwa [fld_succ] at this

/-- Dividing by 128 acts fieldwise when every field is `0` or `128`. -/
theorem fld_div128 : ∀ (j a : ℕ), (∀ i, fld a i = 0 ∨ fld a i = 128) → fld (a / 128) j = fld a j / 128
  | j, a, h => by
    have e := Nat.mod_add_div a Bs
    have h0 := h 0
    have h1 := h 1
    simp only [fld_zero] at h0
    rw [fld_succ, fld_zero] at h1
    have e' := Nat.mod_add_div (a / Bs) Bs
    -- a / 128 = a % Bs / 128 + 2 * (a / Bs), and 2 * (a / Bs) has field 0 equal to 0 mod Bs
    have q : a / 128 = a % Bs / 128 + Bs * (a / Bs / 128) := by
      simp only [Bs] at *; omega
    cases j with
    | zero =>
      rw [fld_zero, fld_zero, q, Nat.add_mul_mod_self_left]
      simp only [Bs] at *; omega
    | succ j =>
      have q2 : a / 128 / Bs = a / Bs / 128 := by
        rw [q, Nat.add_mul_div_left _ _ (by simp [Bs])]
        simp only [Bs] at *; omega
      rw [fld_succ, fld_succ, q2]
      exact fld_div128 j _ fun i => by
        have := h (i + 1); rwa [fld_succ] at this
termination_by j => j

/-! ### Constants and the smallness check -/

theorem fld_oneS (N j : ℕ) : fld (oneS N) j = if j < N then 1 else 0 := by
  rw [oneS_eq, fld_ofFun N _ (fun _ => by simp [Bs])]

/-- Bit 7 in every lane below `N`. -/
def GS (N : ℕ) : ℕ := oneS N * 128

/-- Bits 0–6 in every lane below `N`. -/
def MS (N : ℕ) : ℕ := oneS N * 127

theorem fld_GS (N j : ℕ) : fld (GS N) j = if j < N then 128 else 0 := by
  unfold GS
  rw [fld_mulc j _ _ fun i => by rw [fld_oneS]; split_ifs <;> simp [Bs], fld_oneS]
  split_ifs <;> rfl

theorem fld_MS (N j : ℕ) : fld (MS N) j = if j < N then 127 else 0 := by
  unfold MS
  rw [fld_mulc j _ _ fun i => by rw [fld_oneS]; split_ifs <;> simp [Bs], fld_oneS]
  split_ifs <;> rfl

/-- Every lane below 128, nothing above lane `N`. -/
def chkS (N a : ℕ) : Bool := (a >>> (8 * N) == 0) && (a &&& GS N == 0)

theorem byte_and128 : ∀ v < 256, v &&& 128 = 0 → v < 128 := by decide +kernel

theorem small_of_chk {N a : ℕ} (h : chkS N a = true) : a < Bs ^ N ∧ ∀ j, fld a j < 128 := by
  simp only [chkS, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  have ha : a < Bs ^ N := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at h1
    rcases h1 with h1 | h1
    · simp at h1
    · simpa [Bs, pow_mul] using h1
  refine ⟨ha, fun j => ?_⟩
  by_cases hj : j < N
  · have := congrArg (fun x => fld x j) h2
    simp only [fld_land, fld_GS, hj, ↓reduceIte] at this
    exact byte_and128 _ (fld_lt a j) (by simpa [fld] using this)
  · rw [fld_of_lt ha (by omega)]; norm_num

/-! ### The operations, on numbers whose lanes are below 128 -/

/-- Truncated difference, lane by lane. -/
def subS (N a b : ℕ) : ℕ :=
  let r := a + GS N - b
  let gm := r &&& GS N
  r &&& (gm / 128 * 127)

/-- Lanes with `a < b`, as bit 7 of each lane. -/
def ltS (N a b : ℕ) : ℕ := GS N ^^^ ((a + GS N - b) &&& GS N)

theorem byte_ge : ∀ v < 256, v &&& 128 = if 128 ≤ v then 128 else 0 := by decide +kernel

theorem byte_low : ∀ v < 128, (v + 128) &&& 127 = v := by decide +kernel

/-- The lanes of `a + G - b`. -/
theorem fld_r {N a b : ℕ} (ha : a < Bs ^ N ∧ ∀ j, fld a j < 128) (hb : b < Bs ^ N ∧ ∀ j, fld b j < 128)
    (j : ℕ) : fld (a + GS N - b) j = if j < N then fld a j + 128 - fld b j else 0 := by
  have hadd : ∀ i, fld (a + GS N) i = fld a i + fld (GS N) i :=
    fun i => fld_add i _ _ fun k => by
      have := ha.2 k; rw [fld_GS]; split_ifs <;> simp [Bs] <;> omega
  rw [fld_sub j _ _ fun i => by
    rw [hadd, fld_GS]; split_ifs with hi
    · have := hb.2 i; omega
    · rw [fld_of_lt hb.1 (by omega)]; omega, hadd, fld_GS]
  split_ifs with hj
  · rfl
  · rw [fld_of_lt ha.1 (by omega), fld_of_lt hb.1 (by omega)]

theorem fld_subS {N a b : ℕ} (ha : a < Bs ^ N ∧ ∀ j, fld a j < 128)
    (hb : b < Bs ^ N ∧ ∀ j, fld b j < 128) (j : ℕ) : fld (subS N a b) j = fld a j - fld b j := by
  unfold subS
  simp only
  have hr := fld_r ha hb
  have hgm : ∀ i, fld ((a + GS N - b) &&& GS N) i = if i < N ∧ fld b i ≤ fld a i then 128 else 0 := by
    intro i
    rw [fld_land, hr, fld_GS]
    by_cases hi : i < N
    · have := byte_ge (fld a i + 128 - fld b i) (by have := ha.2 i; omega)
      simp only [hi, true_and, ↓reduceIte, this]
      split_ifs <;> omega
    · simp [hi]
  have hdiv : ∀ i, fld (((a + GS N - b) &&& GS N) / 128) i =
      if i < N ∧ fld b i ≤ fld a i then 1 else 0 := by
    intro i
    rw [fld_div128 i _ fun k => by rw [hgm]; split_ifs <;> simp, hgm]
    split_ifs <;> rfl
  have hmul : ∀ i, fld (((a + GS N - b) &&& GS N) / 128 * 127) i =
      if i < N ∧ fld b i ≤ fld a i then 127 else 0 := by
    intro i
    rw [fld_mulc i _ _ fun k => by rw [hdiv]; split_ifs <;> simp [Bs], hdiv]
    split_ifs <;> rfl
  rw [fld_land, hr, hmul]
  by_cases hj : j < N
  · by_cases hab : fld b j ≤ fld a j
    · simp only [hj, hab, and_self, ↓reduceIte]
      have := byte_low (fld a j - fld b j) (by have := ha.2 j; omega)
      rw [show fld a j + 128 - fld b j = fld a j - fld b j + 128 by omega, this]
    · simp only [hj, hab, and_false, ↓reduceIte, Nat.and_zero]; omega
  · simp only [hj, ↓reduceIte, false_and, Nat.zero_and]
    rw [fld_of_lt ha.1 (by omega), fld_of_lt hb.1 (by omega)]

theorem testBit_ltS {N a b j : ℕ} (ha : a < Bs ^ N ∧ ∀ j, fld a j < 128)
    (hb : b < Bs ^ N ∧ ∀ j, fld b j < 128) (hj : j < N) :
    (ltS N a b).testBit (8 * j + 7) = decide (fld a j < fld b j) := by
  have h7 : ∀ x, x.testBit (8 * j + 7) = (fld x j).testBit 7 := by
    intro x; rw [testBit_fld]; rfl
  rw [h7]
  unfold ltS
  rw [fld_xor, fld_land, fld_r ha hb, fld_GS]
  simp only [hj, ↓reduceIte]
  have := byte_ge (fld a j + 128 - fld b j) (by have := ha.2 j; omega)
  rw [this]
  split_ifs with h
  · have : ¬ fld a j < fld b j := by omega
    simp only [this, decide_false, Nat.xor_self]; rfl
  · have : fld a j < fld b j := by omega
    simp only [this, decide_true, Nat.xor_zero]; rfl

/-! ### Lane Booleans in bit 0 of each lane -/

theorem testBit_fld0 (a j : ℕ) : a.testBit (8 * j) = (fld a j).testBit 0 := by
  rw [testBit_fld]; rfl

theorem testBit_oneS {N j : ℕ} : (oneS N).testBit (8 * j) = decide (j < N) := by
  rw [testBit_fld0, fld_oneS]; split_ifs with h <;> simp [h]

/-- Lanes with `a < b`, in bit 0. -/
def ltB (N a b : ℕ) : ℕ := ltS N a b >>> 7

theorem testBit_ltB {N a b j : ℕ} (ha : a < Bs ^ N ∧ ∀ j, fld a j < 128)
    (hb : b < Bs ^ N ∧ ∀ j, fld b j < 128) (hj : j < N) :
    (ltB N a b).testBit (8 * j) = decide (fld a j < fld b j) := by
  unfold ltB
  rw [Nat.testBit_shiftRight, show 7 + 8 * j = 8 * j + 7 by ring, testBit_ltS ha hb hj]

/-- Lanes with `a = b`, in bit 0: the lane of `a xor b` is zero exactly when adding 127 leaves
bit 7 clear. -/
def eqB (N a b : ℕ) : ℕ := (GS N ^^^ (((a ^^^ b) + MS N) &&& GS N)) >>> 7

theorem byte_eq : ∀ u < 128, ∀ v < 128, ((u ^^^ v) + 127) &&& 128 = if u = v then 0 else 128 := by
  decide +kernel

theorem testBit_eqB {N a b j : ℕ} (ha : a < Bs ^ N ∧ ∀ j, fld a j < 128)
    (hb : b < Bs ^ N ∧ ∀ j, fld b j < 128) (hj : j < N) :
    (eqB N a b).testBit (8 * j) = decide (fld a j = fld b j) := by
  have hx : ∀ i, fld (a ^^^ b) i < 128 := by
    intro i; rw [fld_xor]
    exact Nat.xor_lt_two_pow (n := 7) (ha.2 i) (hb.2 i)
  have hadd : fld ((a ^^^ b) + MS N) j = fld (a ^^^ b) j + 127 := by
    rw [fld_add j _ _ fun i => by have := hx i; rw [fld_MS]; split_ifs <;> simp [Bs] <;> omega,
      fld_MS, ite_eq_left hj]
  unfold eqB
  rw [Nat.testBit_shiftRight, show 7 + 8 * j = 8 * j + 7 by ring]
  have h7 : ∀ x, x.testBit (8 * j + 7) = (fld x j).testBit 7 := by
    intro x; rw [testBit_fld]; rfl
  rw [h7, fld_xor, fld_land, hadd, fld_GS, ite_eq_left hj, fld_xor, byte_eq _ (ha.2 j) _ (hb.2 j)]
  split_ifs with h <;> simp [h]; decide

/-- Lane-wise choice: `a` where bit 0 of `c` is set, else `b`. -/
def iteS (N c a b : ℕ) : ℕ :=
  let sp := (c &&& oneS N) * 127
  (a &&& sp) ||| (b &&& (MS N ^^^ sp))

theorem byte_sel : ∀ v < 128, ∀ u < 128, (v &&& 127 ||| u &&& 0) = v ∧ (v &&& 0 ||| u &&& 127) = u := by
  decide +kernel

theorem fld_iteS {N c a b : ℕ} (ha : ∀ j, fld a j < 128) (hb : ∀ j, fld b j < 128) {j : ℕ}
    (hj : j < N) : fld (iteS N c a b) j = if c.testBit (8 * j) then fld a j else fld b j := by
  unfold iteS
  simp only
  have hc : ∀ i, fld (c &&& oneS N) i = if i < N ∧ c.testBit (8 * i) then 1 else 0 := by
    intro i
    rw [fld_land, fld_oneS]
    by_cases hi : i < N
    · simp only [hi, true_and, ↓reduceIte, Nat.and_one_is_mod, testBit_fld0, Nat.testBit_zero,
        decide_eq_true_eq]
      have := Nat.mod_two_eq_zero_or_one (fld c i)
      split_ifs <;> omega
    · simp [hi]
  have hsp : fld ((c &&& oneS N) * 127) j = if c.testBit (8 * j) then 127 else 0 := by
    rw [fld_mulc j _ _ fun i => by rw [hc]; split_ifs <;> simp [Bs], hc]
    split_ifs <;> simp_all
  rw [fld_lor, fld_land, fld_land, fld_xor, fld_MS, hsp, ite_eq_left hj]
  split_ifs
  · simpa using (byte_sel _ (ha j) _ (hb j)).1
  · simpa using (byte_sel _ (ha j) _ (hb j)).2

/-! ### Results that stay small -/

theorem lt_of_fld_zero : ∀ (N r : ℕ), (∀ j, N ≤ j → fld r j = 0) → r < Bs ^ N
  | 0, r, h => by
    have : ∀ j, fld r j = 0 := fun j => h j (Nat.zero_le _)
    have e : r = 0 := by
      by_contra hr
      have hq := le_of_fld r 0 (fun i => by rw [this]; simp [fld])
      omega
    simp [e]
  | N + 1, r, h => by
    have ih := lt_of_fld_zero N (r / Bs) fun j hj => by rw [← fld_succ]; exact h (j + 1) (by omega)
    have e := Nat.mod_add_div r Bs
    have hm := Nat.mod_lt r (show 0 < Bs by simp [Bs])
    rw [pow_succ]
    simp only [Bs] at *
    nlinarith

theorem byte_lt128 : ∀ v < 128, v &&& 128 = 0 := by decide +kernel

theorem chkS_of {N r : ℕ} (h1 : r < Bs ^ N) (h2 : ∀ j, fld r j < 128) : chkS N r = true := by
  simp only [chkS, Bool.and_eq_true, beq_iff_eq]
  refine ⟨?_, ?_⟩
  · rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff]; right; simpa [Bs, pow_mul] using h1
  · have hz : ∀ j, fld (r &&& GS N) j = 0 := by
      intro j; rw [fld_land, fld_GS]; split_ifs
      · exact byte_lt128 _ (h2 j)
      · simp
    exact Nat.le_zero.mp (le_of_fld _ 0 fun i => by rw [hz]; exact Nat.zero_le _)

theorem chkS_subS {N a b : ℕ} (ha : a < Bs ^ N ∧ ∀ j, fld a j < 128)
    (hb : b < Bs ^ N ∧ ∀ j, fld b j < 128) : chkS N (subS N a b) = true := by
  refine chkS_of (lt_of_fld_zero N _ fun j hj => ?_) fun j => ?_
  · rw [fld_subS ha hb, fld_of_lt ha.1 hj, fld_of_lt hb.1 hj]
  · rw [fld_subS ha hb]; have := ha.2 j; omega

theorem fld_iteS_out {N c a b : ℕ} (hb : b < Bs ^ N) {j : ℕ} (hj : N ≤ j) : fld (iteS N c a b) j = 0 := by
  unfold iteS
  simp only
  have hz : fld ((c &&& oneS N) * 127) j = 0 := by
    rw [fld_mulc j _ _ fun i => by
      rw [fld_land, fld_oneS]; split_ifs
      · have : fld c i &&& 1 ≤ 1 := Nat.and_le_right
        simp [Bs]; omega
      · simp [Bs]]
    rw [fld_land, fld_oneS, ite_eq_right (by omega)]; simp
  rw [fld_lor, fld_land, fld_land, fld_xor, fld_MS, ite_eq_right (by omega), hz, fld_of_lt hb hj]; simp

theorem chkS_iteS {N c a b : ℕ} (ha : a < Bs ^ N ∧ ∀ j, fld a j < 128)
    (hb : b < Bs ^ N ∧ ∀ j, fld b j < 128) : chkS N (iteS N c a b) = true := by
  refine chkS_of (lt_of_fld_zero N _ fun j hj => fld_iteS_out hb.1 hj) fun j => ?_
  by_cases hj : j < N
  · rw [fld_iteS ha.2 hb.2 hj]; split_ifs
    · exact ha.2 j
    · exact hb.2 j
  · rw [fld_iteS_out hb.1 (by omega)]; norm_num

/-! ### Back to bit-planes (the exact fallback) -/

/-- Bit `o` of every lane below `N`, packed into bits `0 … N - 1`. -/
def gath (a o : ℕ) : ℕ → ℕ
  | 0 => 0
  | N + 1 => gath a o N ||| (if a.testBit (8 * N + o) then 2 ^ N else 0)

theorem testBit_gath (a o : ℕ) : ∀ N j, (gath a o N).testBit j = (decide (j < N) && a.testBit (8 * j + o))
  | 0, j => by simp [gath]
  | N + 1, j => by
    simp only [gath, Nat.testBit_or, testBit_gath a o N j]
    split_ifs with h
    · rw [Nat.testBit_two_pow]
      by_cases hj : j = N
      · subst hj; simp [h]
      · have : (N = j) = False := by simp; omega
        by_cases hl : j < N <;> simp [hl, this] <;> omega
    · simp only [Nat.zero_testBit, Bool.or_false]
      by_cases hj : j = N
      · subst hj; simp [h]
      · by_cases hl : j < N <;> simp [hl] <;> omega

/-- The bit-planes of the lanes of `a`. -/
def toPl (N a : ℕ) : List ℕ := (List.range 8).map fun o => gath a o N

theorem byte_val : ∀ v < 256, ((v.testBit 0).toNat + 2 * ((v.testBit 1).toNat + 2 * ((v.testBit 2).toNat +
    2 * ((v.testBit 3).toNat + 2 * ((v.testBit 4).toNat + 2 * ((v.testBit 5).toNat + 2 * ((v.testBit 6).toNat +
    2 * ((v.testBit 7).toNat + 2 * 0)))))))) = v := by
  decide +kernel

theorem val_toPl {N j : ℕ} (hj : j < N) (a : ℕ) : val (toPl N a) j = fld a j := by
  have e : ∀ o, o < 8 → bt (gath a o N) j = ((fld a j).testBit o).toNat := by
    intro o ho
    simp only [bt, testBit_gath, hj, decide_true, Bool.true_and, testBit_fld, show decide (o < 8) = true by simpa]
  simp only [toPl, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, val]
  rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num), e 4 (by norm_num),
    e 5 (by norm_num), e 6 (by norm_num), e 7 (by norm_num)]
  exact byte_val _ (fld_lt a j)

/-! ### From a bit mask to bit 0 of each lane -/

/-- Bit `j` of `y` moved to bit `8 j`, using `f` steps. -/
def spreadF : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, y => y % 2 + 256 * spreadF f (y / 2)

def spread (y : ℕ) : ℕ := spreadF (y + 1) y

theorem testBit_spreadF : ∀ f y j, y < 2 ^ f → (spreadF f y).testBit (8 * j) = y.testBit j
  | 0, y, j, h => by simp at h; subst h; simp [spreadF]
  | f + 1, y, j, h => by
    have hy : y / 2 < 2 ^ f := by rw [pow_succ] at h; omega
    simp only [spreadF]
    have e : y % 2 + 256 * spreadF f (y / 2) = 2 ^ 8 * spreadF f (y / 2) + y % 2 := by ring
    rw [e]
    rw [Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (by norm_num) |>.trans_le (by norm_num))]
    cases j with
    | zero => simp [Nat.testBit_zero]
    | succ j =>
      simp only [show ¬ 8 * (j + 1) < 8 by omega, ↓reduceIte, show 8 * (j + 1) - 8 = 8 * j by omega]
      rw [testBit_spreadF f (y / 2) j hy, Nat.testBit_div_two]

theorem testBit_spread (y j : ℕ) : (spread y).testBit (8 * j) = y.testBit j :=
  testBit_spreadF _ _ _ (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-! ### Column digits in lane form -/

/-- `Q` below `Bs ^ L` in the low lanes, `X` from lane `L` on. -/
theorem fld_shift {Q X L : ℕ} (hQ : Q < Bs ^ L) (j : ℕ) :
    fld (Q + Bs ^ L * X) j = if j < L then fld Q j else fld X (j - L) := by
  induction L generalizing Q j with
  | zero =>
    simp at hQ; subst hQ; simp
  | succ L ih =>
    have h0 : Q % Bs < Bs := Nat.mod_lt _ (by simp [Bs])
    have hq : Q / Bs < Bs ^ L := by
      rw [pow_succ] at hQ; exact Nat.div_lt_of_lt_mul (by linarith)
    have e : Q + Bs ^ (L + 1) * X = Q % Bs + Bs * (Q / Bs + Bs ^ L * X) := by
      have := Nat.mod_add_div Q Bs; rw [pow_succ]; nlinarith
    cases j with
    | zero =>
      rw [e, fld_zero, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0, fld_zero]; simp
    | succ j =>
      rw [e, fld_succ, Nat.add_mul_div_left _ _ (by simp [Bs]), Nat.div_eq_of_lt h0, zero_add,
        ih hq j, fld_succ]
      simp only [Nat.add_lt_add_iff_right, Nat.add_sub_add_right]

/-- `m` copies of an `L`-lane block: `∑ t < m, Bs ^ (t L)`. -/
def repS (m L : ℕ) : ℕ := (Bs ^ (m * L) - 1) / (Bs ^ L - 1)

theorem repS_succ {L : ℕ} (hL : 0 < L) (m : ℕ) : repS (m + 1) L = 1 + Bs ^ L * repS m L := by
  unfold repS
  have hb : 1 < Bs ^ L := Nat.one_lt_pow (by omega) (by simp [Bs])
  have hd : (Bs ^ L - 1) ∣ (Bs ^ (m * L) - 1) := by
    simpa only [one_pow, ← pow_mul, mul_comm L m] using Nat.sub_dvd_pow_sub_pow (Bs ^ L) 1 m
  obtain ⟨k, hk⟩ := hd
  have hp : 1 ≤ Bs ^ (m * L) := Nat.one_le_pow _ _ (by simp [Bs])
  have e1 : Bs ^ ((m + 1) * L) - 1 = (Bs ^ L - 1) * (1 + Bs ^ L * k) := by
    rw [add_mul, one_mul, pow_add]
    have : Bs ^ (m * L) = (Bs ^ L - 1) * k + 1 := by omega
    rw [this]
    have h2 : Bs ^ L = (Bs ^ L - 1) + 1 := by omega
    set t := Bs ^ L - 1
    rw [h2]; ring_nf; omega
  rw [e1, hk, Nat.mul_div_cancel_left _ (by omega), Nat.mul_div_cancel_left _ (by omega)]

theorem fld_mul_repS {Q L : ℕ} (hL : 0 < L) (hQ : Q < Bs ^ L) : ∀ m j,
    fld (Q * repS m L) j = if j < m * L then fld Q (j % L) else 0
  | 0, j => by simp [repS, fld]
  | m + 1, j => by
    rw [repS_succ hL, mul_add, mul_one, ← mul_assoc, mul_comm Q, mul_assoc, fld_shift hQ,
      fld_mul_repS hL hQ m, add_mul, one_mul]
    by_cases h1 : j < L
    · simp only [h1, ↓reduceIte, show j < m * L + L by omega, Nat.mod_eq_of_lt h1]
    · simp only [h1, ↓reduceIte]
      by_cases h2 : j - L < m * L
      · simp only [h2, show j < m * L + L by omega, ↓reduceIte, ← Nat.mod_eq_sub_mod (by omega : L ≤ j)]
      · simp only [h2, show ¬ j < m * L + L by omega, ↓reduceIte]

/-- Lane `j < h L` holds `j / L`. -/
def blockS (L : ℕ) : ℕ → ℕ
  | 0 => 0
  | h + 1 => blockS L h + Bs ^ (h * L) * (h * oneS L)

theorem hmul_lt {h L : ℕ} (hh : h < Bs) : h * oneS L < Bs ^ L := by
  rw [oneS_eq, mul_comm, ofFun_mulc]
  exact ofFun_lt L _ fun _ => by simpa using hh

theorem fld_hmul {h L j : ℕ} (hh : h < Bs) : fld (h * oneS L) j = if j < L then h else 0 := by
  rw [mul_comm, fld_mulc j _ _ fun i => by rw [fld_oneS]; split_ifs <;> simp <;> omega, fld_oneS]
  split_ifs <;> simp

theorem blockS_spec {L : ℕ} (hL : 0 < L) : ∀ h, h ≤ Bs →
    blockS L h < Bs ^ (h * L) ∧ ∀ j, fld (blockS L h) j = if j < h * L then j / L else 0
  | 0, _ => by simp [blockS, fld]
  | h + 1, hh => by
    obtain ⟨b1, b2⟩ := blockS_spec hL h (by omega)
    have hm := hmul_lt (L := L) (show h < Bs by omega)
    refine ⟨?_, fun j => ?_⟩
    · simp only [blockS, add_mul, one_mul, pow_add]
      nlinarith [Nat.one_le_pow (h * L) Bs (by simp [Bs])]
    · simp only [blockS]
      rw [fld_shift b1, fld_hmul (show h < Bs by omega), b2, add_mul, one_mul]
      by_cases h1 : j < h * L
      · simp only [h1, ↓reduceIte, show j < h * L + L by omega]
      · simp only [h1, ↓reduceIte]
        by_cases h2 : j - h * L < L
        · simp only [h2, ↓reduceIte, show j < h * L + L by omega]
          exact (Nat.div_eq_of_lt_le (by omega) (by rw [add_mul, one_mul]; omega)).symm
        · simp only [h2, ↓reduceIte, show ¬ j < h * L + L by omega]


/-- Column `c` of the base-`h` 4-digit numbers below `h ^ 4`, in lane form. -/
def YS (h c : ℕ) : ℕ := blockS (h ^ (3 - c)) h * repS (h ^ c) (h ^ (4 - c))

theorem fld_YS {h c j : ℕ} (hh : 0 < h) (hb : h ≤ Bs) (hc : c ≤ 3) (hj : j < h ^ 4) :
    fld (YS h c) j = j / h ^ (3 - c) % h := by
  have hL : 0 < h ^ (3 - c) := by positivity
  obtain ⟨b1, b2⟩ := blockS_spec hL h hb
  have e1 : h * h ^ (3 - c) = h ^ (4 - c) := by
    rw [show 4 - c = 3 - c + 1 by omega, pow_succ, mul_comm]
  have e2 : h ^ c * h ^ (4 - c) = h ^ 4 := by rw [← pow_add]; congr 1; omega
  rw [e1] at b1
  unfold YS
  rw [fld_mul_repS (by positivity) b1, e2, b2, e1]
  simp only [hj, ↓reduceIte, Nat.mod_lt _ (show 0 < h ^ (4 - c) by positivity)]
  rw [show h ^ (4 - c) = h ^ (3 - c) * h by rw [← e1, mul_comm], Nat.mod_mul_right_div_self]

end ZZN.Lane

/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Cut.Lane

@[expose] public section

/-!
# Input planes for column tuples

Lanes `j < C^4` are the column 4-tuples in base `C`: coordinate `i` of lane `j` is
`(j / C^(3-i)) % C`. `colPlanes C i` holds bit-planes 0–4 of that coordinate
(`val_colPlanes`, for `C ≤ 32`).
-/

namespace ZZN.BoxK

open ZZN.Lane

def rep (x L : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => x ||| (rep x L n <<< L)

theorem testBit_rep {x L : ℕ} (hx : x < 2 ^ L) : ∀ (n j : ℕ),
    (rep x L n).testBit j = (decide (j < n * L) && x.testBit (j % L))
  | 0, j => by simp [rep]
  | n + 1, j => by
    simp only [rep, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hj : j < L
    · have h1 : j % L = j := Nat.mod_eq_of_lt hj
      simp [h1, show ¬ L ≤ j by omega, show j < (n + 1) * L by nlinarith]
    · obtain ⟨t, rfl⟩ : ∃ t, j = L + t := ⟨j - L, by omega⟩
      have hx0 : x.testBit (L + t) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))
      rw [hx0, show L + t - L = t by omega, testBit_rep hx n t]
      simp only [Bool.false_or, show L ≤ L + t by omega, decide_true, Bool.true_and,
        Nat.add_mod_left]
      congr 1
      simp only [decide_eq_decide]
      constructor <;> intro h <;> nlinarith

def blk (st k : ℕ) : ℕ → ℕ
  | 0 => 0
  | y + 1 => blk st k y ||| (if y.testBit k then (2 ^ st - 1) <<< (y * st) else 0)

theorem testBit_blk {st k : ℕ} (hst : 0 < st) : ∀ (n m : ℕ),
    (blk st k n).testBit m = (decide (m < n * st) && (m / st).testBit k)
  | 0, m => by simp [blk]
  | n + 1, m => by
    have e : (n + 1) * st = n * st + st := by ring
    simp only [blk, Nat.testBit_or, testBit_blk hst n m]
    by_cases h1 : m < n * st
    · have h2 : m < (n + 1) * st := by nlinarith
      split_ifs <;> simp [h1, h2, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    · by_cases h2 : m < (n + 1) * st
      · have hq : m / st = n := by
          rw [Nat.div_eq_iff hst]; constructor <;> omega
        split_ifs with hb
        · simp [h1, h2, hq, hb, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
          omega
        · simp [h1, h2, hq, hb]
      · split_ifs <;> simp [h1, h2, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
        intro _
        omega

theorem blk_lt {st k : ℕ} (hst : 0 < st) (n : ℕ) : blk st k n < 2 ^ (n * st) := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_blk hst]; simp; omega

/-- Bit `k` of digit `i` (most significant first) of every lane `j < C^4`. -/
def plane (C i k : ℕ) : ℕ := rep (blk (C ^ (3 - i)) k C) (C * C ^ (3 - i)) (C ^ i)

def colPlanes (C i : ℕ) : List ℕ := (List.range 5).map (plane C i)

/-- Digit `i` of `j` in base `C`. -/
def digit (C i j : ℕ) : ℕ := (j / C ^ (3 - i)) % C

theorem testBit_plane {C i k j : ℕ} (hC : 0 < C) (hi : i ≤ 3) (hj : j < C ^ 4) :
    (plane C i k).testBit j = (digit C i j).testBit k := by
  have hst : 0 < C ^ (3 - i) := Nat.pow_pos hC
  have hb := blk_lt (k := k) hst C
  unfold plane
  rw [testBit_rep (by simpa [mul_comm] using hb), testBit_blk hst]
  have e : C ^ i * (C * C ^ (3 - i)) = C ^ 4 := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  have h1 : j % (C * C ^ (3 - i)) < C * C ^ (3 - i) := Nat.mod_lt _ (by positivity)
  simp only [e, hj, decide_true, Bool.true_and, h1]
  rw [show C * C ^ (3 - i) = C ^ (3 - i) * C by ring, Nat.mod_mul_right_div_self]
  rfl

theorem val_five (d j : ℕ) (f : ℕ → ℕ) (hd : d < 32) (hf : ∀ k, (f k).testBit j = d.testBit k) :
    val ((List.range 5).map f) j = d := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
    List.map_nil, val, bt, hf]
  interval_cases d <;> rfl

theorem val_colPlanes {C i j : ℕ} (hC : 0 < C) (hC32 : C ≤ 32) (hi : i ≤ 3) (hj : j < C ^ 4) :
    val (colPlanes C i) j = digit C i j :=
  val_five _ _ _ (by unfold digit; have := Nat.mod_lt (j / C ^ (3 - i)) hC; omega)
    (fun k => testBit_plane hC hi hj)

end ZZN.BoxK

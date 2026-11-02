/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import Mathlib.Tactic

@[expose] public section

/-!
# Lane arithmetic on bit-planes

A list of naturals `ps` (bit-planes, least significant first) holds one natural number per lane
`j`: `val ps j = Σ k, 2^k · (bit j of ps[k])`. Kernel operations on the planes act on all lanes at
once. Lanes are `j < N`; `ones N` is the all-lanes mask.

Each operation comes with its lane lemma, e.g. `val (addc a b 0) j = val a j + val b j`.
-/

namespace ZZN.Lane

/-- Bit `j` of `n` as 0 or 1. -/
def bt (n j : ℕ) : ℕ := (n.testBit j).toNat

theorem bt_le (n j : ℕ) : bt n j ≤ 1 := Bool.toNat_le _

/-- The value in lane `j`. -/
def val : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, j => bt p j + 2 * val ps j

def ones (N : ℕ) : ℕ := 2 ^ N - 1

theorem testBit_ones {N j : ℕ} (hj : j < N) : (ones N).testBit j = true := by
  unfold ones
  rw [Nat.testBit_two_pow_sub_one]
  simpa using hj

/-- Complement within the lanes. -/
def nt (N x : ℕ) : ℕ := x ^^^ ones N

theorem testBit_nt {N x j : ℕ} (hj : j < N) : (nt N x).testBit j = !x.testBit j := by
  simp [nt, Nat.testBit_xor, testBit_ones hj]

/-! ### Head and tail with zero padding

All binary operations recurse on a fuel (the longer length) and read both lists through `hd`/`tl`,
which treat a missing plane as zero. Structural recursion on the fuel keeps them reducible by the
kernel. -/

def hd (l : List ℕ) : ℕ := l.headD 0
def tl (l : List ℕ) : List ℕ := l.tail

theorem val_hd_tl (l : List ℕ) (j : ℕ) : val l j = bt (hd l) j + 2 * val (tl l) j := by
  cases l <;> simp [val, hd, tl, bt]

theorem len_tl {l : List ℕ} {f : ℕ} (h : l.length ≤ f + 1) : (tl l).length ≤ f := by
  cases l <;> simp [tl] at h ⊢; omega

theorem nil_of_len {l : List ℕ} (h : l.length ≤ 0) : l = [] := List.eq_nil_of_length_eq_zero (by omega)

/-! ### Addition -/

def addcF : ℕ → List ℕ → List ℕ → ℕ → List ℕ
  | 0, _, _, c => [c]
  | f + 1, a, b, c =>
    let p := hd a
    let q := hd b
    (p ^^^ q ^^^ c) :: addcF f (tl a) (tl b) ((p &&& q) ||| (c &&& (p ^^^ q)))

def addc (a b : List ℕ) (c : ℕ) : List ℕ := addcF (max a.length b.length) a b c

theorem val_addcF (j : ℕ) : ∀ (f : ℕ) (a b : List ℕ) (c : ℕ), a.length ≤ f → b.length ≤ f →
    val (addcF f a b c) j = val a j + val b j + bt c j
  | 0, a, b, c, ha, hb => by
    rw [nil_of_len ha, nil_of_len hb]; simp [addcF, val]
  | f + 1, a, b, c, ha, hb => by
    simp only [addcF, val]
    rw [val_addcF j f _ _ _ (len_tl ha) (len_tl hb), val_hd_tl a j, val_hd_tl b j]
    simp only [bt, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_or]
    cases (hd a).testBit j <;> cases (hd b).testBit j <;> cases c.testBit j <;> simp <;> omega

theorem val_addc (a b : List ℕ) (c j : ℕ) : val (addc a b c) j = val a j + val b j + bt c j :=
  val_addcF j _ a b c (le_max_left _ _) (le_max_right _ _)

/-! ### Comparison: the borrow chain -/

/-- The borrow out of `a - b - br`, lane by lane. -/
def borrowF (N : ℕ) : ℕ → List ℕ → List ℕ → ℕ → ℕ
  | 0, _, _, br => br
  | f + 1, a, b, br =>
    let p := hd a
    let q := hd b
    borrowF N f (tl a) (tl b) ((nt N p &&& q) ||| (nt N (p ^^^ q) &&& br))

def borrow (N : ℕ) (a b : List ℕ) (br : ℕ) : ℕ := borrowF N (max a.length b.length) a b br

theorem borrowF_spec {N j : ℕ} (hj : j < N) : ∀ (f : ℕ) (a b : List ℕ) (br : ℕ),
    a.length ≤ f → b.length ≤ f →
    (borrowF N f a b br).testBit j = decide (val a j < val b j + bt br j)
  | 0, a, b, br, ha, hb => by
    rw [nil_of_len ha, nil_of_len hb]
    simp only [borrowF, val, bt]; rcases Bool.eq_false_or_eq_true (br.testBit j) with h | h <;> simp [h]
  | f + 1, a, b, br, ha, hb => by
    simp only [borrowF]
    rw [borrowF_spec hj f _ _ _ (len_tl ha) (len_tl hb), val_hd_tl a j, val_hd_tl b j]
    simp only [bt, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, testBit_nt hj]
    rcases Bool.eq_false_or_eq_true ((hd a).testBit j) with hp | hp <;>
      rcases Bool.eq_false_or_eq_true ((hd b).testBit j) with hq | hq <;>
      rcases Bool.eq_false_or_eq_true (br.testBit j) with hb' | hb' <;> simp [hp, hq, hb'] <;> omega

theorem borrow_spec {N j : ℕ} (hj : j < N) (a b : List ℕ) (br : ℕ) :
    (borrow N a b br).testBit j = decide (val a j < val b j + bt br j) :=
  borrowF_spec hj _ a b br (le_max_left _ _) (le_max_right _ _)

/-- Lanes where `a < b`. -/
def lt (N : ℕ) (a b : List ℕ) : ℕ := borrow N a b 0

theorem testBit_lt {N j : ℕ} (hj : j < N) (a b : List ℕ) :
    (lt N a b).testBit j = decide (val a j < val b j) := by
  simp [lt, borrow_spec hj, bt]

/-! ### Equality: plane by plane -/

/-- Lanes where `a = b`, within the mask `m`. -/
def eqmF (N : ℕ) : ℕ → List ℕ → List ℕ → ℕ → ℕ
  | 0, _, _, m => m
  | f + 1, a, b, m => eqmF N f (tl a) (tl b) (m &&& nt N (hd a ^^^ hd b))

def eqm (N : ℕ) (a b : List ℕ) : ℕ := eqmF N (max a.length b.length) a b (ones N)

theorem eqmF_spec {N j : ℕ} (hj : j < N) : ∀ (f : ℕ) (a b : List ℕ) (m : ℕ),
    a.length ≤ f → b.length ≤ f →
    (eqmF N f a b m).testBit j = (m.testBit j && decide (val a j = val b j))
  | 0, a, b, m, ha, hb => by
    rw [nil_of_len ha, nil_of_len hb]; simp [eqmF, val]
  | f + 1, a, b, m, ha, hb => by
    simp only [eqmF]
    rw [eqmF_spec hj f _ _ _ (len_tl ha) (len_tl hb), val_hd_tl a j, val_hd_tl b j]
    simp only [Nat.testBit_and, Nat.testBit_xor, testBit_nt hj, bt]
    rcases Bool.eq_false_or_eq_true ((hd a).testBit j) with hp | hp <;>
      rcases Bool.eq_false_or_eq_true ((hd b).testBit j) with hq | hq <;>
      rcases Bool.eq_false_or_eq_true (m.testBit j) with hm | hm <;> simp [hp, hq, hm] <;> omega

theorem testBit_eqm {N j : ℕ} (hj : j < N) (a b : List ℕ) :
    (eqm N a b).testBit j = decide (val a j = val b j) := by
  simp [eqm, eqmF_spec hj _ a b _ (le_max_left _ _) (le_max_right _ _), testBit_ones hj]

/-! ### Truncated subtraction -/

/-- `a - b - br` with wrap-around, lane by lane. -/
def subwF (N : ℕ) : ℕ → List ℕ → List ℕ → ℕ → List ℕ
  | 0, _, _, _ => []
  | f + 1, a, b, br =>
    let p := hd a
    let q := hd b
    (p ^^^ q ^^^ br) :: subwF N f (tl a) (tl b) ((nt N p &&& q) ||| (nt N (p ^^^ q) &&& br))

def subw (N : ℕ) (a b : List ℕ) (br : ℕ) : List ℕ := subwF N (max a.length b.length) a b br

theorem val_subwF {N j : ℕ} (hj : j < N) : ∀ (f : ℕ) (a b : List ℕ) (br : ℕ),
    a.length ≤ f → b.length ≤ f →
    val b j + bt br j ≤ val a j → val (subwF N f a b br) j = val a j - val b j - bt br j
  | 0, a, b, br, ha, hb, h => by
    rw [nil_of_len ha, nil_of_len hb] at *; simp [subwF, val] at h ⊢
  | f + 1, a, b, br, ha, hb, h => by
    simp only [subwF, val]
    rw [val_hd_tl a j, val_hd_tl b j] at h ⊢
    have hbor := borrowF_spec hj f (tl a) (tl b) ((nt N (hd a) &&& hd b) ||| (nt N (hd a ^^^ hd b) &&& br))
      (len_tl ha) (len_tl hb)
    have ih := val_subwF hj f (tl a) (tl b) ((nt N (hd a) &&& hd b) ||| (nt N (hd a ^^^ hd b) &&& br))
      (len_tl ha) (len_tl hb)
    simp only [bt, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_or, testBit_nt hj] at h ih hbor ⊢
    rcases Bool.eq_false_or_eq_true ((hd a).testBit j) with hp | hp <;>
      rcases Bool.eq_false_or_eq_true ((hd b).testBit j) with hq | hq <;>
      rcases Bool.eq_false_or_eq_true (br.testBit j) with hb' | hb' <;>
      simp [hp, hq, hb'] at h ih hbor ⊢ <;> omega

theorem val_subw {N j : ℕ} (hj : j < N) (a b : List ℕ) (br : ℕ)
    (h : val b j + bt br j ≤ val a j) : val (subw N a b br) j = val a j - val b j - bt br j :=
  val_subwF hj _ a b br (le_max_left _ _) (le_max_right _ _) h

/-- Mask every plane. -/
def mskp (m : ℕ) (ps : List ℕ) : List ℕ := ps.map (· &&& m)

theorem val_mskp (m : ℕ) (j : ℕ) : ∀ ps : List ℕ, val (mskp m ps) j = if m.testBit j then val ps j else 0
  | [] => by simp [mskp, val]
  | p :: ps => by
    have := val_mskp m j ps
    simp only [mskp, List.map_cons, val] at this ⊢
    rw [this]
    simp only [bt, Nat.testBit_and]
    cases m.testBit j <;> simp

/-- Truncated subtraction. -/
def sub (N : ℕ) (a b : List ℕ) : List ℕ := mskp (nt N (lt N a b)) (subw N a b 0)

theorem val_sub {N j : ℕ} (hj : j < N) (a b : List ℕ) : val (sub N a b) j = val a j - val b j := by
  unfold sub
  rw [val_mskp, testBit_nt hj, testBit_lt hj]
  by_cases h : val a j < val b j
  · simp [h]; omega
  · simp [h]
    rw [val_subw hj a b 0 (by simp [bt]; omega)]
    simp [bt]

/-! ### Select and constants -/

/-- Lane-wise `if m then a else b` (planes padded with zero). -/
def selF (N m : ℕ) : ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _ => []
  | f + 1, a, b => ((hd a &&& m) ||| (hd b &&& nt N m)) :: selF N m f (tl a) (tl b)

def sel (N m : ℕ) (a b : List ℕ) : List ℕ := selF N m (max a.length b.length) a b

theorem val_selF {N j : ℕ} (hj : j < N) (m : ℕ) : ∀ (f : ℕ) (a b : List ℕ),
    a.length ≤ f → b.length ≤ f → val (selF N m f a b) j = if m.testBit j then val a j else val b j
  | 0, a, b, ha, hb => by rw [nil_of_len ha, nil_of_len hb]; simp [selF, val]
  | f + 1, a, b, ha, hb => by
    simp only [selF, val]
    rw [val_selF hj m f _ _ (len_tl ha) (len_tl hb), val_hd_tl a j, val_hd_tl b j]
    simp only [bt, Nat.testBit_and, Nat.testBit_or, testBit_nt hj]
    cases m.testBit j <;> simp

theorem val_sel {N j : ℕ} (hj : j < N) (m : ℕ) (a b : List ℕ) :
    val (sel N m a b) j = if m.testBit j then val a j else val b j :=
  val_selF hj m _ a b (le_max_left _ _) (le_max_right _ _)

/-- Bits of `n` as full or empty planes, with structural fuel (kernel-reducible). -/
def cstF (N : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else (if n % 2 = 1 then ones N else 0) :: cstF N f (n / 2)

/-- The constant `n` in every lane. -/
def cst (N n : ℕ) : List ℕ := cstF N (n + 1) n

theorem val_cstF {N j : ℕ} (hj : j < N) : ∀ (f n : ℕ), n < 2 ^ f → val (cstF N f n) j = n
  | 0, n, h => by simp at h; simp [cstF, val, h]
  | f + 1, n, h => by
    unfold cstF
    split_ifs with h0 h1
    · simp [val, h0]
    · simp only [val, bt, testBit_ones hj, Bool.toNat_true]
      rw [val_cstF hj f (n / 2) (by rw [pow_succ] at h; omega)]; omega
    · simp only [val, bt, Nat.zero_testBit, Bool.toNat_false]
      rw [val_cstF hj f (n / 2) (by rw [pow_succ] at h; omega)]; omega

theorem val_cst {N j : ℕ} (hj : j < N) (n : ℕ) : val (cst N n) j = n :=
  val_cstF hj (n + 1) n (Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by norm_num) (by omega)))

end ZZN.Lane

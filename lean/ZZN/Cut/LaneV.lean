-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Cut.Swar
import GridHam.Forbidden

/-!
# Lane values with constant folding, and IPS acceptability per lane

`LV`: a number per lane, either one constant for all lanes or bit-planes. `LB`: a Boolean per
lane, either a constant or a mask. Operations on constants fold to constants, so tests that only
involve constants cost no kernel bit operations.

`accB` is IPS acceptability written with the operations available on lanes;
`accB_eq : accB w h s t = decide (IsAcceptable w h s t)`. `accV` is its lane version;
`accV_at : (accV …).get j = accB (… get j)`.
-/

namespace ZZN.Lane

inductive LV where
  | k (n : ℕ)
  | v (ps : List ℕ)
  | s (a : ℕ)
  | t (N a : ℕ) (h : chkS N a = true)

inductive LB where
  | b (x : Bool)
  | m (n : ℕ)
  | g (n : ℕ)

namespace LV

def get : LV → ℕ → ℕ
  | k n, _ => n
  | v ps, j => val ps j
  | s a, j => fld a j
  | t _ a _, j => fld a j

def pl (N : ℕ) : LV → List ℕ
  | k n => cst N n
  | v ps => ps
  | s a => toPl N a
  | t _ a _ => toPl N a

theorem val_pl {N j : ℕ} (hj : j < N) : ∀ x : LV, val (x.pl N) j = x.get j
  | k n => val_cst hj n
  | v _ => rfl
  | s a => val_toPl hj a
  | t _ a _ => val_toPl hj a

/-- The 8-bit lane form, when every lane is below 128. -/
def toS (N : ℕ) : LV → Option ℕ
  | k n => if n < 128 then some (n * oneS N) else none
  | v _ => none
  | s a => if chkS N a then some a else none
  | t M a _ => if M = N then some a else if chkS N a then some a else none

theorem toS_spec {N : ℕ} {x : LV} {a : ℕ} (h : toS N x = some a) :
    (a < Bs ^ N ∧ ∀ i, fld a i < 128) ∧ ∀ j, j < N → fld a j = x.get j := by
  cases x with
  | k n =>
    simp only [toS] at h
    split_ifs at h with hn
    cases h
    have hf : ∀ i, fld (n * oneS N) i = if i < N then n else 0 := by
      intro i
      rw [mul_comm, fld_mulc i _ _ fun k => by rw [fld_oneS]; split_ifs <;> simp [Bs]; omega, fld_oneS]
      split_ifs <;> simp
    refine ⟨⟨?_, fun i => by rw [hf]; split_ifs <;> omega⟩, fun j hj => by rw [hf, ite_eq_left hj]; rfl⟩
    rw [oneS_eq, mul_comm, ofFun_mulc]
    exact ofFun_lt N _ fun _ => by simp [Bs]; omega
  | v _ => simp [toS] at h
  | s b =>
    simp only [toS] at h
    split_ifs at h with hc
    cases h
    exact ⟨small_of_chk hc, fun j _ => rfl⟩
  | t M b hb =>
    simp only [toS] at h
    split_ifs at h with hm hc
    · cases h; subst hm; exact ⟨small_of_chk hb, fun j _ => rfl⟩
    · cases h; exact ⟨small_of_chk hc, fun j _ => rfl⟩

def add (N : ℕ) : LV → LV → LV
  | k a, k b => k (a + b)
  | x, y => match toS N x, toS N y with
    | some a, some b => s (a + b)
    | _, _ => v (addc (x.pl N) (y.pl N) 0)

theorem at_add {N j : ℕ} (hj : j < N) (x y : LV) : (add N x y).get j = x.get j + y.get j := by
  have slow : (v (addc (x.pl N) (y.pl N) 0)).get j = x.get j + y.get j := by
    simp [get, val_addc, val_pl hj, bt]
  unfold add
  split
  · rfl
  · split
    · next a b ha hb =>
      obtain ⟨sa, ea⟩ := toS_spec ha
      obtain ⟨sb, eb⟩ := toS_spec hb
      show fld (a + b) j = _
      rw [fld_add j _ _ fun i => by have := sa.2 i; have := sb.2 i; simp [Bs]; omega, ea j hj, eb j hj]
    · exact slow

def sub (N : ℕ) : LV → LV → LV
  | k a, k b => k (a - b)
  | x, y => match hx : toS N x, hy : toS N y with
    | some a, some b => t N (subS N a b) (chkS_subS (toS_spec hx).1 (toS_spec hy).1)
    | _, _ => v (Lane.sub N (x.pl N) (y.pl N))

theorem at_sub {N j : ℕ} (hj : j < N) (x y : LV) : (sub N x y).get j = x.get j - y.get j := by
  have slow : (v (Lane.sub N (x.pl N) (y.pl N))).get j = x.get j - y.get j := by
    simp [get, val_sub hj, val_pl hj]
  unfold sub
  split
  · rfl
  · split
    · rename_i a b ha hb
      obtain ⟨sa, ea⟩ := toS_spec ha
      obtain ⟨sb, eb⟩ := toS_spec hb
      show fld (subS N a b) j = _
      rw [fld_subS sa sb, ea j hj, eb j hj]
    · exact slow

end LV

namespace LB

def get : LB → ℕ → Bool
  | b x, _ => x
  | m n, j => n.testBit j
  | g n, j => n.testBit (8 * j)

def mk (N : ℕ) : LB → ℕ
  | b true => ones N
  | b false => 0
  | m n => n
  | g n => gath n 0 N

theorem testBit_mk {N j : ℕ} (hj : j < N) (x : LB) : (x.mk N).testBit j = x.get j := by
  cases x with
  | b x => cases x <;> simp [mk, get, testBit_ones hj]
  | m n => rfl
  | g n => simp [mk, get, testBit_gath, hj]

/-- The lane Booleans at bits `8 j` (the 8-bit lane form). -/
def mkG (N : ℕ) : LB → ℕ
  | b true => oneS N
  | b false => 0
  | m n => spread n &&& oneS N
  | g n => n &&& oneS N

theorem testBit_mkG {N j : ℕ} (hj : j < N) (x : LB) : (x.mkG N).testBit (8 * j) = x.get j := by
  cases x with
  | b x => cases x <;> simp [mkG, get, testBit_oneS, hj]
  | m n => simp [mkG, get, Nat.testBit_and, testBit_spread, testBit_oneS, hj]
  | g n => simp [mkG, get, Nat.testBit_and, testBit_oneS, hj]

/-- `and` with a field-form first argument; the second is looked at only when needed. -/
def andG (x : ℕ) : LB → LB
  | b false => b false
  | b true => g x
  | m y => g (x &&& spread y)
  | g y => g (x &&& y)

def andM (x : ℕ) : LB → LB
  | b false => b false
  | b true => m x
  | m y => m (x &&& y)
  | g y => g (spread x &&& y)

/-- Lane-wise `and`. When the first argument is false in every lane, the second is not
evaluated. -/
def and : LB → LB → LB
  | b false, _ => b false
  | b true, y => y
  | g x, y => if x = 0 then b false else andG x y
  | m x, y => andM x y

theorem at_and (x y : LB) (j : ℕ) : (and x y).get j = (x.get j && y.get j) := by
  rcases x with ⟨_ | _⟩ | x | x
  · rfl
  · simp [and, get]
  · rcases y with ⟨_ | _⟩ | y | y <;> simp [and, andM, get, Nat.testBit_and, testBit_spread]
  · simp only [and]
    split_ifs with hx
    · subst hx; simp [get]
    · rcases y with ⟨_ | _⟩ | y | y <;> simp [andG, get, Nat.testBit_and, testBit_spread]

def or : LB → LB → LB
  | b true, _ => b true
  | _, b true => b true
  | b false, y => y
  | x, b false => x
  | m x, m y => m (x ||| y)
  | g x, g y => g (x ||| y)
  | g x, m y => g (x ||| spread y)
  | m x, g y => g (spread x ||| y)

theorem at_or (x y : LB) (j : ℕ) : (or x y).get j = (x.get j || y.get j) := by
  rcases x with ⟨_ | _⟩ | x | x <;> rcases y with ⟨_ | _⟩ | y | y <;>
    simp [or, get, Nat.testBit_or, testBit_spread]

def not (N : ℕ) : LB → LB
  | b x => b (!x)
  | m n => m (nt N n)
  | g n => g (n ^^^ oneS N)

theorem at_not {N j : ℕ} (hj : j < N) (x : LB) : (not N x).get j = !x.get j := by
  cases x <;> simp [not, get, testBit_nt hj, Nat.testBit_xor, testBit_oneS, hj]

/-- Lane-wise `if c then x else y` on Booleans. -/
def ite (N : ℕ) (c x y : LB) : LB := or (and c x) (and (not N c) y)

theorem at_ite {N j : ℕ} (hj : j < N) (c x y : LB) :
    (ite N c x y).get j = if c.get j then x.get j else y.get j := by
  simp only [ite, at_or, at_and, at_not hj]; cases c.get j <;> simp

end LB

namespace LV

def lt (N : ℕ) : LV → LV → LB
  | k a, k b => LB.b (decide (a < b))
  | x, y => match toS N x, toS N y with
    | some a, some b => LB.g (ltB N a b)
    | _, _ => LB.m (Lane.lt N (x.pl N) (y.pl N))

theorem at_lt {N j : ℕ} (hj : j < N) (x y : LV) : (lt N x y).get j = decide (x.get j < y.get j) := by
  have slow : (LB.m (Lane.lt N (x.pl N) (y.pl N))).get j = decide (x.get j < y.get j) := by
    simp [LB.get, testBit_lt hj, val_pl hj]
  unfold lt
  split
  · rfl
  · split
    · next a b ha hb =>
      obtain ⟨sa, ea⟩ := toS_spec ha
      obtain ⟨sb, eb⟩ := toS_spec hb
      show (ltB N a b).testBit (8 * j) = _
      rw [testBit_ltB sa sb hj, ea j hj, eb j hj]
    · exact slow

def le (N : ℕ) (x y : LV) : LB := LB.not N (lt N y x)

theorem at_le {N j : ℕ} (hj : j < N) (x y : LV) : (le N x y).get j = decide (x.get j ≤ y.get j) := by
  simp only [le, LB.at_not hj, at_lt hj]
  by_cases h : x.get j ≤ y.get j <;> simp [h]; omega

def eq (N : ℕ) : LV → LV → LB
  | k a, k b => LB.b (decide (a = b))
  | x, y => match toS N x, toS N y with
    | some a, some b => LB.g (eqB N a b)
    | _, _ => LB.m (Lane.eqm N (x.pl N) (y.pl N))

theorem at_eq {N j : ℕ} (hj : j < N) (x y : LV) : (eq N x y).get j = decide (x.get j = y.get j) := by
  have slow : (LB.m (Lane.eqm N (x.pl N) (y.pl N))).get j = decide (x.get j = y.get j) := by
    simp [LB.get, testBit_eqm hj, val_pl hj]
  unfold eq
  split
  · rfl
  · split
    · next a b ha hb =>
      obtain ⟨sa, ea⟩ := toS_spec ha
      obtain ⟨sb, eb⟩ := toS_spec hb
      show (eqB N a b).testBit (8 * j) = _
      rw [testBit_eqB sa sb hj, ea j hj, eb j hj]
    · exact slow

/-- Lane-wise `if c then x else y` on numbers. -/
def ite (N : ℕ) : LB → LV → LV → LV
  | LB.b true, x, _ => x
  | LB.b false, _, y => y
  | LB.m c, x, y => v (sel N c (x.pl N) (y.pl N))
  | LB.g c, x, y => if c = 0 then y else match hx : toS N x, hy : toS N y with
    | some a, some b => t N (iteS N c a b) (chkS_iteS (toS_spec hx).1 (toS_spec hy).1)
    | _, _ => v (sel N (gath c 0 N) (x.pl N) (y.pl N))

theorem at_ite {N j : ℕ} (hj : j < N) (c : LB) (x y : LV) :
    (ite N c x y).get j = if c.get j then x.get j else y.get j := by
  rcases c with ⟨_ | _⟩ | c | c
  · rfl
  · rfl
  · simp [ite, LB.get, get, val_sel hj, val_pl hj]; congr
  · simp only [ite]
    by_cases hc0 : c = 0
    · subst hc0; simp [LB.get]
    rw [ite_eq_right hc0]
    split
    · rename_i a b ha hb
      obtain ⟨sa, ea⟩ := toS_spec ha
      obtain ⟨sb, eb⟩ := toS_spec hb
      show fld (iteS N c a b) j = _
      rw [fld_iteS sa.2 sb.2 hj, ea j hj, eb j hj]; rfl
    · show val (sel N (gath c 0 N) (x.pl N) (y.pl N)) j = _
      rw [val_sel hj, val_pl hj, val_pl hj, testBit_gath]
      simp only [hj, decide_true, Bool.true_and, LB.get]
      rfl

/-- Lanes holding an odd number. -/
def odd : LV → LB
  | k n => LB.b (decide (n % 2 = 1))
  | v [] => LB.b false
  | v (p :: _) => LB.m p
  | s a => LB.g a
  | t _ a _ => LB.g a

theorem at_odd (x : LV) (j : ℕ) : (odd x).get j = decide (x.get j % 2 = 1) := by
  cases x with
  | k n => rfl
  | v ps =>
    cases ps with
    | nil => simp [odd, get, val, LB.get]
    | cons p ps =>
      simp only [odd, LB.get, get, val, bt]
      rcases Bool.eq_false_or_eq_true (p.testBit j) with hp | hp <;> simp [hp]
  | s a =>
    simp only [odd, LB.get, get, testBit_fld0, Nat.testBit_zero]
    rfl
  | t _ a _ =>
    simp only [odd, LB.get, get, testBit_fld0, Nat.testBit_zero]
    rfl

end LV

/-! ### IPS acceptability with lane operations -/

open GridHam

/-- IPS acceptability, written with `+`, `-`, `<`, `=`, odd and if-then-else only. -/
def accB (w h : ℕ) (s t : Coord) : Bool :=
  let ps := decide ((s.1 + s.2) % 2 = 1)
  let pt := decide ((t.1 + t.2) % 2 = 1)
  let ow := decide (w % 2 = 1)
  let oh := decide (h % 2 = 1)
  let cc := if ow && oh then (!ps && !pt) else (ps != pt)
  let corner := fun v : Coord => (decide (v.1 = 0) || decide (v.1 = w - 1)) &&
    (decide (v.2 = 0) || decide (v.2 = h - 1))
  -- case 1
  let isW1 := decide (w = 1)
  let fx := if isW1 then 0 else w - 1
  let fy := if isW1 then h - 1 else 0
  let f1 := !((decide (s.1 = 0) && decide (s.2 = 0) && decide (t.1 = fx) && decide (t.2 = fy)) ||
    (decide (s.1 = fx) && decide (s.2 = fy) && decide (t.1 = 0) && decide (t.2 = 0)))
  -- case 2
  let f2 := !corner s && !corner t &&
    ((decide (w = 2) && decide (s.2 = t.2)) || (decide (h = 2) && decide (s.1 = t.1)))
  -- case 3
  let isW3 := decide (w = 3)
  let oppOdd := if isW3 then oh else ow
  let c0 := if isW3 then s.2 else s.1
  let c1 := if isW3 then t.2 else t.1
  let oc := if isW3 then s.1 else s.2
  let gr := decide (c1 < c0)
  let dist := if gr then c0 - c1 else c1 - c0
  let dsat := if decide (oc = 1) then decide (0 < dist) else decide (1 < dist)
  let f3 := !oppOdd && (ps != pt) && dsat && ((gr && !ps) || (!gr && ps))
  let forb := if decide (w = 1) || decide (h = 1) then f1
    else if decide (w = 2) || decide (h = 2) then f2
    else if decide (w = 3) || decide (h = 3) then f3 else false
  cc && !forb

set_option maxHeartbeats 4000000 in
theorem accB_eq (w h : ℕ) (s t : Coord) : accB w h s t = decide (IsAcceptable w h s t) := by
  obtain ⟨s1, s2⟩ := s
  obtain ⟨t1, t2⟩ := t
  have hwh : (w * h) % 2 = 1 ↔ (w % 2 = 1 ∧ h % 2 = 1) := by
    rw [Nat.mul_mod]
    rcases Nat.mod_two_eq_zero_or_one w with a | a <;>
      rcases Nat.mod_two_eq_zero_or_one h with b | b <;> simp [a, b]
  simp only [accB, GridHam.IsAcceptable, GridHam.ColorCompatible, GridHam.IsForbidden,
    GridHam.ForbiddenCase1, GridHam.ForbiddenCase2, GridHam.ForbiddenCase3, GridHam.IsCorner,
    GridHam.parity]
  have hm2 : (w * h) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  generalize (w * h) % 2 = m at hwh hm2 ⊢
  by_cases hw1 : w = 1 <;> by_cases hh1 : h = 1 <;> by_cases hw2 : w = 2 <;> by_cases hh2 : h = 2 <;>
    by_cases hw3 : w = 3 <;> by_cases hh3 : h = 3 <;> simp only [hw1, hh1, hw2, hh2, hw3, hh3] <;>
    simp (config := { decide := true }) <;>
    (rw [Bool.eq_iff_iff]; simp; (try split_ifs) <;> omega)

@[simp] theorem LV.get_k (n j : ℕ) : (LV.k n).get j = n := rfl
@[simp] theorem LB.get_b (x : Bool) (j : ℕ) : (LB.b x).get j = x := rfl

namespace LB

def xor (N : ℕ) (x y : LB) : LB := or (and x (not N y)) (and (not N x) y)

theorem at_xor {N j : ℕ} (hj : j < N) (x y : LB) : (xor N x y).get j = (x.get j != y.get j) := by
  simp only [xor, at_or, at_and, at_not hj]; cases x.get j <;> cases y.get j <;> rfl

end LB

/-- `accB` on lanes. -/
def accV (N : ℕ) (w h : LV) (s t : LV × LV) : LB :=
  let K := LV.k
  let eq := LV.eq N
  let ps := (LV.add N s.1 s.2).odd
  let pt := (LV.add N t.1 t.2).odd
  let ow := w.odd
  let oh := h.odd
  let cc := LB.ite N (LB.and ow oh) (LB.and (LB.not N ps) (LB.not N pt)) (LB.xor N ps pt)
  let w1 := LV.sub N w (K 1)
  let h1 := LV.sub N h (K 1)
  let corner := fun v : LV × LV =>
    LB.and (LB.or (eq v.1 (K 0)) (eq v.1 w1)) (LB.or (eq v.2 (K 0)) (eq v.2 h1))
  let isW1 := eq w (K 1)
  let fx := LV.ite N isW1 (K 0) w1
  let fy := LV.ite N isW1 h1 (K 0)
  let f1 := LB.not N (LB.or
    (LB.and (LB.and (LB.and (eq s.1 (K 0)) (eq s.2 (K 0))) (eq t.1 fx)) (eq t.2 fy))
    (LB.and (LB.and (LB.and (eq s.1 fx) (eq s.2 fy)) (eq t.1 (K 0))) (eq t.2 (K 0))))
  let f2 := LB.and (LB.and (LB.not N (corner s)) (LB.not N (corner t)))
    (LB.or (LB.and (eq w (K 2)) (eq s.2 t.2)) (LB.and (eq h (K 2)) (eq s.1 t.1)))
  let isW3 := eq w (K 3)
  let oppOdd := LB.ite N isW3 oh ow
  let c0 := LV.ite N isW3 s.2 s.1
  let c1 := LV.ite N isW3 t.2 t.1
  let oc := LV.ite N isW3 s.1 s.2
  let gr := LV.lt N c1 c0
  let dist := LV.ite N gr (LV.sub N c0 c1) (LV.sub N c1 c0)
  let dsat := LB.ite N (eq oc (K 1)) (LV.lt N (K 0) dist) (LV.lt N (K 1) dist)
  let f3 := LB.and (LB.and (LB.and (LB.not N oppOdd) (LB.xor N ps pt)) dsat)
    (LB.or (LB.and gr (LB.not N ps)) (LB.and (LB.not N gr) ps))
  let forb := LB.ite N (LB.or (eq w (K 1)) (eq h (K 1))) f1
    (LB.ite N (LB.or (eq w (K 2)) (eq h (K 2))) f2
      (LB.ite N (LB.or (eq w (K 3)) (eq h (K 3))) f3 (LB.b false)))
  LB.and cc (LB.not N forb)

theorem accV_get {N j : ℕ} (hj : j < N) (w h : LV) (s t : LV × LV) :
    (accV N w h s t).get j = accB (w.get j) (h.get j) (s.1.get j, s.2.get j) (t.1.get j, t.2.get j) := by
  simp only [accV, accB, LB.at_and, LB.at_or, LB.at_not hj, LB.at_ite hj, LB.at_xor hj,
    LV.at_eq hj, LV.at_lt hj, LV.at_ite hj, LV.at_sub hj, LV.at_add hj, LV.at_odd, LV.get_k, LB.get_b]
  rfl

end ZZN.Lane

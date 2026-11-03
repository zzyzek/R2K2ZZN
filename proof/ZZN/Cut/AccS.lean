/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Cut.LaneV

@[expose] public section

/-!
# IPS acceptability on 8-bit lanes

`accS` is `accB` written directly with whole-number operations on lanes in 8-bit fields; lane
Booleans sit in bit `8 j`. With every input lane below 128 (`Sm`), lane `j` of `accS` is `accB` of
lane `j` (`accS_get`). `accV3` uses it when all inputs have the field form and `accV` otherwise; `accV2` uses `accV`
when the width and height are both constants and `accV3` otherwise.
-/

namespace ZZN.Lane

/-- Every lane below 128, nothing above lane `N`. -/
def Sm (N a : ℕ) : Prop := a < Bs ^ N ∧ ∀ j, fld a j < 128

theorem Sm_subS {N a b : ℕ} (ha : Sm N a) (hb : Sm N b) : Sm N (subS N a b) :=
  small_of_chk (chkS_subS ha hb)

theorem Sm_iteS {N c a b : ℕ} (ha : Sm N a) (hb : Sm N b) : Sm N (iteS N c a b) :=
  small_of_chk (chkS_iteS ha hb)

/-- The constant `c` in every lane below `N`. -/
def kS (N c : ℕ) : ℕ := c * oneS N

theorem fld_kS {N c j : ℕ} (hc : c < 128) (hj : j < N) : fld (kS N c) j = c := by
  unfold kS
  rw [mul_comm, fld_mulc j _ _ fun k => by rw [fld_oneS]; split_ifs <;> simp [Bs]; omega, fld_oneS,
    ite_eq_left hj, one_mul]

theorem Sm_kS {N c : ℕ} (hc : c < 128) : Sm N (kS N c) := by
  have hf : ∀ i, fld (kS N c) i = if i < N then c else 0 := by
    intro i; unfold kS
    rw [mul_comm, fld_mulc i _ _ fun k => by rw [fld_oneS]; split_ifs <;> simp [Bs]; omega, fld_oneS]
    split_ifs <;> simp
  refine ⟨?_, fun i => by rw [hf]; split_ifs <;> omega⟩
  unfold kS
  rw [oneS_eq, mul_comm, ofFun_mulc]
  exact ofFun_lt N _ fun _ => by simp [Bs]; omega

/-- Lane-Boolean helpers in bit `8 j`. -/
def notS (N x : ℕ) : ℕ := x ^^^ oneS N

theorem tb_not {N x j : ℕ} (hj : j < N) : (notS N x).testBit (8 * j) = !x.testBit (8 * j) := by
  simp [notS, Nat.testBit_xor, testBit_oneS, hj]

theorem tb_fld (a j : ℕ) : a.testBit (8 * j) = decide (fld a j % 2 = 1) := by
  rw [testBit_fld0, Nat.testBit_zero]

theorem tb_eq {N a b j : ℕ} (hj : j < N) (ha : Sm N a) (hb : Sm N b) :
    (eqB N a b).testBit (8 * j) = decide (fld a j = fld b j) := testBit_eqB ha hb hj

theorem tb_lt {N a b j : ℕ} (hj : j < N) (ha : Sm N a) (hb : Sm N b) :
    (ltB N a b).testBit (8 * j) = decide (fld a j < fld b j) := testBit_ltB ha hb hj

theorem fl_sub {N a b j : ℕ} (ha : Sm N a) (hb : Sm N b) : fld (subS N a b) j = fld a j - fld b j :=
  fld_subS ha hb j

theorem fl_ite {N c a b j : ℕ} (hj : j < N) (ha : Sm N a) (hb : Sm N b) :
    fld (iteS N c a b) j = if c.testBit (8 * j) then fld a j else fld b j := fld_iteS ha.2 hb.2 hj

/-- Smallness side goals. -/
macro "sm_tac" : tactic => `(tactic| first
  | assumption
  | (repeat (first | assumption | apply Sm_subS | apply Sm_iteS | (apply Sm_kS; norm_num))))

/-- Acceptability on lanes. -/
def accS (N W H S1 S2 T1 T2 : ℕ) : ℕ :=
  let o := oneS N
  let z := kS N 0
  let one := kS N 1
  let ps := S1 ^^^ S2
  let pt := T1 ^^^ T2
  let ow := W
  let oh := H
  let cc := ((ow &&& oh) &&& (notS N ps &&& notS N pt)) ||| (notS N (ow &&& oh) &&& (ps ^^^ pt))
  let w1 := subS N W one
  let h1 := subS N H one
  let corner := fun (v1 v2 : ℕ) => (eqB N v1 z ||| eqB N v1 w1) &&& (eqB N v2 z ||| eqB N v2 h1)
  let isW1 := eqB N W one
  let fx := iteS N isW1 z w1
  let fy := iteS N isW1 h1 z
  let f1 := notS N ((eqB N S1 z &&& eqB N S2 z &&& eqB N T1 fx &&& eqB N T2 fy) |||
    (eqB N S1 fx &&& eqB N S2 fy &&& eqB N T1 z &&& eqB N T2 z))
  let f2 := notS N (corner S1 S2) &&& notS N (corner T1 T2) &&&
    ((eqB N W (kS N 2) &&& eqB N S2 T2) ||| (eqB N H (kS N 2) &&& eqB N S1 T1))
  let isW3 := eqB N W (kS N 3)
  let oppOdd := (isW3 &&& oh) ||| (notS N isW3 &&& ow)
  let c0 := iteS N isW3 S2 S1
  let c1 := iteS N isW3 T2 T1
  let oc := iteS N isW3 S1 S2
  let gr := ltB N c1 c0
  let dist := iteS N gr (subS N c0 c1) (subS N c1 c0)
  let e1 := eqB N oc one
  let dsat := (e1 &&& ltB N z dist) ||| (notS N e1 &&& ltB N one dist)
  let f3 := notS N oppOdd &&& (ps ^^^ pt) &&& dsat &&& ((gr &&& notS N ps) ||| (notS N gr &&& ps))
  let c1w := eqB N W one ||| eqB N H one
  let c2w := eqB N W (kS N 2) ||| eqB N H (kS N 2)
  let c3w := eqB N W (kS N 3) ||| eqB N H (kS N 3)
  let forb := (c1w &&& f1) ||| (notS N c1w &&& ((c2w &&& f2) ||| (notS N c2w &&& (c3w &&& f3))))
  (cc &&& notS N forb) &&& o

theorem accS_get {N W H S1 S2 T1 T2 j : ℕ} (hj : j < N) (hW : Sm N W) (hH : Sm N H) (hS1 : Sm N S1)
    (hS2 : Sm N S2) (hT1 : Sm N T1) (hT2 : Sm N T2) :
    (accS N W H S1 S2 T1 T2).testBit (8 * j) =
      accB (fld W j) (fld H j) (fld S1 j, fld S2 j) (fld T1 j, fld T2 j) := by
  have k0 : fld (kS N 0) j = 0 := fld_kS (by norm_num) hj
  have k1 : fld (kS N 1) j = 1 := fld_kS (by norm_num) hj
  have k2 : fld (kS N 2) j = 2 := fld_kS (by norm_num) hj
  have k3 : fld (kS N 3) j = 3 := fld_kS (by norm_num) hj
  have tW := tb_fld W j
  have tH := tb_fld H j
  have tS1 := tb_fld S1 j
  have tS2 := tb_fld S2 j
  have tT1 := tb_fld T1 j
  have tT2 := tb_fld T2 j
  unfold accS
  simp (disch := sm_tac) only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, tb_not hj,
    testBit_oneS, hj, decide_true, Bool.and_true, tb_eq hj, tb_lt hj, fl_sub, fl_ite hj, k0, k1, k2,
    k3, tW, tH, tS1, tS2, tT1, tT2]
  unfold accB
  generalize fld W j = w, fld H j = h, fld S1 j = s1, fld S2 j = s2, fld T1 j = t1, fld T2 j = t2
  have par : ∀ a b : ℕ, decide ((a + b) % 2 = 1) = (decide (a % 2 = 1) ^^ decide (b % 2 = 1)) := by
    intro a b
    rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;> rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
      simp [Nat.add_mod, ha, hb]
  simp only [par]
  by_cases hw1 : w = 1 <;> by_cases hw2 : w = 2 <;> by_cases hw3 : w = 3 <;>
    by_cases hh1 : h = 1 <;> by_cases hh2 : h = 2 <;> by_cases hh3 : h = 3 <;>
    simp only [hw1, hw2, hw3, hh1, hh2, hh3, decide_true, decide_false, Bool.true_or, Bool.or_true,
      Bool.false_or, Bool.or_false, Bool.true_and, Bool.and_true, Bool.false_and, Bool.and_false,
      Bool.not_true, Bool.not_false, ↓reduceIte, Bool.false_eq_true] <;> (try omega) <;>
    (try split_ifs) <;> (try simp_all)
  rcases Nat.mod_two_eq_zero_or_one w with a1 | a1 <;> rcases Nat.mod_two_eq_zero_or_one h with a2 | a2 <;>
    rcases Nat.mod_two_eq_zero_or_one s1 with a3 | a3 <;> rcases Nat.mod_two_eq_zero_or_one s2 with a4 | a4 <;>
    rcases Nat.mod_two_eq_zero_or_one t1 with a5 | a5 <;> rcases Nat.mod_two_eq_zero_or_one t2 with a6 | a6 <;>
    simp_all
/-- Acceptability on lanes: the 8-bit-field computation when every input has that form. -/
def accV3 (N : ℕ) (w h : LV) (s t : LV × LV) : LB :=
  match LV.toS N w, LV.toS N h, LV.toS N s.1, LV.toS N s.2,
    LV.toS N t.1, LV.toS N t.2 with
  | some W, some H, some S1, some S2, some T1, some T2 => LB.g (accS N W H S1 S2 T1 T2)
  | _, _, _, _, _, _ => accV N w h s t

theorem accV3_get {N j : ℕ} (hj : j < N) (w h : LV) (s t : LV × LV) :
    (accV3 N w h s t).get j = accB (w.get j) (h.get j) (s.1.get j, s.2.get j) (t.1.get j, t.2.get j) := by
  unfold accV3
  split
  · rename_i W H S1 S2 T1 T2 e1 e2 e3 e4 e5 e6
    obtain ⟨a1, b1⟩ := LV.toS_spec e1
    obtain ⟨a2, b2⟩ := LV.toS_spec e2
    obtain ⟨a3, b3⟩ := LV.toS_spec e3
    obtain ⟨a4, b4⟩ := LV.toS_spec e4
    obtain ⟨a5, b5⟩ := LV.toS_spec e5
    obtain ⟨a6, b6⟩ := LV.toS_spec e6
    show (accS N W H S1 S2 T1 T2).testBit (8 * j) = _
    rw [accS_get hj a1 a2 a3 a4 a5 a6, b1 j hj, b2 j hj, b3 j hj, b4 j hj, b5 j hj, b6 j hj]
  · exact accV_get hj w h s t

/-- Acceptability on lanes: folding when both sides are constant, the 8-bit-field computation
otherwise. -/
def accV2 (N : ℕ) (w h : LV) (s t : LV × LV) : LB :=
  match w, h with
  | LV.k _, LV.k _ => accV N w h s t
  | _, _ => accV3 N w h s t

theorem accV2_get {N j : ℕ} (hj : j < N) (w h : LV) (s t : LV × LV) :
    (accV2 N w h s t).get j = accB (w.get j) (h.get j) (s.1.get j, s.2.get j) (t.1.get j, t.2.get j) := by
  unfold accV2
  split
  · exact accV_get hj _ _ s t
  · exact accV3_get hj _ _ s t

end ZZN.Lane

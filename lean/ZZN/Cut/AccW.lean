-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Cut.AccS
import ZZN.Cut.CheckF

/-!
# Acceptability with the width and the rows as scalars

In a leaf of a slice check the width of the piece and the rows of both endpoints are the same in
every lane; only the height and the columns vary. `accSW` takes those three as numbers and decides
every test on them once, with `if`, leaving lane operations for the height and the columns only.
Lane `j` of `accSW` is `accB` of lane `j` (`accSW_get`), as for `accS`.
-/

namespace ZZN.Lane

open ZZN.Cut

def accSW (N w H s1 S2 t1 T2 : ℕ) : ℕ :=
  let o := oneS N
  let z := kS N 0
  let one := kS N 1
  let ps := if s1 % 2 = 1 then notS N S2 else S2
  let pt := if t1 % 2 = 1 then notS N T2 else T2
  let cc := if w % 2 = 1 then (H &&& (notS N ps &&& notS N pt)) ||| (notS N H &&& (ps ^^^ pt))
    else ps ^^^ pt
  let h1 := subS N H one
  let hc := fun (v1 v2 : ℕ) => if v1 = 0 ∨ v1 = w - 1 then eqB N v2 z ||| eqB N v2 h1 else 0
  let f1 :=
    if w = 1 then
      notS N ((if s1 = 0 ∧ t1 = 0 then eqB N S2 z &&& eqB N T2 h1 else 0) |||
        (if s1 = 0 ∧ t1 = 0 then eqB N S2 h1 &&& eqB N T2 z else 0))
    else
      notS N ((if s1 = 0 ∧ t1 = w - 1 then eqB N S2 z &&& eqB N T2 z else 0) |||
        (if s1 = w - 1 ∧ t1 = 0 then eqB N S2 z &&& eqB N T2 z else 0))
  let f2 := notS N (hc s1 S2) &&& notS N (hc t1 T2) &&&
    ((if w = 2 then eqB N S2 T2 else 0) ||| (if s1 = t1 then eqB N H (kS N 2) else 0))
  let f3 :=
    if w = 3 then
      let gr := ltB N T2 S2
      let dist := iteS N gr (subS N S2 T2) (subS N T2 S2)
      let dsat := if s1 = 1 then ltB N z dist else ltB N one dist
      notS N H &&& (ps ^^^ pt) &&& dsat &&& ((gr &&& notS N ps) ||| (notS N gr &&& ps))
    else if w % 2 = 1 then 0
    else
      let dist := if t1 < s1 then s1 - t1 else t1 - s1
      let e1 := eqB N S2 one
      let dsat := if 1 < dist then o else if 0 < dist then e1 else 0
      (ps ^^^ pt) &&& dsat &&& (if t1 < s1 then notS N ps else ps)
  let hh1 := eqB N H one
  let hh2 := eqB N H (kS N 2)
  let hh3 := eqB N H (kS N 3)
  let forb :=
    if w = 1 then f1
    else if w = 2 then (hh1 &&& f1) ||| (notS N hh1 &&& f2)
    else if w = 3 then (hh1 &&& f1) ||| (notS N hh1 &&& ((hh2 &&& f2) ||| (notS N hh2 &&& f3)))
    else (hh1 &&& f1) ||| (notS N hh1 &&& ((hh2 &&& f2) ||| (notS N hh2 &&& (hh3 &&& f3))))
  (cc &&& notS N forb) &&& o

private theorem tb_ite (c : Prop) [Decidable c] (a b k : ℕ) :
    (if c then a else b).testBit k = if c then a.testBit k else b.testBit k := by
  split_ifs <;> rfl

/-- `accB` arranged like `accSW`: tests on the width and the rows decided first. -/
def accBW (w h s1 s2 t1 t2 : ℕ) : Bool :=
  let ps := if s1 % 2 = 1 then !decide (s2 % 2 = 1) else decide (s2 % 2 = 1)
  let pt := if t1 % 2 = 1 then !decide (t2 % 2 = 1) else decide (t2 % 2 = 1)
  let oh := decide (h % 2 = 1)
  let cc := if w % 2 = 1 then (oh && (!ps && !pt)) || (!oh && (ps ^^ pt)) else ps ^^ pt
  let hc := fun (v1 v2 : ℕ) => if v1 = 0 ∨ v1 = w - 1 then decide (v2 = 0) || decide (v2 = h - 1) else false
  let f1 :=
    if w = 1 then
      !((if s1 = 0 ∧ t1 = 0 then decide (s2 = 0) && decide (t2 = h - 1) else false) ||
        (if s1 = 0 ∧ t1 = 0 then decide (s2 = h - 1) && decide (t2 = 0) else false))
    else
      !((if s1 = 0 ∧ t1 = w - 1 then decide (s2 = 0) && decide (t2 = 0) else false) ||
        (if s1 = w - 1 ∧ t1 = 0 then decide (s2 = 0) && decide (t2 = 0) else false))
  let f2 := !hc s1 s2 && !hc t1 t2 &&
    ((if w = 2 then decide (s2 = t2) else false) || (if s1 = t1 then decide (h = 2) else false))
  let f3 :=
    if w = 3 then
      let gr := decide (t2 < s2)
      let dist := if gr then s2 - t2 else t2 - s2
      let dsat := if s1 = 1 then decide (0 < dist) else decide (1 < dist)
      !oh && (ps ^^ pt) && dsat && ((gr && !ps) || (!gr && ps))
    else if w % 2 = 1 then false
    else
      let dist := if t1 < s1 then s1 - t1 else t1 - s1
      let e1 := decide (s2 = 1)
      let dsat := if 1 < dist then true else if 0 < dist then e1 else false
      (ps ^^ pt) && dsat && (if t1 < s1 then !ps else ps)
  let hh1 := decide (h = 1)
  let hh2 := decide (h = 2)
  let hh3 := decide (h = 3)
  let forb :=
    if w = 1 then f1
    else if w = 2 then (hh1 && f1) || (!hh1 && f2)
    else if w = 3 then (hh1 && f1) || (!hh1 && ((hh2 && f2) || (!hh2 && f3)))
    else (hh1 && f1) || (!hh1 && ((hh2 && f2) || (!hh2 && (hh3 && f3))))
  cc && !forb

set_option maxHeartbeats 8000000 in
theorem accBW_eq (w h s1 s2 t1 t2 : ℕ) : accBW w h s1 s2 t1 t2 = accB w h (s1, s2) (t1, t2) := by
  have par : ∀ a b : ℕ, decide ((a + b) % 2 = 1) = (decide (a % 2 = 1) ^^ decide (b % 2 = 1)) := by
    intro a b
    rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;> rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
      simp [Nat.add_mod, ha, hb]
  unfold accBW accB
  simp only [par]
  rcases Nat.mod_two_eq_zero_or_one s1 with a3 | a3 <;>
    rcases Nat.mod_two_eq_zero_or_one t1 with a5 | a5 <;>
    simp only [a3, a5] <;>
    rcases (show w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 0 ∨ 4 ≤ w by omega) with hw | hw | hw | hw | hw <;>
    (try subst hw) <;>
    by_cases hh1 : h = 1 <;> by_cases hh2 : h = 2 <;> by_cases hh3 : h = 3 <;>
    simp_all <;> (try split_ifs) <;> (try simp_all) <;>
    (first | omega | ac_rfl | (simp only [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]; done) |
      (rcases Nat.mod_two_eq_zero_or_one s2 with b2 | b2 <;> rcases Nat.mod_two_eq_zero_or_one t2 with b4 | b4 <;>
        by_cases c1 : s1 < t1 <;> by_cases c2 : t1 < s1 <;> by_cases c3 : 1 < t1 - s1 <;>
        simp_all <;> omega))

/-- Lane `j` of `accSW` is `accBW` of lane `j`: the two have the same shape. -/
theorem accSW_getW {N w H s1 S2 t1 T2 j : ℕ} (hj : j < N) (hH : Sm N H) (hS2 : Sm N S2)
    (hT2 : Sm N T2) :
    (accSW N w H s1 S2 t1 T2).testBit (8 * j) = accBW w (fld H j) s1 (fld S2 j) t1 (fld T2 j) := by
  have k0 : fld (kS N 0) j = 0 := fld_kS (by norm_num) hj
  have k1 : fld (kS N 1) j = 1 := fld_kS (by norm_num) hj
  have k2 : fld (kS N 2) j = 2 := fld_kS (by norm_num) hj
  have k3 : fld (kS N 3) j = 3 := fld_kS (by norm_num) hj
  have tH := tb_fld H j
  have tS2 := tb_fld S2 j
  have tT2 := tb_fld T2 j
  unfold accSW accBW
  simp (config := {maxSteps := 4000000}) (disch := sm_tac) only [tb_ite, Nat.testBit_and,
    Nat.testBit_or, Nat.testBit_xor, tb_not hj, testBit_oneS, hj, decide_true, Bool.and_true, tb_eq hj,
    tb_lt hj, fl_sub, fl_ite hj, k0, k1, k2, k3, tH, tS2, tT2, Nat.zero_testBit]

/-- Lane `j` of `accSW` is `accB` of lane `j`. -/
theorem accSW_get {N w H s1 S2 t1 T2 j : ℕ} (hj : j < N) (hH : Sm N H) (hS2 : Sm N S2)
    (hT2 : Sm N T2) :
    (accSW N w H s1 S2 t1 T2).testBit (8 * j) = accB w (fld H j) (s1, fld S2 j) (t1, fld T2 j) := by
  rw [accSW_getW hj hH hS2 hT2, accBW_eq]

end ZZN.Lane

-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.WinSound

/-!
# Soundness of the B, C and D entries from window certificates

The certificates themselves are the finite computation `CertFacts`.
-/

namespace ZZN.Win

open GridHam

/-- The window size of a C/D entry: 6, or 8 when a coordinate is 6 or 7. -/
def winC (AB : List (ℕ × ℕ) × List (ℕ × ℕ)) : ℕ :=
  if (AB.1 ++ AB.2).all (fun x => x.1 < 6 && x.2 < 6) then 6 else 8

/-- The terminal list of a C/D entry, colours as given (`c = false`) or swapped. -/
def tmC (AB : List (ℕ × ℕ) × List (ℕ × ℕ)) (c : Bool) : List ((ℕ × ℕ) × ℕ) :=
  AB.1.map (fun x => (x, if c then 1 else 0)) ++ AB.2.map (fun x => (x, if c then 0 else 1))

/-- The B entry's terminal list: colour `A` at `a1, a2`, the other colour at `b`. -/
def tmB (e : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) (A : ℕ) : List ((ℕ × ℕ) × ℕ) :=
  [(e.1, A), (e.2.1, A), (e.2.2, 1 - A)]

/-- F's sign, as parity forces it. -/
def fsB (e : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) (odd : ℕ) : Int :=
  2 * (odd : Int) - (sgn e.1 + sgn e.2.1 + sgn e.2.2)

/-- **The window certificates** for every B, C and D entry, both colourings, every F case. -/
structure CertFacts : Prop where
  c_even : ∀ AB ∈ CORNER4, ∀ c : Bool, certify (winC AB) (winC AB) (tmC AB c) 0 none = true
  c_odd : ∀ AB ∈ CORNER4_ODD, ∀ c : Bool, certify (winC AB) (winC AB) (tmC AB c) 1 none = true
  b_even : ∀ e ∈ BOUNDARY3_EVEN, ∀ A, A ≤ 1 → ∀ fsl ∈ [none, some 0, some 11],
    (fsB e 0 = 1 ∨ fsB e 0 = -1) → (fsl ≠ none → fsB e 0 = 1) →
      certify 6 6 (tmB e A) 0 (some (1 - A, fsB e 0, fsl)) = true
  b_odd : ∀ e ∈ BOUNDARY3_ODD, ∀ A, A ≤ 1 → ∀ fsl ∈ [none, some 0, some 11],
    (fsB e 1 = 1 ∨ fsB e 1 = -1) → (fsl ≠ none → fsB e 1 = 1) →
      certify 6 6 (tmB e A) 1 (some (1 - A, fsB e 1, fsl)) = true

/-! ### Shapes of the entry lists, checked by `decide` -/

theorem corner_shape : ∀ AB ∈ CORNER4 ++ CORNER4_ODD, AB.1.length = 2 ∧ AB.2.length = 2 ∧
    (AB.1 ++ AB.2).Nodup ∧ (∀ x ∈ AB.1 ++ AB.2, x.1 < winC AB ∧ x.2 < winC AB) ∧
    (winC AB = 6 ∨ winC AB = 8) := by
  decide

theorem boundary_shape : ∀ e ∈ BOUNDARY3_EVEN ++ BOUNDARY3_ODD, [e.1, e.2.1, e.2.2].Nodup ∧
    ∀ x ∈ [e.1, e.2.1, e.2.2], x.1 < 6 ∧ x.2 < 6 := by
  decide

/-! ### C and D -/

theorem sameSet_two {a a' x y : Coord} (ha : a ≠ a') (_hxy : x ≠ y) (h : sameSet [a, a'] [x, y] = true) :
    (a = x ∧ a' = y) ∨ (a = y ∧ a' = x) := by
  unfold sameSet at h
  simp only [List.length_cons, List.length_nil, beq_self_eq_true, List.all_cons, List.all_nil,
    Bool.and_true, Bool.true_and, Bool.and_eq_true, List.contains_cons, List.contains_nil, Bool.or_false,
    Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨h1 | h1, h2 | h2⟩ := h
  · exact absurd (h1.trans h2.symm) ha
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) ha

theorem termAt_four {a a' b b' y : Coord} {c0 c1 : ℕ} :
    termAt [(a, c0), (a', c0), (b, c1), (b', c1)] y =
      if y = a ∨ y = a' then some c0 else if y = b ∨ y = b' then some c1 else none := by
  unfold termAt
  by_cases h1 : a = y
  · simp [h1]
  · by_cases h2 : a' = y
    · simp [h1, h2]
    · by_cases h3 : b = y
      · simp [h1, h2, h3, Ne.symm h1, Ne.symm h2]
      · by_cases h4 : b' = y
        · simp [h1, h2, h3, h4, Ne.symm h1, Ne.symm h2, Ne.symm h3]
        · simp [h1, h2, h3, h4, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4]

theorem ite_swap {P Q : Prop} [Decidable P] [Decidable Q] (h : ¬ (P ∧ Q)) (u v w : Option ℕ) :
    (if P then u else if Q then v else w) = (if Q then v else if P then u else w) := by
  by_cases hp : P <;> by_cases hq : Q <;> simp_all

/-- The C/D window setup, once the entry's pairs match the endpoints. -/
theorem cd_sound (_CF : CertFacts) {J : Inst} (hwf : J.WellFormed) (hS : Solvable J) (hw : 11 ≤ J.w)
    (hh : 11 ≤ J.h) {AB : List (ℕ × ℕ) × List (ℕ × ℕ)} (hAB : AB ∈ CORNER4 ++ CORNER4_ODD)
    (hcert : ∀ c : Bool, certify (winC AB) (winC AB) (tmC AB c) ((J.w * J.h) % 2) none = true)
    {c : Bool} (hm : sameSet AB.1 (if c then [J.s1, J.t1] else [J.s0, J.t0]) = true ∧
      sameSet AB.2 (if c then [J.s0, J.t0] else [J.s1, J.t1]) = true) : False := by
  obtain ⟨p, q, sol⟩ := hS
  obtain ⟨l1, l2, nd, inw, wk⟩ := corner_shape AB hAB
  obtain ⟨a, a', e1⟩ := List.length_eq_two.mp l1
  obtain ⟨b, b', e2⟩ := List.length_eq_two.mp l2
  obtain ⟨A, B⟩ := AB
  simp only at e1 e2; subst e1; subst e2
  simp only [List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at nd
  obtain ⟨⟨n1, n2, n3⟩, ⟨n4, n5⟩, n6, -⟩ := nd
  obtain ⟨b0, b1, b2, b3, w1, w2, w3, w4, w5, w6⟩ := hwf
  set k := winC ([a, a'], [b, b'])
  have inW : ∀ x, (x = a ∨ x = a' ∨ x = b ∨ x = b') → x.1 < k ∧ x.2 < k := fun x hx => inw x (by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]; exact hx)
  -- the endpoints are the entry's cells
  have m1 : ∀ {x y : Coord}, x ≠ y → sameSet [a, a'] [x, y] = true → (a = x ∧ a' = y) ∨ (a = y ∧ a' = x) :=
    fun hxy h => sameSet_two n1 hxy h
  have m2 : ∀ {x y : Coord}, x ≠ y → sameSet [b, b'] [x, y] = true → (b = x ∧ b' = y) ∨ (b = y ∧ b' = x) :=
    fun hxy h => sameSet_two n6 hxy h
  have setup : WinSetup k J p q none := by
    refine ⟨by rcases wk with h | h <;> omega, by rcases wk with h | h <;> omega,
      by rcases wk with h | h <;> rw [h], by rcases wk with h | h <;> omega, by rcases wk with h | h <;> omega,
      sol, ⟨b0, b1, b2, b3, w1, w2, w3, w4, w5, w6⟩, Or.inl ⟨rfl, ?_⟩⟩
    intro E hE
    apply inW
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte] at hm
      rcases m1 w1 hm.1 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases m2 w6 hm.2 with ⟨e3, e4⟩ | ⟨e3, e4⟩ <;>
        rcases hE with rfl | rfl | rfl | rfl <;> simp_all
    · simp only [↓reduceIte] at hm
      rcases m1 w6 hm.1 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases m2 w1 hm.2 with ⟨e3, e4⟩ | ⟨e3, e4⟩ <;>
        rcases hE with rfl | rfl | rfl | rfl <;> simp_all
  apply window_sound setup (tm := tmC ([a, a'], [b, b']) c) _ (hcert c)
  intro y _ _
  unfold tmC endCol
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  rw [termAt_four]
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte] at hm ⊢
    rcases m1 w1 hm.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases m2 w6 hm.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [or_comm]
  · simp only [↓reduceIte] at hm ⊢
    have dis : ¬ ((y = J.s1 ∨ y = J.t1) ∧ (y = J.s0 ∨ y = J.t0)) := by
      rintro ⟨h1 | h1, h2 | h2⟩ <;> rw [h1] at h2
      · exact w2 h2.symm
      · exact w4 h2.symm
      · exact w3 h2.symm
      · exact w5 h2.symm
    rw [ite_swap (P := y = J.s0 ∨ y = J.t0) (Q := y = J.s1 ∨ y = J.t1) (fun h => dis ⟨h.2, h.1⟩)]
    rcases m1 w6 hm.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases m2 w1 hm.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [or_comm]

/-- **C and D are sound**, given the certificates. -/
theorem cSound_of (CF : CertFacts) : ∀ J : Inst, J.WellFormed → Solvable J → 11 ≤ J.w → 11 ≤ J.h →
    corner4 J.w J.h idF (ptsOf J) = false := by
  intro J hwf hS hw hh
  by_contra hf
  rw [Bool.not_eq_false] at hf
  unfold corner4 at hf
  simp only [ptsOf, List.filter_cons, List.filter_nil, beq_self_eq_true, ↓reduceIte, List.map_cons,
    idF_to] at hf
  have e01 : ((1 : ℕ) == 0) = false := rfl
  have e10 : ((0 : ℕ) == 1) = false := rfl
  simp only [e01, e10, Bool.false_eq_true, ↓reduceIte] at hf
  split_ifs at hf with hpar
  · obtain ⟨AB, hAB, h⟩ := List.any_eq_true.mp hf
    have hp : (J.w * J.h) % 2 = 0 := by simpa using hpar
    have hcert : ∀ c : Bool, certify (winC AB) (winC AB) (tmC AB c) ((J.w * J.h) % 2) none = true := by
      intro c; rw [hp]; exact CF.c_even AB hAB c
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | h
    · exact cd_sound CF hwf hS hw hh (List.mem_append_left _ hAB) hcert (c := false) (by simpa using h)
    · exact cd_sound CF hwf hS hw hh (List.mem_append_left _ hAB) hcert (c := true) (by simpa using h)
  · obtain ⟨AB, hAB, h⟩ := List.any_eq_true.mp hf
    have hp : (J.w * J.h) % 2 = 1 := by simp at hpar; omega
    have hcert : ∀ c : Bool, certify (winC AB) (winC AB) (tmC AB c) ((J.w * J.h) % 2) none = true := by
      intro c; rw [hp]; exact CF.c_odd AB hAB c
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | h
    · exact cd_sound CF hwf hS hw hh (List.mem_append_right _ hAB) hcert (c := false) (by simpa using h)
    · exact cd_sound CF hwf hS hw hh (List.mem_append_right _ hAB) hcert (c := true) (by simpa using h)

/-! ### B -/

/-- F's exit slot, if F is an exit cell of the 6 × 6 window on the perimeter. -/
def fslOf (E : Coord) : Option ℕ := if E = (0, 6) then some 0 else if E = (6, 0) then some 11 else none

theorem fslOf_spec {J : Inst} (hw : 11 ≤ J.w) (hh : 11 ≤ J.h) {E : Coord} (hE1 : E.1 < J.w) (hE2 : E.2 < J.h)
    (hout : ¬ (E.1 < 6 ∧ E.2 < 6)) (hp : E.1 = 0 ∨ E.2 = 0 ∨ E.1 = J.w - 1 ∨ E.2 = J.h - 1) :
    ∀ sl, fslOf E = some sl ↔ sl < 2 * 6 ∧ exitCell 6 6 sl = E := by
  intro sl
  obtain ⟨e1, e2⟩ := E
  simp only at hE1 hE2 hout hp
  unfold fslOf
  by_cases g1 : ((e1, e2) : Coord) = (0, 6)
  · rw [ite_eq_left g1]; simp only [Prod.mk.injEq] at g1; obtain ⟨rfl, rfl⟩ := g1
    constructor
    · intro h; simp only [Option.some.injEq] at h; subst h; simp [exitCell]
    · rintro ⟨h1, h2⟩; unfold exitCell at h2
      split_ifs at h2 <;> simp only [Prod.mk.injEq] at h2 <;> simp only [Option.some.injEq] <;> omega
  · rw [ite_eq_right g1]
    by_cases g2 : ((e1, e2) : Coord) = (6, 0)
    · rw [ite_eq_left g2]; simp only [Prod.mk.injEq] at g2; obtain ⟨rfl, rfl⟩ := g2
      constructor
      · intro h; simp only [Option.some.injEq] at h; subst h; simp [exitCell]
      · rintro ⟨h1, h2⟩; unfold exitCell at h2
        split_ifs at h2 <;> simp only [Prod.mk.injEq] at h2 <;> simp only [Option.some.injEq] <;> omega
    · rw [ite_eq_right g2]
      constructor
      · intro h; simp at h
      · rintro ⟨h1, h2⟩; exfalso; unfold exitCell at h2
        simp only [Prod.mk.injEq] at g1 g2
        split_ifs at h2 <;> simp only [Prod.mk.injEq] at h2 <;> omega

theorem fslOf_sign {E : Coord} (h : fslOf E ≠ none) : sgn E = 1 := by
  unfold fslOf at h
  by_cases g1 : E = (0, 6)
  · subst g1; rfl
  · by_cases g2 : E = (6, 0)
    · subst g2; rfl
    · rw [ite_eq_right g1, ite_eq_right g2] at h; exact absurd rfl h

theorem termAt_three {a a' b y : Coord} {c0 c1 : ℕ} :
    termAt [(a, c0), (a', c0), (b, c1)] y = if y = a ∨ y = a' then some c0 else if y = b then some c1 else none := by
  unfold termAt
  by_cases h1 : a = y
  · simp [h1]
  · by_cases h2 : a' = y
    · simp [h1, h2]
    · by_cases h3 : b = y
      · simp [h1, h2, h3, Ne.symm h1, Ne.symm h2]
      · simp [h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3]

theorem endB0 {s0 t0 s1 t1 b E y : Coord} (hb : (b = s1 ∧ E = t1) ∨ (b = t1 ∧ E = s1)) (hyE : y ≠ E) :
    (if y = s0 ∨ y = t0 then some 0 else if y = b then some 1 else none) =
      (if y = s0 ∨ y = t0 then (some 0 : Option ℕ) else if y = s1 ∨ y = t1 then some 1 else none) := by
  congr 1
  apply if_congr _ rfl rfl
  rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨Or.inl, fun h => h.resolve_right hyE⟩
  · exact ⟨Or.inr, fun h => h.resolve_left hyE⟩

theorem endB1 {s0 t0 s1 t1 b E y : Coord} (hb : (b = s0 ∧ E = t0) ∨ (b = t0 ∧ E = s0)) (hyE : y ≠ E)
    (hd : ¬ ((y = s1 ∨ y = t1) ∧ (y = s0 ∨ y = t0))) :
    (if y = s1 ∨ y = t1 then some 1 else if y = b then some 0 else none) =
      (if y = s0 ∨ y = t0 then (some 0 : Option ℕ) else if y = s1 ∨ y = t1 then some 1 else none) := by
  rw [ite_swap (P := y = s0 ∨ y = t0) (Q := y = s1 ∨ y = t1) (fun h => hd ⟨h.2, h.1⟩)]
  congr 1
  apply if_congr _ rfl rfl
  rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨Or.inl, fun h => h.resolve_right hyE⟩
  · exact ⟨Or.inr, fun h => h.resolve_left hyE⟩

set_option maxHeartbeats 1000000 in
/-- **The B window setup**, once the entry's cells are identified with the endpoints: colour 0 at
`a1, a2` and colour 1 at `b` and F (the other colouring by symmetry of the statement). -/
theorem b_core {J : Inst} (hwf : J.WellFormed) (hS : Solvable J) (hw : 11 ≤ J.w) (hh : 11 ≤ J.h)
    {e : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)} (he : e ∈ BOUNDARY3_EVEN ++ BOUNDARY3_ODD) {A : ℕ} (hA : A ≤ 1)
    {E : Coord} (hid : (A = 0 ∧ ((e.1 = J.s0 ∧ e.2.1 = J.t0) ∨ (e.1 = J.t0 ∧ e.2.1 = J.s0)) ∧
        ((e.2.2 = J.s1 ∧ E = J.t1) ∨ (e.2.2 = J.t1 ∧ E = J.s1))) ∨
      (A = 1 ∧ ((e.1 = J.s1 ∧ e.2.1 = J.t1) ∨ (e.1 = J.t1 ∧ e.2.1 = J.s1)) ∧
        ((e.2.2 = J.s0 ∧ E = J.t0) ∨ (e.2.2 = J.t0 ∧ E = J.s0))))
    (hout : ¬ (E.1 < 6 ∧ E.2 < 6)) (hp : E.1 = 0 ∨ E.2 = 0 ∨ E.1 = J.w - 1 ∨ E.2 = J.h - 1)
    (hcert : certify 6 6 (tmB e A) ((J.w * J.h) % 2) (some (1 - A, fsB e ((J.w * J.h) % 2), fslOf E)) = true) :
    False := by
  have hpar := parity_of_solvable hS
  obtain ⟨p, q, sol⟩ := hS
  obtain ⟨nd, inw⟩ := boundary_shape e he
  obtain ⟨a1, a2, b⟩ := e
  simp only at hid nd inw hcert ⊢
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at nd
  obtain ⟨⟨n1, n2⟩, n3, -⟩ := nd
  obtain ⟨b0, b1, b2, b3, w1, w2, w3, w4, w5, w6⟩ := hwf
  have iw : ∀ x, (x = a1 ∨ x = a2 ∨ x = b) → x.1 < 6 ∧ x.2 < 6 := fun x hx => inw x (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact hx)
  -- F's sign, from parity
  have hs : fsB (a1, a2, b) ((J.w * J.h) % 2) = sgn E := by
    unfold fsB
    simp only [sgnW_eq]
    rcases hid with ⟨rfl, h1 | h1, h2 | h2⟩ | ⟨rfl, h1 | h1, h2 | h2⟩ <;>
      obtain ⟨rfl, rfl⟩ := h1 <;> obtain ⟨rfl, rfl⟩ := h2 <;> linarith
  have hEg : E.1 < J.w ∧ E.2 < J.h := by
    rcases hid with ⟨-, -, h2 | h2⟩ | ⟨-, -, h2 | h2⟩ <;> rw [h2.2]
    · exact b3
    · exact b2
    · exact b1
    · exact b0
  have setup : WinSetup 6 J p q (some (1 - A, fsB (a1, a2, b) ((J.w * J.h) % 2), fslOf E)) := by
    refine ⟨by omega, by omega, rfl, by omega, by omega, sol, ⟨b0, b1, b2, b3, w1, w2, w3, w4, w5, w6⟩,
      Or.inr ⟨E, 1 - A, _, _, rfl, ?_, hout, ?_, fun E' hE' ne => ?_, hp, hs, fslOf_spec hw hh hEg.1 hEg.2 hout hp⟩⟩
    · rcases hid with ⟨-, -, h2 | h2⟩ | ⟨-, -, h2 | h2⟩ <;> rw [h2.2] <;> unfold IsEnd <;> simp
    · rcases hid with ⟨rfl, -, h2 | h2⟩ | ⟨rfl, -, h2 | h2⟩
      · exact Or.inr ⟨rfl, Or.inr h2.2⟩
      · exact Or.inr ⟨rfl, Or.inl h2.2⟩
      · exact Or.inl ⟨rfl, Or.inr h2.2⟩
      · exact Or.inl ⟨rfl, Or.inl h2.2⟩
    · apply iw
      rcases hid with ⟨-, h1 | h1, h2 | h2⟩ | ⟨-, h1 | h1, h2 | h2⟩ <;>
        obtain ⟨rfl, rfl⟩ := h1 <;> obtain ⟨rfl, rfl⟩ := h2 <;>
        rcases hE' with rfl | rfl | rfl | rfl <;>
        first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact absurd rfl ne
  apply window_sound setup (tm := tmB (a1, a2, b) A) _ hcert
  intro y hy1 hy2
  have yE : y ≠ E := fun h => hout (h ▸ ⟨hy1, hy2⟩)
  unfold tmB endCol
  simp only
  rw [termAt_three]
  have hd : ¬ ((y = J.s1 ∨ y = J.t1) ∧ (y = J.s0 ∨ y = J.t0)) := by
    rintro ⟨h1 | h1, h2 | h2⟩ <;> rw [h1] at h2
    · exact w2 h2.symm
    · exact w4 h2.symm
    · exact w3 h2.symm
    · exact w5 h2.symm
  rcases hid with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩
  · have e1 : (y = a1 ∨ y = a2) ↔ (y = J.s0 ∨ y = J.t0) := by
      rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Iff.rfl
      · exact or_comm
    rw [if_congr e1 rfl rfl]
    exact endB0 h2 yE
  · have e1 : (y = a1 ∨ y = a2) ↔ (y = J.s1 ∨ y = J.t1) := by
      rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Iff.rfl
      · exact or_comm
    rw [if_congr e1 rfl rfl]
    exact endB1 h2 yE hd

/-! ### Evaluating `boundaryOnly` on the endpoints -/

theorem beq_dec {x y : Coord} : (x == y) = decide (x = y) := by
  by_cases h : x = y <;> simp [h]

theorem bne_dec {x y : Coord} : (x != y) = !decide (x = y) := by
  by_cases h : x = y <;> simp [h]

section Eval

variable (s0 t0 s1 t1 : Coord)

theorem find_col1 (b : Coord) :
    [(s0, 0), (t0, 0), (s1, 1), (t1, 1)].find? (fun q : Coord × ℕ => q.2 == 1 && q.1 == b) =
      if s1 = b then some (s1, 1) else if t1 = b then some (t1, 1) else none := by
  by_cases h1 : s1 = b <;> by_cases h2 : t1 = b <;> simp [List.find?, beq_dec, h1, h2]

theorem find_col0 (b : Coord) :
    [(s0, 0), (t0, 0), (s1, 1), (t1, 1)].find? (fun q : Coord × ℕ => q.2 == 0 && q.1 == b) =
      if s0 = b then some (s0, 0) else if t0 = b then some (t0, 0) else none := by
  by_cases h1 : s0 = b <;> by_cases h2 : t0 = b <;> simp [List.find?, beq_dec, h1, h2]

theorem find_other1 (b : Coord) :
    [(s0, 0), (t0, 0), (s1, 1), (t1, 1)].find? (fun q : Coord × ℕ => q.2 == 1 && q.1 != b) =
      if s1 ≠ b then some (s1, 1) else if t1 ≠ b then some (t1, 1) else none := by
  by_cases h1 : s1 = b <;> by_cases h2 : t1 = b <;> simp [List.find?, bne_dec, h1, h2]

theorem find_other0 (b : Coord) :
    [(s0, 0), (t0, 0), (s1, 1), (t1, 1)].find? (fun q : Coord × ℕ => q.2 == 0 && q.1 != b) =
      if s0 ≠ b then some (s0, 0) else if t0 ≠ b then some (t0, 0) else none := by
  by_cases h1 : s0 = b <;> by_cases h2 : t0 = b <;> simp [List.find?, bne_dec, h1, h2]

theorem any_col (c : ℕ) (hc : c ≤ 1) (a : Coord) :
    [(s0, 0), (t0, 0), (s1, 1), (t1, 1)].any (fun q : Coord × ℕ => q.2 == c && q.1 == a) = true ↔
      (c = 0 ∧ (s0 = a ∨ t0 = a)) ∨ (c = 1 ∧ (s1 = a ∨ t1 = a)) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl <;> simp

end Eval

/-! ### B is sound -/

theorem fsB_sgn {J : Inst} (hS : Solvable J) {e : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)} {A : ℕ} {E : Coord}
    (hid : (A = 0 ∧ ((e.1 = J.s0 ∧ e.2.1 = J.t0) ∨ (e.1 = J.t0 ∧ e.2.1 = J.s0)) ∧
        ((e.2.2 = J.s1 ∧ E = J.t1) ∨ (e.2.2 = J.t1 ∧ E = J.s1))) ∨
      (A = 1 ∧ ((e.1 = J.s1 ∧ e.2.1 = J.t1) ∨ (e.1 = J.t1 ∧ e.2.1 = J.s1)) ∧
        ((e.2.2 = J.s0 ∧ E = J.t0) ∨ (e.2.2 = J.t0 ∧ E = J.s0)))) :
    fsB e ((J.w * J.h) % 2) = sgn E := by
  have hpar := parity_of_solvable hS
  obtain ⟨a1, a2, b⟩ := e
  unfold fsB
  simp only [sgnW_eq]
  simp only at hid
  rcases hid with ⟨-, h1 | h1, h2 | h2⟩ | ⟨-, h1 | h1, h2 | h2⟩ <;>
    obtain ⟨rfl, rfl⟩ := h1 <;> obtain ⟨rfl, rfl⟩ := h2 <;> linarith

theorem sgn_pm (x : Coord) : sgn x = 1 ∨ sgn x = -1 := by unfold sgn; split_ifs <;> simp

theorem fslOf_mem (E : Coord) : fslOf E ∈ [none, some 0, some 11] := by
  unfold fslOf; split_ifs <;> simp

/-- The certificate for a B match, from `CertFacts`. -/
theorem b_cert (CF : CertFacts) {J : Inst} (hS : Solvable J) {e : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)} {A : ℕ}
    (hA : A ≤ 1) {E : Coord}
    (hid : (A = 0 ∧ ((e.1 = J.s0 ∧ e.2.1 = J.t0) ∨ (e.1 = J.t0 ∧ e.2.1 = J.s0)) ∧
        ((e.2.2 = J.s1 ∧ E = J.t1) ∨ (e.2.2 = J.t1 ∧ E = J.s1))) ∨
      (A = 1 ∧ ((e.1 = J.s1 ∧ e.2.1 = J.t1) ∨ (e.1 = J.t1 ∧ e.2.1 = J.s1)) ∧
        ((e.2.2 = J.s0 ∧ E = J.t0) ∨ (e.2.2 = J.t0 ∧ E = J.s0))))
    (he : e ∈ if (J.w % 2 == 1 && J.h % 2 == 1) = true then BOUNDARY3_ODD else BOUNDARY3_EVEN) :
    certify 6 6 (tmB e A) ((J.w * J.h) % 2) (some (1 - A, fsB e ((J.w * J.h) % 2), fslOf E)) = true := by
  have hs := fsB_sgn hS hid
  have pm : fsB e ((J.w * J.h) % 2) = 1 ∨ fsB e ((J.w * J.h) % 2) = -1 := by rw [hs]; exact sgn_pm E
  have one : fslOf E ≠ none → fsB e ((J.w * J.h) % 2) = 1 := fun h => by rw [hs]; exact fslOf_sign h
  split_ifs at he with hc
  · have hodd : (J.w * J.h) % 2 = 1 := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hc; rw [Nat.mul_mod, hc.1, hc.2]
    rw [hodd] at pm one ⊢
    exact CF.b_odd e he A hA (fslOf E) (fslOf_mem E) pm one
  · have hev : (J.w * J.h) % 2 = 0 := by
      simp only [Bool.and_eq_true, beq_iff_eq, not_and] at hc
      rcases Nat.mod_two_eq_zero_or_one J.w with h1 | h1
      · rw [Nat.mul_mod, h1]; simp
      · rcases Nat.mod_two_eq_zero_or_one J.h with h2 | h2
        · rw [Nat.mul_mod, h2]; simp
        · exact absurd h2 (hc h1)
    rw [hev] at pm one ⊢
    exact CF.b_even e he A hA (fslOf E) (fslOf_mem E) pm one

/-- **B is sound**, given the certificates. -/
theorem bSound_of (CF : CertFacts) : ∀ J : Inst, J.WellFormed → Solvable J → 11 ≤ J.w → 11 ≤ J.h →
    boundaryOnly J.w J.h idF (ptsOf J) = false := by
  intro J hwf hS hw hh
  by_contra hf
  rw [Bool.not_eq_false] at hf
  unfold boundaryOnly at hf
  have hmap : List.map (fun q : Pt => (Frame.to J.w J.h ⟨false, false, false⟩ q.1, q.2))
      [(J.s0, 0), (J.t0, 0), (J.s1, 1), (J.t1, 1)] = [(J.s0, 0), (J.t0, 0), (J.s1, 1), (J.t1, 1)] := by
    simp [Frame.to]
  simp only [idF, Frame.H, Frame.W, Bool.false_eq_true, ↓reduceIte, ptsOf, List.any_eq_true, hmap] at hf
  obtain ⟨e, he, x, hx, h⟩ := hf
  have heAll : e ∈ BOUNDARY3_EVEN ++ BOUNDARY3_ODD := by
    split_ifs at he
    · exact List.mem_append_right _ he
    · exact List.mem_append_left _ he
  obtain ⟨nd, -⟩ := boundary_shape e heAll
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at nd
  obtain ⟨⟨n1, -⟩, -, -⟩ := nd
  obtain ⟨b0, b1, b2, b3, w1, w2, w3, w4, w5, w6⟩ := hwf
  -- the colour-`c` endpoints at `a1, a2`
  have pair : ∀ {x y : Coord}, x ≠ y → (x = e.1 ∨ y = e.1) → (x = e.2.1 ∨ y = e.2.1) →
      (e.1 = x ∧ e.2.1 = y) ∨ (e.1 = y ∧ e.2.1 = x) := by
    intro x y hxy h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.symm.trans h2) n1
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h1.symm, h2.symm⟩
    · exact absurd (h1.symm.trans h2) n1
  have fin := fun {A : ℕ} (hA : A ≤ 1) {E : Coord} hid (hout : ¬ (E.1 < 6 ∧ E.2 < 6))
      (hp : E.1 = 0 ∨ E.2 = 0 ∨ E.1 = J.w - 1 ∨ E.2 = J.h - 1) =>
    b_core ⟨b0, b1, b2, b3, w1, w2, w3, w4, w5, w6⟩ hS hw hh heAll hA (E := E) hid hout hp
      (b_cert CF hS hA hid he)
  have outOf : ∀ {E : Coord}, (!(decide (E.1 < 6) && decide (E.2 < 6))) = true → ¬ (E.1 < 6 ∧ E.2 < 6) := by
    intro E h c; simp [c.1, c.2] at h
  have perOf : ∀ {E : Coord}, (E.1 == 0 || E.2 == 0 || E.1 == J.w - 1 || E.2 == J.h - 1) = true →
      E.1 = 0 ∨ E.2 = 0 ∨ E.1 = J.w - 1 ∨ E.2 = J.h - 1 := by
    intro E h; simp only [Bool.or_eq_true, beq_iff_eq] at h; tauto
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · -- colour 0 at a1, a2
    rw [show (1 : ℕ) - 0 = 1 from rfl, find_col1, find_other1] at h
    have c0 : ∀ {z : Coord}, ([(J.s0, 0), (J.t0, 0), (J.s1, 1), (J.t1, 1)].any
        (fun q : Coord × ℕ => q.2 == 0 && q.1 == z)) = true → (J.s0 = z ∨ J.t0 = z) := by
      intro z hz; rcases (any_col J.s0 J.t0 J.s1 J.t1 0 (by omega) z).mp hz with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · omega
    by_cases hb1 : J.s1 = e.2.2
    · have ht : J.t1 ≠ e.2.2 := fun c => w6 (hb1.trans c.symm)
      rw [ite_eq_left hb1, ite_eq_right (not_not.mpr hb1), ite_eq_left ht] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨ha1, ha2⟩, hper, hnw⟩ := h
      exact fin (by omega) (E := J.t1) (Or.inl ⟨rfl, pair w1 (c0 ha1) (c0 ha2), Or.inl ⟨hb1.symm, rfl⟩⟩)
        (outOf hnw) (perOf hper)
    · by_cases hb2 : J.t1 = e.2.2
      · rw [ite_eq_right hb1, ite_eq_left hb2, ite_eq_left hb1] at h
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨ha1, ha2⟩, hper, hnw⟩ := h
        exact fin (by omega) (E := J.s1) (Or.inl ⟨rfl, pair w1 (c0 ha1) (c0 ha2), Or.inr ⟨hb2.symm, rfl⟩⟩)
          (outOf hnw) (perOf hper)
      · rw [ite_eq_right hb1, ite_eq_right hb2] at h; simp at h
  · -- colour 1 at a1, a2
    rw [show (1 : ℕ) - 1 = 0 from rfl, find_col0, find_other0] at h
    have c1 : ∀ {z : Coord}, ([(J.s0, 0), (J.t0, 0), (J.s1, 1), (J.t1, 1)].any
        (fun q : Coord × ℕ => q.2 == 1 && q.1 == z)) = true → (J.s1 = z ∨ J.t1 = z) := by
      intro z hz; rcases (any_col J.s0 J.t0 J.s1 J.t1 1 (by omega) z).mp hz with ⟨h, -⟩ | ⟨-, h⟩
      · omega
      · exact h
    by_cases hb1 : J.s0 = e.2.2
    · have ht : J.t0 ≠ e.2.2 := fun c => w1 (hb1.trans c.symm)
      rw [ite_eq_left hb1, ite_eq_right (not_not.mpr hb1), ite_eq_left ht] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨ha1, ha2⟩, hper, hnw⟩ := h
      exact fin (by omega) (E := J.t0) (Or.inr ⟨rfl, pair w6 (c1 ha1) (c1 ha2), Or.inl ⟨hb1.symm, rfl⟩⟩)
        (outOf hnw) (perOf hper)
    · by_cases hb2 : J.t0 = e.2.2
      · rw [ite_eq_right hb1, ite_eq_left hb2, ite_eq_left hb1] at h
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨ha1, ha2⟩, hper, hnw⟩ := h
        exact fin (by omega) (E := J.s0) (Or.inr ⟨rfl, pair w6 (c1 ha1) (c1 ha2), Or.inr ⟨hb2.symm, rfl⟩⟩)
          (outOf hnw) (perOf hper)
      · rw [ite_eq_right hb1, ite_eq_right hb2] at h; simp at h

/-! ### Theorem B from the certificates -/

theorem bFacts_of (CF : CertFacts) : BFacts := ⟨bSound_of CF, cSound_of CF⟩

/-- **Theorem B**, given only the window certificates (a finite computation). -/
theorem theoremB_cert (CF : CertFacts) {I : Inst} (hI : InDom I) (hS : Solvable I) : Passes I :=
  theoremB_R (bFacts_of CF) hI hS

end ZZN.Win

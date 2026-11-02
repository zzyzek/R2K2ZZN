/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.BoxK.Slice

@[expose] public section

/-!
# Firing lanes with a witness entry

A lane fails `passImgB` when the catalogue fires on all four reflections. `fires3` evaluates the
entries in order and stops at the first that fires, so a lane whose firing entry comes late pays
for every entry before it. A witness names, for each reflection, one entry that fires (`fireW`):
the parity test, T1, T2, L1, L6, one of the eight frames, or the outer-walk test. Only that entry
is evaluated.
-/

namespace ZZN.BoxK

open ZZN GridHam

/-- Entry `k` of the catalogue: 0 parity, 1 T1, 2 T2, 3 L1, 4 L6, 5–12 frame `k - 5`, 13 the
outer walk; any other code never fires. -/
def fireW (R C : ℕ) (s0 t0 s1 t1 : ℕ × ℕ) (k : ℕ) : Bool :=
  let pts : List Pt := [(s0, 0), (t0, 0), (s1, 1), (t1, 1)]
  match k with
  | 0 => !parityOk R C pts
  | 1 => t1Fires R C pts
  | 2 => t2Fires [s0, t0, s1, t1]
  | 3 => l1Fires R C pts
  | 4 => l6Fires R C pts
  | 13 => effAlt3 R C pts
  | k => decide (5 ≤ k ∧ k < 13) && frameFires R C pts (frames.getD (k - 5) ⟨false, false, false⟩)

theorem fireW_sound {R C : ℕ} {s0 t0 s1 t1 : ℕ × ℕ} {k : ℕ} (h : fireW R C s0 t0 s1 t1 k = true) :
    fires3 R C s0 t0 s1 t1 = true := by
  unfold fires3
  unfold fireW at h
  split at h <;> simp only [h, Bool.true_or, Bool.or_true]
  rename_i h1 h2 h3 h4 h5 h6
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hk1, hk2⟩, hf⟩ := h
  have hmem : frames.getD (k - 5) ⟨false, false, false⟩ ∈ frames := by
    rw [List.getD_eq_getElem _ _ (by simp [frames]; omega)]
    exact List.getElem_mem _
  have : frames.any (frameFires R C [(s0, 0), (t0, 0), (s1, 1), (t1, 1)]) = true :=
    List.any_eq_true.mpr ⟨_, hmem, hf⟩
  simp only [this, Bool.true_or, Bool.or_true]

def fireI (J : Inst) (k : ℕ) : Bool := fireW J.w J.h J.s0 J.t0 J.s1 J.t1 k

/-- All four reflections fire, with witnesses packed in base 16: `c % 16` for `J`, then
`J.reflectX`, `J.reflectY`, `J.reflectX.reflectY`. -/
def failW (J : Inst) (c : ℕ) : Bool :=
  fireI J (c % 16) && fireI J.reflectX (c / 16 % 16) && fireI J.reflectY (c / 256 % 16) &&
    fireI J.reflectX.reflectY (c / 4096 % 16)

theorem not_passes_of_fireI {J : Inst} {k : ℕ} (h : fireI J k = true) : decide (Passes J) = false := by
  have := fireW_sound h
  simp only [Passes, decide_eq_false_iff_not]
  intro hp
  rw [hp] at this
  exact Bool.false_ne_true this

theorem failW_sound {J : Inst} {c : ℕ} (h : failW J c = true) : passImgB J = false := by
  simp only [failW, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  simp only [passImgB, not_passes_of_fireI h0, not_passes_of_fireI h1, not_passes_of_fireI h2,
    not_passes_of_fireI h3, Bool.or_self]

/-- Firing lanes with witnesses: `(lane, codes)`. -/
def firesW (N w h : ℕ) (x : Fin 4 → ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (j, c) :: js => (if j < N ∧ failW (laneI w h x j) c = true then 2 ^ (8 * j) else 0) |||
      firesW N w h x js

theorem firesW_sound {N w h j : ℕ} (x : Fin 4 → ℕ) : ∀ (js : List (ℕ × ℕ)),
    (firesW N w h x js).testBit (8 * j) = true → passImgB (laneI w h x j) = false
  | [], h1 => by simp [firesW] at h1
  | (k, c) :: js, h1 => by
    simp only [firesW, Nat.testBit_or, Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · split_ifs at h1 with hk
      · rw [Nat.testBit_two_pow] at h1
        have : k = j := by simp at h1; omega
        subst this; exact failW_sound hk.2
      · simp at h1
    · exact firesW_sound x js h1

end ZZN.BoxK

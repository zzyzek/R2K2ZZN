/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.BoxK.SliceC

@[expose] public section

/-!
# Slice certificates with witnesses

`sliceCOK_sound` concludes `Solvable` for each valid lane. `sliceCOK_wit` concludes which entry of
the certificate solves it (`LaneW`): a template that checks on a symmetry of the lane, or a stored
pair of paths for that lane. Lanes that are neither do not pass (`passImgB = false`).
-/

namespace ZZN.BoxK

open ZZN ZZN.Lane ZZN.Cut GridHam

/-- Lane `j` of the slice `(w, h, x)` is solved by a template of `pairs` or a stored pair of `sols`. -/
def LaneW (w h : ℕ) (x : Fin 4 → ℕ) (pairs : List (CTree TPos × Sym))
    (sols : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (j : ℕ) : Prop :=
  (∃ e ∈ pairs, tcheck e.1 (e.2.apply (laneI w h x j)) = true) ∨
  (∃ e ∈ sols, e.1 = j ∧ solF (laneI w h x j) (decPath e.2.1 e.2.2.1) (decPath e.2.2.2.1 e.2.2.2.2) = true)

/-- What a certificate with witnesses proves about a slice. -/
def SliceW (w h : ℕ) (x : Fin 4 → ℕ) (pairs : List (CTree TPos × Sym))
    (sols : List (ℕ × ℕ × ℕ × ℕ × ℕ)) : Prop :=
  ∀ j, j < h ^ 4 → axBB h [digit h 0 j, digit h 1 j, digit h 2 j, digit h 3 j] = true →
    (∀ σ ∈ stabL w x, keyR (fun i => digit h i j) ≤ keyR (yS0 σ h (fun i => digit h i j))) →
    (w = h → keyR x ≤ keyR (fun i => digit h i j)) → (∀ i, x i < 32) →
    (laneI w h x j).WellFormed → LaneW w h x pairs sols j ∨ passImgB (laneI w h x j) = false

theorem coverFW_wit {N w h j : ℕ} (hh : 0 < h) (h32 : h ≤ 32) (hw : w ≤ 32) (hN : N = h ^ 4)
    (hj : j < N) (x : Fin 4 → ℕ) (hx : ∀ i, x i < 32) {Y : Fin 4 → ℕ} (hY : ∀ i, Y i = YS h i.val) :
    ∀ (ps : List (CTree TPos × Sym)), (coverFW N w h x Y ps).testBit (8 * j) = true →
      ∃ e ∈ ps, tcheck e.1 (e.2.apply (laneI w h x j)) = true
  | [], h1 => by simp [coverFW] at h1
  | (T, σ) :: ps, h1 => by
    simp only [coverFW, Nat.testBit_or, Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · split_ifs at h1 with hs
      · simp at h1
      · simp only [Bool.not_eq_true', not_or, Bool.not_eq_false] at hs
        obtain ⟨⟨htr, hry⟩, hT⟩ := hs
        have htr' : σ.tr = false := by simpa using htr
        have hry' : σ.ry = false := by simpa using hry
        subst hN
        rw [tcheckFW_get hj (fun i => by unfold xS; have := hx (lperm σ i); split_ifs <;> omega)
          (by omega) (fun i => by rw [hY]; exact YS_sm64 hh h32 (by omega)) (by omega) hT] at h1
        have e : laneF w h (xS σ w x) (fun i => Y (lperm σ i)) j =
            σ.apply (laneI w h x j) := by
          rw [apply_laneI htr' hh h32 rfl hj]
          simp [laneF, laneInst, yS, hry', Ycols, LV.get, hY]
        rw [e] at h1
        exact ⟨(T, σ), List.mem_cons_self, h1⟩
    · obtain ⟨e, he, h⟩ := coverFW_wit hh h32 hw hN hj x hx hY ps h1
      exact ⟨e, List.mem_cons_of_mem _ he, h⟩

theorem solsM_wit {N w h j : ℕ} (x : Fin 4 → ℕ) : ∀ (js : List (ℕ × ℕ × ℕ × ℕ × ℕ)),
    (solsM N w h x js).testBit (8 * j) = true →
      ∃ e ∈ js, e.1 = j ∧ solF (laneI w h x j) (decPath e.2.1 e.2.2.1) (decPath e.2.2.2.1 e.2.2.2.2) = true
  | [], h1 => by simp [solsM] at h1
  | (k, np, cp, nq, cq) :: js, h1 => by
    simp only [solsM, Nat.testBit_or, Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · split_ifs at h1 with hk
      · rw [Nat.testBit_two_pow] at h1
        have : k = j := by simp at h1; omega
        subst this
        exact ⟨(k, np, cp, nq, cq), List.mem_cons_self, rfl, hk.2⟩
      · simp at h1
    · obtain ⟨e, he, h⟩ := solsM_wit x js h1
      exact ⟨e, List.mem_cons_of_mem _ he, h⟩

theorem maskOK_wit {w h : ℕ} (hh : 0 < h) (h32 : h ≤ 32) {x : Fin 4 → ℕ} {B M : ℕ}
    (hB : baseM h (stabL w x) = B) (hok : maskOK w h x B M = true) (P : ℕ → Prop)
    (hM : ∀ j, j < h ^ 4 → M.testBit (8 * j) = true → (laneI w h x j).WellFormed →
      P j ∨ passImgB (laneI w h x j) = false) :
    ∀ j, j < h ^ 4 → axBB h [digit h 0 j, digit h 1 j, digit h 2 j, digit h 3 j] = true →
      (∀ σ ∈ stabL w x, keyR (fun i => digit h i j) ≤ keyR (yS0 σ h (fun i => digit h i j))) →
      (w = h → keyR x ≤ keyR (fun i => digit h i j)) → (∀ i, x i < 32) →
      (laneI w h x j).WellFormed → P j ∨ passImgB (laneI w h x j) = false := by
  intro j hj hax hst htc hx32 hwf
  have g : ∀ i : Fin 4, (Ycols h i).get j = digit h i j := Ycols_get hh h32 hj
  by_cases hp : parityOk w h (ptsOf' (laneI w h x j)) = true
  · unfold maskOK validM at hok
    rw [← hB] at hok
    simp only [beq_iff_eq] at hok
    have hb := congrArg (fun n => n.testBit (8 * j)) hok
    simp only [baseM, Nat.testBit_and, Nat.zero_testBit, Nat.testBit_xor, testBit_oneS, hj,
      decide_true, LB.testBit_mkG hj, LB.at_and] at hb
    have gl : ∀ i, (Ycols h i).get j < h := fun i => by rw [g]; exact digit_lt hh
    have v1 : (axBBV (h ^ 4) h (Ycols h)).get j = true := by
      rw [axBBV_get hj]; simpa [colsAt, g] using hax
    have v2 : (distinctV (h ^ 4) x (Ycols h)).get j = true := by
      rw [distinctV_get hj]
      obtain ⟨-, -, -, -, n01, n02, n03, n12, n13, n23⟩ := hwf
      simp [pairsIdx, cellAt, g, laneI] at n01 n02 n03 n12 n13 n23 ⊢
      exact ⟨imp_iff_not_or.mp n01, imp_iff_not_or.mp n02, imp_iff_not_or.mp n03,
        imp_iff_not_or.mp n12, imp_iff_not_or.mp n13, imp_iff_not_or.mp n23⟩
    have v3 : (parityV (h ^ 4) w h x (Ycols h)).get j = true := by
      rw [parityV_get hj]; simpa [ptsOf', laneI, g] using hp
    have v4 : (stabVL (h ^ 4) h (stabL w x) (Ycols h)).get j = true := by
      rw [show stabVL (h ^ 4) h (stabL w x) (Ycols h) = stabV (h ^ 4) w h x (Ycols h) from rfl,
        stabV_get hj h32 _ _ gl]
      refine List.all_eq_true.mpr fun σ hσ => ?_
      simpa [g] using hst σ hσ
    have v5 : (trV (h ^ 4) w h x (Ycols h)).get j = true := by
      rw [trV_get hj _ _ hx32 (fun i => by have := gl i; omega)]
      by_cases hwh : w = h
      · simp only [hwh, decide_true, Bool.not_true, Bool.false_or, decide_eq_true_eq]
        simpa [g] using htc hwh
      · simp [hwh]
    rw [v1, v4, v5, v2, v3] at hb
    have hm : M.testBit (8 * j) = true := by
      cases e : M.testBit (8 * j) <;> simp_all
    exact hM j hj hm hwf
  · right
    exact passImgB_of_parity hwf (by simp only [Bool.not_eq_true] at hp; exact hp)

/-- **A slice certificate names the entry that solves each valid lane.** -/
theorem sliceCOK_wit {w h : ℕ} (hh : 5 ≤ h) (h32 : h ≤ 32) (hw32 : w ≤ 32) {x : Fin 4 → ℕ}
    (hx32 : ∀ i, x i < 32) {L : List Sym} {B : ℕ} (hB : baseM h L = B) {w0 : ℕ} {x0 : Fin 4 → ℕ}
    {ss : List RStep} {pairs : List (CTree TPos × Sym)} {fires : List (ℕ × ℕ)}
    {sols : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
    (hok : sliceCOK w h x L B w0 x0 ss 0 pairs fires [] sols = true) :
    SliceW w h x pairs sols := by
  simp only [sliceCOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hL, -⟩, hm⟩ := hok
  refine maskOK_wit (by omega) h32 (by rw [hL]; exact hB) hm _ fun j hj hb hwf => ?_
  simp only [Nat.zero_or, ownM, coverFWD_eq, Nat.testBit_or, Bool.or_eq_true] at hb
  rcases hb with ((hb | hb) | hb) | hb
  · exact Or.inl (Or.inl (coverFW_wit (by omega) h32 hw32 rfl hj x hx32 (sel4_YS h) pairs hb))
  · exact Or.inr (firesW_sound x fires hb)
  · simp [instM] at hb
  · exact Or.inl (Or.inr (solsM_wit x sols hb))

end ZZN.BoxK

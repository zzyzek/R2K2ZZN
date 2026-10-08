-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Moves

/-!
# Theorem A from explicit assumptions

`PROOF.md` Theorem A: every instance with both sides ≥ 11 that passes the catalogue is solvable.

Here it is proved (`theoremA`) from a structure `Facts` whose fields are proved in later files:

* `passX`, `passT` — the catalogue facts: the reductions preserve passing (§4.3–§4.5;
  `PassX.lean`, `PassXR.lean`, `PassXAssemble.lean`, `PassStrip.lean`), and the catalogue is
  symmetric under transposition (`PassT.lean`, `PassTR.lean`);
* `finite` — the computations (§5): every passing instance in the domain with both sides ≤ 22 to
  which no reduction applies has a valid move (`MoveOK`, exactly what the one-step checker
  accepts), or is solvable outright (the box checks, `Boxes.lean`).

Everything else (the induction, the case analysis, lifting solutions through every reduction,
transposition) is checked here. `theoremA_final` (`Boxes.lean`) is Theorem A with no hypotheses.
-/

namespace ZZN

open GridHam

/-- The domain 𝔇: both sides ≥ 11, endpoints distinct and in bounds. -/
def InDom (I : Inst) : Prop := 11 ≤ I.w ∧ 11 ≤ I.h ∧ I.WellFormed

/-- Some endpoint lies on a line `< k`. -/
def EndBelow (I : Inst) (k : ℕ) : Prop := ∃ e ∈ I.ends, e.1 < k

/-- Some endpoint lies on a line `> k`. -/
def EndAbove (I : Inst) (k : ℕ) : Prop := ∃ e ∈ I.ends, k < e.1

/-- An x-axis reduction deleting lines `d, d+1` (`PROOF.md` §3), keeping the side ≥ 11:
* a strip: the 4 lines at an edge are free;
* a compression: `d, d+1` lie in a window of 10 free lines, with endpoints on both sides;
* an interior compression: `d, d+1` and a neighbouring line are free, endpoints lie on both
  sides, and `8 ≤ d ≤ w − 10`. -/
def RedX (I : Inst) (d : ℕ) : Prop :=
  13 ≤ I.w ∧
  ((d = 0 ∧ ∀ k, k ≤ 3 → I.FreeLine k) ∨
   (d + 2 = I.w ∧ ∀ k, I.w ≤ k + 4 → k < I.w → I.FreeLine k) ∨
   (∃ lo, lo ≤ d ∧ d + 1 ≤ lo + 9 ∧ lo + 10 ≤ I.w ∧ (∀ k, lo ≤ k → k ≤ lo + 9 → I.FreeLine k) ∧
      EndBelow I lo ∧ EndAbove I (lo + 9)) ∨
   (8 ≤ d ∧ d + 10 ≤ I.w ∧ I.FreeLine d ∧ I.FreeLine (d + 1) ∧
      ((1 ≤ d ∧ I.FreeLine (d - 1)) ∨ I.FreeLine (d + 2)) ∧ EndBelow I d ∧ EndAbove I (d + 1)))

/-- A same-color split on the x-axis (`PROOF.md` §4.6): a cut at `x = p` with one color's pair on
each side, and a Hamiltonian path for each piece. -/
def QSplitX (I : Inst) : Prop :=
  ∃ p, 0 < p ∧ p < I.w ∧
    ((I.s0.1 < p ∧ I.t0.1 < p ∧ p ≤ I.s1.1 ∧ p ≤ I.t1.1 ∧
      HasHamPath p I.h I.s0 I.t0 ∧
      HasHamPath (I.w - p) I.h (I.s1.1 - p, I.s1.2) (I.t1.1 - p, I.t1.2)) ∨
     (I.s1.1 < p ∧ I.t1.1 < p ∧ p ≤ I.s0.1 ∧ p ≤ I.t0.1 ∧
      HasHamPath p I.h I.s1 I.t1 ∧
      HasHamPath (I.w - p) I.h (I.s0.1 - p, I.s0.2) (I.t0.1 - p, I.t0.2)))

/-- Instances where some reduction applies, on either axis. -/
def Reducible (I : Inst) : Prop :=
  (∃ d, RedX I d) ∨ (∃ d, RedX I.transpose d) ∨ QSplitX I ∨ QSplitX I.transpose

/-- The facts `theoremA` assumes. -/
structure Facts : Prop where
  passX  : ∀ I d, InDom I → RedX I d → Passes I → Passes (I.deleteAt d)
  passT  : ∀ I, InDom I → Passes I → Passes I.transpose
  finite : ∀ I, InDom I → I.w ≤ 22 → I.h ≤ 22 → Passes I → ¬ Reducible I →
    MoveOK I ∨ Solvable I

/-! ### Deleting lines keeps an instance well formed -/

theorem delAt_inBounds {d w h : ℕ} {v : Coord} (hdw : d + 2 ≤ w) (hv : InBounds w h v)
    (hd : v.1 ≠ d) (hd1 : v.1 ≠ d + 1) : InBounds (w - 2) h (delAt d v) := by
  unfold InBounds at hv ⊢
  unfold delAt
  split_ifs <;> constructor <;> (try dsimp only) <;> omega

theorem delAt_inj {d : ℕ} {u v : Coord} (hu : u.1 ≠ d) (hu1 : u.1 ≠ d + 1) (hv : v.1 ≠ d)
    (hv1 : v.1 ≠ d + 1) (h : delAt d u = delAt d v) : u = v := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  simp only at hu hu1 hv hv1
  unfold delAt at h
  split_ifs at h <;> simp only [Prod.mk.injEq] at h ⊢ <;> omega

theorem RedX.free {I : Inst} {d : ℕ} (h : RedX I d) :
    I.FreeLine d ∧ I.FreeLine (d + 1) ∧
      ((d + 3 ≤ I.w ∧ I.FreeLine (d + 2)) ∨ (1 ≤ d ∧ d + 2 ≤ I.w ∧ I.FreeLine (d - 1))) := by
  obtain ⟨hw, h⟩ := h
  rcases h with ⟨rfl, hf⟩ | ⟨hd, hf⟩ | ⟨lo, hl, hh, hbound, hf, -, -⟩ |
      ⟨h8, hdw, f0, f1, f2, -, -⟩
  · exact ⟨hf 0 (by omega), hf 1 (by omega), Or.inl ⟨by omega, hf 2 (by omega)⟩⟩
  · exact ⟨hf d (by omega) (by omega), hf (d + 1) (by omega) (by omega),
      Or.inr ⟨by omega, by omega, hf (d - 1) (by omega) (by omega)⟩⟩
  · refine ⟨hf d hl (by omega), hf (d + 1) (by omega) hh, ?_⟩
    by_cases hc : d + 2 ≤ lo + 9
    · exact Or.inl ⟨by omega, hf (d + 2) (by omega) hc⟩
    · exact Or.inr ⟨by omega, by omega, hf (d - 1) (by omega) (by omega)⟩
  · rcases f2 with ⟨h1, f2⟩ | f2
    · exact ⟨f0, f1, Or.inr ⟨h1, by omega, f2⟩⟩
    · exact ⟨f0, f1, Or.inl ⟨by omega, f2⟩⟩

theorem RedX.width {I : Inst} {d : ℕ} (h : RedX I d) : 13 ≤ I.w := h.1

theorem inDom_deleteAt {I : Inst} {d : ℕ} (hI : InDom I) (hr : RedX I d) :
    InDom (I.deleteAt d) := by
  obtain ⟨hw, hh, b0, b1, b2, b3, n01, n02, n03, n12, n13, n23⟩ := hI
  obtain ⟨f0, f1, hthird⟩ := hr.free
  have hdw : d + 2 ≤ I.w := by rcases hthird with ⟨h, -⟩ | ⟨-, h, -⟩ <;> omega
  have g : ∀ e ∈ I.ends, e.1 ≠ d ∧ e.1 ≠ d + 1 := fun e he => ⟨f0 e he, f1 e he⟩
  simp only [Inst.ends, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at g
  obtain ⟨⟨g0, g0'⟩, ⟨g1, g1'⟩, ⟨g2, g2'⟩, ⟨g3, g3'⟩⟩ := g
  have w13 := hr.width
  refine ⟨by show 11 ≤ I.w - 2; omega, hh, delAt_inBounds hdw b0 g0 g0',
    delAt_inBounds hdw b1 g1 g1', delAt_inBounds hdw b2 g2 g2', delAt_inBounds hdw b3 g3 g3',
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => n01 (delAt_inj g0 g0' g1 g1' h)
  · exact fun h => n02 (delAt_inj g0 g0' g2 g2' h)
  · exact fun h => n03 (delAt_inj g0 g0' g3 g3' h)
  · exact fun h => n12 (delAt_inj g1 g1' g2 g2' h)
  · exact fun h => n13 (delAt_inj g1 g1' g3 g3' h)
  · exact fun h => n23 (delAt_inj g2 g2' g3 g3' h)

theorem inDom_transpose {I : Inst} (hI : InDom I) : InDom I.transpose := by
  obtain ⟨hw, hh, b0, b1, b2, b3, n01, n02, n03, n12, n13, n23⟩ := hI
  have sb : ∀ {v : Coord}, InBounds I.w I.h v → InBounds I.h I.w v.swap := fun {v} hv =>
    ⟨hv.2, hv.1⟩
  have sn : ∀ {u v : Coord}, u ≠ v → u.swap ≠ v.swap := fun {u v} h e =>
    h (Prod.swap_injective e)
  exact ⟨hh, hw, sb b0, sb b1, sb b2, sb b3, sn n01, sn n02, sn n03, sn n12, sn n13, sn n23⟩

/-! ### The leftover family is finite: a side ≥ 23 always has a reduction -/

theorem not_free {I : Inst} {k : ℕ} (h : ¬ I.FreeLine k) : ∃ e ∈ I.ends, e.1 = k := by
  unfold Inst.FreeLine at h
  push Not at h
  exact h

/-- **Finiteness.** With endpoints in the grid and `w ≥ 23`, some x-axis reduction applies. Proof:
no strip means endpoints at `x ≤ 3` and at `x ≥ w − 4`; the two other endpoints cannot block all
three windows `7–9`, `10–12`, `13–15`, and a free window gives an interior compression. -/
theorem redX_of_wide (I : Inst) (hw : 23 ≤ I.w) :
    ∃ d, RedX I d := by
  by_cases hL : ∀ k, k ≤ 3 → I.FreeLine k
  · exact ⟨0, by omega, Or.inl ⟨rfl, hL⟩⟩
  by_cases hR : ∀ k, I.w ≤ k + 4 → k < I.w → I.FreeLine k
  · exact ⟨I.w - 2, by omega, Or.inr (Or.inl ⟨by omega, hR⟩)⟩
  push Not at hL hR
  obtain ⟨kA, hkA, hA⟩ := hL
  obtain ⟨kB, hkB, hkBw, hB⟩ := hR
  obtain ⟨eA, heA, rfl⟩ := not_free hA
  obtain ⟨eB, heB, rfl⟩ := not_free hB
  have below : ∀ d, 8 ≤ d → EndBelow I d := fun d hd => ⟨eA, heA, by omega⟩
  have above : ∀ d, d ≤ 15 → EndAbove I d := fun d hd => ⟨eB, heB, by omega⟩
  by_cases f1 : ∀ k, 7 ≤ k → k ≤ 9 → I.FreeLine k
  · exact ⟨8, by omega, Or.inr (Or.inr (Or.inr ⟨le_refl _, by omega, f1 8 (by omega) (by omega),
      f1 9 (by omega) (by omega), Or.inl ⟨by omega, f1 7 (by omega) (by omega)⟩,
      below 8 (le_refl _), above 9 (by omega)⟩))⟩
  by_cases f2 : ∀ k, 10 ≤ k → k ≤ 12 → I.FreeLine k
  · exact ⟨10, by omega, Or.inr (Or.inr (Or.inr ⟨by omega, by omega, f2 10 (by omega) (by omega),
      f2 11 (by omega) (by omega), Or.inr (f2 12 (by omega) (by omega)),
      below 10 (by omega), above 11 (by omega)⟩))⟩
  by_cases f3 : ∀ k, 13 ≤ k → k ≤ 15 → I.FreeLine k
  · exact ⟨13, by omega, Or.inr (Or.inr (Or.inr ⟨by omega, by omega, f3 13 (by omega) (by omega),
      f3 14 (by omega) (by omega), Or.inr (f3 15 (by omega) (by omega)),
      below 13 (by omega), above 14 (by omega)⟩))⟩
  exfalso
  push Not at f1 f2 f3
  obtain ⟨k1, a1, b1, c1⟩ := f1
  obtain ⟨k2, a2, b2, c2⟩ := f2
  obtain ⟨k3, a3, b3, c3⟩ := f3
  obtain ⟨e1, he1, rfl⟩ := not_free c1
  obtain ⟨e2, he2, rfl⟩ := not_free c2
  obtain ⟨e3, he3, rfl⟩ := not_free c3
  let X : Finset ℕ := (I.ends.map Prod.fst).toFinset
  have mem : ∀ e ∈ I.ends, e.1 ∈ X := fun e he =>
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, he, rfl⟩)
  have hsub : ({eA.1, e1.1, e2.1, e3.1, eB.1} : Finset ℕ) ⊆ X := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact mem _ heA
    · exact mem _ he1
    · exact mem _ he2
    · exact mem _ he3
    · exact mem _ heB
  have h5 : ({eA.1, e1.1, e2.1, e3.1, eB.1} : Finset ℕ).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (by omega)]
  have h4 : X.card ≤ 4 := (List.toFinset_card_le _).trans (by simp [Inst.ends])
  have := Finset.card_le_card hsub
  omega

/-- Lifting a solution through an x-axis reduction. -/
theorem lift_redX {I : Inst} {d : ℕ} (hr : RedX I d) (hS : Solvable (I.deleteAt d)) :
    Solvable I := by
  obtain ⟨f0, f1, h⟩ := hr.free
  rcases h with ⟨hw, f2⟩ | ⟨hd, hw, fm⟩
  · exact lift_delete I d hw f0 f1 f2 hS
  · exact lift_delete' I d hd hw fm f0 f1 hS

/-- A same-color split gives a solution (`glue_same`, both color orders). -/
theorem glueQ {I : Inst} (hq : QSplitX I) : Solvable I := by
  obtain ⟨p, hp0, hp, h | h⟩ := hq
  · obtain ⟨a, b, c, d, hA, hB⟩ := h
    exact glue_same I p hp a b c d hA hB
  · obtain ⟨a, b, c, d, hA, hB⟩ := h
    exact solvable_swapColors (glue_same I.swapColors p hp a b c d hA hB)

/-! ### Theorem A -/

theorem theoremA (F : Facts) : ∀ I, InDom I → Passes I → Solvable I := by
  intro I
  induction hn : I.w * I.h using Nat.strong_induction_on generalizing I with
  | _ n ih =>
    intro hI hP
    have IH : ∀ J, InDom J → J.w * J.h < I.w * I.h → Passes J → Solvable J := by
      intro J hJ hlt hJP
      exact ih _ (hn ▸ hlt) J rfl hJ hJP
    have hh11 := hI.2.1
    have hw11 := hI.1
    by_cases hx : ∃ d, RedX I d
    · obtain ⟨d, hd⟩ := hx
      refine lift_redX hd (IH _ (inDom_deleteAt hI hd) ?_ (F.passX I d hI hd hP))
      show (I.w - 2) * I.h < I.w * I.h
      have := hd.width
      exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    by_cases hy : ∃ d, RedX I.transpose d
    · obtain ⟨d, hd⟩ := hy
      have hT := inDom_transpose hI
      have hTP := F.passT I hI hP
      refine solvable_transpose_iff.mp (lift_redX hd (IH _ (inDom_deleteAt hT hd) ?_
        (F.passX _ d hT hd hTP)))
      show (I.h - 2) * I.w < I.w * I.h
      have := hd.width
      rw [Nat.mul_comm I.w]
      exact Nat.mul_lt_mul_of_pos_right (by simp [Inst.transpose] at this; omega) (by omega)
    by_cases hq : QSplitX I
    · exact glueQ hq
    by_cases hq' : QSplitX I.transpose
    · exact solvable_transpose_iff.mp (glueQ hq')
    have hw22 : I.w ≤ 22 := by
      by_contra h
      exact hx (redX_of_wide I (by omega))
    have hh22 : I.h ≤ 22 := by
      by_contra h
      exact hy (redX_of_wide I.transpose (by simp [Inst.transpose]; omega))
    rcases F.finite I hI hw22 hh22 hP (by
      rintro (h | h | h | h)
      · exact hx h
      · exact hy h
      · exact hq h
      · exact hq' h) with hm | hs
    · exact hm.solvable hI.2.2 (fun J hw hh hwf ha hp => IH J ⟨hw, hh, hwf⟩ ha hp)
    · exact hs

/-- **Theorem A**, stated plainly: given `Facts`, every well-formed instance with both sides
`≥ 11` that passes the catalogue is solvable. -/
theorem theoremA_main (F : Facts) (I : Inst) (hwf : I.WellFormed) (hw : 11 ≤ I.w) (hh : 11 ≤ I.h)
    (hP : Passes I) : Solvable I :=
  theoremA F I ⟨hw, hh, hwf⟩ hP

end ZZN

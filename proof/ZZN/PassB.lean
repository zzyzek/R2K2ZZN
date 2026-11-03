/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.B5Fire
public import ZZN.B5Hit

@[expose] public section

/-!
# Band compressions

`RedB I d`: lines `d, d+1` are free with a free neighbour, endpoints lie on both sides,
`5 ≤ d`, `d + 7 ≤ w`, and after the deletion every endpoint is at least 5 lines from the edge
it approaches (`FarK 5`). The compressions of `RedX` need 8 lines.

`passB`: band compressions preserve passing. The views agree on frame coordinates `≤ 4`
(`frames_any_of5`). A window-8 C entry (`c8_firesF`) or a B entry with a cell at coordinate 5
(`b5_all`) that matches on the smaller instance makes R fire there, and R gives the same answer
on both instances (`effAlt3_comp`).
-/

namespace ZZN

open GridHam ZZN.Win

def RedB (I : Inst) (d : ℕ) : Prop := 13 ≤ I.w ∧ 5 ≤ d ∧ d + 7 ≤ I.w ∧ CompCore I d

theorem inDom_deleteB {I : Inst} {d : ℕ} (hI : InDom I) (hr : RedB I d) :
    InDom (I.deleteAt d) := by
  obtain ⟨hw, hh, b0, b1, b2, b3, n01, n02, n03, n12, n13, n23⟩ := hI
  obtain ⟨w13, -, -, f0, f1, hdw, -⟩ := hr
  have g : ∀ e ∈ I.ends, e.1 ≠ d ∧ e.1 ≠ d + 1 := fun e he => ⟨f0 e he, f1 e he⟩
  simp only [Inst.ends, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at g
  obtain ⟨⟨g0, g0'⟩, ⟨g1, g1'⟩, ⟨g2, g2'⟩, ⟨g3, g3'⟩⟩ := g
  refine ⟨by show 11 ≤ I.w - 2; omega, hh, delAt_inBounds hdw b0 g0 g0',
    delAt_inBounds hdw b1 g1 g1', delAt_inBounds hdw b2 g2 g2', delAt_inBounds hdw b3 g3 g3',
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => n01 (delAt_inj g0 g0' g1 g1' h)
  · exact fun h => n02 (delAt_inj g0 g0' g2 g2' h)
  · exact fun h => n03 (delAt_inj g0 g0' g3 g3' h)
  · exact fun h => n12 (delAt_inj g1 g1' g2 g2' h)
  · exact fun h => n13 (delAt_inj g1 g1' g3 g3' h)
  · exact fun h => n23 (delAt_inj g2 g2' g3 g3' h)

/-- Lifting a solution through a band compression. -/
theorem lift_redB {I : Inst} {d : ℕ} (hr : RedB I d) (hS : Solvable (I.deleteAt d)) :
    Solvable I := by
  obtain ⟨-, -, hd7, f0, f1, hw, (⟨hd, fm⟩ | fp), -⟩ := hr
  · exact lift_delete' I d hd hw fm f0 f1 hS
  · exact lift_delete I d (by omega) f0 f1 fp hS

/-- A matched entry, in frame coordinates, pins the endpoint tuple to one of `ords`. -/
theorem ords_ofF {e : Coord × Coord × Coord × Coord} (ha : e.1 ≠ e.2.1) (hb : e.2.2.1 ≠ e.2.2.2)
    {s0 t0 s1 t1 : Coord} (d1 : s0 ≠ t0) (d6 : s1 ≠ t1)
    (hm : (sameSet (toAB e).1 [s0, t0] && sameSet (toAB e).2 [s1, t1] ||
      sameSet (toAB e).1 [s1, t1] && sameSet (toAB e).2 [s0, t0]) = true) :
    (s0, t0, s1, t1) ∈ ords e := by
  obtain ⟨a, a', b, b'⟩ := e
  simp only [toAB, Bool.or_eq_true, Bool.and_eq_true] at ha hb hm ⊢
  rcases hm with ⟨m1, m2⟩ | ⟨m1, m2⟩
  · rcases sameSet_two ha d1 m1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases sameSet_two hb d6 m2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [ords]
  · rcases sameSet_two ha d6 m1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases sameSet_two hb d1 m2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [ords]

theorem small6_winC (e : List (ℕ × ℕ) × List (ℕ × ℕ)) : small6 e = true ↔ winC e = 6 := by
  unfold small6 winC
  split_ifs with h
  · simp only [iff_true]; simpa using h
  · simp only [iff_false, Nat.reduceEqDiff]; simpa using h

/-- **A big C match makes R fire.** -/
theorem bigHit_R {J : Inst} (hI : InDom J) {f : Frame}
    (hb : BigHit J.w J.h f [(J.s0, 0), (J.t0, 0), (J.s1, 1), (J.t1, 1)]) :
    effAlt3 J.w J.h (ptsOf J) = true := by
  obtain ⟨hp, AB, hAB, hs, hm⟩ := hb
  have h8 : AB ∈ CORNER4.filter (fun AB => ¬ winC AB = 6) :=
    List.mem_filter.mpr ⟨hAB, by
      have := (small6_winC AB).not.mp (by simp [hs]); simpa using this⟩
  rw [big_entries'] at h8
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp h8
  obtain ⟨ha, hb', -⟩ := c8_small e he
  obtain ⟨-, -, b0, b1, b2, b3, d1, -, -, -, -, d6⟩ := id hI
  have e01 : ((1 : ℕ) == 0) = false := rfl
  have e10 : ((0 : ℕ) == 1) = false := rfl
  simp only [List.filter_cons, List.filter_nil, beq_self_eq_true, e01, e10, ↓reduceIte,
    Bool.false_eq_true, List.map_cons, List.map_nil] at hm
  have hq := ords_ofF ha hb' (fun h => d1 (to_inj f b0 b1 h)) (fun h => d6 (to_inj f b2 b3 h)) hm
  exact c8_firesF hI hp he hq

theorem goodL_ptsOf {J : Inst} (hI : InDom J) : GoodL J.w J.h (ptsOf J) := by
  obtain ⟨-, -, b0, b1, b2, b3, d1, d2, d3, d4, d5, d6⟩ := hI
  refine ⟨?_, ?_⟩
  · simp [ptsOf, cellsOf, d1, d2, d3, d4, d5, d6]
  · intro q hq
    simp only [ptsOf, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    exacts [b0, b1, b2, b3]

/-- **A B match with a cell at coordinate 5 makes R fire.** -/
theorem b5Hit_R {J : Inst} (hI : InDom J) {f : Frame}
    (hb : B5Hit J.w J.h f [(J.s0, 0), (J.t0, 0), (J.s1, 1), (J.t1, 1)]) :
    effAlt3 J.w J.h (ptsOf J) = true := by
  obtain ⟨hp, e, he, x, hx, hperm⟩ := b5Hit_pts hI hb
  have hw := hI.1
  have hh := hI.2.1
  have hg := goodL_ptsOf hI
  have hall := b5_all _ J.w J.h rfl hw hh hp f e he x hx
  rcases hperm with h | h
  · rw [← effAlt3_perm (by omega) (by omega) hg h]; exact hall
  · rw [← effAlt3_relab, ← effAlt3_perm (by omega) (by omega) hg.map_relab h]; exact hall

/-- **Band compressions preserve passing.** -/
theorem passB {I : Inst} {d : ℕ} (hI : InDom I) (h : RedB I d) (hP : Passes I) :
    Passes (I.deleteAt d) := by
  have hJ := inDom_deleteB hI h
  obtain ⟨hw13, hd5, hd7, hc⟩ := h
  have hC := hI.2.1
  obtain ⟨-, -, b0, b1, b2, b3, -⟩ := id hI
  obtain ⟨f0, f1, -⟩ := compCore_free hc
  have av : ∀ q ∈ [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)], Av d I.w (q : Pt).1 := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨f0 _ (by simp [Inst.ends]), f1 _ (by simp [Inst.ends]), b0.1⟩
    · exact ⟨f0 _ (by simp [Inst.ends]), f1 _ (by simp [Inst.ends]), b1.1⟩
    · exact ⟨f0 _ (by simp [Inst.ends]), f1 _ (by simp [Inst.ends]), b2.1⟩
    · exact ⟨f0 _ (by simp [Inst.ends]), f1 _ (by simp [Inst.ends]), b3.1⟩
  have hpts : [(delAt d I.s0, 0), (delAt d I.t0, 0), (delAt d I.s1, 1), (delAt d I.t1, 1)] =
      delPts d [(I.s0, (0 : ℕ)), (I.t0, 0), (I.s1, 1), (I.t1, 1)] := rfl
  have hR := effAlt3_comp (C := I.h) hd5 hd7 (by omega) av
  unfold Passes at hP ⊢
  by_contra hf
  apply absurd hP
  rw [Bool.not_eq_false] at hf ⊢
  unfold fires3 at hf ⊢
  simp only [Inst.deleteAt] at hf
  simp only [Bool.or_eq_true] at hf ⊢
  rcases hf with (((((hp | ht1) | ht2) | hl1) | hl6) | hfr) | hea
  · left; left; left; left; left; left
    rw [← parityOk_deleteAt (by omega) f0 f1]
    exact hp
  · left; left; left; left; left; right
    exact t1_comp hI hc hw13 ht1
  · rw [t2_comp hI hc] at ht2; exact absurd ht2 (by simp)
  · left; left; left; right
    rw [l1Fires_iff] at hl1 ⊢
    exact l1_comp hI hc hl1
  · left; left; right
    exact l6_comp hI hc hw13 hl6
  · rcases frames_any_of5 (by omega) (winRel5_core hI hc) (by omega) (e1_comp hI hc) hfr with
      g | ⟨f, hb⟩ | ⟨f, hb⟩
    · left; right; exact g
    · right
      have hb' := bigHit_R hJ hb
      change effAlt3 (I.w - 2) I.h (delPts d [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)]) = true
        at hb'
      rw [← hR]
      exact hb'
    · right
      have hb' := b5Hit_R hJ hb
      change effAlt3 (I.w - 2) I.h (delPts d [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)]) = true
        at hb'
      rw [← hR]
      exact hb'
  · right
    rw [hpts, hR] at hea
    exact hea

/-! ### Theorem A with band compressions -/

/-- Instances where some reduction applies, band compressions included. -/
def ReducibleB (I : Inst) : Prop :=
  Reducible I ∨ (∃ d, RedB I d) ∨ (∃ d, RedB I.transpose d)

/-- Every `RedX` reduction preserves passing. -/
theorem passX_all {I : Inst} {d : ℕ} (hI : InDom I) (hr : RedX I d) (hP : Passes I) :
    Passes (I.deleteAt d) := by
  obtain ⟨hw, h⟩ := hr
  rcases h with h | h | h | h
  · exact passStrip hI hw (Or.inl h) hP
  · exact passStrip hI hw (Or.inr h) hP
  · exact passX_comp hI hw (Or.inl h) hP
  · exact passX_comp hI hw (Or.inr h) hP

/-- What Theorem A assumes with band compressions: the computation on the boxes. -/
structure FactsFiniteB : Prop where
  finite : ∀ I, InDom I → I.w ≤ 22 → I.h ≤ 22 → Passes I → ¬ ReducibleB I →
    MoveOK I ∨ Solvable I

theorem theoremA_B (F : FactsFiniteB) : ∀ I, InDom I → Passes I → Solvable I := by
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
      refine lift_redX hd (IH _ (inDom_deleteAt hI hd) ?_ (passX_all hI hd hP))
      show (I.w - 2) * I.h < I.w * I.h
      have := hd.width
      exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    by_cases hy : ∃ d, RedX I.transpose d
    · obtain ⟨d, hd⟩ := hy
      have hT := inDom_transpose hI
      have hTP := passT hI hP
      refine solvable_transpose_iff.mp (lift_redX hd (IH _ (inDom_deleteAt hT hd) ?_
        (passX_all hT hd hTP)))
      show (I.h - 2) * I.w < I.w * I.h
      have := hd.width
      rw [Nat.mul_comm I.w]
      exact Nat.mul_lt_mul_of_pos_right (by simp [Inst.transpose] at this; omega) (by omega)
    by_cases hbx : ∃ d, RedB I d
    · obtain ⟨d, hd⟩ := hbx
      refine lift_redB hd (IH _ (inDom_deleteB hI hd) ?_ (passB hI hd hP))
      show (I.w - 2) * I.h < I.w * I.h
      have := hd.1
      exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    by_cases hby : ∃ d, RedB I.transpose d
    · obtain ⟨d, hd⟩ := hby
      have hT := inDom_transpose hI
      have hTP := passT hI hP
      refine solvable_transpose_iff.mp (lift_redB hd (IH _ (inDom_deleteB hT hd) ?_
        (passB hT hd hTP)))
      show (I.h - 2) * I.w < I.w * I.h
      have := hd.1
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
      rintro ((h | h | h | h) | h | h)
      · exact hx h
      · exact hy h
      · exact hq h
      · exact hq' h
      · exact hbx h
      · exact hby h) with hm | hs
    · exact hm.solvable hI.2.2 (fun J hw hh hwf ha hp => IH J ⟨hw, hh, hwf⟩ ha hp)
    · exact hs

end ZZN

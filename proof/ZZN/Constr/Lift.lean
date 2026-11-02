/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Statement
public import ZZN.Constr.Band
public import ZZN.Skeleton
public import ZZN.Solve
public import ZZN.Symmetry

@[expose] public section

/-!
# Finding a reduction and lifting a solution through it

* `redB I d` decides `RedX I d` (`redB_iff`), and `findRed I` finds one (`findRed_some`,
  `findRed_none`).
* `liftE I d p q` turns a solution of `I.deleteAt d` into one of `I` by band extension
  (`liftE_sol`), following `lift_delete`.
* `IsSolution.transpose`: transposing a solution.
* `solB_complete`: the checker `solB` accepts every solution.
-/

namespace ZZN

open GridHam

/-! ### Deciding a reduction -/


theorem freeLineB_iff (I : Inst) (k : ℕ) : freeLineB I k = true ↔ I.FreeLine k := by
  simp [freeLineB, Inst.FreeLine]


theorem endBelowB_iff (I : Inst) (k : ℕ) : endBelowB I k = true ↔ EndBelow I k := by
  simp [endBelowB, EndBelow]


theorem endAboveB_iff (I : Inst) (k : ℕ) : endAboveB I k = true ↔ EndAbove I k := by
  simp [endAboveB, EndAbove]


theorem redB_iff (I : Inst) (d : ℕ) : redB I d = true ↔ RedX I d := by
  unfold redB RedX
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.any_eq_true, List.mem_range, freeLineB_iff, endBelowB_iff, endAboveB_iff, Bool.not_eq_true',
    decide_eq_false_iff_not]
  apply and_congr_right
  intro _
  constructor
  · intro h
    rcases h with (h | h) | h
    · rcases h with ⟨rfl, hf⟩ | ⟨hd, hf⟩
      · exact Or.inl ⟨rfl, fun k hk => hf k (by omega)⟩
      · refine Or.inr (Or.inl ⟨hd, fun k hk hkw => ?_⟩)
        rcases hf k hkw with h | h
        · omega
        · exact h
    · obtain ⟨lo, hlo, hP⟩ := h
      obtain ⟨⟨⟨⟨h1, h2⟩, hf⟩, hb⟩, ha⟩ := hP
      refine Or.inr (Or.inr (Or.inl ⟨lo, by omega, h1, h2, fun k hk1 hk2 => ?_, hb, ha⟩))
      have := hf (k - lo) (by omega)
      rwa [show lo + (k - lo) = k by omega] at this
    · obtain ⟨⟨⟨⟨⟨⟨h8, h10⟩, f0⟩, f1⟩, f2⟩, hb⟩, ha⟩ := h
      exact Or.inr (Or.inr (Or.inr ⟨h8, h10, f0, f1, f2, hb, ha⟩))
  · intro h
    rcases h with h | h | h | h
    · obtain ⟨rfl, hf⟩ := h
      exact Or.inl (Or.inl (Or.inl ⟨rfl, fun k hk => hf k (by omega)⟩))
    · obtain ⟨hd, hf⟩ := h
      refine Or.inl (Or.inl (Or.inr ⟨hd, fun k hk => ?_⟩))
      by_cases hk4 : I.w ≤ k + 4
      · exact Or.inr (hf k hk4 hk)
      · exact Or.inl hk4
    · obtain ⟨lo, hlo, h1, h2, hf, hb, ha⟩ := h
      exact Or.inl (Or.inr ⟨lo, by omega, ⟨⟨⟨h1, h2⟩, fun j hj => hf (lo + j) (by omega) (by omega)⟩,
        hb⟩, ha⟩)
    · obtain ⟨h8, h10, f0, f1, f2, hb, ha⟩ := h
      exact Or.inr ⟨⟨⟨⟨⟨⟨h8, h10⟩, f0⟩, f1⟩, f2⟩, hb⟩, ha⟩

theorem RedX.lt {I : Inst} {d : ℕ} (h : RedX I d) : d < I.w := by
  obtain ⟨-, -, hthird⟩ := h.free
  rcases hthird with ⟨h, -⟩ | ⟨-, h, -⟩ <;> omega


theorem findRed_some {I : Inst} {d : ℕ} (h : findRed I = some d) : RedX I d :=
  (redB_iff I d).1 (List.find?_some h)

theorem findRed_none {I : Inst} (h : findRed I = none) (d : ℕ) : ¬ RedX I d := by
  intro hr
  rw [findRed, List.find?_eq_none] at h
  exact absurd ((redB_iff I d).2 hr) (h d (List.mem_range.mpr hr.lt))

/-! ### Lifting a solution through a reduction -/


theorem liftE_sol {I : Inst} {d : ℕ} {p q : List Coord} (hr : RedX I d)
    (hs : IsSolution (I.deleteAt d) p q) : IsSolution I (liftE I d p q).1 (liftE I d p q).2 := by
  obtain ⟨f0, f1, hthird⟩ := hr.free
  unfold liftE
  by_cases hc : d + 3 ≤ I.w ∧ freeLineB I (d + 2) = true
  · rw [ite_t hc]
    have f2 : I.FreeLine (d + 2) := (freeLineB_iff I _).1 hc.2
    have hw := hc.1
    have hfree : LineFree (I.deleteAt d) d := by
      intro y
      have k : ∀ e ∈ I.ends, (d, y) ≠ delAt d e := by
        intro e he hde
        have a0 := f0 e he
        have a1 := f1 e he
        have a2 := f2 e he
        obtain ⟨ex, ey⟩ := e
        simp only at a0 a1 a2
        unfold delAt at hde
        split_ifs at hde with hlt
        · simp only [Prod.mk.injEq] at hde; simp at hlt; omega
        · simp only [Prod.mk.injEq] at hde; omega
      exact ⟨k _ (by simp [Inst.ends]), k _ (by simp [Inst.ends]), k _ (by simp [Inst.ends]),
        k _ (by simp [Inst.ends])⟩
    have hb := bandExtE_sol hs (by show d < I.w - 2; omega) hfree
    have e : (I.deleteAt d).insertAt d = I := by
      have key : ∀ e ∈ I.ends, shiftAt d (delAt d e) = e := fun e he =>
        shift_del d d e (f0 e he) (f1 e he) (Or.inl rfl) (fun _ => f2 e he) (fun h => by omega)
      cases I
      simp only [Inst.insertAt, Inst.deleteAt, Inst.ends] at key ⊢
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at key
      obtain ⟨k0, k1, k2, k3⟩ := key
      simp only [k0, k1, k2, k3, Inst.mk.injEq, and_true]
      simp only at hw ⊢
      omega
    rw [e] at hb
    exact hb
  · rw [ite_f hc]
    have h3 : 1 ≤ d ∧ d + 2 ≤ I.w ∧ I.FreeLine (d - 1) := by
      rcases hthird with ⟨h1, h2⟩ | h
      · exact absurd ⟨h1, (freeLineB_iff I _).2 h2⟩ hc
      · exact h
    obtain ⟨hd, hw, f0'⟩ := h3
    have hfree : LineFree (I.deleteAt d) (d - 1) := by
      intro y
      have k : ∀ e ∈ I.ends, (d - 1, y) ≠ delAt d e := by
        intro e he hde
        have a0 := f0' e he
        unfold delAt at hde
        split_ifs at hde with hlt
        · rw [← hde] at a0; simp at a0
        · have := congrArg Prod.fst hde; simp at this; have := f0 e he; have := f1 e he; omega
      exact ⟨k _ (by simp [Inst.ends]), k _ (by simp [Inst.ends]), k _ (by simp [Inst.ends]),
        k _ (by simp [Inst.ends])⟩
    have hb := bandExtE_sol hs (by show d - 1 < I.w - 2; omega) hfree
    have e : (I.deleteAt d).insertAt (d - 1) = I := by
      have key : ∀ e ∈ I.ends, shiftAt (d - 1) (delAt d e) = e := fun e he =>
        shift_del (d - 1) d e (f0 e he) (f1 e he) (Or.inr (by omega)) (fun h => by omega)
          (fun _ => Or.inl (f0' e he))
      cases I
      simp only [Inst.insertAt, Inst.deleteAt, Inst.ends] at key ⊢
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at key
      obtain ⟨k0, k1, k2, k3⟩ := key
      simp only [k0, k1, k2, k3, Inst.mk.injEq, and_true]
      simp only at hw ⊢
      omega
    rw [e] at hb
    exact hb

/-! ### Transposing a solution -/

theorem IsSolution.transpose {I : Inst} {p q : List Coord} (hS : IsSolution I p q) :
    IsSolution I.transpose (p.map Prod.swap) (q.map Prod.swap) := by
  obtain ⟨hp, hq, hd, hc⟩ := hS
  refine ⟨hp.swap, hq.swap, ?_, ?_⟩
  · intro v hv hv'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    obtain ⟨u', hu', he⟩ := List.mem_map.mp hv'
    exact hd u hu (Prod.swap_injective he ▸ hu')
  · intro v hv
    have hb : InBounds I.w I.h v.swap := by
      unfold InBounds at hv ⊢
      exact ⟨hv.2, hv.1⟩
    rcases hc v.swap hb with h | h
    · exact Or.inl (List.mem_map.mpr ⟨v.swap, h, Prod.swap_swap v⟩)
    · exact Or.inr (List.mem_map.mpr ⟨v.swap, h, Prod.swap_swap v⟩)

theorem IsSolution.of_transpose {I : Inst} {p q : List Coord} (hS : IsSolution I.transpose p q) :
    IsSolution I (p.map Prod.swap) (q.map Prod.swap) := by
  have := hS.transpose
  rwa [Inst.transpose_transpose] at this

/-! ### The checker accepts every solution -/

theorem solB_complete {I : Inst} {p q : List Coord} (hS : IsSolution I p q) : solB I p q = true := by
  classical
  obtain ⟨hp, hq, hd, hc⟩ := hS
  have hn : (p ++ q).Nodup :=
    List.nodup_append.mpr ⟨hp.2.2.1, hq.2.2.1, fun x hx y hy hxy => by subst hxy; exact hd x hx hy⟩
  have hset : (p ++ q).toFinset = Finset.range I.w ×ˢ Finset.range I.h := by
    ext v
    simp only [List.mem_toFinset, List.mem_append, Finset.mem_product, Finset.mem_range]
    constructor
    · rintro (h | h)
      · exact hp.2.2.2.1 v h
      · exact hq.2.2.2.1 v h
    · intro hv; exact hc v hv
  have hlen : (p ++ q).length = I.w * I.h := by
    rw [← List.toFinset_card_of_nodup hn, hset, Finset.card_product, Finset.card_range,
      Finset.card_range]
  simp only [solB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨hp, hq⟩, hn⟩, ?_⟩
  rw [← List.length_append]; exact hlen

end ZZN

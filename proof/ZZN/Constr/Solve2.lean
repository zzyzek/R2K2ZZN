/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Constr.LiftL
public import ZZN.Constr.Solve
public import ZZN.PassB
public import ZZN.FiniteB
public import ZZN.BoxK.None

@[expose] public section

/-!
# The construction with band compressions

`solveRec2` is `solveRec` with two changes: a reduction is any `RedX` or `RedB` (band
compression), and a lifted solution is not checked again. Band extension lifts both kinds of
reduction (`liftE_solF`, needing only the free lines of `FreeShape`). An instance with both sides
at least 11 where no reduction applies on either axis has both sides at most 16 (`leaf16`: sides
of 23 or more reduce by `redX_of_wide`, sides 17 to 22 by the kernel check `none_all`).
-/

namespace ZZN

open GridHam

/-! ### The free lines that band extension needs -/

/-- Lines `d, d + 1` are free, and line `d + 2` or line `d - 1` is free too. -/
def FreeShape (I : Inst) (d : ℕ) : Prop :=
  13 ≤ I.w ∧ I.FreeLine d ∧ I.FreeLine (d + 1) ∧
    ((d + 3 ≤ I.w ∧ I.FreeLine (d + 2)) ∨ (1 ≤ d ∧ d + 2 ≤ I.w ∧ I.FreeLine (d - 1)))

theorem RedX.shape {I : Inst} {d : ℕ} (h : RedX I d) : FreeShape I d :=
  ⟨h.1, h.free.1, h.free.2.1, h.free.2.2⟩

theorem RedB.shape {I : Inst} {d : ℕ} (h : RedB I d) : FreeShape I d := by
  obtain ⟨hw, hd5, hd7, f0, f1, hd2, h3, -, -, -⟩ := h
  refine ⟨hw, f0, f1, ?_⟩
  rcases h3 with ⟨h1, hm⟩ | hp
  · exact Or.inr ⟨h1, by omega, hm⟩
  · exact Or.inl ⟨by omega, hp⟩

theorem liftE_solF {I : Inst} {d : ℕ} {p q : List Coord} (hr : FreeShape I d)
    (hs : IsSolution (I.deleteAt d) p q) : IsSolution I (liftE I d p q).1 (liftE I d p q).2 := by
  obtain ⟨-, f0, f1, hthird⟩ := hr
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


theorem liftL_eqF {I : Inst} {d : ℕ} {p q : List Coord} (hr : FreeShape I d)
    (hs : IsSolution (I.deleteAt d) p q) : liftL I d p q = liftE I d p q := by
  obtain ⟨-, f0, f1, hthird⟩ := hr
  unfold liftL liftE
  by_cases hc : d + 3 ≤ I.w ∧ freeLineB I (d + 2) = true
  · rw [ite_t hc, ite_t hc]
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
    exact bandExtL_eq hs (by show d < I.w - 2; omega) hfree
  · rw [ite_f hc, ite_f hc]
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
    exact bandExtL_eq hs (by show d - 1 < I.w - 2; omega) hfree



/-! ### Searching for a reduction -/

/-- `RedB I d`, decided. -/
def redBB (I : Inst) (d : ℕ) : Bool :=
  decide (13 ≤ I.w) && decide (5 ≤ d) && decide (d + 7 ≤ I.w) && freeLineB I d &&
    freeLineB I (d + 1) && ((decide (1 ≤ d) && freeLineB I (d - 1)) || freeLineB I (d + 2)) &&
    endBelowB I d && endAboveB I (d + 1)

theorem redBB_iff (I : Inst) (d : ℕ) : redBB I d = true ↔ RedB I d := by
  unfold redBB RedB CompCore
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, freeLineB_iff, endBelowB_iff,
    endAboveB_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨hw, hd5⟩, hd7⟩, f0⟩, f1⟩, h3⟩, hb⟩, ha⟩
    refine ⟨hw, hd5, hd7, f0, f1, by omega, h3, hb, ha, fun e he => ?_⟩
    have g0 := f0 e he
    have g1 := f1 e he
    unfold FarK
    constructor <;> intro <;> omega
  · rintro ⟨hw, hd5, hd7, f0, f1, -, h3, hb, ha, -⟩
    exact ⟨⟨⟨⟨⟨⟨⟨hw, hd5⟩, hd7⟩, f0⟩, f1⟩, h3⟩, hb⟩, ha⟩

/-- A reduction of either kind at `d`. -/
def redAny (I : Inst) (d : ℕ) : Bool := redB I d || redBB I d

/-- The first reduction of either kind. -/
def findRed2 (I : Inst) : Option ℕ := (List.range I.w).find? (redAny I)

theorem findRed2_some {I : Inst} {d : ℕ} (h : findRed2 I = some d) : RedX I d ∨ RedB I d := by
  have := List.find?_some h
  unfold redAny at this
  rcases Bool.or_eq_true_iff.mp this with h1 | h1
  · exact Or.inl ((redB_iff I d).1 h1)
  · exact Or.inr ((redBB_iff I d).1 h1)

theorem findRed2_none {I : Inst} (h : findRed2 I = none) (d : ℕ) : ¬ RedX I d ∧ ¬ RedB I d := by
  rw [findRed2, List.find?_eq_none] at h
  constructor
  · intro hr
    have := h d (List.mem_range.mpr hr.lt)
    simp [redAny, (redB_iff I d).2 hr] at this
  · intro hr
    have hlt : d < I.w := by have := hr.2.2.1; omega
    have := h d (List.mem_range.mpr hlt)
    simp [redAny, (redBB_iff I d).2 hr] at this

theorem findRed2_shape {I : Inst} {d : ℕ} (h : findRed2 I = some d) : FreeShape I d := by
  rcases findRed2_some h with h | h
  · exact h.shape
  · exact h.shape

/-! ### The construction -/

/-- The construction with both kinds of reduction; lifted solutions are not checked again. -/
def solveRec2 (thin : Inst → Option (List Coord × List Coord)) :
    ℕ → Inst → Option (List Coord × List Coord)
  | 0, _ => none
  | n + 1, I =>
    if I.w ≤ 10 ∨ I.h ≤ 10 then checkE I (thin I) else
    match findRed2 I with
    | some d =>
      match solveRec2 thin n (I.deleteAt d) with
      | some pq => some (liftE I d pq.1 pq.2)
      | none => none
    | none =>
      match findRed2 I.transpose with
      | some d =>
        match solveRec2 thin n (I.transpose.deleteAt d) with
        | some pq => some ((liftE I.transpose d pq.1 pq.2).1.map Prod.swap,
            (liftE I.transpose d pq.1 pq.2).2.map Prod.swap)
        | none => none
      | none => checkE I (thin I)

/-- The construction, on well-formed instances. -/
def solveZ2 (thin : Inst → Option (List Coord × List Coord)) (I : Inst) :
    Option (List Coord × List Coord) :=
  if I.WellFormed then solveRec2 thin (I.w + I.h) I else none

/-- **Every answer is a solution**, for any `thin`. -/
theorem solveRec2_sound (thin : Inst → Option (List Coord × List Coord)) :
    ∀ (n : ℕ) (I : Inst) (p q : List Coord), solveRec2 thin n I = some (p, q) → IsSolution I p q := by
  intro n
  induction n with
  | zero => intro I p q h; simp [solveRec2] at h
  | succ n ih =>
    intro I p q h
    simp only [solveRec2] at h
    split_ifs at h
    · exact checkE_some h
    · split at h
      · rename_i d hf
        split at h
        · rename_i pq hpq
          have e := Option.some.inj h
          have h1 : p = (liftE I d pq.1 pq.2).1 := by rw [e]
          have h2 : q = (liftE I d pq.1 pq.2).2 := by rw [e]
          rw [h1, h2]
          exact liftE_solF (findRed2_shape hf) (ih _ pq.1 pq.2 hpq)
        · cases h
      · split at h
        · rename_i d hf
          split at h
          · rename_i pq hpq
            have e := Option.some.inj h
            have h1 : p = (liftE I.transpose d pq.1 pq.2).1.map Prod.swap := (Prod.mk.inj e).1.symm
            have h2 : q = (liftE I.transpose d pq.1 pq.2).2.map Prod.swap := (Prod.mk.inj e).2.symm
            rw [h1, h2]
            exact (liftE_solF (findRed2_shape hf) (ih _ pq.1 pq.2 hpq)).of_transpose
          · cases h
        · exact checkE_some h

/-- **No reduction on an axis of length at least 11 leaves it at most 16.** -/
theorem leaf16 {I : Inst} (hwf : I.WellFormed) (_hw : 11 ≤ I.w)
    (hn : ∀ d, ¬ RedX I d ∧ ¬ RedB I d) : I.w ≤ 16 := by
  by_contra hc
  by_cases h23 : 23 ≤ I.w
  · obtain ⟨d, hd⟩ := redX_of_wide I h23
    exact (hn d).1 hd
  · have hok := BoxK.none_all I.w (by omega) (by omega)
    have hwf' := hwf
    obtain ⟨b0, b1, b2, b3, -⟩ := hwf
    have hf := BoxK.noneOK_sound (by omega) (by omega) hok
      (x := ![I.s0.1, I.t0.1, I.s1.1, I.t1.1]) (fun i => by
        fin_cases i
        exacts [b0.1, b1.1, b2.1, b3.1])
    have ht := axBB_of_noRed hwf' (fun ⟨d, hd⟩ => (hn d).1 hd)
      (fun ⟨d, hd⟩ => (hn d).2 hd)
    have e : xsOf I = [I.s0.1, I.t0.1, I.s1.1, I.t1.1] := rfl
    have e2 : [(![I.s0.1, I.t0.1, I.s1.1, I.t1.1] : Fin 4 → ℕ) 0, ![I.s0.1, I.t0.1, I.s1.1, I.t1.1] 1,
        ![I.s0.1, I.t0.1, I.s1.1, I.t1.1] 2, ![I.s0.1, I.t0.1, I.s1.1, I.t1.1] 3] =
        [I.s0.1, I.t0.1, I.s1.1, I.t1.1] := rfl
    rw [e] at ht
    rw [e2] at hf
    rw [hf] at ht
    exact absurd ht (by decide)

/-- What the thin solver must do here: solve instances with a side at most 10 or both at most 16. -/
def ThinOK16 (thin : Inst → Option (List Coord × List Coord)) : Prop :=
  ∀ J, J.WellFormed → Solvable J → (J.w ≤ 10 ∨ J.h ≤ 10 ∨ (J.w ≤ 16 ∧ J.h ≤ 16)) →
    ∃ p q, thin J = some (p, q) ∧ IsSolution J p q

theorem solveRec2_complete {thin : Inst → Option (List Coord × List Coord)} (hthin : ThinOK16 thin) :
    ∀ (n : ℕ) (I : Inst), I.WellFormed → Solvable I → I.w + I.h ≤ 2 * n →
      ∃ p q, solveRec2 thin n I = some (p, q) ∧ IsSolution I p q := by
  intro n
  induction n with
  | zero =>
    intro I hwf _ hn
    have := hwf.1
    unfold InBounds at this
    omega
  | succ n ih =>
    intro I hwf hS hn
    simp only [solveRec2]
    by_cases hthinI : I.w ≤ 10 ∨ I.h ≤ 10
    · rw [ite_t hthinI]
      obtain ⟨p, q, hpq, hsol⟩ := hthin I hwf hS (by tauto)
      rw [hpq, checkE_of_sol hsol]
      exact ⟨p, q, rfl, hsol⟩
    · rw [ite_f hthinI]
      have hI : InDom I := ⟨by omega, by omega, hwf⟩
      have hP : Passes I := (passes_iff_solvable I hwf hI.1 hI.2.1).2 hS
      -- one reduction step on an instance in the domain
      have step : ∀ (J : Inst) (d : ℕ), InDom J → Passes J → findRed2 J = some d →
          InDom (J.deleteAt d) ∧ Passes (J.deleteAt d) := by
        intro J d hJ hPJ hf
        rcases findRed2_some hf with hr | hr
        · exact ⟨inDom_deleteAt hJ hr, passX_all hJ hr hPJ⟩
        · exact ⟨inDom_deleteB hJ hr, passB hJ hr hPJ⟩
      cases hf : findRed2 I with
      | some d =>
        obtain ⟨hI', hP'⟩ := step I d hI hP hf
        have hS' := (passes_iff_solvable _ hI'.2.2 hI'.1 hI'.2.1).1 hP'
        have hw' : (I.deleteAt d).w = I.w - 2 := rfl
        have hh' : (I.deleteAt d).h = I.h := rfl
        obtain ⟨p, q, hpq, hsol⟩ := ih (I.deleteAt d) hI'.2.2 hS' (by rw [hw', hh']; omega)
        simp only [hpq]
        exact ⟨_, _, rfl, liftE_solF (findRed2_shape hf) hsol⟩
      | none =>
        have hIT := inDom_transpose hI
        have hPT := passT hI hP
        cases hfT : findRed2 I.transpose with
        | some d =>
          obtain ⟨hI', hP'⟩ := step I.transpose d hIT hPT hfT
          have hS' := (passes_iff_solvable _ hI'.2.2 hI'.1 hI'.2.1).1 hP'
          have hw' : (I.transpose.deleteAt d).w = I.h - 2 := rfl
          have hh' : (I.transpose.deleteAt d).h = I.w := rfl
          obtain ⟨p, q, hpq, hsol⟩ := ih (I.transpose.deleteAt d) hI'.2.2 hS' (by rw [hw', hh']; omega)
          simp only [hpq]
          exact ⟨_, _, rfl, (liftE_solF (findRed2_shape hfT) hsol).of_transpose⟩
        | none =>
          have hw16 : I.w ≤ 16 := leaf16 hwf hI.1 (findRed2_none hf)
          have hh16 : I.h ≤ 16 := leaf16 hIT.2.2 hIT.1 (findRed2_none hfT)
          obtain ⟨p, q, hpq, hsol⟩ := hthin I hwf hS (Or.inr (Or.inr ⟨hw16, hh16⟩))
          rw [hpq, checkE_of_sol hsol]
          exact ⟨p, q, rfl, hsol⟩

theorem solveZ2_sound (thin : Inst → Option (List Coord × List Coord)) {I : Inst}
    {p q : List Coord} (h : solveZ2 thin I = some (p, q)) : IsSolution I p q := by
  unfold solveZ2 at h
  split_ifs at h
  exact solveRec2_sound thin _ I p q h

theorem solveZ2_complete {thin : Inst → Option (List Coord × List Coord)} (hthin : ThinOK16 thin)
    {I : Inst} (hwf : I.WellFormed) (hS : Solvable I) : ∃ p q, solveZ2 thin I = some (p, q) := by
  obtain ⟨p, q, hpq, -⟩ := solveRec2_complete hthin (I.w + I.h) I hwf hS (by omega)
  exact ⟨p, q, by unfold solveZ2; rw [ite_t hwf]; exact hpq⟩

end ZZN

/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Constr.ThinWit
public import ZZN.Thin.SortKey

@[expose] public section

/-!
# The witness-carrying plug DP with duplicates removed by sorting

`thinSolveW2` is `thinSolveW` with `dedupKey` (keep the first entry of each state, by a scan
against the states seen so far) replaced by `dedupK Prod.fst` (sort by state, keep one entry per
state). The proofs of `thinSolveW` use only that duplicate removal keeps entries of its input and
every state of its input, so they carry over (`thinSolveW2_sound`, `thinSolveW2_complete`).
-/

namespace ZZN.Thin

open GridHam

/-- One stage, duplicates removed by sorting. -/
def stageW2 (J : Inst) (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (S : List (St × Wit)) (i : ℕ) :
    List (St × Wit) :=
  dedupK Prod.fst ((S.flatMap (stepCellW J a b (termAt tm (cell b i)) (cell b i).1 (cell b i).2)).filter
    fun sw => noExit a b sw.1)

def insideW2 (J : Inst) (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) : List (St × Wit) :=
  (List.range (a * b)).foldl (stageW2 J a b tm) [(([], 0), ([], ([], [])))]

def solveDP2 (J : Inst) : Option (List Coord × List Coord) :=
  ((insideW2 J J.w J.h (tmOf J)).find? fun sw => sw.1 == (([], 3) : St)).map fun sw => sw.2.2

/-- **The solver**, duplicates removed by sorting. -/
def thinSolveW2 (J : Inst) : Option (List Coord × List Coord) :=
  if J.h ≤ J.w then solveDP2 J
  else (solveDP2 J.transpose).map fun pq => (pq.1.map Prod.swap, pq.2.map Prod.swap)

section Stages

variable {a b : ℕ} {J : Inst} {tm : List ((ℕ × ℕ) × ℕ)}

/-- **The states of the witness-carrying DP are those of `insideF`**, stage by stage. -/
theorem foldW2_fst (n : ℕ) (s : St) :
    s ∈ ((List.range n).foldl (stageW2 J a b tm) [(([], 0), ([], ([], [])))]).map Prod.fst ↔
      s ∈ (List.range n).foldl (stageF a b tm) [([], 0)] := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    unfold stageW2 stageF stage
    rw [mem_dedupK_key, List.mem_filter, mem_normS, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨sw, hsw, rfl⟩
      rw [List.mem_filter, List.mem_flatMap] at hsw
      obtain ⟨⟨t, ht, hst⟩, hne⟩ := hsw
      refine ⟨⟨t.1, (ih t.1).mp (List.mem_map_of_mem ht), ?_⟩, hne⟩
      rw [← stepCellW_fst J]
      exact List.mem_map_of_mem hst
    · rintro ⟨⟨t, ht, hst⟩, hne⟩
      obtain ⟨tw, htw, rfl⟩ := List.mem_map.mp ((ih t).mpr ht)
      rw [← stepCellW_fst J] at hst
      obtain ⟨sw, hsw, rfl⟩ := List.mem_map.mp hst
      exact ⟨sw, List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨tw, htw, hsw⟩, hne⟩, rfl⟩

theorem mem_insideW2_fst {s : St} : s ∈ (insideW2 J a b tm).map Prod.fst ↔ s ∈ insideF a b tm :=
  foldW2_fst _ s

/-- **Every entry of the witness-carrying DP satisfies the witness invariant.** -/
theorem insideW2_WC (htm : ∀ y : Coord, y.1 < a → y.2 < b → termAt tm y = endCol J y) :
    ∀ sw ∈ insideW2 J a b tm, WC a b J (a * b) sw := by
  unfold insideW2
  suffices h : ∀ n, n ≤ a * b →
      ∀ sw ∈ (List.range n).foldl (stageW2 J a b tm) [(([], 0), ([], ([], [])))], WC a b J n sw from
    h _ (le_refl _)
  intro n
  induction n with
  | zero => intro _ sw hs; rw [List.mem_singleton.mp hs]; exact WC_zero
  | succ n ih =>
    intro hn sw hs
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hs
    unfold stageW2 at hs
    have hs := dedupK_sub Prod.fst hs
    rw [List.mem_filter, List.mem_flatMap] at hs
    obtain ⟨⟨t, ht, hst⟩, -⟩ := hs
    exact stepW_WC htm (by omega) (ih (by omega) t ht) hst

end Stages

/-! ### The solver is sound and complete -/

theorem solveDP2_sound {J : Inst} {p q : List Coord} (h : solveDP2 J = some (p, q)) : IsSolution J p q := by
  unfold solveDP2 at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨sw, hf, hpq⟩ := h
  have hmem := List.mem_of_find?_eq_some hf
  have hs : sw.1 = (([], 3) : St) := by simpa using List.find?_some hf
  obtain ⟨⟨-, -, -, hdone, hnod, hcov⟩, -, -⟩ := insideW2_WC (fun y _ _ => termAt_tmOf J y) sw hmem
  rw [hs] at hdone hnod hcov
  have hd : doneCols 3 = [0, 1] := by decide
  simp only [hd, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hdone
  obtain ⟨p0, p1⟩ := hdone
  simp only [ends2, ite_true, show (1 : ℕ) ≠ 0 by omega, ite_false] at p0 p1
  have e0 : dpOf sw.2.2 0 = p := by unfold dpOf; rw [hpq]; rfl
  have e1 : dpOf sw.2.2 1 = q := by unfold dpOf; rw [hpq]; rfl
  rw [e0] at p0
  rw [e1] at p1
  have ha : allOf (lookD sw.2.1) (dpOf sw.2.2) (([], 3) : St) = p ++ q := by
    simp [allOf, hd, e0, e1]
  rw [ha] at hnod hcov
  refine ⟨p0, p1, fun v hv hv' => List.disjoint_of_nodup_append hnod hv hv', fun v hv => ?_⟩
  exact List.mem_append.mp ((hcov v).mp (prI_all.mpr ⟨hv.1, hv.2⟩))

theorem solveDP2_complete {J : Inst} (hwf : J.WellFormed) (hS : Solvable J) : (solveDP2 J).isSome := by
  have h := (dpAcceptF_iff hwf).mpr hS
  unfold dpAcceptF at h
  rw [List.contains_iff_mem, ← mem_insideW2_fst (J := J)] at h
  obtain ⟨sw, hsw, hs⟩ := List.mem_map.mp h
  unfold solveDP2
  rw [Option.isSome_map, List.find?_isSome]
  exact ⟨sw, hsw, by simp [hs]⟩

/-- **The solver is sound**: whatever it returns is a solution (no well-formedness needed). -/
theorem thinSolveW2_sound {J : Inst} {p q : List Coord} (h : thinSolveW2 J = some (p, q)) :
    IsSolution J p q := by
  unfold thinSolveW2 at h
  split_ifs at h
  · exact solveDP2_sound h
  · rw [Option.map_eq_some_iff] at h
    obtain ⟨⟨p', q'⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    have := isSolution_transpose (solveDP2_sound h1)
    rwa [Inst.transpose_transpose] at this

/-- **The solver is complete**: a solvable well-formed instance gets a solution. -/
theorem thinSolveW2_complete {J : Inst} (hwf : J.WellFormed) (hS : Solvable J) : (thinSolveW2 J).isSome := by
  unfold thinSolveW2
  split_ifs
  · exact solveDP2_complete hwf hS
  · rw [Option.isSome_map]
    exact solveDP2_complete (wf_transpose hwf) (solvable_transpose hS)

/-- **The solver decides solvability.** -/
theorem thinSolveW2_isSome_iff {J : Inst} (hwf : J.WellFormed) : (thinSolveW2 J).isSome ↔ Solvable J := by
  refine ⟨fun h => ?_, thinSolveW2_complete hwf⟩
  obtain ⟨⟨p, q⟩, hpq⟩ := Option.isSome_iff_exists.mp h
  exact ⟨p, q, thinSolveW2_sound hpq⟩

end ZZN.Thin

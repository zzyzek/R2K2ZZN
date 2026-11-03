/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.TimedStatement
public import ZZN.Constr.ThinWit
public import ZZN.Timed.Thin

@[expose] public section

/-!
# The counted witness-carrying plug DP

`thinSolveWT` is the solver `Thin.thinSolveW` (`ZZN/Statement.lean`; lemmas in `ZZN/Constr/ThinWit.lean`) written with the counted
operations of `TimeM.lean`; `thinSolveWT_ret` shows it returns the same answer.

Beyond the helpers of `Timed/Thin.lean`, constant-time work used directly: `mkP`, `setDp`,
`colE`, `ends2`, `List.head?` (one pattern match), `degOf`, `ninOf`, `optsOf` (a list of at most
two lists of at most two numbers), and matches on options. Comparing two states (`stEqT`) is
written recursively and charged one step per matching piece; removing repeated states
(`dedupKeyT`) is written recursively with `lanyT` over the states already kept, so it is charged
quadratically.
-/

namespace ZZN.T

open ZZN ZZN.Thin GridHam

/-! ### Comparisons and duplicate removal -/





/-! ### Segments -/







/-! ### One cell -/




/-! ### The DP and the solver -/






/-! ### Same answer -/

lemma lbeqT_ret : ∀ l m : List ℕ, (lbeqT l m).ret = decide (l = m)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: l, y :: m => by
    unfold lbeqT
    by_cases h : x = y
    · subst h; simp [lbeqT_ret l m]
    · simp [h]

lemma stEqT_ret (s t : St) : (stEqT s t).ret = decide (s = t) := by
  simp only [stEqT, ret_bind, lbeqT_ret, ret_pure]
  rw [Bool.eq_iff_iff]
  simp [Prod.ext_iff]

lemma dedupKeyAuxT_ret : ∀ (seen : List St) (l : List (St × Wit)),
    (dedupKeyAuxT seen l).ret = dedupKeyAux seen l
  | _, [] => rfl
  | seen, x :: l => by
    have hm : (lanyT (fun t => stEqT t x.1) seen).ret = decide (x.1 ∈ seen) := by
      simp only [lanyT, stEqT_ret]
      rw [Bool.eq_iff_iff]
      simp
    unfold dedupKeyAuxT dedupKeyAux
    simp only [ret_bind, hm]
    by_cases h : x.1 ∈ seen
    · simp only [h, decide_true, ↓reduceIte]; exact dedupKeyAuxT_ret seen l
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, ret_bind, ret_pure]
      rw [dedupKeyAuxT_ret]

lemma dedupKeyT_ret (l : List (St × Wit)) : (dedupKeyT l).ret = dedupKey l := dedupKeyAuxT_ret [] l

lemma lookDT_ret (l : List (ℕ × List Coord)) (z : ℕ) : (lookDT l z).ret = lookD l z := by
  simp only [lookDT, ret_bind, lfindT, ret_pure, lookD]
  cases l.find? (fun q => q.1 == z) <;> rfl

lemma orientST_ret (e z : ℕ) (L : List Coord) : (orientST e z L).ret = orientS e z L := by
  unfold orientST orientS; split <;> rfl

lemma orientNT_ret (x y : ℕ) (L : List Coord) : (orientNT x y L).ret = orientN x y L := by
  unfold orientNT orientN; split <;> rfl

lemma orientPT_ret (J : Inst) (col : ℕ) (L : List Coord) : (orientPT J col L).ret = orientP J col L := by
  unfold orientPT orientP; split <;> rfl

lemma segNewT_ret (b r c : ℕ) (w : List (ℕ × List Coord)) (pu pl : Option ℕ) :
    (segNewT b r c w pu pl).ret = segNew b r c (lookD w) pu pl := by
  cases pu <;> cases pl <;>
    simp [segNewT, segNew, lookDT_ret, orientST_ret, lappendT, lreverseT]

lemma closeWitT_ret (J : Inst) (a b x y : ℕ) (Ln : List Coord) (sgR : List (ℕ × List Coord))
    (d : List Coord × List Coord) : (closeWitT J a b x y Ln sgR d).ret = closeWit J a b x y Ln sgR d := by
  unfold closeWitT closeWit
  split <;> simp [orientPT_ret, orientNT_ret]

lemma closeOptGT_ret (a b : ℕ) (ins outs rest : List ℕ) (dn : ℕ) :
    (closeOptGT a b ins outs rest dn).ret =
      (match ins ++ outs with
        | [x, y] => (closeP a b x y rest dn).map fun s' => ((x, y), s')
        | _ => none) := by
  simp only [closeOptGT, ret_bind, lappendT]
  split
  · next _ x y h =>
    rw [h]
    simp only [ret_bind, closePT_ret, ret_pure]
  · next _ h => simp [h, ret_pure]
  · next _ _ h => simp [h, ret_pure]
  · next _ _ _ _ _ h => simp [h, ret_pure]

lemma stepTailGT_ret (a b : ℕ) (e : Option ℕ) (r c : ℕ) (s : St) :
    (stepTailGT a b e r c s (puOf s r c) (plOf b s c)).ret = stepCellG a b e r c s := by
  unfold stepTailGT stepCellG
  split_ifs
  · rfl
  · rfl
  · simp only [ret_bind, lfilterMapT, closeOptGT_ret, closeOuts, restT_ret, endsL_eq, insOf]
    rfl

lemma lookT_pu (s : St) (r c : ℕ) : (lookT (r == 0) c s.1).ret = puOf s r c := by
  rw [lookT_ret]; simp [puOf]

lemma stepCellWT_ret (J : Inst) (a b : ℕ) (e : Option ℕ) (r c : ℕ) (sw : St × Wit) :
    (stepCellWT J a b e r c sw).ret = stepCellW J a b e r c sw := by
  simp only [stepCellWT, ret_bind, lookT_pu]
  have e1 : puOf sw.1 c b = plOf b sw.1 c := rfl
  rw [e1]
  simp only [stepCellW, segNewT_ret, stepTailGT_ret, lmapT, closeWitT_ret, ret_bind, ret_pure, lfilterT,
    dropKeys]

lemma stageWT_ret (J : Inst) (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (S : List (St × Wit)) (i : ℕ) :
    (stageWT J a b tm S i).ret = stageW J a b tm S i := by
  simp only [stageWT, stageW, ret_bind, dedupKeyT_ret, lfilterT, lflatMapT, termAt_eq, stepCellWT_ret,
    noExitT, lallT, ret_pure, noExit]

lemma insideWT_ret (J : Inst) (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) :
    (insideWT J a b tm).ret = insideW J a b tm := by
  simp only [insideWT, insideW, ret_bind, rangeT, ret_lfoldlT, stageWT_ret]

lemma solveDPT_ret (J : Inst) : (solveDPT J).ret = solveDP J := by
  simp only [solveDPT, solveDP, ret_bind, insideWT_ret, lfindT, stEqT_ret, ret_pure]
  have : (fun sw : St × Wit => decide (sw.1 = (([], 3) : St))) = fun sw => sw.1 == (([], 3) : St) := by
    funext sw; rw [Bool.eq_iff_iff]; simp
  rw [this]
  cases (insideW J J.w J.h (tmOf J)).find? (fun sw => sw.1 == (([], 3) : St)) <;> rfl

/-- **The counted solver returns the solver's answer.** -/
theorem thinSolveWT_ret (J : Inst) : (thinSolveWT J).ret = Thin.thinSolveW J := by
  unfold thinSolveWT thinSolveW
  split
  · exact solveDPT_ret J
  · simp only [ret_bind, solveDPT_ret]
    cases solveDP J.transpose with
    | none => rfl
    | some pq => simp [swapPairT, lmapT]

end ZZN.T

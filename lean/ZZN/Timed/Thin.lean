-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.TimedStatement
import ZZN.Thin.Fast
import ZZN.Timed.TimeM

/-!
# The counted plug DP

`thinBFT` is the plug DP of `ZZN/Thin/Fast.lean` (`thinBF`) written with the counted operations.
One step differs: after each cell the state list is cleaned with `ldedupT` (every duplicate
removed, cost `|l|² + 1`) instead of the merge sort with adjacent deduplication (`normS`). Both
keep exactly the same states, so the final answer is the same (`thinBFT_ret`).

Constant-time helpers used directly: arithmetic on numbers, `hasEnd`, `other`, `mkP`, `termE`,
`isTerm`, `colE`, `exitE`, `okEnd`, `cell`, and pattern matches on options and on lists of at most
five elements.
-/

namespace ZZN.T

open ZZN ZZN.Thin GridHam

/-! ### One cell -/


@[simp] lemma insSortedT_ret (x : ℕ) : ∀ l : List ℕ, (insSortedT x l).ret = insSorted x l
  | [] => rfl
  | y :: l => by
    unfold insSortedT insSorted
    split_ifs
    · rfl
    · simp only [ret_bind]; rw [insSortedT_ret x l]


@[simp] lemma closePT_ret (a b x y : ℕ) (rest : List ℕ) (dn : ℕ) :
    (closePT a b x y rest dn).ret = closeP a b x y rest dn := by
  unfold closePT closeP
  split <;> simp


lemma restT_ret (ps : List ℕ) (pu pl : Option ℕ) :
    (restT ps pu pl).ret = (if pu.isSome then (if pl.isSome then (ps.erase (pu.getD 0)).erase (pl.getD 0)
      else ps.erase (pu.getD 0)) else (if pl.isSome then ps.erase (pl.getD 0) else ps)) := by
  cases pu <;> cases pl <;> rfl



lemma closeOptT_ret (a b : ℕ) (ins outs : List ℕ) (rest : List ℕ) (dn : ℕ) :
    (closeOptT a b ins outs rest dn).ret =
      (match ins ++ outs with | [x, y] => closeP a b x y rest dn | _ => none) := by
  simp only [closeOptT, ret_bind, lappendT]
  split <;> simp_all

lemma endsL_eq (a b c : ℕ) (e pu pl : Option ℕ) :
    endsL a b c e pu pl = (pu.map (other c)).toList ++ (pl.map (other b)).toList ++
      (e.map (termE a b)).toList := by
  cases pu <;> cases pl <;> cases e <;> rfl


/-- `stepCell` after the two lookups, as a function of their results. -/
def stepCellFrom (a b : ℕ) (e : Option ℕ) (r c : ℕ) (s : St) (pu pl : Option ℕ) : List St :=
  let ps := s.1
  let down := if r + 1 < a then c else exitE b (a + (b - 1 - c))
  let right := if c + 1 < b then b else exitE b r
  let nin := (if pu.isSome then 1 else 0) + (if pl.isSome then 1 else 0)
  let deg := if e.isSome then 1 else 2
  if deg < nin then [] else
  if pu.isSome && pu == pl then [] else
  let rest := if pu.isSome then (if pl.isSome then (ps.erase (pu.getD 0)).erase (pl.getD 0)
    else ps.erase (pu.getD 0)) else (if pl.isSome then ps.erase (pl.getD 0) else ps)
  let ins := (pu.map (other c)).toList ++ (pl.map (other b)).toList ++ (e.map (termE a b)).toList
  let opts : List (List ℕ) := match deg - nin with
    | 0 => [[]]
    | 1 => [[down], [right]]
    | _ => [[down, right]]
  opts.filterMap fun outs =>
    match ins ++ outs with
    | [x, y] => closeP a b x y rest s.2
    | _ => none

lemma stepCell_eq (a b : ℕ) (e : Option ℕ) (r c : ℕ) (s : St) :
    stepCell a b e r c s = stepCellFrom a b e r c s (if r = 0 then none else s.1.find? (hasEnd c))
      (if c = 0 then none else s.1.find? (hasEnd b)) := rfl


lemma stepTailT_ret (a b : ℕ) (e : Option ℕ) (r c : ℕ) (s : St) (pu pl : Option ℕ) :
    (stepTailT a b e r c s pu pl).ret = stepCellFrom a b e r c s pu pl := by
  unfold stepTailT stepCellFrom
  dsimp only
  generalize (if e.isSome = true then 1 else 2) = deg
  generalize (if pu.isSome = true then 1 else 0) + (if pl.isSome = true then 1 else 0) = nin
  by_cases h1 : deg < nin
  · simp only [h1, ↓reduceIte]; rfl
  · simp only [h1, ↓reduceIte]
    by_cases h2 : (pu.isSome && pu == pl) = true
    · simp only [h2, ↓reduceIte]; rfl
    · simp only [Bool.not_eq_true] at h2
      simp only [h2, Bool.false_eq_true, ↓reduceIte]
      simp only [ret_bind, restT_ret, lfilterMapT, closeOptT_ret, endsL_eq]
      rfl


lemma lookT_ret (skip : Bool) (k : ℕ) (ps : List ℕ) :
    (lookT skip k ps).ret = if skip then none else ps.find? (hasEnd k) := by
  unfold lookT; split <;> rfl


lemma stepCellT_ret (a b : ℕ) (e : Option ℕ) (r c : ℕ) (s : St) :
    (stepCellT a b e r c s).ret = stepCell a b e r c s := by
  rw [stepCell_eq]
  simp only [stepCellT, ret_bind, stepTailT_ret, lookT_ret, beq_iff_eq]

/-! ### The DP -/







/-! ### Same answer -/

lemma termAt_eq (tm : List ((ℕ × ℕ) × ℕ)) (x : ℕ × ℕ) :
    optSnd (lfindT (fun q => (pure (q.1 == x) : TimeM Bool)) tm).ret = termAt tm x := by
  simp only [lfindT, termAt, ret_pure, optSnd]
  cases tm.find? (fun q => q.1 == x) <;> rfl

lemma mem_stageT (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (S : List St) (i : ℕ) (s : St) :
    s ∈ (stageT a b tm S i).ret ↔
      noExit a b s = true ∧ ∃ s0 ∈ S, s ∈ stepCell a b (termAt tm (cell b i)) (cell b i).1 (cell b i).2 s0 := by
  simp only [stageT, ret_bind, lfilterT, ldedupT, lflatMapT, List.mem_filter, List.mem_dedup,
    List.mem_flatMap, termAt_eq, stepCellT_ret, noExitT, lallT, ret_pure, noExit]
  tauto

lemma mem_stageF (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (S : List St) (i : ℕ) (s : St) :
    s ∈ stageF a b tm S i ↔
      noExit a b s = true ∧ ∃ s0 ∈ S, s ∈ stepCell a b (termAt tm (cell b i)) (cell b i).1 (cell b i).2 s0 := by
  simp only [stageF, stage, List.mem_filter, mem_normS, List.mem_flatMap]
  tauto

lemma insideT_mem (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) :
    ∀ n (s : St), s ∈ (List.range n).foldl (fun S i => (stageT a b tm S i).ret) [([], 0)] ↔
      s ∈ (List.range n).foldl (stageF a b tm) [([], 0)] := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [mem_stageT, mem_stageF]
    constructor
    · rintro ⟨h1, s0, h2, h3⟩; exact ⟨h1, s0, (ih s0).1 h2, h3⟩
    · rintro ⟨h1, s0, h2, h3⟩; exact ⟨h1, s0, (ih s0).2 h2, h3⟩

@[simp] lemma dpAcceptT_ret (J : Inst) : (dpAcceptT J).ret = dpAcceptF J := by
  simp only [dpAcceptT, insideT, ret_bind, rangeT, ret_lfoldlT, lcontainsT, dpAcceptF, insideF]
  have := insideT_mem J.w J.h (tmOf J) (J.w * J.h) ([], 3)
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
  exact this

@[simp] lemma thinBFT_ret (J : Inst) : (thinBFT J).ret = thinBF J := by
  unfold thinBFT thinBF; split <;> simp

end ZZN.T

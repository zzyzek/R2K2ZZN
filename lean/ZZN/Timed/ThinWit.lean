-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Constr.ThinWit
import ZZN.Timed.Thin

/-!
# The counted witness-carrying plug DP

`thinSolveWT` is the solver `Thin.thinSolveW` (`ZZN/Constr/ThinWit.lean`) written with the counted
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

/-- Equality of two lists of numbers, one step per matching entry. -/
def lbeqT : List ℕ → List ℕ → TimeM Bool
  | [], [] => pure true
  | x :: l, y :: m => if x = y then do
      let r ← lbeqT l m
      ⟨r, 1⟩
    else pure false
  | _, _ => pure false

/-- Equality of two states. -/
def stEqT (s t : St) : TimeM Bool := do
  let r ← lbeqT s.1 t.1
  pure (r && decide (s.2 = t.2))

/-- Keep the first entry of each state not among `seen`. -/
def dedupKeyAuxT : List St → List (St × Wit) → TimeM (List (St × Wit))
  | _, [] => pure []
  | seen, x :: l => do
      let m ← lanyT (fun t => stEqT t x.1) seen
      if m then dedupKeyAuxT seen l else do
        let r ← dedupKeyAuxT (x.1 :: seen) l
        pure (x :: r)

def dedupKeyT (l : List (St × Wit)) : TimeM (List (St × Wit)) := dedupKeyAuxT [] l

/-! ### Segments -/

/-- The stored segment of piece `z` (`[]` if none). -/
def lookDT (l : List (ℕ × List Coord)) (z : ℕ) : TimeM (List Coord) := do
  let o ← lfindT (fun q => pure (q.1 == z)) l
  pure (match o with | some q => q.2 | none => [])

def orientST (e z : ℕ) (L : List Coord) : TimeM (List Coord) :=
  if lo z = e then lreverseT L else pure L

def orientNT (x y : ℕ) (L : List Coord) : TimeM (List Coord) :=
  if x ≤ y then pure L else lreverseT L

def orientPT (J : Inst) (col : ℕ) (L : List Coord) : TimeM (List Coord) :=
  if L.head? = some (ends2 J col).1 then pure L else lreverseT L

/-- The new segment through cell `(r, c)`. -/
def segNewT (b r c : ℕ) (w : List (ℕ × List Coord)) (pu pl : Option ℕ) : TimeM (List Coord) :=
  match pu, pl with
  | some zu, some zl => do
    let Lu0 ← lookDT w zu
    let Lu ← orientST c zu Lu0
    let Ll0 ← lookDT w zl
    let Ll ← orientST b zl Ll0
    let t ← lappendT Lu [(r, c)]
    let rl ← lreverseT Ll
    lappendT t rl
  | some zu, none => do
    let Lu0 ← lookDT w zu
    let Lu ← orientST c zu Lu0
    lappendT Lu [(r, c)]
  | none, some zl => do
    let Ll0 ← lookDT w zl
    let Ll ← orientST b zl Ll0
    lappendT Ll [(r, c)]
  | none, none => pure [(r, c)]

def closeWitT (J : Inst) (a b x y : ℕ) (Ln : List Coord) (sgR : List (ℕ × List Coord))
    (d : List Coord × List Coord) : TimeM Wit :=
  if isTerm a b x && isTerm a b y then do
    let P ← orientPT J (colE a b x) Ln
    pure (sgR, setDp d (colE a b x) P)
  else do
    let L ← orientNT x y Ln
    pure ((mkP x y, L) :: sgR, d)

/-! ### One cell -/

def closeOptGT (a b : ℕ) (ins outs rest : List ℕ) (dn : ℕ) : TimeM (Option ((ℕ × ℕ) × St)) := do
  let l ← lappendT ins outs
  match l with
  | [x, y] => do
    let o ← closePT a b x y rest dn
    pure (match o with | some s' => some ((x, y), s') | none => none)
  | _ => pure none

/-- `stepCellG` after the two lookups. -/
def stepTailGT (a b : ℕ) (e : Option ℕ) (r c : ℕ) (s : St) (pu pl : Option ℕ) :
    TimeM (List ((ℕ × ℕ) × St)) :=
  if degOf e < ninOf pu pl then pure [] else
  if pu.isSome && pu == pl then pure [] else do
  let rest ← restT s.1 pu pl
  lfilterMapT (fun outs => closeOptGT a b (endsL a b c e pu pl) outs rest s.2) (optsOf a b r c e pu pl)

def stepCellWT (J : Inst) (a b : ℕ) (e : Option ℕ) (r c : ℕ) (sw : St × Wit) :
    TimeM (List (St × Wit)) := do
  let pu ← lookT (r == 0) c sw.1.1
  let pl ← lookT (c == 0) b sw.1.1
  let Ln ← segNewT b r c sw.2.1 pu pl
  let sgR ← lfilterT (fun q => pure (pu != some q.1 && pl != some q.1)) sw.2.1
  let G ← stepTailGT a b e r c sw.1 pu pl
  lmapT (fun g => do
    let w ← closeWitT J a b g.1.1 g.1.2 Ln sgR sw.2.2
    pure (g.2, w)) G

/-! ### The DP and the solver -/

def stageWT (J : Inst) (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (S : List (St × Wit)) (i : ℕ) :
    TimeM (List (St × Wit)) := do
  let o ← lfindT (fun q => pure (q.1 == cell b i)) tm
  let e := optSnd o
  let l ← lflatMapT (stepCellWT J a b e (cell b i).1 (cell b i).2) S
  let f ← lfilterT (fun sw => noExitT a b sw.1) l
  dedupKeyT f

def insideWT (J : Inst) (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) : TimeM (List (St × Wit)) := do
  let is ← rangeT (a * b)
  lfoldlT (stageWT J a b tm) [(([], 0), ([], ([], [])))] is

def solveDPT (J : Inst) : TimeM (Option (List Coord × List Coord)) := do
  let S ← insideWT J J.w J.h (tmOf J)
  let o ← lfindT (fun sw => stEqT sw.1 ([], 3)) S
  pure (match o with | some sw => some sw.2.2 | none => none)

def swapPairT (pq : List Coord × List Coord) : TimeM (List Coord × List Coord) := do
  let p ← lmapT (fun x => pure x.swap) pq.1
  let q ← lmapT (fun x => pure x.swap) pq.2
  pure (p, q)

/-- **The counted solver.** -/
def thinSolveWT (J : Inst) : TimeM (Option (List Coord × List Coord)) :=
  if J.h ≤ J.w then solveDPT J else do
    let o ← solveDPT J.transpose
    match o with
    | some pq => do
      let r ← swapPairT pq
      pure (some r)
    | none => pure none

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
  · simp only [ret_bind, closePT_ret, ret_pure]
    cases closeP a b _ _ rest dn <;> rfl
  · rfl

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

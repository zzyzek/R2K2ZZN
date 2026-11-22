/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Timed.SortKeyG
public import ZZN.Timed.ThinWit
public import ZZN.Constr.ThinWit2

@[expose] public section

/-!
# The witness-carrying plug DP with segments as trees

`thinSolveWT` copies a segment (a list of up to `a b` cells) whenever a cell extends it, so one
stage costs `O(a b)` per state. Here a segment is a tree (`Rp`): append and reverse build one node,
so a cell costs `O(1)` beyond the piece-list work. A completed path is stored unoriented and
oriented once, when the answer is read out; the trees are flattened only then (`flatT`, one step
per node).

Flattening every stored tree and orienting the completed paths (`flatE`) maps each stage of this
DP to the corresponding stage of `stageW2` (`stageWRT_flat`), so `thinSolveWRT` returns
`thinSolveW2` (`thinSolveWRT_ret`).

Constant-time work used directly, as in `Timed/ThinWit.lean`: building a tree node, `mkP`, `colE`,
`degOf`, `ninOf`, `optsOf`, matches on options.
-/

namespace ZZN.T

open ZZN ZZN.Thin GridHam

/-- A segment as a tree: empty, one cell, concatenation, reversal. -/
inductive Rp where
  | nil : Rp
  | leaf : Coord → Rp
  | app : Rp → Rp → Rp
  | rev : Rp → Rp

namespace Rp

/-- The cells of a tree, in order. -/
def toL : Rp → List Coord
  | nil => []
  | leaf x => [x]
  | app l r => l.toL ++ r.toL
  | rev r => r.toL.reverse

/-- The number of nodes. -/
def size : Rp → ℕ
  | nil => 1
  | leaf _ => 1
  | app l r => 1 + l.size + r.size
  | rev r => 1 + r.size

end Rp

/-- Segments of the open pieces as trees; completed paths as unoriented trees. -/
abbrev WitR := List (ℕ × Rp) × (Rp × Rp)

/-- The list witness of a tree witness: flatten, orient the completed paths. -/
def flatW (J : Inst) (w : WitR) : Wit :=
  (w.1.map (fun q => (q.1, q.2.toL)), (orientP J 0 w.2.1.toL, orientP J 1 w.2.2.toL))

/-- An entry with its witness flattened. -/
def flatE (J : Inst) (sw : St × WitR) : St × Wit := (sw.1, flatW J sw.2)

/-! ### Counted operations -/

/-- The stored tree of piece `z` (`nil` if none). -/
def lookDRT (l : List (ℕ × Rp)) (z : ℕ) : TimeM Rp := do
  let o ← lfindT (fun q => pure (q.1 == z)) l
  pure (match o with | some q => q.2 | none => Rp.nil)

def orientSR (e z : ℕ) (R : Rp) : Rp := if lo z = e then Rp.rev R else R

def orientNR (x y : ℕ) (R : Rp) : Rp := if x ≤ y then R else Rp.rev R

def setDpR (d : Rp × Rp) (col : ℕ) (P : Rp) : Rp × Rp := if col = 0 then (P, d.2) else (d.1, P)

/-- The new segment through cell `(r, c)`, as a tree. -/
def segNewRT (b r c : ℕ) (w : List (ℕ × Rp)) (pu pl : Option ℕ) : TimeM Rp :=
  match pu, pl with
  | some zu, some zl => do
    let Lu ← lookDRT w zu
    let Ll ← lookDRT w zl
    pure (Rp.app (Rp.app (orientSR c zu Lu) (Rp.leaf (r, c))) (Rp.rev (orientSR b zl Ll)))
  | some zu, none => do
    let Lu ← lookDRT w zu
    pure (Rp.app (Rp.app (orientSR c zu Lu) (Rp.leaf (r, c))) (Rp.rev Rp.nil))
  | none, some zl => do
    let Ll ← lookDRT w zl
    pure (Rp.app (orientSR b zl Ll) (Rp.leaf (r, c)))
  | none, none => pure (Rp.app Rp.nil (Rp.leaf (r, c)))

def closeWitR (a b x y : ℕ) (Ln : Rp) (sgR : List (ℕ × Rp)) (d : Rp × Rp) : WitR :=
  if isTerm a b x && isTerm a b y then (sgR, setDpR d (colE a b x) Ln)
  else ((mkP x y, orientNR x y Ln) :: sgR, d)

/-- **One cell of the tree-witness DP.** -/
def stepCellWRT (a b : ℕ) (e : Option ℕ) (r c : ℕ) (sw : St × WitR) : TimeM (List (St × WitR)) := do
  let pu ← lookT (r == 0) c sw.1.1
  let pl ← lookT (c == 0) b sw.1.1
  let Ln ← segNewRT b r c sw.2.1 pu pl
  let sgR ← lfilterT (fun q => pure (pu != some q.1 && pl != some q.1)) sw.2.1
  let G ← stepTailGT a b e r c sw.1 pu pl
  lmapT (fun g => pure (g.2, closeWitR a b g.1.1 g.1.2 Ln sgR sw.2.2)) G

def stageWRT (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (S : List (St × WitR)) (i : ℕ) :
    TimeM (List (St × WitR)) := do
  let o ← lfindT (fun q => pure (q.1 == cell b i)) tm
  let e := optSnd o
  let l ← lflatMapT (stepCellWRT a b e (cell b i).1 (cell b i).2) S
  let f ← lfilterT (fun sw => noExitT a b sw.1) l
  dedupGT f

def insideWRT (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) : TimeM (List (St × WitR)) := do
  let is ← rangeT (a * b)
  lfoldlT (stageWRT a b tm) [(([], 0), ([], (Rp.nil, Rp.nil)))] is

/-- Flatten a tree, reversed if `rv`, in front of `acc`: one step per node. -/
def flatAccT : Rp → Bool → List Coord → TimeM (List Coord)
  | Rp.nil, _, acc => ⟨acc, 1⟩
  | Rp.leaf x, _, acc => ⟨x :: acc, 1⟩
  | Rp.app l r, rv, acc => do
    let t ← (if rv then flatAccT l true acc else flatAccT r false acc)
    let u ← (if rv then flatAccT r true t else flatAccT l false t)
    ⟨u, 1⟩
  | Rp.rev r, rv, acc => do
    let t ← flatAccT r (!rv) acc
    ⟨t, 1⟩

def flatT (R : Rp) : TimeM (List Coord) := flatAccT R false []

def solveDPRT (J : Inst) : TimeM (Option (List Coord × List Coord)) := do
  let S ← insideWRT J.w J.h (tmOf J)
  let o ← lfindT (fun sw => stEqT sw.1 ([], 3)) S
  match o with
  | some sw => do
    let p0 ← flatT sw.2.2.1
    let p ← orientPT J 0 p0
    let q0 ← flatT sw.2.2.2
    let q ← orientPT J 1 q0
    pure (some (p, q))
  | none => pure none

/-- **The counted solver with tree segments.** -/
def thinSolveWRT (J : Inst) : TimeM (Option (List Coord × List Coord)) :=
  if J.h ≤ J.w then solveDPRT J else do
    let o ← solveDPRT J.transpose
    match o with
    | some pq => do
      let r ← swapPairT pq
      pure (some r)
    | none => pure none

/-! ### Same answer -/

lemma flatAccT_ret : ∀ (R : Rp) (rv : Bool) (acc : List Coord),
    (flatAccT R rv acc).ret = (if rv then R.toL.reverse else R.toL) ++ acc
  | Rp.nil, rv, acc => by cases rv <;> simp [flatAccT, Rp.toL]
  | Rp.leaf x, rv, acc => by cases rv <;> simp [flatAccT, Rp.toL]
  | Rp.app l r, rv, acc => by
    cases rv <;> simp [flatAccT, Rp.toL, flatAccT_ret l, flatAccT_ret r]
  | Rp.rev r, rv, acc => by
    cases rv <;> simp [flatAccT, Rp.toL, flatAccT_ret r]

lemma flatT_ret (R : Rp) : (flatT R).ret = R.toL := by simp [flatT, flatAccT_ret]

lemma lookDRT_ret (l : List (ℕ × Rp)) (z : ℕ) :
    ((lookDRT l z).ret).toL = lookD (l.map (fun q => (q.1, q.2.toL))) z := by
  simp only [lookDRT, ret_bind, lfindT, ret_pure, lookD, List.find?_map]
  cases h : l.find? (fun q => q.1 == z) <;> simp [h, Rp.toL]

lemma orientSR_toL (e z : ℕ) (R : Rp) : (orientSR e z R).toL = orientS e z R.toL := by
  unfold orientSR orientS; split <;> simp [Rp.toL]

lemma orientNR_toL (x y : ℕ) (R : Rp) : (orientNR x y R).toL = orientN x y R.toL := by
  unfold orientNR orientN; split <;> simp [Rp.toL]

lemma segNewRT_ret (b r c : ℕ) (w : List (ℕ × Rp)) (pu pl : Option ℕ) :
    ((segNewRT b r c w pu pl).ret).toL =
      segNew b r c (lookD (w.map (fun q => (q.1, q.2.toL)))) pu pl := by
  cases pu <;> cases pl <;>
    simp [segNewRT, segNew, Rp.toL, orientSR_toL, ← lookDRT_ret]

lemma orientP_ne {J : Inst} {col : ℕ} (h : col ≠ 0) (L : List Coord) : orientP J col L = orientP J 1 L := by
  unfold orientP ends2; simp [h]

lemma closeWitR_flat (J : Inst) (a b x y : ℕ) (Ln : Rp) (sgR : List (ℕ × Rp)) (d : Rp × Rp) :
    flatW J (closeWitR a b x y Ln sgR d) =
      closeWit J a b x y Ln.toL (sgR.map (fun q => (q.1, q.2.toL))) (flatW J ([], d)).2 := by
  unfold closeWitR closeWit flatW
  split
  · unfold setDpR setDp
    split_ifs with h
    · simp [h]
    · simp [orientP_ne h]
  · simp [orientNR_toL]

lemma stepCellWRT_flat (J : Inst) (a b : ℕ) (e : Option ℕ) (r c : ℕ) (sw : St × WitR) :
    ((stepCellWRT a b e r c sw).ret).map (flatE J) = stepCellW J a b e r c (flatE J sw) := by
  simp only [stepCellWRT, ret_bind, lookT_pu]
  have e1 : puOf sw.1 c b = plOf b sw.1 c := rfl
  rw [e1, stepTailGT_ret]
  simp only [stepCellW, lmapT, ret_pure, lfilterT, List.map_map, flatE, Function.comp_def]
  congr 1
  funext g
  rw [closeWitR_flat, segNewRT_ret]
  simp only [dropKeys, flatW]
  rw [List.filter_map]
  rfl

section SortMap
variable {α β : Type} (g : α → β) (k : α → St) (k' : β → St) (hk : ∀ x, k' (g x) = k x)
include hk

omit hk in
lemma splitK_map : ∀ l : List α, splitK (l.map g) = ((splitK l).1.map g, (splitK l).2.map g)
  | [] => rfl
  | [_] => rfl
  | x :: y :: l => by simp [splitK, splitK_map l]

lemma msortK_map : ∀ (f : ℕ) (l : List α), msortK k' f (l.map g) = (msortK k f l).map g
  | 0, l => rfl
  | f + 1, l => by
    simp only [msortK, List.length_map]
    split_ifs
    · rfl
    · rw [splitK_map g, msortK_map f, msortK_map f, List.map_merge]
      intro x _ y _
      simp [leK, hk]

lemma dedupAdjK_map : ∀ l : List α, dedupAdjK k' (l.map g) = (dedupAdjK k l).map g
  | x :: y :: l => by
    simp only [List.map_cons]
    rw [dedupAdjK, dedupAdjK, hk, hk]
    split_ifs
    · exact dedupAdjK_map (x :: l)
    · simp only [List.map_cons]; rw [← dedupAdjK_map (y :: l)]; rfl
  | [] => by simp [dedupAdjK]
  | [_] => by simp [dedupAdjK]
termination_by l => l.length

lemma dedupK_map (l : List α) : dedupK k' (l.map g) = (dedupK k l).map g := by
  unfold dedupK
  rw [List.length_map, msortK_map g k k' hk, dedupAdjK_map g k k' hk]

end SortMap

lemma stageWRT_flat (J : Inst) (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (S : List (St × WitR)) (i : ℕ) :
    ((stageWRT a b tm S i).ret).map (flatE J) = stageW2 J a b tm (S.map (flatE J)) i := by
  simp only [stageWRT, stageW2, ret_bind, dedupGT_ret, lfilterT, lflatMapT, termAt_eq, noExitT, lallT,
    ret_pure, noExit]
  rw [← dedupK_map (flatE J) Prod.fst Prod.fst (fun _ => rfl)]
  congr 1
  have hfm : List.flatMap (stepCellW J a b (termAt tm (cell b i)) (cell b i).1 (cell b i).2) (S.map (flatE J)) =
      (List.flatMap (fun x => (stepCellWRT a b (termAt tm (cell b i)) (cell b i).1 (cell b i).2 x).ret) S).map
        (flatE J) := by
    simp only [List.flatMap_map, List.map_flatMap]
    congr 1
    funext sw
    exact (stepCellWRT_flat J a b _ _ _ sw).symm
  rw [hfm, List.filter_map]
  rfl

lemma foldWR_flat (J : Inst) (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (n : ℕ) :
    ((List.range n).foldl (fun S i => (stageWRT a b tm S i).ret)
        [(([], 0), ([], (Rp.nil, Rp.nil)))]).map (flatE J) =
      (List.range n).foldl (stageW2 J a b tm) [(([], 0), ([], ([], [])))] := by
  induction n with
  | zero => simp [flatE, flatW, Rp.toL, orientP]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, List.foldl_append,
      List.foldl_cons, List.foldl_nil, stageWRT_flat, ih]

lemma insideWRT_flat (J : Inst) (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) :
    ((insideWRT a b tm).ret).map (flatE J) = insideW2 J a b tm := by
  simp only [insideWRT, insideW2, ret_bind, rangeT, ret_lfoldlT]
  exact foldWR_flat J a b tm _

lemma solveDPRT_ret (J : Inst) : (solveDPRT J).ret = solveDP2 J := by
  simp only [solveDPRT, solveDP2, ret_bind, lfindT, stEqT_ret]
  rw [← insideWRT_flat J, List.find?_map]
  have : (fun sw : St × WitR => decide (sw.1 = (([], 3) : St))) =
      (fun sw : St × Wit => sw.1 == (([], 3) : St)) ∘ flatE J := by
    funext sw; rw [Bool.eq_iff_iff]; simp [flatE]
  rw [this]
  cases ((insideWRT J.w J.h (tmOf J)).ret).find? ((fun sw : St × Wit => sw.1 == (([], 3) : St)) ∘ flatE J) with
  | none => rfl
  | some sw => simp [flatT_ret, orientPT_ret, flatE, flatW]

/-- **The tree-witness solver returns the solver's answer.** -/
theorem thinSolveWRT_ret (J : Inst) : (thinSolveWRT J).ret = Thin.thinSolveW2 J := by
  unfold thinSolveWRT thinSolveW2
  split
  · exact solveDPRT_ret J
  · simp only [ret_bind, solveDPRT_ret]
    cases solveDP2 J.transpose with
    | none => rfl
    | some pq => simp [swapPairT, lmapT]

end ZZN.T

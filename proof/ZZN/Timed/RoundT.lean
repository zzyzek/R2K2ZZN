/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Constr.RoundCount
public import ZZN.Timed.BandL
public import ZZN.Timed.Construct

@[expose] public section

/-!
# The counted block construction: definitions and return values

`wideBandT` counts the wide band `innerLift`. It finds the seed as `bandExtLT` does, then builds a
table of the attached rows of every covered row once (`tblT`), so each crossing reads its rows
with one lookup. `edgeLiftT` and `edgeLiftLT` count the edge lifts, `solveRT` the construction
`solveR`.
-/

namespace ZZN.T

open ZZN GridHam

/-! ### Definitions -/

/-- Row `y` is covered: a crossing, or a flip row. -/
def cvT (cr : List ℕ) (R : ℕ) (fl : Bool) (y : ℕ) : TimeM Bool := do
  let c ← lcontainsT cr y
  pure (c || (fl && (y + 1 == R || y == R)))

def runDnT (cv : ℕ → TimeM Bool) : ℕ → TimeM (List ℕ)
  | 0 => pure []
  | n + 1 => do
    let c ← cv n
    if c then pure [] else do
      let rest ← runDnT cv n
      ⟨n :: rest, 1⟩

def runUpFT (cv : ℕ → TimeM Bool) : ℕ → ℕ → TimeM (List ℕ)
  | 0, _ => pure []
  | k + 1, y => do
    let c ← cv y
    if c then pure [] else do
      let rest ← runUpFT cv k (y + 1)
      ⟨y :: rest, 1⟩

def attWT (cv : ℕ → TimeM Bool) (h R a : ℕ) : TimeM (List ℕ) :=
  if a < R then runDnT cv a else runUpFT cv (h - (a + 1)) (a + 1)

/-- The attached rows of every covered row below `h`. -/
def tblT (cv : ℕ → TimeM Bool) (h R : ℕ) : TimeM (List (ℕ × List ℕ)) := do
  let rs ← rangeT h
  lfilterMapT (fun a => do
    let c ← cv a
    if c then do
      let l ← attWT cv h R a
      pure (some (a, l))
    else pure none) rs

/-- The row `y` and its attached rows, read from the table. -/
def grpT (tbl : List (ℕ × List ℕ)) (y : ℕ) : TimeM (List ℕ) := do
  let o ← lfindT (fun e => pure (e.1 == y)) tbl
  match o with
  | some e => pure (y :: e.2)
  | none => pure [y]

/-- `k` pairs of columns from `x` over the rows `A`. -/
def colSnakeT (x : ℕ) (A : List ℕ) (k : ℕ) : TimeM (List Coord) := do
  let is ← rangeT k
  let ra ← lreverseT A
  lflatMapT (fun i => do
    let a ← lmapT (fun y => pure (x + 2 * i, y)) A
    let b ← lmapT (fun y => pure (x + 2 * i + 1, y)) ra
    lappendT a b) is

def snWT (r k : ℕ) (tbl : List (ℕ × List ℕ)) (a : ℕ) : TimeM (List Coord) := do
  let g ← grpT tbl a
  colSnakeT (r + 1) g k

def GWT (r k R : ℕ) (fl : Bool) (tbl : List (ℕ × List ℕ)) (u v : Coord) : TimeM (List Coord) :=
  if u.1 = r ∧ v.1 = r + 2 * k + 1 ∧ u.2 = v.2 then snWT r k tbl u.2
  else if u.1 = r + 2 * k + 1 ∧ v.1 = r ∧ u.2 = v.2 then do
    let s ← snWT r k tbl u.2
    lreverseT s
  else if fl = true ∧ u = (r, R - 1) ∧ v = (r, R) then do
    let a ← snWT r k tbl (R - 1)
    let b ← snWT r k tbl R
    let rb ← lreverseT b
    lappendT a rb
  else if fl = true ∧ u = (r, R) ∧ v = (r, R - 1) then do
    let a ← snWT r k tbl (R - 1)
    let b ← snWT r k tbl R
    let rb ← lreverseT b
    let f ← lappendT a rb
    lreverseT f
  else pure []

def insManyT (G : Coord → Coord → TimeM (List Coord)) : List Coord → TimeM (List Coord)
  | a :: b :: l => do
    let i ← G a b
    let rest ← insManyT G (b :: l)
    let m ← lappendT i rest
    pure (a :: m)
  | [a] => pure [a]
  | [] => pure []

def shWT (r W : ℕ) (L : List Coord) : TimeM (List Coord) := lmapT (fun v => pure (shW r W v)) L

/-- The wide band after the seed: the table, the shift, and the insertion pass. -/
def wideTailT (h r k : ℕ) (cr : List ℕ) (R : ℕ) (fl : Bool) (p q : List Coord) :
    TimeM (List Coord × List Coord) := do
  let tbl ← tblT (cvT cr R fl) h R
  let sp ← shWT r (2 * k) p
  let sq ← shWT r (2 * k) q
  let P ← insManyT (GWT r k R fl tbl) sp
  let Q ← insManyT (GWT r k R fl tbl) sq
  pure (P, Q)

/-- **The wide band, counted**: `2k` lines inserted after line `r`, band height `h`. -/
def wideBandT (h r k : ℕ) (p q : List Coord) : TimeM (List Coord × List Coord) := do
  let cp ← crossRowsT r p
  let cq ← crossRowsT r q
  let cr ← lappendT cp cq
  let fp ← flipRowsT r p
  let fq ← flipRowsT r q
  let fr ← lappendT fp fq
  let rs ← rangeT (h + 1)
  let o ← lfindT (seedT h cr fr) rs
  let c0 ← lcontainsT cr (o.getD 0 - 1)
  let c1 ← lcontainsT cr (o.getD 0)
  wideTailT h r k cr (o.getD 0) (o.isSome && !((o.getD 0 == 0 || c0) && (o.getD 0 == h || c1))) p q

/-- The first step of `L` along the line `r`. -/
def findVT (r : ℕ) : List Coord → TimeM (Option (Coord × Coord))
  | u :: v :: l => if vertAt r u v then ⟨some (u, v), 1⟩ else do
      let o ← findVT r (v :: l)
      ⟨o, 1⟩
  | [_] => pure none
  | [] => pure none

def edgeBlockT (w h y k : ℕ) : TimeM (List Coord) := do
  let d ← rangeT (y + 1)
  let dr ← lreverseT d
  let u0 ← rangeT (h - (y + 1))
  let u ← lmapT (fun i => pure (i + (y + 1))) u0
  let A ← colSnakeT w dr k
  let B ← colSnakeT w u k
  let rB ← lreverseT B
  lappendT A rB

def blkET (w h k : ℕ) (a b : Coord) : TimeM (List Coord) :=
  if a.2 < b.2 then edgeBlockT w h a.2 k else do
    let e ← edgeBlockT w h b.2 k
    lreverseT e

def insBT (a b : Coord) (X : List Coord) : List Coord → TimeM (List Coord)
  | x :: y :: l => if x = a ∧ y = b then do
      let m ← lappendT X (y :: l)
      ⟨x :: m, 1⟩
    else do
      let r ← insBT a b X (y :: l)
      ⟨x :: r, 1⟩
  | [x] => pure [x]
  | [] => pure []

/-- **The right edge lift, counted.** -/
def edgeLiftT (w h k : ℕ) (p q : List Coord) : TimeM (List Coord × List Coord) := do
  let o ← findVT (w - 1) p
  match o with
  | some (a, b) => do
    let X ← blkET w h k a b
    let P ← insBT a b X p
    pure (P, q)
  | none => do
    let o' ← findVT (w - 1) q
    match o' with
    | some (a, b) => do
      let X ← blkET w h k a b
      let Q ← insBT a b X q
      pure (p, Q)
    | none => pure (p, q)

def reflT (w : ℕ) (L : List Coord) : TimeM (List Coord) := lmapT (fun v => pure (reflX w v)) L

/-- **The left edge lift, counted.** -/
def edgeLiftLT (w h k : ℕ) (p q : List Coord) : TimeM (List Coord × List Coord) := do
  let p' ← reflT w p
  let q' ← reflT w q
  let e ← edgeLiftT w h k p' q'
  let P ← reflT (w + 2 * k) e.1
  let Q ← reflT (w + 2 * k) e.2
  pure (P, Q)

def innerPairT (I : Inst) : TimeM (Option (ℕ × ℕ)) := do
  let xs ← lmapT (fun e => pure e.1) I.ends
  let ps ← lflatMapT (fun a => lmapT (fun b => pure (a, b)) xs) xs
  lfindT (fun ab => do
    let c ← lallT (fun x => pure (!(decide (ab.1 < x) && decide (x < ab.2)))) xs
    pure (decide (ab.1 < ab.2) && c && decide (1 ≤ innerK I ab.1 ab.2))) ps

/-- **The block to delete, counted.** -/
def blkXT (I : Inst) : TimeM (Option Blk) :=
  if 1 ≤ leftK I then pure (some (.left (leftK I)))
  else if 1 ≤ rightK I then pure (some (.right (rightK I)))
  else do
    let o ← innerPairT I
    match o with
    | some ab => pure (some (.inner (ab.1 + 1) (innerK I ab.1 ab.2)))
    | none => pure none

def _root_.ZZN.Blk.liftT : Blk → Inst → List Coord → List Coord → TimeM (List Coord × List Coord)
  | .left k, J, p, q => edgeLiftLT J.w J.h k p q
  | .right k, J, p, q => edgeLiftT J.w J.h k p q
  | .inner r k, J, p, q => wideBandT J.h r k p q

def liftBT (b : Blk) (J : Inst) : Sol → TimeM Sol
  | some pq => do
    let l ← b.liftT J pq.1 pq.2
    pure (some l)
  | none => pure none

def liftBTT (b : Blk) (J : Inst) : Sol → TimeM Sol
  | some pq => do
    let l ← b.liftT J pq.1 pq.2
    let a ← swapT l.1
    let c ← swapT l.2
    pure (some (a, c))
  | none => pure none

/-- **The block construction, counted.** -/
def solveRT (thinT : Inst → TimeM Sol) : ℕ → Inst → TimeM Sol
  | n + 1, I =>
    if I.w ≤ 10 ∨ I.h ≤ 10 then solveZT thinT I else do
    let o ← blkXT I
    match o with
    | none => do
      let o' ← blkXT I.transpose
      match o' with
      | some b => solveRT thinT n (b.del I.transpose) >>= liftBTT b (b.del I.transpose)
      | none => solveZT thinT I
    | some b => solveRT thinT n (b.del I) >>= liftBT b (b.del I)
  | 0, _ => pure none

def solveZ3T (thinT : Inst → TimeM Sol) (I : Inst) : TimeM Sol :=
  if wfB I then solveRT thinT (I.w + I.h) I else pure none

/-! ### Return values -/

theorem colSnake_eq (x : ℕ) (A : List ℕ) : ∀ k, colSnake x A k =
    (List.range k).flatMap (fun i => colRun (x + 2 * i) A ++ colRun (x + 2 * i + 1) A.reverse)
  | 0 => rfl
  | k + 1 => by
    rw [colSnake, colSnake_eq x A k, List.range_succ, List.flatMap_append, List.flatMap_singleton]

theorem colSnakeT_ret (x : ℕ) (A : List ℕ) (k : ℕ) : (colSnakeT x A k).ret = colSnake x A k := by
  rw [colSnake_eq]
  simp [colSnakeT, lflatMapT, lmapT, lappendT, lreverseT, rangeT, colRun]

theorem runDnT_ret (cv : ℕ → TimeM Bool) (c : ℕ → Bool) (hc : ∀ y, (cv y).ret = c y) :
    ∀ a, (runDnT cv a).ret = runDn c a
  | 0 => rfl
  | n + 1 => by
    simp only [runDnT, runDn, ret_bind, hc]
    split_ifs
    · rfl
    · simp [runDnT_ret cv c hc n]

theorem runUpFT_ret (cv : ℕ → TimeM Bool) (c : ℕ → Bool) (hc : ∀ y, (cv y).ret = c y) :
    ∀ k y, (runUpFT cv k y).ret = runUpF c k y
  | 0, _ => rfl
  | k + 1, y => by
    simp only [runUpFT, runUpF, ret_bind, hc]
    split_ifs
    · rfl
    · simp [runUpFT_ret cv c hc k (y + 1)]

theorem attWT_ret (cv : ℕ → TimeM Bool) (c : ℕ → Bool) (hc : ∀ y, (cv y).ret = c y) (h R a : ℕ) :
    (attWT cv h R a).ret = attW c h R a := by
  unfold attWT attW runUp
  split_ifs
  · exact runDnT_ret cv c hc a
  · exact runUpFT_ret cv c hc _ _

theorem tblT_ret (cv : ℕ → TimeM Bool) (c : ℕ → Bool) (hc : ∀ y, (cv y).ret = c y) (h R : ℕ) :
    (tblT cv h R).ret =
      (List.range h).filterMap (fun a => if c a then some (a, attW c h R a) else none) := by
  simp only [tblT, lfilterMapT, rangeT, ret_bind, hc]
  congr 1
  funext a
  split_ifs <;> simp [attWT_ret cv c hc]

theorem find_tbl (c : ℕ → Bool) (g : ℕ → List ℕ) {y : ℕ} (hy : c y = true) :
    ∀ l : List ℕ, y ∈ l →
      (l.filterMap (fun a => if c a then some (a, g a) else none)).find? (fun e => e.1 == y) =
        some (y, g y)
  | [], h => by simp at h
  | a :: l, h => by
    by_cases e : a = y
    · subst e
      simp [hy]
    · have hl : y ∈ l := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm e
        · exact h
      rw [List.filterMap_cons]
      split_ifs
      · rw [List.find?_cons]
        have : (a == y) = false := by simp [e]
        simp only [this]
        exact find_tbl c g hy l hl
      · exact find_tbl c g hy l hl

theorem grpT_ret_cov (c : ℕ → Bool) (h R : ℕ) {y : ℕ} (hy : c y = true) (hyh : y < h) :
    (grpT ((List.range h).filterMap (fun a => if c a then some (a, attW c h R a) else none))
      y).ret = grpW c h R y := by
  simp only [grpT, lfindT, ret_bind]
  have := find_tbl c (attW c h R) hy (List.range h) (List.mem_range.mpr hyh)
  simp only [ret_pure] at this ⊢
  rw [this]
  rfl

/-- The table of attached rows, as a list. -/
def tblL (c : ℕ → Bool) (h R : ℕ) : List (ℕ × List ℕ) :=
  (List.range h).filterMap (fun a => if c a then some (a, attW c h R a) else none)

theorem snWT_ret (c : ℕ → Bool) (r k h R : ℕ) {a : ℕ} (ha : c a = true) (hah : a < h) :
    (snWT r k (tblL c h R) a).ret = snW r k h R c a := by
  simp only [snWT, ret_bind]
  rw [show (grpT (tblL c h R) a).ret = grpW c h R a from grpT_ret_cov c h R ha hah,
    colSnakeT_ret]
  rfl

/-- The rows `GW` reads are covered and below `h`. -/
def GoodPair (c : ℕ → Bool) (r k h R : ℕ) (fl : Bool) (u v : Coord) : Prop :=
  (u.1 = r ∧ v.1 = r + 2 * k + 1 ∧ u.2 = v.2 → c u.2 = true ∧ u.2 < h) ∧
  (u.1 = r + 2 * k + 1 ∧ v.1 = r ∧ u.2 = v.2 → c u.2 = true ∧ u.2 < h) ∧
  (fl = true → c (R - 1) = true ∧ c R = true ∧ R < h)

theorem GWT_ret (c : ℕ → Bool) (r k h R : ℕ) (fl : Bool) {u v : Coord}
    (hg : GoodPair c r k h R fl u v) :
    (GWT r k R fl (tblL c h R) u v).ret = GW r k h R fl c u v := by
  obtain ⟨g1, g2, g3⟩ := hg
  unfold GWT GW
  by_cases h1 : u.1 = r ∧ v.1 = r + 2 * k + 1 ∧ u.2 = v.2
  · rw [ite_t h1, ite_t h1]
    exact snWT_ret c r k h R (g1 h1).1 (g1 h1).2
  rw [ite_f h1, ite_f h1]
  by_cases h2 : u.1 = r + 2 * k + 1 ∧ v.1 = r ∧ u.2 = v.2
  · rw [ite_t h2, ite_t h2]
    simp only [ret_bind, lreverseT]
    rw [snWT_ret c r k h R (g2 h2).1 (g2 h2).2]
  rw [ite_f h2, ite_f h2]
  by_cases h3 : fl = true ∧ u = (r, R - 1) ∧ v = (r, R)
  · rw [ite_t h3, ite_t h3]
    obtain ⟨c1, c2, c3⟩ := g3 h3.1
    simp only [ret_bind, lreverseT, lappendT]
    rw [snWT_ret c r k h R c1 (by omega), snWT_ret c r k h R c2 c3]
    rfl
  rw [ite_f h3, ite_f h3]
  by_cases h4 : fl = true ∧ u = (r, R) ∧ v = (r, R - 1)
  · rw [ite_t h4, ite_t h4]
    obtain ⟨c1, c2, c3⟩ := g3 h4.1
    simp only [ret_bind, lreverseT, lappendT]
    rw [snWT_ret c r k h R c1 (by omega), snWT_ret c r k h R c2 c3]
    rfl
  rw [ite_f h4, ite_f h4]
  rfl

theorem insManyT_ret (G : Coord → Coord → TimeM (List Coord)) (G' : Coord → Coord → List Coord) :
    ∀ L : List Coord, (∀ a b, [a, b] <:+: L → (G a b).ret = G' a b) →
      (insManyT G L).ret = insMany G' L
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    have ih := insManyT_ret G G' (b :: l)
      (fun x y hxy => h x y (hxy.trans (List.suffix_cons a _).isInfix))
    simp only [insManyT, insMany, ret_bind, lappendT, ret_pure, ih, h a b ⟨[], l, rfl⟩]

theorem shWT_ret (r W : ℕ) (L : List Coord) : (shWT r W L).ret = L.map (shW r W) := by
  simp [shWT, lmapT]

theorem cvT_ret {p q : List Coord} {r : ℕ} (cr : List ℕ) (hcr : ∀ y, y ∈ cr ↔ Cross p q r y)
    (R : ℕ) (fl : Bool) (y : ℕ) : (cvT cr R fl y).ret = cvW p q r R fl y := by
  have : cr.contains y = decide (Cross p q r y) := by
    rw [Bool.eq_iff_iff, List.contains_iff_mem, hcr]; simp
  simp only [cvT, cvW, lcontainsT, ret_bind, ret_pure, this]

/-- Crossing and flip steps of a path with rows below `h` read covered rows below `h`. -/
theorem goodPair_of {p q L : List Coord} {r k h R : ℕ} {fl : Bool}
    (hL : ∀ v ∈ L, v.2 < h) (hU : ∀ u v, [u, v] <:+: L → Used p u v ∨ Used q u v)
    (hfl : fl = true → 1 ≤ R ∧ R < h) {a b : Coord} (hab : [a, b] <:+: L) :
    GoodPair (cvW p q r R fl) r k h R fl (shW r (2 * k) a) (shW r (2 * k) b) := by
  have ha := hL a (hab.subset (by simp))
  have hb := hL b (hab.subset (by simp))
  refine ⟨fun h1 => ?_, fun h2 => ?_, fun hf => ?_⟩
  · obtain ⟨e1, e2, e3⟩ := h1
    have ea : a = (r, a.2) := by
      rw [← shW_eq_r (W := 2 * k)]; exact Prod.ext e1 (shW_snd a)
    have eb : b = (r + 1, a.2) := by
      rw [← shW_eq_far (W := 2 * k)]
      refine Prod.ext e2 ?_
      show (shW r (2 * k) b).2 = a.2
      rw [← e3, shW_snd]
    rw [shW_snd]
    refine ⟨?_, ha⟩
    have hu := hU a b hab
    rw [ea, eb] at hu
    simp [cvW, Cross, hu]
  · obtain ⟨e1, e2, e3⟩ := h2
    have ea : a = (r + 1, a.2) := by
      rw [← shW_eq_far (W := 2 * k)]; exact Prod.ext e1 (shW_snd a)
    have eb : b = (r, a.2) := by
      rw [← shW_eq_r (W := 2 * k)]
      refine Prod.ext e2 ?_
      show (shW r (2 * k) b).2 = a.2
      rw [← e3, shW_snd]
    rw [shW_snd]
    refine ⟨?_, ha⟩
    have hu := hU a b hab
    rw [ea, eb] at hu
    have hu' : Used p (r, a.2) (r + 1, a.2) ∨ Used q (r, a.2) (r + 1, a.2) := by
      rcases hu with hu | hu
      · exact Or.inl hu.symm
      · exact Or.inr hu.symm
    simp [cvW, Cross, hu']
  · obtain ⟨h1, h2⟩ := hfl hf
    refine ⟨?_, ?_, h2⟩
    · simp [cvW, hf]; omega
    · simp [cvW, hf]

theorem insW_ret {p q L : List Coord} {r k h R : ℕ} {fl : Bool} (cr : List ℕ)
    (hcr : ∀ y, y ∈ cr ↔ Cross p q r y)
    (hL : ∀ v ∈ L, v.2 < h) (hU : ∀ u v, [u, v] <:+: L → Used p u v ∨ Used q u v)
    (hfl : fl = true → 1 ≤ R ∧ R < h) :
    (insManyT (GWT r k R fl (tblT (cvT cr R fl) h R).ret) (shWT r (2 * k) L).ret).ret =
      wideExt r k h R fl (cvW p q r R fl) L := by
  rw [tblT_ret _ (cvW p q r R fl) (cvT_ret cr hcr R fl), shWT_ret]
  refine insManyT_ret _ _ _ (fun u v huv => ?_)
  obtain ⟨a, b, hab, rfl, rfl⟩ := infix_map_pair huv
  exact GWT_ret _ r k h R fl (goodPair_of hL hU hfl hab)

theorem wideBandT_ret (J : Inst) (r k : ℕ) (p q : List Coord) (hp : ∀ v ∈ p, v.2 < J.h)
    (hq : ∀ v ∈ q, v.2 < J.h) : (wideBandT J.h r k p q).ret = innerLift J r k p q := by
  set cr := (crossRowsT r p).ret ++ (crossRowsT r q).ret with hcrd
  set fr := (flipRowsT r p).ret ++ (flipRowsT r q).ret with hfrd
  have hcr : ∀ y, y ∈ cr ↔ Cross p q r y := by
    intro y; rw [hcrd, List.mem_append, crossRowsT_mem, crossRowsT_mem]; rfl
  have hfr : ∀ y, y ∈ fr ↔ (Used p (r, y) (r, y + 1) ∨ Used q (r, y) (r, y + 1)) := by
    intro y; rw [hfrd, List.mem_append, flipRowsT_mem, flipRowsT_mem]
  have hfind : (List.range (J.h + 1)).find? (fun R => (seedT J.h cr fr R).ret) =
      (List.range (J.h + 1)).find? (fun R => decide (SeedAt J.h p q r R)) := by
    congr 1; funext R; exact seedT_ret J.h r p q cr fr hcr hfr R
  have cont : ∀ y, cr.contains y = decide (Cross p q r y) := fun y => by
    rw [Bool.eq_iff_iff, List.contains_iff_mem, hcr]; simp
  have hUp : ∀ u v, [u, v] <:+: p → Used p u v ∨ Used q u v := fun u v h => Or.inl (Or.inl h)
  have hUq : ∀ u v, [u, v] <:+: q → Used p u v ∨ Used q u v := fun u v h => Or.inr (Or.inl h)
  simp only [wideBandT, wideTailT, ret_bind, lappendT, rangeT, lfindT, lcontainsT, ret_pure]
  rw [← hcrd, ← hfrd, hfind]
  unfold innerLift seedW
  cases ho : (List.range (J.h + 1)).find? (fun R => decide (SeedAt J.h p q r R)) with
  | none =>
    simp only [Option.getD_none, Option.isSome_none, Bool.false_and]
    have hfl : false = true → 1 ≤ 0 ∧ 0 < J.h := fun h => by cases h
    rw [insW_ret cr hcr hp hUp hfl, insW_ret cr hcr hq hUq hfl]
  | some R =>
    simp only [Option.getD_some, Option.isSome_some, Bool.true_and, cont]
    have hs : SeedAt J.h p q r R := by
      have := List.find?_some ho
      simpa using this
    have e : (!((R == 0 || decide (Cross p q r (R - 1))) && (R == J.h || decide (Cross p q r R)))) =
        !decide ((R = 0 ∨ Cross p q r (R - 1)) ∧ (R = J.h ∨ Cross p q r R)) := by
      simp only [Bool.decide_and, Bool.decide_or]
      rfl
    rw [e]
    have hfl : (!decide ((R = 0 ∨ Cross p q r (R - 1)) ∧ (R = J.h ∨ Cross p q r R))) = true →
        1 ≤ R ∧ R < J.h := by
      intro hf
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hf
      rcases hs with hs | ⟨h1, h2, -⟩
      · exact absurd hs hf
      · exact ⟨h1, h2⟩
    rw [insW_ret cr hcr hp hUp hfl, insW_ret cr hcr hq hUq hfl]

theorem findVT_ret (r : ℕ) : ∀ L : List Coord, (findVT r L).ret = findV r L
  | [] => rfl
  | [_] => rfl
  | u :: v :: l => by
    unfold findVT findV
    split_ifs
    · rfl
    · simp [findVT_ret r (v :: l)]

theorem edgeBlockT_ret (w h y k : ℕ) : (edgeBlockT w h y k).ret = edgeBlock w h y k := by
  simp only [edgeBlockT, ret_bind, rangeT, lreverseT, lmapT, lappendT, colSnakeT_ret, ret_pure]
  rfl

theorem blkET_ret (w h k : ℕ) (a b : Coord) : (blkET w h k a b).ret = blkE w h k a b := by
  unfold blkET blkE
  split_ifs
  · exact edgeBlockT_ret _ _ _ _
  · simp [lreverseT, edgeBlockT_ret]

theorem insBT_ret (a b : Coord) (X : List Coord) : ∀ L, (insBT a b X L).ret = insB a b X L
  | [] => rfl
  | [_] => rfl
  | x :: y :: l => by
    unfold insBT insB
    split_ifs
    · rfl
    · simp [insBT_ret a b X (y :: l)]

theorem edgeLiftT_ret (w h k : ℕ) (p q : List Coord) :
    (edgeLiftT w h k p q).ret = edgeLift w h k p q := by
  unfold edgeLiftT edgeLift
  simp only [ret_bind, findVT_ret]
  cases findV (w - 1) p with
  | some ab => obtain ⟨a, b⟩ := ab; simp [blkET_ret, insBT_ret]
  | none =>
    simp only [ret_bind, findVT_ret]
    cases findV (w - 1) q with
    | some ab => obtain ⟨a, b⟩ := ab; simp [blkET_ret, insBT_ret]
    | none => rfl

theorem reflT_ret (w : ℕ) (L : List Coord) : (reflT w L).ret = L.map (reflX w) := by
  simp [reflT, lmapT]

theorem edgeLiftLT_ret (w h k : ℕ) (p q : List Coord) :
    (edgeLiftLT w h k p q).ret = edgeLiftL w h k p q := by
  simp only [edgeLiftLT, ret_bind, reflT_ret, edgeLiftT_ret, ret_pure]
  rfl

theorem innerPairT_ret (I : Inst) : (innerPairT I).ret = innerPair I := by
  simp only [innerPairT, ret_bind, lmapT, lflatMapT, lfindT, lallT, ret_pure]
  rfl

theorem blkXT_ret (I : Inst) : (blkXT I).ret = blkX I := by
  unfold blkXT blkX
  split_ifs
  · rfl
  · rfl
  · simp only [ret_bind, innerPairT_ret]
    cases innerPair I <;> rfl

theorem liftT_ret (b : Blk) (J : Inst) (p q : List Coord) (hp : ∀ v ∈ p, v.2 < J.h)
    (hq : ∀ v ∈ q, v.2 < J.h) : (b.liftT J p q).ret = b.lift J p q := by
  cases b with
  | left k => exact edgeLiftLT_ret _ _ _ _ _
  | right k => exact edgeLiftT_ret _ _ _ _ _
  | inner r k => exact wideBandT_ret J r k p q hp hq

theorem rows_lt {I : Inst} {p q : List Coord} (h : IsSolution I p q) :
    (∀ v ∈ p, v.2 < I.h) ∧ (∀ v ∈ q, v.2 < I.h) :=
  ⟨fun v hv => (h.1.2.2.2.1 v hv).2, fun v hv => (h.2.1.2.2.2.1 v hv).2⟩

theorem solveRT_ret {thinT : Inst → TimeM Sol} {thin : Inst → Sol}
    (hret : ∀ J, (thinT J).ret = thin J) :
    ∀ (n : ℕ) (I : Inst), I.WellFormed → (solveRT thinT n I).ret = solveR thin n I := by
  intro n
  induction n with
  | zero => intro I _; rfl
  | succ n ih =>
    intro I hwf
    simp only [solveRT, solveR]
    split_ifs with hs
    · exact solveZT_ret hret I
    · have hI := inDom_of hwf hs
      simp only [ret_bind, blkXT_ret]
      cases hb : blkX I with
      | some b =>
        have ok := blkX_ok hI hb
        have hJ := (chain_inDom ok.chain hI).2.2
        simp only [ret_bind, ih _ hJ]
        cases hs' : solveR thin n (b.del I) with
        | none => rfl
        | some pq =>
          have hsol := solveR_sound thin n _ pq.1 pq.2 hJ hs'
          obtain ⟨r1, r2⟩ := rows_lt hsol
          simp only [liftBT, ret_bind, ret_pure, liftT_ret b _ _ _ r1 r2]
      | none =>
        simp only [ret_bind, blkXT_ret]
        cases hbT : blkX I.transpose with
        | some b =>
          have hIT := inDom_transpose hI
          have ok := blkX_ok hIT hbT
          have hJ := (chain_inDom ok.chain hIT).2.2
          simp only [ret_bind, ih _ hJ]
          cases hs' : solveR thin n (b.del I.transpose) with
          | none => rfl
          | some pq =>
            have hsol := solveR_sound thin n _ pq.1 pq.2 hJ hs'
            obtain ⟨r1, r2⟩ := rows_lt hsol
            simp only [liftBTT, ret_bind, ret_pure, liftT_ret b _ _ _ r1 r2, swapT_ret]
        | none => exact solveZT_ret hret I

theorem solveZ3T_ret {thinT : Inst → TimeM Sol} {thin : Inst → Sol}
    (hret : ∀ J, (thinT J).ret = thin J) (I : Inst) : (solveZ3T thinT I).ret = solveZ3 thin I := by
  unfold solveZ3T solveZ3
  by_cases hwf : I.WellFormed
  · rw [ite_t ((wfB_iff I).2 hwf), ite_t hwf]
    exact solveRT_ret hret _ I hwf
  · rw [ite_f (fun h => hwf ((wfB_iff I).1 h)), ite_f hwf]
    rfl

end ZZN.T

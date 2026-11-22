/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Constr.WideBand
public import ZZN.Constr.Solve2

@[expose] public section

/-!
# Deleting blocks of free lines

A block is a run of `2k` free lines deleted at once: at the left edge, at the right edge, or after
a free line `r` inside a gap between endpoints. Each block deletion is a chain of `RedX` steps
(`Chain`), so it keeps an instance in the domain and passing the catalogue (`chain_pass`). The
block is put back by one lift: `edgeLiftL`, `edgeLift`, or the wide band `wideExt`.
-/

namespace ZZN

open GridHam

/-! ### Chains of reductions -/

/-- `J` is reached from `I` by `RedX` steps on the x-axis. -/
inductive Chain : Inst → Inst → Prop
  | refl (I : Inst) : Chain I I
  | step {I J : Inst} (d : ℕ) (h : RedX I d) (c : Chain (I.deleteAt d) J) : Chain I J

theorem chain_pass {I J : Inst} (c : Chain I J) (hI : InDom I) (hP : Passes I) :
    InDom J ∧ Passes J := by
  induction c with
  | refl => exact ⟨hI, hP⟩
  | step d h _ ih => exact ih (inDom_deleteAt hI h) (passX_all hI h hP)

/-! ### The instances after a block deletion -/

/-- Replace the width and move the endpoints by `f`. -/
def Inst.mapE (I : Inst) (w : ℕ) (f : Coord → Coord) : Inst := ⟨w, I.h, f I.s0, f I.t0, f I.s1, f I.t1⟩

/-- Delete the lines `0 … m - 1`. -/
def Inst.dropL (I : Inst) (m : ℕ) : Inst := I.mapE (I.w - m) (fun v => (v.1 - m, v.2))

/-- Delete the last `m` lines. -/
def Inst.dropR (I : Inst) (m : ℕ) : Inst := I.mapE (I.w - m) id

/-- Delete the lines `r + 1 … r + m`. -/
def Inst.dropIn (I : Inst) (r m : ℕ) : Inst :=
  I.mapE (I.w - m) (fun v => if v.1 ≤ r then v else (v.1 - m, v.2))

theorem Inst.ext' {I J : Inst} (hw : I.w = J.w) (hh : I.h = J.h) (h0 : I.s0 = J.s0)
    (h1 : I.t0 = J.t0) (h2 : I.s1 = J.s1) (h3 : I.t1 = J.t1) : I = J := by
  cases I; cases J; simp_all

theorem ends_mapE (I : Inst) (w : ℕ) (f : Coord → Coord) : (I.mapE w f).ends = I.ends.map f := rfl

theorem ends_deleteAt (I : Inst) (d : ℕ) : (I.deleteAt d).ends = I.ends.map (delAt d) := rfl

/-- Apply a fact about each endpoint to all four. -/
theorem ends_all {I : Inst} {P : Coord → Prop} (h : ∀ e ∈ I.ends, P e) :
    P I.s0 ∧ P I.t0 ∧ P I.s1 ∧ P I.t1 := by
  simp only [Inst.ends, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h
  exact h

/-! ### Each block deletion is a chain -/

/-- **Left blocks.** -/
theorem chain_left : ∀ (k : ℕ) (I : Inst), (∀ e ∈ I.ends, 2 * k + 2 ≤ e.1) →
    2 * k + 11 ≤ I.w → Chain I (I.dropL (2 * k))
  | 0, I, _, _ => by
    have : I.dropL (2 * 0) = I := by
      apply Inst.ext' <;> simp [Inst.dropL, Inst.mapE]
    rw [this]; exact Chain.refl I
  | k + 1, I, he, hw => by
    have hr : RedX I 0 := ⟨by omega, Or.inl ⟨rfl, fun x hx e hm => by
      have := he e hm; omega⟩⟩
    refine Chain.step 0 hr ?_
    have e : (I.deleteAt 0).dropL (2 * k) = I.dropL (2 * (k + 1)) := by
      obtain ⟨a0, a1, a2, a3⟩ := ends_all he
      apply Inst.ext' <;> simp [Inst.dropL, Inst.mapE, Inst.deleteAt, delAt] <;> omega
    rw [← e]
    refine chain_left k _ (fun e' hm => ?_) (by simp [Inst.deleteAt]; omega)
    rw [ends_deleteAt, List.mem_map] at hm
    obtain ⟨e0, h0, rfl⟩ := hm
    have := he e0 h0
    simp only [delAt]
    split_ifs <;> (try simp only) <;> omega

/-- **Right blocks.** -/
theorem chain_right : ∀ (k : ℕ) (I : Inst), (∀ e ∈ I.ends, e.1 + 2 * k + 2 < I.w) →
    2 * k + 11 ≤ I.w → Chain I (I.dropR (2 * k))
  | 0, I, _, _ => by
    have : I.dropR (2 * 0) = I := by
      apply Inst.ext' <;> simp [Inst.dropR, Inst.mapE]
    rw [this]; exact Chain.refl I
  | k + 1, I, he, hw => by
    have hr : RedX I (I.w - 2) := ⟨by omega, Or.inr (Or.inl ⟨by omega, fun x h1 h2 e hm => by
      have := he e hm; omega⟩)⟩
    refine Chain.step _ hr ?_
    have e : (I.deleteAt (I.w - 2)).dropR (2 * k) = I.dropR (2 * (k + 1)) := by
      obtain ⟨a0, a1, a2, a3⟩ := ends_all he
      apply Inst.ext' <;> simp [Inst.dropR, Inst.mapE, Inst.deleteAt, delAt] <;> omega
    rw [← e]
    refine chain_right k _ (fun e' hm => ?_) (by simp [Inst.deleteAt]; omega)
    rw [ends_deleteAt, List.mem_map] at hm
    obtain ⟨e0, h0, rfl⟩ := hm
    have := he e0 h0
    simp only [delAt, Inst.deleteAt]
    split_ifs <;> (try simp only) <;> omega

/-- **Inner blocks**: after the free line `r`, with ten free lines from `r` at every step and
endpoints on both sides. -/
theorem chain_inner (r : ℕ) : ∀ (k : ℕ) (I : Inst),
    (∀ e ∈ I.ends, e.1 < r ∨ r + 2 * k + 8 ≤ e.1) → EndBelow I r → EndAbove I (r + 2 * k + 7) →
    r + 2 * k + 8 ≤ I.w → 2 * k + 11 ≤ I.w → Chain I (I.dropIn r (2 * k))
  | 0, I, _, _, _, _, _ => by
    have : I.dropIn r (2 * 0) = I := by
      apply Inst.ext' <;> simp [Inst.dropIn, Inst.mapE]
    rw [this]; exact Chain.refl I
  | k + 1, I, he, hb, ha, hw1, hw => by
    have hr : RedX I (r + 1) := by
      refine ⟨by omega, Or.inr (Or.inr (Or.inl ⟨r, by omega, by omega, by
        obtain ⟨e, hm, he1⟩ := ha
        have := he e hm
        omega, fun x h1 h2 e hm => ?_, hb, ?_⟩))⟩
      · have := he e hm; omega
      · obtain ⟨e, hm, he1⟩ := ha
        exact ⟨e, hm, by omega⟩
    refine Chain.step _ hr ?_
    have e : (I.deleteAt (r + 1)).dropIn r (2 * k) = I.dropIn r (2 * (k + 1)) := by
      obtain ⟨a0, a1, a2, a3⟩ := ends_all he
      rcases I with ⟨w, hh, ⟨x0, y0⟩, ⟨x1, y1⟩, ⟨x2, y2⟩, ⟨x3, y3⟩⟩
      simp only at a0 a1 a2 a3 hw
      apply Inst.ext' <;> simp only [Inst.dropIn, Inst.mapE, Inst.deleteAt, delAt]
      · omega
      all_goals
        split_ifs <;> (try simp only [Prod.mk.injEq, and_true] at *) <;> omega
    rw [← e]
    have hd : ∀ e ∈ I.ends, delAt (r + 1) e = if e.1 < r then e else (e.1 - 2, e.2) := by
      intro e0 h0
      have := he e0 h0
      unfold delAt
      split_ifs <;> first | rfl | omega
    refine chain_inner r k _ (fun e' hm => ?_) ?_ ?_ (by simp [Inst.deleteAt]; omega)
      (by simp [Inst.deleteAt]; omega)
    · rw [ends_deleteAt, List.mem_map] at hm
      obtain ⟨e0, h0, rfl⟩ := hm
      have := he e0 h0
      rw [hd e0 h0]
      split_ifs <;> (try simp only) <;> omega
    · obtain ⟨e0, h0, h1⟩ := hb
      exact ⟨delAt (r + 1) e0, by rw [ends_deleteAt]; exact List.mem_map_of_mem h0,
        by rw [hd e0 h0, ite_t h1]; exact h1⟩
    · obtain ⟨e0, h0, h1⟩ := ha
      refine ⟨delAt (r + 1) e0, by rw [ends_deleteAt]; exact List.mem_map_of_mem h0, ?_⟩
      have := he e0 h0
      rw [hd e0 h0, ite_f (by omega)]
      simp only; omega

theorem chain_inDom {I J : Inst} (c : Chain I J) (hI : InDom I) : InDom J := by
  induction c with
  | refl => exact hI
  | step d h _ ih => exact ih (inDom_deleteAt hI h)

/-! ### Putting a block back -/

theorem dropL_widenL {I : Inst} {m : ℕ} (he : ∀ e ∈ I.ends, m ≤ e.1) (hw : m ≤ I.w) :
    (I.dropL m).widenL m = I := by
  obtain ⟨a0, a1, a2, a3⟩ := ends_all he
  apply Inst.ext' <;> simp only [Inst.dropL, Inst.mapE, Inst.widenL]
  · omega
  · exact Prod.ext (by simp only; omega) rfl
  · exact Prod.ext (by simp only; omega) rfl
  · exact Prod.ext (by simp only; omega) rfl
  · exact Prod.ext (by simp only; omega) rfl

theorem dropR_widen {I : Inst} {m : ℕ} (hw : m ≤ I.w) : (I.dropR m).widen m = I := by
  apply Inst.ext' <;> simp [Inst.dropR, Inst.mapE, Inst.widen]
  omega

theorem dropIn_insertW {I : Inst} {r m : ℕ} (he : ∀ e ∈ I.ends, e.1 ≤ r ∨ r + m < e.1)
    (hw : m ≤ I.w) : (I.dropIn r m).insertW r m = I := by
  have key : ∀ e ∈ I.ends,
      shW r m (if e.1 ≤ r then e else (e.1 - m, e.2)) = e := by
    intro e hm
    have := he e hm
    split_ifs with h1
    · exact shW_le h1
    · rw [shW_gt (by simp only; omega)]
      exact Prod.ext (by simp only; omega) rfl
  obtain ⟨a0, a1, a2, a3⟩ := ends_all key
  apply Inst.ext' <;> simp only [Inst.dropIn, Inst.mapE, Inst.insertW]
  · omega
  all_goals assumption

/-! ### The seed for the wide band -/

/-- The seed row and the flip flag, as `bandExtE` finds them. -/
def seedW (h : ℕ) (p q : List Coord) (r : ℕ) : ℕ × Bool :=
  match (List.range (h + 1)).find? (fun R => decide (SeedAt h p q r R)) with
  | some R => (R, !decide ((R = 0 ∨ Cross p q r (R - 1)) ∧ (R = h ∨ Cross p q r R)))
  | none => (0, false)

/-- The covered rows: crossings, and the two flip rows. -/
def cvW (p q : List Coord) (r R : ℕ) (flip : Bool) (y : ℕ) : Bool :=
  decide (Cross p q r y) || (flip && (y + 1 == R || y == R))

/-- **The inner lift**: the wide band after line `r`, with the seed found. -/
def innerLift (J : Inst) (r k : ℕ) (p q : List Coord) : List Coord × List Coord :=
  (wideExt r k J.h (seedW J.h p q r).1 (seedW J.h p q r).2
      (cvW p q r (seedW J.h p q r).1 (seedW J.h p q r).2) p,
   wideExt r k J.h (seedW J.h p q r).1 (seedW J.h p q r).2
      (cvW p q r (seedW J.h p q r).1 (seedW J.h p q r).2) q)

theorem seedW_ok {J : Inst} {p q : List Coord} {r : ℕ} (hsol : IsSolution J p q) (hr : r < J.w)
    (hfree : LineFree J r) (hh : 0 < J.h) :
    WideOK J p q r (seedW J.h p q r).1 (seedW J.h p q r).2
      (cvW p q r (seedW J.h p q r).1 (seedW J.h p q r).2) := by
  unfold seedW
  cases hf : (List.range (J.h + 1)).find? (fun R => decide (SeedAt J.h p q r R)) with
  | none =>
    exfalso
    obtain ⟨R, hR, hs⟩ := seed_or_flip hsol hr hfree hh
    have := List.find?_eq_none.mp hf R (List.mem_range.mpr (by omega))
    exact this (decide_eq_true hs)
  | some R =>
    simp only
    have hs : SeedAt J.h p q r R := by
      have := List.find?_some hf
      simpa using this
    have hR : R ≤ J.h := by
      have := List.mem_range.mp (List.mem_of_find?_eq_some hf)
      omega
    refine ⟨hr, hR, fun hfl => ?_, fun hfl => ?_, fun y => ?_⟩
    · simp only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq] at hfl
      exact hfl
    · simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hfl
      rcases hs with hs | hs
      · exact absurd hs hfl
      · exact hs
    · simp [cvW]

theorem innerLift_sol {J : Inst} {p q : List Coord} {r k : ℕ} (hsol : IsSolution J p q)
    (hr : r < J.w) (hfree : LineFree J r) (hh : 0 < J.h) (hk : 0 < k) :
    IsSolution (J.insertW r (2 * k)) (innerLift J r k p q).1 (innerLift J r k p q).2 :=
  wideExt_sol (seedW_ok hsol hr hfree hh) hk hsol

/-! ### Blocks -/

/-- A block of free lines: `2k` at the left edge, `2k` at the right edge, or `2k` after line `r`. -/
inductive Blk
  | left (k : ℕ)
  | right (k : ℕ)
  | inner (r k : ℕ)

/-- The instance with the block deleted. -/
def Blk.del : Blk → Inst → Inst
  | .left k, I => I.dropL (2 * k)
  | .right k, I => I.dropR (2 * k)
  | .inner r k, I => I.dropIn r (2 * k)

/-- Put the block back into a solution `p, q` of the reduced instance `J`. -/
def Blk.lift : Blk → Inst → List Coord → List Coord → List Coord × List Coord
  | .left k, J, p, q => edgeLiftL J.w J.h k p q
  | .right k, J, p, q => edgeLift J.w J.h k p q
  | .inner r k, J, p, q => innerLift J r k p q

def xmin (I : Inst) : ℕ := min (min I.s0.1 I.t0.1) (min I.s1.1 I.t1.1)
def xmax (I : Inst) : ℕ := max (max I.s0.1 I.t0.1) (max I.s1.1 I.t1.1)

/-- Half the size of the largest left block. -/
def leftK (I : Inst) : ℕ := min ((xmin I - 2) / 2) ((I.w - 11) / 2)
/-- Half the size of the largest right block. -/
def rightK (I : Inst) : ℕ := min ((I.w - 3 - xmax I) / 2) ((I.w - 11) / 2)
/-- Half the size of the largest inner block between endpoint lines `a < b`. -/
def innerK (I : Inst) (a b : ℕ) : ℕ := min ((b - a - 9) / 2) ((I.w - 11) / 2)

/-- `a < b` are endpoint lines with no endpoint between them and room for a block. -/
def gapOK (I : Inst) (ab : ℕ × ℕ) : Bool :=
  decide (ab.1 < ab.2) && (xsOf I).all (fun x => !(decide (ab.1 < x) && decide (x < ab.2))) &&
    decide (1 ≤ innerK I ab.1 ab.2)

def innerPair (I : Inst) : Option (ℕ × ℕ) :=
  ((xsOf I).flatMap fun a => (xsOf I).map fun b => (a, b)).find? (gapOK I)

/-- **The block to delete** on the x-axis, if any. -/
def blkX (I : Inst) : Option Blk :=
  if 1 ≤ leftK I then some (.left (leftK I))
  else if 1 ≤ rightK I then some (.right (rightK I))
  else
    match innerPair I with
    | some ab => some (.inner (ab.1 + 1) (innerK I ab.1 ab.2))
    | none => none

/-- What a block deletion guarantees. -/
structure BlkOK (I : Inst) (b : Blk) : Prop where
  chain : Chain I (b.del I)
  lift : ∀ p q, IsSolution (b.del I) p q →
    IsSolution I (b.lift (b.del I) p q).1 (b.lift (b.del I) p q).2
  smaller : (b.del I).w + 2 ≤ I.w
  sameH : (b.del I).h = I.h

theorem ends_x {I : Inst} : ∀ e ∈ I.ends, xmin I ≤ e.1 ∧ e.1 ≤ xmax I := by
  intro e he
  simp only [Inst.ends, List.mem_cons, List.not_mem_nil, or_false] at he
  unfold xmin xmax
  rcases he with rfl | rfl | rfl | rfl <;> omega

theorem mem_xsOf {I : Inst} {x : ℕ} : x ∈ xsOf I ↔ ∃ e ∈ I.ends, e.1 = x := by
  simp [xsOf]

theorem ends_lt_w {I : Inst} (hwf : I.WellFormed) : ∀ e ∈ I.ends, e.1 < I.w := by
  obtain ⟨b0, b1, b2, b3, -⟩ := hwf
  intro e he
  simp only [Inst.ends, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  exacts [b0.1, b1.1, b2.1, b3.1]

theorem leftK_spec {I : Inst} (h : 1 ≤ leftK I) :
    2 * leftK I + 2 ≤ xmin I ∧ 2 * leftK I + 11 ≤ I.w := by
  have := Nat.min_le_left ((xmin I - 2) / 2) ((I.w - 11) / 2)
  have := Nat.min_le_right ((xmin I - 2) / 2) ((I.w - 11) / 2)
  unfold leftK at *
  omega

theorem rightK_spec {I : Inst} (h : 1 ≤ rightK I) :
    xmax I + 2 * rightK I + 3 ≤ I.w ∧ 2 * rightK I + 11 ≤ I.w := by
  have := Nat.min_le_left ((I.w - 3 - xmax I) / 2) ((I.w - 11) / 2)
  have := Nat.min_le_right ((I.w - 3 - xmax I) / 2) ((I.w - 11) / 2)
  unfold rightK at *
  omega

theorem innerK_spec {I : Inst} {a b : ℕ} (h : 1 ≤ innerK I a b) :
    a + 2 * innerK I a b + 9 ≤ b ∧ 2 * innerK I a b + 11 ≤ I.w := by
  have := Nat.min_le_left ((b - a - 9) / 2) ((I.w - 11) / 2)
  have := Nat.min_le_right ((b - a - 9) / 2) ((I.w - 11) / 2)
  unfold innerK at *
  omega

/-- **Every block found is valid.** -/
theorem blkX_ok {I : Inst} {b : Blk} (hI : InDom I) (hb : blkX I = some b) : BlkOK I b := by
  have h5 : 5 ≤ I.h := by have := hI.2.1; omega
  unfold blkX at hb
  split_ifs at hb with hl hr
  · -- left edge
    cases hb
    obtain ⟨s1, s2⟩ := leftK_spec hl
    set k := leftK I with hk
    have he : ∀ e ∈ I.ends, 2 * k + 2 ≤ e.1 := fun e hm => by
      have := (ends_x e hm).1; omega
    have hw : 2 * k + 11 ≤ I.w := s2
    refine ⟨chain_left k I he hw, fun p q hsol => ?_, by simp [Blk.del, Inst.dropL, Inst.mapE]; omega,
      rfl⟩
    have := edgeLiftL_sol (I := I.dropL (2 * k)) (k := k) h5 (by omega) hsol
    rw [dropL_widenL (fun e hm => by have := he e hm; omega) (by omega)] at this
    exact this
  · -- right edge
    cases hb
    obtain ⟨s1, s2⟩ := rightK_spec hr
    set k := rightK I with hk
    have he : ∀ e ∈ I.ends, e.1 + 2 * k + 2 < I.w := fun e hm => by
      have := (ends_x e hm).2; omega
    have hw : 2 * k + 11 ≤ I.w := s2
    refine ⟨chain_right k I he hw, fun p q hsol => ?_, by simp [Blk.del, Inst.dropR, Inst.mapE]; omega,
      rfl⟩
    have := edgeLift_sol (I := I.dropR (2 * k)) (k := k) h5 (by omega) hsol
    rw [show (I.dropR (2 * k)).w = I.w - 2 * k from rfl, dropR_widen (by omega)] at this
    exact this
  · -- inner block
    cases hp : innerPair I with
    | none => rw [hp] at hb; cases hb
    | some ab =>
      rw [hp] at hb
      cases hb
      obtain ⟨a, c⟩ := ab
      have hg := List.find?_some hp
      have hmem := List.mem_of_find?_eq_some hp
      simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq] at hmem
      obtain ⟨a', ha', c', hc', rfl, rfl⟩ := hmem
      simp only [gapOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
        Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt] at hg
      obtain ⟨⟨hac, hbet⟩, hk1⟩ := hg
      obtain ⟨s1, s2⟩ := innerK_spec hk1
      set k := innerK I a' c' with hk
      set r := a' + 1 with hrdef
      obtain ⟨ea, hea, ea1⟩ := mem_xsOf.mp ha'
      obtain ⟨ec, hec, ec1⟩ := mem_xsOf.mp hc'
      have hcw : c' < I.w := ec1 ▸ ends_lt_w hI.2.2 ec hec
      have hw : 2 * k + 11 ≤ I.w := s2
      have side : ∀ e ∈ I.ends, e.1 ≤ a' ∨ c' ≤ e.1 := by
        intro e hm
        have := hbet e.1 (List.mem_map_of_mem hm)
        omega
      have he : ∀ e ∈ I.ends, e.1 < r ∨ r + 2 * k + 8 ≤ e.1 := fun e hm => by
        have := side e hm; omega
      have hch := chain_inner r k I he ⟨ea, hea, by omega⟩ ⟨ec, hec, by omega⟩ (by omega) hw
      refine ⟨hch, fun p q hsol => ?_, by simp [Blk.del, Inst.dropIn, Inst.mapE]; omega, rfl⟩
      have hfree : LineFree (I.dropIn r (2 * k)) r := by
        intro y
        have key : ∀ e ∈ I.ends, (r, y) ≠ (if e.1 ≤ r then e else (e.1 - 2 * k, e.2)) := by
          intro e hm hre
          have := side e hm
          split_ifs at hre with h1
          · rw [← hre] at this; simp only at this; omega
          · have := congrArg Prod.fst hre; simp only at this; omega
        obtain ⟨k0, k1, k2, k3⟩ := ends_all key
        exact ⟨k0, k1, k2, k3⟩
      have := innerLift_sol (J := I.dropIn r (2 * k)) (r := r) (k := k) hsol
        (by simp [Inst.dropIn, Inst.mapE]; omega) hfree (by simp [Inst.dropIn, Inst.mapE]; omega)
        (by omega)
      rw [dropIn_insertW (fun e hm => by have := side e hm; omega) (by omega)] at this
      exact this

/-! ### The construction with block deletions -/

/-- Delete blocks on the x-axis, then on the y-axis, then finish with `solveZ2`. -/
def solveR (thin : Inst → Option (List Coord × List Coord)) :
    ℕ → Inst → Option (List Coord × List Coord)
  | 0, _ => none
  | n + 1, I =>
    if I.w ≤ 10 ∨ I.h ≤ 10 then solveZ2 thin I else
    match blkX I with
    | some b =>
      match solveR thin n (b.del I) with
      | some pq => some (b.lift (b.del I) pq.1 pq.2)
      | none => none
    | none =>
      match blkX I.transpose with
      | some b =>
        match solveR thin n (b.del I.transpose) with
        | some pq => some ((b.lift (b.del I.transpose) pq.1 pq.2).1.map Prod.swap,
            (b.lift (b.del I.transpose) pq.1 pq.2).2.map Prod.swap)
        | none => none
      | none => solveZ2 thin I

/-- The construction, on well-formed instances. -/
def solveZ3 (thin : Inst → Option (List Coord × List Coord)) (I : Inst) :
    Option (List Coord × List Coord) :=
  if I.WellFormed then solveR thin (I.w + I.h) I else none

theorem inDom_of {I : Inst} (hwf : I.WellFormed) (h : ¬ (I.w ≤ 10 ∨ I.h ≤ 10)) : InDom I :=
  ⟨by omega, by omega, hwf⟩

/-- **Every answer is a solution**, for any `thin`. -/
theorem solveR_sound (thin : Inst → Option (List Coord × List Coord)) :
    ∀ (n : ℕ) (I : Inst) (p q : List Coord), I.WellFormed → solveR thin n I = some (p, q) →
      IsSolution I p q := by
  intro n
  induction n with
  | zero => intro I p q _ h; simp [solveR] at h
  | succ n ih =>
    intro I p q hwf h
    simp only [solveR] at h
    split_ifs at h with hs
    · exact solveZ2_sound thin h
    · have hI := inDom_of hwf hs
      split at h
      · rename_i b hb
        have ok := blkX_ok hI hb
        split at h
        · rename_i pq hpq
          have e := Option.some.inj h
          have h1 : p = (b.lift (b.del I) pq.1 pq.2).1 := by rw [e]
          have h2 : q = (b.lift (b.del I) pq.1 pq.2).2 := by rw [e]
          rw [h1, h2]
          exact ok.lift _ _ (ih _ _ _ (chain_inDom ok.chain hI).2.2 hpq)
        · cases h
      · split at h
        · rename_i b hb
          have hIT := inDom_transpose hI
          have ok := blkX_ok hIT hb
          split at h
          · rename_i pq hpq
            have e := Option.some.inj h
            have h1 : p = (b.lift (b.del I.transpose) pq.1 pq.2).1.map Prod.swap :=
              (Prod.mk.inj e).1.symm
            have h2 : q = (b.lift (b.del I.transpose) pq.1 pq.2).2.map Prod.swap :=
              (Prod.mk.inj e).2.symm
            rw [h1, h2]
            exact (ok.lift _ _ (ih _ _ _ (chain_inDom ok.chain hIT).2.2 hpq)).of_transpose
          · cases h
        · exact solveZ2_sound thin h

theorem solveR_complete {thin : Inst → Option (List Coord × List Coord)} (hthin : ThinOK16 thin) :
    ∀ (n : ℕ) (I : Inst), I.WellFormed → Solvable I → I.w + I.h ≤ n →
      ∃ p q, solveR thin n I = some (p, q) := by
  intro n
  induction n with
  | zero =>
    intro I hwf _ hn
    have := hwf.1
    unfold InBounds at this
    omega
  | succ n ih =>
    intro I hwf hS hn
    simp only [solveR]
    by_cases hs : I.w ≤ 10 ∨ I.h ≤ 10
    · rw [ite_t hs]; exact solveZ2_complete hthin hwf hS
    · rw [ite_f hs]
      have hI := inDom_of hwf hs
      have hP : Passes I := (passes_iff_solvable I hwf hI.1 hI.2.1).2 hS
      cases hb : blkX I with
      | some b =>
        have ok := blkX_ok hI hb
        obtain ⟨hJ, hPJ⟩ := chain_pass ok.chain hI hP
        have hSJ := (passes_iff_solvable _ hJ.2.2 hJ.1 hJ.2.1).1 hPJ
        obtain ⟨p, q, hpq⟩ := ih _ hJ.2.2 hSJ (by have := ok.smaller; have := ok.sameH; omega)
        simp only [hpq]
        exact ⟨_, _, rfl⟩
      | none =>
        have hIT := inDom_transpose hI
        have hPT := passT hI hP
        cases hbT : blkX I.transpose with
        | some b =>
          have ok := blkX_ok hIT hbT
          obtain ⟨hJ, hPJ⟩ := chain_pass ok.chain hIT hPT
          have hSJ := (passes_iff_solvable _ hJ.2.2 hJ.1 hJ.2.1).1 hPJ
          have hTw : I.transpose.w = I.h := rfl
          have hTh : I.transpose.h = I.w := rfl
          obtain ⟨p, q, hpq⟩ := ih _ hJ.2.2 hSJ (by have := ok.smaller; have := ok.sameH; omega)
          simp only [hpq]
          exact ⟨_, _, rfl⟩
        | none => exact solveZ2_complete hthin hwf hS

theorem solveZ3_sound (thin : Inst → Option (List Coord × List Coord)) {I : Inst}
    {p q : List Coord} (h : solveZ3 thin I = some (p, q)) : IsSolution I p q := by
  unfold solveZ3 at h
  split_ifs at h with hwf
  exact solveR_sound thin _ I p q hwf h

theorem solveZ3_complete {thin : Inst → Option (List Coord × List Coord)} (hthin : ThinOK16 thin)
    {I : Inst} (hwf : I.WellFormed) (hS : Solvable I) : ∃ p q, solveZ3 thin I = some (p, q) := by
  unfold solveZ3
  rw [ite_t hwf]
  exact solveR_complete hthin _ I hwf hS le_rfl

end ZZN

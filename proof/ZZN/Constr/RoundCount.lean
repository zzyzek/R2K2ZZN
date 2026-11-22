/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Constr.Round

@[expose] public section

/-!
# How many blocks, and how large the instance is at the end

`phi I` counts the gaps that still admit a block, on both axes: the left gap, the right gap and
the pairs of adjacent endpoint lines with room between them. It is at most 36 (`phi_le`), and
every block deletion lowers it (`phi_del`, `phi_delT`). When no block is left on an axis, that side
is at most 37 (`w_le_of_none`): at most 3 free lines at each edge and at most 10 between adjacent
endpoint lines.
-/

namespace ZZN

open GridHam

theorem countP_lt {α : Type} {P Q : α → Bool} :
    ∀ {l : List α}, (∀ y ∈ l, P y = true → Q y = true) → (∃ z ∈ l, Q z = true ∧ P z = false) →
      l.countP P < l.countP Q
  | [], _, h => by obtain ⟨z, hz, -⟩ := h; simp at hz
  | y :: l, hPQ, ⟨z, hz, hQ, hP⟩ => by
    have hle : l.countP P ≤ l.countP Q :=
      List.countP_mono_left (fun x hx hp => hPQ x (List.mem_cons_of_mem _ hx) hp)
    rw [List.countP_cons, List.countP_cons]
    rcases List.mem_cons.mp hz with rfl | hz
    · simp [hQ, hP]; omega
    · have := countP_lt (fun x hx hp => hPQ x (List.mem_cons_of_mem _ hx) hp) ⟨z, hz, hQ, hP⟩
      cases hy : P y
      · simp; split_ifs <;> omega
      · simp [hPQ y List.mem_cons_self hy]; omega

theorem countP_le_of {α : Type} {P Q : α → Bool} {l : List α}
    (hPQ : ∀ y ∈ l, P y = true → Q y = true) : l.countP P ≤ l.countP Q :=
  List.countP_mono_left hPQ

/-! ### The span of the endpoint lines -/

/-- Adjacent values of `xs` (no value strictly between) differ by at most `g`: then each value is
within `g` per larger value of the largest. -/
theorem span_le (xs : List ℕ) (g : ℕ)
    (hgap : ∀ a ∈ xs, ∀ b ∈ xs, a < b → (∀ x ∈ xs, ¬ (a < x ∧ x < b)) → b ≤ a + g) :
    ∀ c x, x ∈ xs → xs.countP (fun y => decide (x < y)) = c → ∀ M ∈ xs, M ≤ x + g * c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro x hx hc M hM
    by_cases hlt : x < M
    · classical
      have hex : ∃ n, n ∈ xs ∧ x < n := ⟨M, hM, hlt⟩
      let n := Nat.find hex
      have hn : n ∈ xs ∧ x < n := Nat.find_spec hex
      have hmin : ∀ y ∈ xs, x < y → n ≤ y := fun y hy hxy => Nat.find_min' hex ⟨hy, hxy⟩
      have hnx : n ≤ x + g := hgap x hx n hn.1 hn.2 (fun z hz h => by
        have := hmin z hz h.1; omega)
      have hcnt : xs.countP (fun y => decide (n < y)) < c := by
        rw [← hc]
        refine countP_lt (fun y _ h => ?_) ⟨n, hn.1, by simp [hn.2], by simp⟩
        simp only [decide_eq_true_eq] at h ⊢; omega
      have := ih _ hcnt n hn.1 rfl M hM
      have hc1 : 1 ≤ c := by omega
      have : g * xs.countP (fun y => decide (n < y)) + g ≤ g * c := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hcnt
      omega
    · omega

theorem xmin_le {I : Inst} : ∀ x ∈ xsOf I, xmin I ≤ x ∧ x ≤ xmax I := by
  intro x hx
  obtain ⟨e, he, rfl⟩ := mem_xsOf.mp hx
  exact ends_x e he

theorem xmin_mem (I : Inst) : xmin I ∈ xsOf I := by
  simp only [xmin, xsOf, Inst.ends, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false]
  omega

theorem xmax_mem (I : Inst) : xmax I ∈ xsOf I := by
  simp only [xmax, xsOf, Inst.ends, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false]
  omega

/-- **With no block left on the x-axis, the width is at most 37.** -/
theorem w_le_of_none {I : Inst} (h : blkX I = none) : I.w ≤ 37 := by
  unfold blkX at h
  split_ifs at h with hl hr
  cases hp : innerPair I with
  | some ab => rw [hp] at h; cases h
  | none =>
    by_contra hw
    have hl' : xmin I ≤ 3 := by
      unfold leftK at hl
      omega
    have hr' : I.w ≤ xmax I + 4 := by
      unfold rightK at hr
      omega
    have hgap : ∀ a ∈ xsOf I, ∀ b ∈ xsOf I, a < b → (∀ x ∈ xsOf I, ¬ (a < x ∧ x < b)) →
        b ≤ a + 10 := by
      intro a ha b hb hab hbet
      have hn := List.find?_eq_none.mp hp (a, b) (by
        simp only [List.mem_flatMap, List.mem_map]
        exact ⟨a, ha, b, hb, rfl⟩)
      simp only [gapOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
        Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt, not_and] at hn
      have hk : ¬ 1 ≤ innerK I a b := fun hk => hn ⟨hab, fun x hx => by
        have := hbet x hx
        omega⟩ hk
      unfold innerK at hk
      omega
    have hc : (xsOf I).countP (fun y => decide (xmin I < y)) ≤ 3 := by
      have h1 := countP_lt (P := fun y => decide (xmin I < y)) (Q := fun _ => true)
        (l := xsOf I) (fun _ _ _ => rfl) ⟨xmin I, xmin_mem I, rfl, by simp⟩
      rw [List.countP_true] at h1
      have h2 : (xsOf I).length = 4 := rfl
      omega
    have := span_le (xsOf I) 10 hgap _ (xmin I) (xmin_mem I) rfl (xmax I) (xmax_mem I)
    omega

/-! ### The number of open gaps -/

def pairsOf (xs : List ℕ) : List (ℕ × ℕ) := xs.flatMap fun a => xs.map fun b => (a, b)

/-- The gaps on the x-axis that still admit a block. -/
def phiX (I : Inst) : ℕ :=
  (if 1 ≤ leftK I then 1 else 0) + (if 1 ≤ rightK I then 1 else 0) +
    (pairsOf (xsOf I)).countP (gapOK I)

/-- The gaps on both axes that still admit a block. -/
def phi (I : Inst) : ℕ := phiX I + phiX I.transpose

theorem phiX_le (I : Inst) : phiX I ≤ 18 := by
  have h1 := List.countP_le_length (p := gapOK I) (l := pairsOf (xsOf I))
  have h2 : (pairsOf (xsOf I)).length = 16 := rfl
  unfold phiX
  split_ifs <;> omega

theorem phi_le (I : Inst) : phi I ≤ 36 := by
  have := phiX_le I; have := phiX_le I.transpose; unfold phi; omega

theorem xs_four {I J : Inst} {g : ℕ → ℕ} (h : xsOf J = (xsOf I).map g) :
    J.s0.1 = g I.s0.1 ∧ J.t0.1 = g I.t0.1 ∧ J.s1.1 = g I.s1.1 ∧ J.t1.1 = g I.t1.1 := by
  simp only [xsOf, Inst.ends, List.map_cons, List.map_nil, List.cons.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem phiX_congr {I J : Inst} (hw : I.w = J.w) (hx : xsOf I = xsOf J) : phiX I = phiX J := by
  have e := xs_four (g := id) (I := I) (J := J) (by rw [List.map_id]; exact hx.symm)
  simp only [id] at e
  obtain ⟨e0, e1, e2, e3⟩ := e
  unfold phiX leftK rightK xmin xmax gapOK innerK
  rw [hx, hw, e0, e1, e2, e3]

theorem pairsOf_map (g : ℕ → ℕ) (xs : List ℕ) :
    pairsOf (xs.map g) = (pairsOf xs).map (Prod.map g g) := by
  unfold pairsOf
  rw [List.flatMap_map, List.map_flatMap]
  congr 1
  funext a
  rw [List.map_map, List.map_map]
  rfl

theorem mem_pairsOf {xs : List ℕ} {ab : ℕ × ℕ} : ab ∈ pairsOf xs ↔ ab.1 ∈ xs ∧ ab.2 ∈ xs := by
  obtain ⟨a, b⟩ := ab
  simp [pairsOf]

/-- **Deleting lines never opens a gap**: the left and right sizes do not grow, and every pair
that admits a block afterwards admitted one before. -/
theorem phiX_core {I J : Inst} (g : ℕ → ℕ) (k : ℕ) (hxs : xsOf J = (xsOf I).map g)
    (hw : J.w = I.w - 2 * k) (hk : 2 * k + 11 ≤ I.w)
    (g1 : ∀ x ∈ xsOf I, g x ≤ x ∧ x ≤ g x + 2 * k)
    (g2 : ∀ a ∈ xsOf I, ∀ b ∈ xsOf I, a < b → g a < g b ∧ g b + a ≤ b + g a) :
    leftK J ≤ leftK I ∧ rightK J ≤ rightK I ∧
      (pairsOf (xsOf J)).countP (gapOK J) =
        (pairsOf (xsOf I)).countP (fun ab => gapOK J (g ab.1, g ab.2)) ∧
      (∀ ab ∈ pairsOf (xsOf I), gapOK J (g ab.1, g ab.2) = true → gapOK I ab = true) := by
  obtain ⟨e0, e1, e2, e3⟩ := xs_four hxs
  have m : ∀ e ∈ I.ends, e.1 ∈ xsOf I := fun e he => List.mem_map_of_mem he
  obtain ⟨m0, m1, m2, m3⟩ := ends_all m
  have f0 := g1 _ m0; have f1 := g1 _ m1; have f2 := g1 _ m2; have f3 := g1 _ m3
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold leftK xmin; rw [e0, e1, e2, e3, hw]; omega
  · unfold rightK xmax; rw [e0, e1, e2, e3, hw]; omega
  · rw [hxs, pairsOf_map, List.countP_map]; rfl
  · rintro ⟨a, b⟩ hab hg
    obtain ⟨ha, hb⟩ := mem_pairsOf.mp hab
    simp only [gapOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
      Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt] at hg ⊢
    obtain ⟨⟨hlt, hbet⟩, hk1⟩ := hg
    have hab' : a < b := by
      rcases Nat.lt_trichotomy a b with h | rfl | h
      · exact h
      · omega
      · have := (g2 b hb a ha h).1; omega
    have hd := (g2 a ha b hb hab').2
    refine ⟨⟨hab', fun x hx => ?_⟩, ?_⟩
    · have := hbet (g x) (by rw [hxs]; exact List.mem_map_of_mem hx)
      by_contra hc
      push Not at hc
      obtain ⟨c1, c2⟩ := hc
      have := (g2 a ha x hx c1).1
      have := (g2 x hx b hb c2).1
      omega
    · unfold innerK at hk1 ⊢
      rw [hw] at hk1
      omega

/-- The map of x-coordinates of a block deletion. -/
def Blk.gx : Blk → ℕ → ℕ
  | .left k => fun x => x - 2 * k
  | .right _ => id
  | .inner r k => fun x => if x ≤ r then x else x - 2 * k

def Blk.k : Blk → ℕ
  | .left k => k
  | .right k => k
  | .inner _ k => k

theorem xsOf_del (b : Blk) (I : Inst) : xsOf (b.del I) = (xsOf I).map b.gx := by
  cases b with
  | left k => rfl
  | right k => rfl
  | inner r k =>
    simp only [xsOf, Inst.ends, Blk.del, Blk.gx, Inst.dropIn, Inst.mapE, List.map_cons,
      List.map_nil, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs <;> rfl

theorem w_del (b : Blk) (I : Inst) : (b.del I).w = I.w - 2 * b.k := by
  cases b <;> rfl

theorem ysOf_del (b : Blk) (I : Inst) :
    xsOf (b.del I).transpose = xsOf I.transpose := by
  cases b with
  | left k => rfl
  | right k => rfl
  | inner r k =>
    simp only [xsOf, Inst.ends, Inst.transpose, Blk.del, Inst.dropIn, Inst.mapE, List.map_cons,
      List.map_nil, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs <;> rfl

/-- **A block deletion leaves the other axis alone.** -/
theorem phiX_delT (b : Blk) (I : Inst) : phiX (b.del I).transpose = phiX I.transpose :=
  phiX_congr (by cases b <;> rfl) (ysOf_del b I)

/-- **A block deletion closes its gap.** -/
theorem phiX_del {I : Inst} {b : Blk} (hb : blkX I = some b) :
    phiX (b.del I) < phiX I := by
  unfold blkX at hb
  split_ifs at hb with hl hr
  · -- left edge
    cases hb
    obtain ⟨s1, s2⟩ := leftK_spec hl
    have hk : leftK I = min ((min (min I.s0.1 I.t0.1) (min I.s1.1 I.t1.1) - 2) / 2)
      ((I.w - 11) / 2) := rfl
    have hxl : ∀ x ∈ xsOf I, 2 * leftK I + 2 ≤ x := fun x hx => by
      have := (xmin_le x hx).1; omega
    obtain ⟨-, cR, cE, cI⟩ := phiX_core (I := I) (J := (Blk.left (leftK I)).del I)
      (Blk.left (leftK I)).gx (leftK I) (xsOf_del _ I) (w_del _ I) s2
      (fun x hx => by have := hxl x hx; simp only [Blk.gx]; omega)
      (fun a ha b hb hab => by
        have := hxl a ha; have := hxl b hb; simp only [Blk.gx]; omega)
    have h0 : ¬ 1 ≤ leftK ((Blk.left (leftK I)).del I) := by
      obtain ⟨e0, e1, e2, e3⟩ := xs_four (xsOf_del (Blk.left (leftK I)) I)
      have hw' := w_del (Blk.left (leftK I)) I
      simp only [Blk.gx, Blk.k] at e0 e1 e2 e3 hw'
      generalize (Blk.left (leftK I)).del I = J at e0 e1 e2 e3 hw' ⊢
      generalize leftK I = k at *
      unfold leftK xmin
      rw [e0, e1, e2, e3, hw']
      omega
    have hle := countP_le_of cI
    unfold phiX
    rw [cE, ite_f h0, ite_t hl]
    split_ifs <;> omega
  · -- right edge
    cases hb
    obtain ⟨s1, s2⟩ := rightK_spec hr
    have hk : rightK I = min ((I.w - 3 - max (max I.s0.1 I.t0.1) (max I.s1.1 I.t1.1)) / 2)
      ((I.w - 11) / 2) := rfl
    obtain ⟨cL, -, cE, cI⟩ := phiX_core (I := I) (J := (Blk.right (rightK I)).del I)
      (Blk.right (rightK I)).gx (rightK I) (xsOf_del _ I) (w_del _ I) s2
      (fun x hx => by simp only [Blk.gx, id]; omega)
      (fun a ha b hb hab => by simp only [Blk.gx, id]; omega)
    have h0 : ¬ 1 ≤ rightK ((Blk.right (rightK I)).del I) := by
      obtain ⟨e0, e1, e2, e3⟩ := xs_four (xsOf_del (Blk.right (rightK I)) I)
      have hw' := w_del (Blk.right (rightK I)) I
      simp only [Blk.gx, Blk.k, id] at e0 e1 e2 e3 hw'
      generalize (Blk.right (rightK I)).del I = J at e0 e1 e2 e3 hw' ⊢
      generalize rightK I = k at *
      unfold rightK xmax
      rw [e0, e1, e2, e3, hw']
      omega
    have hle := countP_le_of cI
    unfold phiX
    rw [cE, ite_f h0, ite_t hr]
    split_ifs <;> omega
  · -- inner block
    cases hp : innerPair I with
    | none => rw [hp] at hb; cases hb
    | some ab =>
      rw [hp] at hb
      cases hb
      obtain ⟨a, c⟩ := ab
      have hg := List.find?_some hp
      have hmem := List.mem_of_find?_eq_some hp
      have hmem' : (a, c) ∈ pairsOf (xsOf I) := hmem
      simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq] at hmem
      obtain ⟨a', ha', c', hc', rfl, rfl⟩ := hmem
      have hg' := hg
      simp only [gapOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
        Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt] at hg'
      obtain ⟨⟨hac, hbet⟩, hk1⟩ := hg'
      obtain ⟨s1, s2⟩ := innerK_spec hk1
      have hkdef : innerK I a' c' = min ((c' - a' - 9) / 2) ((I.w - 11) / 2) := rfl
      have side : ∀ x ∈ xsOf I, x ≤ a' ∨ c' ≤ x := fun x hx => by
        have := hbet x hx; omega
      generalize hK : innerK I a' c' = k at s1 s2 hkdef hk1
      have hz : innerK ((Blk.inner (a' + 1) k).del I) a' (c' - 2 * k) = 0 := by
        unfold innerK
        rw [w_del]
        simp only [Blk.k]
        omega
      obtain ⟨cL, cR, cE, cI⟩ := phiX_core (I := I) (J := (Blk.inner (a' + 1) k).del I)
        (Blk.inner (a' + 1) k).gx k (xsOf_del _ I) (w_del _ I) s2
        (fun x hx => by have := side x hx; simp only [Blk.gx]; split_ifs <;> omega)
        (fun x hx y hy hxy => by
          have := side x hx; have := side y hy; simp only [Blk.gx]; split_ifs <;> omega)
      have hPz : gapOK ((Blk.inner (a' + 1) k).del I)
          ((Blk.inner (a' + 1) k).gx a', (Blk.inner (a' + 1) k).gx c') = false := by
        have g1 : (Blk.inner (a' + 1) k).gx a' = a' := by simp only [Blk.gx]; rw [ite_t (by omega)]
        have g2 : (Blk.inner (a' + 1) k).gx c' = c' - 2 * k := by
          simp only [Blk.gx]; rw [ite_f (by omega)]
        rw [g1, g2]
        simp only [gapOK, hz, Bool.and_eq_false_iff, decide_eq_false_iff_not]
        right; omega
      have hstrict : (pairsOf (xsOf I)).countP (fun ab => gapOK ((Blk.inner (a' + 1) k).del I)
            ((Blk.inner (a' + 1) k).gx ab.1, (Blk.inner (a' + 1) k).gx ab.2)) <
          (pairsOf (xsOf I)).countP (gapOK I) :=
        countP_lt (fun y hy h => cI y hy h) ⟨(a', c'), hmem', hg, hPz⟩
      show phiX ((Blk.inner (a' + 1) k).del I) < phiX I
      unfold phiX
      rw [cE]
      split_ifs <;> omega

/-- **Each block level lowers `phi`**, on either axis. -/
theorem phi_del {I : Inst} {b : Blk} (hb : blkX I = some b) :
    phi (b.del I) < phi I := by
  unfold phi
  rw [phiX_delT]
  have := phiX_del hb
  omega

theorem phi_delT {I : Inst} {b : Blk} (hb : blkX I.transpose = some b) :
    phi (b.del I.transpose) < phi I := by
  unfold phi
  rw [phiX_delT, Inst.transpose_transpose]
  have := phiX_del hb
  omega

end ZZN

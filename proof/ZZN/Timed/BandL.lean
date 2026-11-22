/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.TimedStatement
public import ZZN.Constr.LiftL
public import ZZN.Timed.Band
public import ZZN.Timed.BandCost

@[expose] public section

/-!
# The counted one-pass band extension

`bandExtLT` (`ZZN/TimedStatement.lean`) returns `bandExtL` (`bandExtLT_ret`). The counts `K` of
the pure version are a function; the counted version keeps them in a list read with `[z]!`
(`toF`).
-/

namespace ZZN.T

open ZZN GridHam

instance (l : List Coord) (u v : Coord) : Decidable (Used l u v) := by
  unfold Used; infer_instance

/-- A list of counts read as a function. -/
def toF (l : List ℕ) : ℕ → ℕ := fun z => l[z]!

theorem toF_modify (l : List ℕ) (c : ℕ) (hc : c < l.length) :
    toF (l.modify c (· + 1)) = Function.update (toF l) c (toF l c + 1) := by
  funext z
  unfold toF
  by_cases hz : z = c
  · subst hz
    simp [Function.update_self, List.getElem!_eq_getElem?_getD, hc]
  · rw [Function.update_of_ne hz]
    simp [List.getElem!_eq_getElem?_getD, Ne.symm hz]

/-! ### Pair scans -/

theorem infix_pair_cons {a b u v : Coord} {l : List Coord} :
    [u, v] <:+: a :: b :: l ↔ (a = u ∧ b = v) ∨ [u, v] <:+: b :: l := by
  rw [List.infix_cons_iff]
  constructor
  · rintro (h | h)
    · left
      obtain ⟨t, ht⟩ := h
      simp only [List.cons_append, List.cons.injEq] at ht
      exact ⟨ht.1.symm, ht.2.1.symm⟩
    · exact Or.inr h
  · rintro (⟨rfl, rfl⟩ | h)
    · exact Or.inl ⟨l, rfl⟩
    · exact Or.inr h

theorem used_cons {a b u v : Coord} {l : List Coord} :
    Used (a :: b :: l) u v ↔ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) ∨ Used (b :: l) u v := by
  unfold Used
  rw [infix_pair_cons, infix_pair_cons]
  tauto

theorem crossRowsT_mem (r : ℕ) : ∀ (l : List Coord) (y : ℕ),
    y ∈ (crossRowsT r l).ret ↔ Used l (r, y) (r + 1, y)
  | [], y => by simp [crossRowsT, Used]
  | [a], y => by
    simp only [crossRowsT, ret_pure, List.not_mem_nil, false_iff]
    rintro (h | h) <;> have := h.length_le <;> simp at this
  | a :: b :: l, y => by
    have ih := crossRowsT_mem r (b :: l) y
    rw [used_cons, ← ih]
    simp only [crossRowsT, ret_bind]
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    have key : ((((a1 = r ∧ b1 = r + 1) ∨ (a1 = r + 1 ∧ b1 = r)) ∧ a2 = b2) ∧ y = a2) ↔
        (((a1, a2) = (r, y) ∧ (b1, b2) = (r + 1, y)) ∨ ((a1, a2) = (r + 1, y) ∧ (b1, b2) = (r, y))) := by
      simp only [Prod.mk.injEq]; omega
    rw [← key]
    show y ∈ (if (((a1 = r ∧ b1 = r + 1) ∨ (a1 = r + 1 ∧ b1 = r)) ∧ a2 = b2) then
      a2 :: (crossRowsT r ((b1, b2) :: l)).ret else (crossRowsT r ((b1, b2) :: l)).ret) ↔ _
    by_cases hc : ((a1 = r ∧ b1 = r + 1) ∨ (a1 = r + 1 ∧ b1 = r)) ∧ a2 = b2
    · rw [ite_t hc, List.mem_cons]; tauto
    · rw [ite_f hc]; tauto

theorem flipRowsT_mem (r : ℕ) : ∀ (l : List Coord) (y : ℕ),
    y ∈ (flipRowsT r l).ret ↔ Used l (r, y) (r, y + 1)
  | [], y => by simp [flipRowsT, Used]
  | [a], y => by
    simp only [flipRowsT, ret_pure, List.not_mem_nil, false_iff]
    rintro (h | h) <;> have := h.length_le <;> simp at this
  | a :: b :: l, y => by
    have ih := flipRowsT_mem r (b :: l) y
    rw [used_cons, ← ih]
    simp only [flipRowsT, ret_bind]
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    have key : ((a1 = r ∧ b1 = r ∧ b2 = a2 + 1) ∧ y = a2) ∨
        ((¬(a1 = r ∧ b1 = r ∧ b2 = a2 + 1)) ∧ (a1 = r ∧ b1 = r ∧ a2 = b2 + 1) ∧ y = b2) ↔
        (((a1, a2) = (r, y) ∧ (b1, b2) = (r, y + 1)) ∨ ((a1, a2) = (r, y + 1) ∧ (b1, b2) = (r, y))) := by
      simp only [Prod.mk.injEq]; omega
    rw [← key]
    show y ∈ (if (a1 = r ∧ b1 = r ∧ b2 = a2 + 1) then a2 :: (flipRowsT r ((b1, b2) :: l)).ret
      else if (a1 = r ∧ b1 = r ∧ a2 = b2 + 1) then b2 :: (flipRowsT r ((b1, b2) :: l)).ret
      else (flipRowsT r ((b1, b2) :: l)).ret) ↔ _
    by_cases hc1 : a1 = r ∧ b1 = r ∧ b2 = a2 + 1
    · rw [ite_t hc1, List.mem_cons]; tauto
    · rw [ite_f hc1]
      by_cases hc2 : a1 = r ∧ b1 = r ∧ a2 = b2 + 1
      · rw [ite_t hc2, List.mem_cons]; tauto
      · rw [ite_f hc2]; tauto

/-! ### Return values -/

theorem seedT_ret (h r : ℕ) (p q : List Coord) (cr fr : List ℕ)
    (hcr : ∀ y, y ∈ cr ↔ Cross p q r y)
    (hfr : ∀ y, y ∈ fr ↔ (Used p (r, y) (r, y + 1) ∨ Used q (r, y) (r, y + 1))) (R : ℕ) :
    (seedT h cr fr R).ret = decide (SeedAt h p q r R) := by
  have c0 : cr.contains (R - 1) = decide (Cross p q r (R - 1)) := by
    rw [Bool.eq_iff_iff, List.contains_iff_mem, hcr]; simp
  have c1 : cr.contains R = decide (Cross p q r R) := by
    rw [Bool.eq_iff_iff, List.contains_iff_mem, hcr]; simp
  have f0 : fr.contains (R - 1) = decide (Used p (r, R - 1) (r, R - 1 + 1) ∨
      Used q (r, R - 1) (r, R - 1 + 1)) := by
    rw [Bool.eq_iff_iff, List.contains_iff_mem, hfr]; simp
  simp only [seedT, lcontainsT, ret_bind, ret_pure, c0, c1, f0]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not]
  unfold SeedAt
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · simp
  · have e : R - 1 + 1 = R := by omega
    rw [e]
    tauto

theorem planLeftT_ret : ∀ (L : ℕ) (U : Finset ℕ) (K : List ℕ) (c : ℕ), L ≤ c → c < K.length →
    toF (planLeftT L U K c).ret = planLeft L U (toF K) c ∧ (planLeftT L U K c).ret.length = K.length
  | 0, _, _, _, _, _ => ⟨rfl, rfl⟩
  | L + 1, U, K, c, hLc, hcK => by
    simp only [planLeftT, planLeft, fmemT, ret_bind]
    by_cases hL : L ∈ U
    · simp only [hL, decide_true, ↓reduceIte, feraseT, lmodifyT, ret_bind]
      have hlen : (K.modify c (· + 1)).length = K.length := by simp
      obtain ⟨e1, e2⟩ := planLeftT_ret L (U.erase L) (K.modify c (· + 1)) c (by omega) (by omega)
      rw [e1, e2, hlen, toF_modify K c hcK]
      exact ⟨rfl, rfl⟩
    · simp only [hL, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact planLeftT_ret L U K L le_rfl (by omega)

theorem planRightT_ret (h : ℕ) : ∀ (n R0 : ℕ) (U : Finset ℕ) (K : List ℕ) (c : ℕ), c < K.length →
    h ≤ K.length →
    toF (planRightT h n R0 U K c).ret = planRight h n R0 U (toF K) c ∧
      (planRightT h n R0 U K c).ret.length = K.length
  | 0, _, _, _, _, _, _ => ⟨rfl, rfl⟩
  | n + 1, R0, U, K, c, hcK, hhK => by
    simp only [planRightT, planRight, fmemT, ret_bind]
    by_cases hR : R0 + 1 ∈ U
    · simp only [hR, decide_true, ↓reduceIte, feraseT, lmodifyT, ret_bind]
      have hlen : (K.modify c (· + 1)).length = K.length := by simp
      obtain ⟨e1, e2⟩ := planRightT_ret h n (R0 + 1) (U.erase (R0 + 1)) (K.modify c (· + 1)) c
        (by omega) (by omega)
      rw [e1, e2, hlen, toF_modify K c hcK]
      exact ⟨rfl, rfl⟩
    · simp only [hR, decide_false, Bool.false_eq_true, ↓reduceIte]
      by_cases hlast : R0 + 1 < h
      · simp only [hlast, ↓reduceIte]
        exact planRightT_ret h n (R0 + 1) U K (R0 + 1) (by omega) hhK
      · simp only [hlast, ↓reduceIte, ret_pure]
        refine ⟨?_, ?_⟩ <;> first | rfl | trivial

theorem detT_ret1 (r a k : ℕ) (up : Bool) : (detT r a k up 1).ret = Gf r a k up := by
  simp [detT, rangeT, lmapT, lreverseT, lappendT, Gf, runRow]

theorem detT_ret2 (r a k : ℕ) (up : Bool) : (detT r a k up 2).ret = Gb r a k up := by
  simp [detT, rangeT, lmapT, lreverseT, lappendT, Gb, runRow]

theorem insKT_ret (r : ℕ) (K : List ℕ) (R : ℕ) (fl : Bool) (x y : Coord) :
    (insKT r K R fl x y).ret = insK r (toF K) R fl x y := by
  unfold insKT insK
  split_ifs <;> simp [lgetT, detT_ret1, detT_ret2, lappendT, toF]

theorem extLT_ret (r : ℕ) (K : List ℕ) (R : ℕ) (fl : Bool) :
    ∀ l : List Coord, (extLT r K R fl l).ret = extL r (toF K) R fl l
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    simp only [extLT, extL, ret_bind, ret_pure, lappendT, insKT_ret, extLT_ret r K R fl (b :: l)]

theorem extPT_ret (r : ℕ) (K : List ℕ) (R : ℕ) (fl : Bool) (p q : List Coord) :
    (extPT r K R fl p q).ret = extP r (toF K) R fl p q := by
  simp [extPT, extP, extLT_ret]

/-- **The counted band extension returns `bandExtL`.** -/
theorem bandExtLT_ret (I : Inst) (r : ℕ) (p q : List Coord) :
    (bandExtLT I.h r p q).ret = bandExtL I r p q := by
  have hcr : ∀ y, y ∈ (crossRowsT r p).ret ++ (crossRowsT r q).ret ↔ Cross p q r y := by
    intro y; rw [List.mem_append, crossRowsT_mem, crossRowsT_mem]; rfl
  have hfr : ∀ y, y ∈ (flipRowsT r p).ret ++ (flipRowsT r q).ret ↔
      (Used p (r, y) (r, y + 1) ∨ Used q (r, y) (r, y + 1)) := by
    intro y; rw [List.mem_append, flipRowsT_mem, flipRowsT_mem]
  have hcon : ∀ y, ((crossRowsT r p).ret ++ (crossRowsT r q).ret).contains y =
      decide (Cross p q r y) := by
    intro y; rw [Bool.eq_iff_iff, List.contains_iff_mem, hcr]; simp
  have hseed : (fun x => (seedT I.h ((crossRowsT r p).ret ++ (crossRowsT r q).ret)
      ((flipRowsT r p).ret ++ (flipRowsT r q).ret) x).ret) =
      (fun R => decide (SeedAt I.h p q r R)) := funext (seedT_ret I.h r p q _ _ hcr hfr)
  have hU0 : (frangeFilterT I.h (fun y => do
      let c ← lcontainsT ((crossRowsT r p).ret ++ (crossRowsT r q).ret) y
      pure !c)).ret = (Finset.range I.h).filter (fun y => ¬ Cross p q r y) := by
    simp only [frangeFilterT, ret_bind, lcontainsT, ret_pure, hcon]
    ext y; simp
  have hK0 : toF ((List.range (I.h + 1)).map (fun _ => 0)) = fun _ => 0 := by
    funext z; simp [toF, List.getElem!_eq_getElem?_getD]
  have hK0l : ((List.range (I.h + 1)).map (fun (_ : ℕ) => (0 : ℕ))).length = I.h + 1 := by simp
  simp only [bandExtLT, bandExtL, ret_bind, lappendT, rangeT, lfindT, lmapT, ret_pure, hseed]
  cases hf : (List.range (I.h + 1)).find? (fun R => decide (SeedAt I.h p q r R)) with
  | none => simp [stretchT_ret]
  | some R =>
    have hR : R ≤ I.h := by
      have := List.mem_range.mp (List.mem_of_find?_eq_some hf); omega
    dsimp only
    simp only [ret_bind]
    rw [hU0]
    simp only [lcontainsT, hcon]
    have hb : ((R == 0 || decide (Cross p q r (R - 1))) && (R == I.h || decide (Cross p q r R))) = true ↔
        ((R = 0 ∨ Cross p q r (R - 1)) ∧ (R = I.h ∨ Cross p q r R)) := by simp
    by_cases hc1 : (R = 0 ∨ Cross p q r (R - 1)) ∧ (R = I.h ∨ Cross p q r R)
    · rw [ite_t (hb.mpr hc1), ite_t hc1]
      by_cases hR0 : R = 0
      · rw [ite_t hR0, ite_t hR0]
        simp only [ret_bind, extPT_ret]
        rw [(planRightT_ret I.h _ _ _ _ _ (by rw [hK0l]; omega) (by rw [hK0l]; omega)).1, hK0]
      · rw [ite_f hR0, ite_f hR0]
        by_cases hRh : R = I.h
        · rw [ite_t hRh, ite_t hRh]
          simp only [ret_bind, extPT_ret]
          rw [(planLeftT_ret _ _ _ _ le_rfl (by rw [hK0l]; omega)).1, hK0]
        · rw [ite_f hRh, ite_f hRh]
          simp only [ret_bind, extPT_ret, ffilterT]
          obtain ⟨e1, e2⟩ := planLeftT_ret (R - 1) ((Finset.range I.h).filter (fun y => ¬ Cross p q r y))
            ((List.range (I.h + 1)).map (fun _ => 0)) (R - 1) le_rfl (by rw [hK0l]; omega)
          rw [(planRightT_ret I.h _ _ _ _ _ (by rw [e2, hK0l]; omega) (by rw [e2, hK0l]; omega)).1, e1, hK0]
          simp
    · rw [ite_f (fun h => hc1 (hb.mp h)), ite_f hc1]
      simp only [ret_bind, extPT_ret, ffilterT, feraseT]
      obtain ⟨e1, e2⟩ := planLeftT_ret (R - 1)
        ((((Finset.range I.h).filter (fun y => ¬ Cross p q r y)).erase (R - 1)).erase (R - 1 + 1))
        ((List.range (I.h + 1)).map (fun _ => 0)) (R - 1) le_rfl (by rw [hK0l]; omega)
      rw [(planRightT_ret I.h _ _ _ _ _ (by rw [e2, hK0l]; omega) (by rw [e2, hK0l]; omega)).1, e1, hK0]
      simp

/-! ### Sizes of the scans -/

theorem crossRowsT_time (r : ℕ) : ∀ l : List Coord, (crossRowsT r l).time ≤ l.length
  | [] => by simp [crossRowsT]
  | [_] => by simp [crossRowsT]
  | a :: b :: l => by
    have := crossRowsT_time r (b :: l)
    simp only [crossRowsT, time_bind, List.length_cons] at this ⊢
    omega

theorem flipRowsT_time (r : ℕ) : ∀ l : List Coord, (flipRowsT r l).time ≤ l.length
  | [] => by simp [flipRowsT]
  | [_] => by simp [flipRowsT]
  | a :: b :: l => by
    have := flipRowsT_time r (b :: l)
    simp only [flipRowsT, time_bind, List.length_cons] at this ⊢
    omega

theorem crossRowsT_nodup (r : ℕ) : ∀ l : List Coord, l.Nodup → (crossRowsT r l).ret.Nodup
  | [], _ => by simp [crossRowsT]
  | [_], _ => by simp [crossRowsT]
  | a :: b :: l, hn => by
    have ih := crossRowsT_nodup r (b :: l) (List.Nodup.of_cons hn)
    have ha : a ∉ b :: l := (List.nodup_cons.mp hn).1
    simp only [crossRowsT, ret_bind]
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    show (if (((a1 = r ∧ b1 = r + 1) ∨ (a1 = r + 1 ∧ b1 = r)) ∧ a2 = b2) then
      a2 :: (crossRowsT r ((b1, b2) :: l)).ret else (crossRowsT r ((b1, b2) :: l)).ret).Nodup
    by_cases hc : ((a1 = r ∧ b1 = r + 1) ∨ (a1 = r + 1 ∧ b1 = r)) ∧ a2 = b2
    · rw [ite_t hc, List.nodup_cons]
      refine ⟨fun hm => ?_, ih⟩
      have hu := (crossRowsT_mem r _ a2).mp hm
      rcases hc with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩
      · exact ha (Used.mem_left hu)
      · exact ha (Used.mem_right hu)
    · rw [ite_f hc]; exact ih

theorem flipRowsT_nodup (r : ℕ) : ∀ l : List Coord, l.Nodup → (flipRowsT r l).ret.Nodup
  | [], _ => by simp [flipRowsT]
  | [_], _ => by simp [flipRowsT]
  | a :: b :: l, hn => by
    have ih := flipRowsT_nodup r (b :: l) (List.Nodup.of_cons hn)
    have ha : a ∉ b :: l := (List.nodup_cons.mp hn).1
    simp only [flipRowsT, ret_bind]
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    show (if (a1 = r ∧ b1 = r ∧ b2 = a2 + 1) then a2 :: (flipRowsT r ((b1, b2) :: l)).ret
      else if (a1 = r ∧ b1 = r ∧ a2 = b2 + 1) then b2 :: (flipRowsT r ((b1, b2) :: l)).ret
      else (flipRowsT r ((b1, b2) :: l)).ret).Nodup
    by_cases hc1 : a1 = r ∧ b1 = r ∧ b2 = a2 + 1
    · rw [ite_t hc1, List.nodup_cons]
      refine ⟨fun hm => ?_, ih⟩
      have hu := (flipRowsT_mem r _ a2).mp hm
      obtain ⟨rfl, rfl, rfl⟩ := hc1
      exact ha (Used.mem_left hu)
    · rw [ite_f hc1]
      by_cases hc2 : a1 = r ∧ b1 = r ∧ a2 = b2 + 1
      · rw [ite_t hc2, List.nodup_cons]
        refine ⟨fun hm => ?_, ih⟩
        have hu := (flipRowsT_mem r _ b2).mp hm
        obtain ⟨rfl, rfl, rfl⟩ := hc2
        exact ha (Used.mem_right hu)
      · rw [ite_f hc2]; exact ih

/-- A list of distinct numbers below `h` has at most `h` entries. -/
theorem length_le_of_nodup_lt {l : List ℕ} {h : ℕ} (hn : l.Nodup) (hl : ∀ y ∈ l, y < h) :
    l.length ≤ h := by
  have hsub : l.toFinset ⊆ Finset.range h := fun y hy =>
    Finset.mem_range.mpr (hl y (List.mem_toFinset.mp hy))
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hn, Finset.card_range] at this
  exact this

theorem crossRowsT_len (r h : ℕ) {l : List Coord} (hn : l.Nodup) (hb : ∀ v ∈ l, v.2 < h) :
    (crossRowsT r l).ret.length ≤ h :=
  length_le_of_nodup_lt (crossRowsT_nodup r l hn)
    (fun y hy => hb _ (Used.mem_left ((crossRowsT_mem r l y).mp hy)))

theorem flipRowsT_len (r h : ℕ) {l : List Coord} (hn : l.Nodup) (hb : ∀ v ∈ l, v.2 < h) :
    (flipRowsT r l).ret.length ≤ h :=
  length_le_of_nodup_lt (flipRowsT_nodup r l hn)
    (fun y hy => hb _ (Used.mem_left ((flipRowsT_mem r l y).mp hy)))

/-! ### Step counts of the parts -/

theorem seedT_time (h : ℕ) (cr fr : List ℕ) (R : ℕ) :
    (seedT h cr fr R).time ≤ 2 * cr.length + fr.length + 3 := by
  simp [seedT, lcontainsT]; omega

theorem planLeftT_time : ∀ (L : ℕ) (U : Finset ℕ) (K : List ℕ) (c : ℕ),
    (planLeftT L U K c).time ≤ L * (2 * U.card + K.length + 3)
  | 0, _, _, _ => by simp [planLeftT]
  | L + 1, U, K, c => by
    simp only [planLeftT, fmemT, time_bind]
    by_cases hL : L ∈ U
    · simp only [hL, decide_true, ↓reduceIte, feraseT, lmodifyT, time_bind]
      have ih := planLeftT_time L (U.erase L) (K.modify c (· + 1)) c
      have h1 : (U.erase L).card ≤ U.card := Finset.card_erase_le
      have h2 : (K.modify c (· + 1)).length = K.length := by simp
      rw [h2] at ih
      have : L * (2 * (U.erase L).card + K.length + 3) ≤ L * (2 * U.card + K.length + 3) :=
        Nat.mul_le_mul_left _ (by omega)
      rw [Nat.succ_mul]; omega
    · simp only [hL, decide_false, Bool.false_eq_true, ↓reduceIte]
      have ih := planLeftT_time L U K L
      rw [Nat.succ_mul]; omega

theorem planRightT_time (h : ℕ) : ∀ (n R0 : ℕ) (U : Finset ℕ) (K : List ℕ) (c : ℕ),
    (planRightT h n R0 U K c).time ≤ n * (2 * U.card + K.length + 3)
  | 0, _, _, _, _ => by simp [planRightT]
  | n + 1, R0, U, K, c => by
    simp only [planRightT, fmemT, time_bind]
    by_cases hR : R0 + 1 ∈ U
    · simp only [hR, decide_true, ↓reduceIte, feraseT, lmodifyT, time_bind]
      have ih := planRightT_time h n (R0 + 1) (U.erase (R0 + 1)) (K.modify c (· + 1)) c
      have h1 : (U.erase (R0 + 1)).card ≤ U.card := Finset.card_erase_le
      have h2 : (K.modify c (· + 1)).length = K.length := by simp
      rw [h2] at ih
      have : n * (2 * (U.erase (R0 + 1)).card + K.length + 3) ≤ n * (2 * U.card + K.length + 3) :=
        Nat.mul_le_mul_left _ (by omega)
      rw [Nat.succ_mul]; omega
    · simp only [hR, decide_false, Bool.false_eq_true, ↓reduceIte]
      by_cases hlast : R0 + 1 < h
      · simp only [hlast, ↓reduceIte]
        have ih := planRightT_time h n (R0 + 1) U K (R0 + 1)
        rw [Nat.succ_mul]; omega
      · simp only [hlast, ↓reduceIte, time_pure]; rw [Nat.succ_mul]; omega

theorem detT_time (r a k : ℕ) (up : Bool) (c : ℕ) :
    (detT r a k up c).time ≤ 3 * (detT r a k up c).ret.length + 2 := by
  simp [detT, rangeT, lmapT, lreverseT, lappendT]
  omega

theorem insKT_time (r : ℕ) (K : List ℕ) (R : ℕ) (fl : Bool) (x y : Coord) :
    (insKT r K R fl x y).time ≤ (K.length + 8) * (insKT r K R fl x y).ret.length := by
  have dl : ∀ a k up c, 2 ≤ (detT r a k up c).ret.length := by
    intro a k up c; simp [detT, rangeT, lmapT, lreverseT, lappendT]; omega
  unfold insKT
  split_ifs
  · simp only [time_bind, ret_bind, lgetT]
    have := detT_time r x.2 (K[x.2]!) (decide (R ≤ x.2)) 1
    have := dl x.2 (K[x.2]!) (decide (R ≤ x.2)) 1
    nlinarith
  · simp only [time_bind, ret_bind, lgetT]
    have := detT_time r x.2 (K[x.2]!) (decide (R ≤ x.2)) 2
    have := dl x.2 (K[x.2]!) (decide (R ≤ x.2)) 2
    nlinarith
  · simp only [time_bind, ret_bind, lgetT, lappendT, List.length_append]
    have := detT_time r (R - 1) (K[R - 1]!) false 1
    have := detT_time r R (K[R]!) true 2
    have := dl (R - 1) (K[R - 1]!) false 1
    have := dl R (K[R]!) true 2
    nlinarith
  · simp only [time_bind, ret_bind, lgetT, lappendT, List.length_append]
    have := detT_time r R (K[R]!) true 1
    have := detT_time r (R - 1) (K[R - 1]!) false 2
    have := dl R (K[R]!) true 1
    have := dl (R - 1) (K[R - 1]!) false 2
    nlinarith
  · simp

theorem extLT_time (r : ℕ) (K : List ℕ) (R : ℕ) (fl : Bool) : ∀ l : List Coord,
    l.length ≤ (extLT r K R fl l).ret.length ∧
      (extLT r K R fl l).time ≤ 2 * l.length + (K.length + 9) * ((extLT r K R fl l).ret.length - l.length)
  | [] => by simp [extLT]
  | [_] => by simp [extLT]
  | a :: b :: l => by
    obtain ⟨ih1, ih2⟩ := extLT_time r K R fl (b :: l)
    have hi := insKT_time r K R fl a b
    simp only [extLT, time_bind, ret_bind, ret_pure, time_pure, lappendT, List.length_cons,
      List.length_append] at ih1 ih2 hi ⊢
    constructor
    · omega
    · generalize (insKT r K R fl a b).ret.length = i at hi ⊢
      generalize (extLT r K R fl (b :: l)).ret.length = m at ih1 ih2 ⊢
      generalize (insKT r K R fl a b).time = ti at hi ⊢
      generalize (extLT r K R fl (b :: l)).time = tm at ih2 ⊢
      have e : i + m + 1 - (l.length + 1 + 1) = i + (m - (l.length + 1)) := by omega
      rw [e, Nat.mul_add]
      nlinarith

theorem planLeftT_len : ∀ (L : ℕ) (U : Finset ℕ) (K : List ℕ) (c : ℕ),
    (planLeftT L U K c).ret.length = K.length
  | 0, _, _, _ => rfl
  | L + 1, U, K, c => by
    simp only [planLeftT, fmemT, ret_bind]
    split_ifs
    · simp only [feraseT, lmodifyT, ret_bind, planLeftT_len L _ _ c, List.length_modify]
    · exact planLeftT_len L U K L

theorem planRightT_len (h : ℕ) : ∀ (n R0 : ℕ) (U : Finset ℕ) (K : List ℕ) (c : ℕ),
    (planRightT h n R0 U K c).ret.length = K.length
  | 0, _, _, _, _ => rfl
  | n + 1, R0, U, K, c => by
    simp only [planRightT, fmemT, ret_bind]
    split_ifs
    · simp only [feraseT, lmodifyT, ret_bind, planRightT_len h n _ _ _ c, List.length_modify]
    · exact planRightT_len h n _ U K _
    · rfl

theorem extPT_time (r : ℕ) (K : List ℕ) (R : ℕ) (fl : Bool) (p q : List Coord) :
    (extPT r K R fl p q).time ≤ 2 * (p.length + q.length) + (K.length + 9) *
      ((extPT r K R fl p q).ret.1.length + (extPT r K R fl p q).ret.2.length - (p.length + q.length)) := by
  obtain ⟨a1, a2⟩ := extLT_time r K R fl p
  obtain ⟨b1, b2⟩ := extLT_time r K R fl q
  simp only [extPT, time_bind, ret_bind, ret_pure, time_pure]
  have e : (extLT r K R fl p).ret.length + (extLT r K R fl q).ret.length - (p.length + q.length) =
      ((extLT r K R fl p).ret.length - p.length) + ((extLT r K R fl q).ret.length - q.length) := by omega
  rw [e, Nat.mul_add (K.length + 9)]; omega

theorem ar_find (h : ℕ) : (h + 1) * (6 * h + 3 + 1) ≤ 6 * (h + 1) ^ 2 := by nlinarith
theorem ar_U0 (h : ℕ) : h * (2 * h + 2) ≤ 2 * (h + 1) ^ 2 := by nlinarith
theorem ar_plan (h : ℕ) : h * (3 * h + 4) ≤ 3 * (h + 1) ^ 2 := by nlinarith
theorem ar_ext (h : ℕ) : (h + 10) * (2 * h) ≤ 10 * (h + 1) ^ 2 := by nlinarith
theorem ar_lin (h : ℕ) : h + 1 ≤ (h + 1) ^ 2 := by nlinarith

set_option maxHeartbeats 1000000 in
/-- **The step count of the one-pass band extension**: linear in the paths plus `O(h²)`, when
the result has `2 h` more cells than `p` and `q`. -/
theorem bandExtLT_time (h r : ℕ) (p q : List Coord) (hp : p.Nodup) (hq : q.Nodup)
    (hbp : ∀ v ∈ p, v.2 < h) (hbq : ∀ v ∈ q, v.2 < h)
    (hout : (bandExtLT h r p q).ret.1.length + (bandExtLT h r p q).ret.2.length ≤
      p.length + q.length + 2 * h) :
    (bandExtLT h r p q).time ≤ 6 * (p.length + q.length) + 40 * (h + 1) ^ 2 := by
  have tcp := crossRowsT_time r p
  have tcq := crossRowsT_time r q
  have tfp := flipRowsT_time r p
  have tfq := flipRowsT_time r q
  have lcp := crossRowsT_len r h hp hbp
  have lcq := crossRowsT_len r h hq hbq
  have lfp := flipRowsT_len r h hp hbp
  have lfq := flipRowsT_len r h hq hbq
  set cr := (crossRowsT r p).ret ++ (crossRowsT r q).ret with hcr
  set fr := (flipRowsT r p).ret ++ (flipRowsT r q).ret with hfr
  have lcr : cr.length ≤ 2 * h := by rw [hcr, List.length_append]; omega
  have lfr : fr.length ≤ 2 * h := by rw [hfr, List.length_append]; omega
  have hS1 := ar_lin h
  generalize hS : (h + 1) ^ 2 = S at hS1 ⊢
  have tfind : (lfindT (seedT h cr fr) (List.range (h + 1))).time ≤ 6 * S := by
    have := lfindT_time_le (seedT h cr fr) (List.range (h + 1)) (6 * h + 3)
      (fun R _ => by have := seedT_time h cr fr R; omega)
    simp only [List.length_range] at this
    have := ar_find h
    rw [hS] at this
    omega
  have tU0 : (frangeFilterT h (fun y => do let c ← lcontainsT cr y; pure !c)).time ≤ 2 * S := by
    simp only [frangeFilterT, time_bind, lcontainsT, time_pure]
    have := lsum_le (List.range h) (fun _ => cr.length + 1 + 0 + 1) (2 * h + 2) (fun _ _ => by omega)
    simp only [List.length_range] at this
    have := ar_U0 h
    rw [hS] at this
    simp only [Nat.add_zero] at *
    omega
  have cU0 : (frangeFilterT h (fun y => do let c ← lcontainsT cr y; pure !c)).ret.card ≤ h := by
    simp only [frangeFilterT]
    exact le_trans (Finset.card_filter_le _ _) (by simp)
  have tK0 : (lmapT (fun (_ : ℕ) => (pure 0 : TimeM ℕ)) (List.range (h + 1))).time ≤ h + 1 := by
    have := lmapT_time_le (fun (_ : ℕ) => (pure 0 : TimeM ℕ)) (List.range (h + 1)) 0 (fun _ _ => by simp)
    simpa using this
  have lK0 : (lmapT (fun (_ : ℕ) => (pure 0 : TimeM ℕ)) (List.range (h + 1))).ret.length = h + 1 := by
    simp [lmapT]
  have pl : ∀ (L : ℕ) (U : Finset ℕ) (K : List ℕ) (c : ℕ), L ≤ h → U.card ≤ h → K.length = h + 1 →
      (planLeftT L U K c).time ≤ 3 * S := by
    intro L U K c hL hU hK
    have := planLeftT_time L U K c
    rw [hK] at this
    have : L * (2 * U.card + (h + 1) + 3) ≤ h * (3 * h + 4) := Nat.mul_le_mul hL (by omega)
    have := ar_plan h
    rw [hS] at this
    omega
  have pr : ∀ (n R0 : ℕ) (U : Finset ℕ) (K : List ℕ) (c : ℕ), n ≤ h → U.card ≤ h →
      K.length = h + 1 → (planRightT h n R0 U K c).time ≤ 3 * S := by
    intro n R0 U K c hn hU hK
    have := planRightT_time h n R0 U K c
    rw [hK] at this
    have : n * (2 * U.card + (h + 1) + 3) ≤ h * (3 * h + 4) := Nat.mul_le_mul hn (by omega)
    have := ar_plan h
    rw [hS] at this
    omega
  have ex : ∀ (K : List ℕ) (R : ℕ) (fl : Bool), K.length = h + 1 →
      (extPT r K R fl p q).ret.1.length + (extPT r K R fl p q).ret.2.length ≤
        p.length + q.length + 2 * h →
      (extPT r K R fl p q).time ≤ 2 * (p.length + q.length) + 10 * S := by
    intro K R fl hK hl
    have := extPT_time r K R fl p q
    rw [hK] at this
    have : (h + 1 + 9) * ((extPT r K R fl p q).ret.1.length + (extPT r K R fl p q).ret.2.length -
        (p.length + q.length)) ≤ (h + 10) * (2 * h) := Nat.mul_le_mul (by omega) (by omega)
    have := ar_ext h
    rw [hS] at this
    omega
  have cE : ∀ (U : Finset ℕ) (x : ℕ), U.card ≤ h → (U.erase x).card ≤ h := fun U x hU =>
    le_trans Finset.card_erase_le hU
  have cF : ∀ (U : Finset ℕ) (f : ℕ → Bool), U.card ≤ h → (U.filter (fun z => f z = true)).card ≤ h :=
    fun U f hU => le_trans (Finset.card_filter_le _ _) hU
  simp only [bandExtLT, time_bind, ret_bind, lappendT, rangeT] at hout ⊢
  rw [← hcr, ← hfr] at hout ⊢
  split at hout
  · rename_i hfnone
    simp only [time_bind, time_pure]
    have s1 := stretchT_time r p
    have s2 := stretchT_time r q
    omega
  · rename_i R hfR
    have hR : R ≤ h := by
      have := List.mem_range.mp (List.mem_of_find?_eq_some hfR); omega
    simp only [time_bind, ret_bind] at hout ⊢
    generalize hU : (frangeFilterT h fun y => do let c ← lcontainsT cr y; pure !c) = U0 at hout tU0 cU0 ⊢
    generalize hK : lmapT (fun (_ : ℕ) => (pure 0 : TimeM ℕ)) (List.range (h + 1)) = K0 at hout tK0 lK0 ⊢
    have tc0 : (lcontainsT cr (R - 1)).time ≤ 2 * h + 1 := by simp [lcontainsT]; omega
    have tc1 : (lcontainsT cr R).time ≤ 2 * h + 1 := by simp [lcontainsT]; omega
    split_ifs at hout ⊢
    · simp only [time_bind, ret_bind] at hout ⊢
      have := pr (h - 0) 0 U0.ret K0.ret 0 (by omega) cU0 lK0
      have := ex _ R false (by rw [planRightT_len]; exact lK0) hout
      omega
    · simp only [time_bind, ret_bind] at hout ⊢
      have := pl (R - 1) U0.ret K0.ret (R - 1) (by omega) cU0 lK0
      have := ex _ R false (by rw [planLeftT_len]; exact lK0) hout
      omega
    · simp only [time_bind, ret_bind, ffilterT] at hout ⊢
      have := pl (R - 1) U0.ret K0.ret (R - 1) (by omega) cU0 lK0
      have := pr (h - R) R (U0.ret.filter (fun z => decide (R - 1 < z) = true))
        (planLeftT (R - 1) U0.ret K0.ret (R - 1)).ret R (by omega) (cF _ _ cU0)
        (by rw [planLeftT_len]; exact lK0)
      have := ex _ R false (by rw [planRightT_len, planLeftT_len]; exact lK0) hout
      omega
    · simp only [time_bind, ret_bind, ffilterT, feraseT] at hout ⊢
      have c1 := cE U0.ret (R - 1) cU0
      have c2 := cE _ (R - 1 + 1) c1
      have := pl (R - 1) ((U0.ret.erase (R - 1)).erase (R - 1 + 1)) K0.ret (R - 1) (by omega) c2 lK0
      have := pr (h - (R - 1 + 1)) (R - 1 + 1)
        (((U0.ret.erase (R - 1)).erase (R - 1 + 1)).filter (fun z => decide (R - 1 < z) = true))
        (planLeftT (R - 1) ((U0.ret.erase (R - 1)).erase (R - 1 + 1)) K0.ret (R - 1)).ret (R - 1 + 1)
        (by omega) (cF _ _ c2) (by rw [planLeftT_len]; exact lK0)
      have := ex _ R true (by rw [planRightT_len, planLeftT_len]; exact lK0) hout
      have e1 : (feraseT U0.ret (R - 1)).time ≤ h + 1 := by simp [feraseT]; omega
      have e2 : (feraseT (U0.ret.erase (R - 1)) (R - 1 + 1)).time ≤ h + 1 := by simp [feraseT]; omega
      have e3 : (ffilterT (fun z => decide (R - 1 < z)) ((U0.ret.erase (R - 1)).erase (R - 1 + 1))).time
          ≤ h + 1 := by simp [ffilterT]; omega
      linarith

end ZZN.T

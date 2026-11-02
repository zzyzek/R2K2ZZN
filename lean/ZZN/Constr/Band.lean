-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.BandExtension

/-!
# Band extension as a function

`bandExtE I r p q` computes the solution of `I.insertAt r` that `band_extension` (in
`ZZN/BandExtension.lean`) proves to exist: stretch both paths across the two new lines, find a
seed, and sweep. Every step of that proof builds its new paths by splicing a detour into an edge,
so each step is a function here, with a lemma that it keeps the invariant `PState`.

* `insB a b X l` inserts `X` between consecutive cells `a, b` of `l`.
* `spliceE`, `absorbE`, `flipE`, `sweepLeftE`, `sweepRightE`: the steps.
* `bandExtE_sol`: if `p, q` solve `I` and line `r` holds no endpoint, then `bandExtE I r p q`
  solves `I.insertAt r`.
-/

namespace ZZN

open GridHam

theorem ite_t {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ite_f {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

/-! ### Splicing into an edge -/

/-- Insert `X` between the first consecutive pair `a, b`. -/
def insB (a b : Coord) (X : List Coord) : List Coord → List Coord
  | x :: y :: l => if x = a ∧ y = b then x :: (X ++ y :: l) else x :: insB a b X (y :: l)
  | l => l

theorem insB_eq (a b : Coord) (X l₂ : List Coord) :
    ∀ l₁ : List Coord, (l₁ ++ a :: b :: l₂).Nodup →
      insB a b X (l₁ ++ a :: b :: l₂) = l₁ ++ a :: (X ++ b :: l₂)
  | [], _ => by simp [insB]
  | x :: l₁, hn => by
    have hx : x ≠ a := by
      intro hxa; subst hxa
      exact (List.nodup_cons.mp hn).1 (by simp)
    have ih := insB_eq a b X l₂ l₁ (List.nodup_cons.mp hn).2
    cases l₁ with
    | nil => simp only [List.nil_append] at ih ⊢; simp only [List.cons_append, List.nil_append] at *
             rw [insB, ite_f (fun h => hx h.1), ih]
    | cons z l₁' =>
      simp only [List.cons_append] at ih ⊢
      rw [insB, ite_f (fun h => hx h.1), ih]

theorem splice_edgeC {w h : ℕ} {s t : Coord} {L X : List Coord} {a b : Coord}
    (hL : IsPath w h s t L) (hab : [a, b] <:+: L)
    (hX : chainAdjacent (a :: (X ++ [b])) = true) (hXn : X.Nodup)
    (hXb : ∀ x ∈ X, InBounds w h x) (hfresh : ∀ x ∈ X, x ∉ L) :
    IsPath w h s t (insB a b X L) ∧ (∀ v, v ∈ insB a b X L ↔ v ∈ L ∨ v ∈ X) ∧
      (∀ u v, [u, v] <:+: L → ¬(u = a ∧ v = b) → [u, v] <:+: insB a b X L) ∧
      X <:+: insB a b X L := by
  obtain ⟨l₁, l₂, rfl⟩ := infix_pair_iff.mp hab
  rw [insB_eq a b X l₂ l₁ hL.2.2.1]
  exact ⟨hL.splice hX hXn hXb hfresh, fun v => mem_splice _ _ _ _ _ _,
    fun u v huv hne => infix_splice_of_ne huv hne, infix_splice_self _ _ _ _ _⟩

/-- Splice `X` into the edge `a – b` of whichever path holds it (as `a, b`). -/
def spliceE (P Q : List Coord) (a b : Coord) (X : List Coord) : List Coord × List Coord :=
  if [a, b] <:+: P then (insB a b X P, Q) else (P, insB a b X Q)

theorem PState.spliceC {W h r : ℕ} {s0 t0 s1 t1 : Coord} {U U' : Finset ℕ} {P Q X : List Coord}
    {a b : Coord} (st : PState W h r s0 t0 s1 t1 U P Q)
    (hab : [a, b] <:+: P ∨ [a, b] <:+: Q)
    (hX : chainAdjacent (a :: (X ++ [b])) = true) (hXn : X.Nodup)
    (hXU : ∀ v, v ∈ X ↔ Uncov r U v ∧ ¬ Uncov r U' v)
    (hU' : U' ⊆ U) :
    PState W h r s0 t0 s1 t1 U' (spliceE P Q a b X).1 (spliceE P Q a b X).2 ∧
      (X <:+: (spliceE P Q a b X).1 ∨ X <:+: (spliceE P Q a b X).2) ∧
      (∀ u v, ¬(u = a ∧ v = b) → ¬(u = b ∧ v = a) →
        Used P u v ∨ Used Q u v → Used (spliceE P Q a b X).1 u v ∨ Used (spliceE P Q a b X).2 u v) := by
  have hXb : ∀ x ∈ X, InBounds W h x := by
    intro x hx
    obtain ⟨⟨h1, h2⟩, -⟩ := (hXU x).mp hx
    have := st.Ub _ h2
    have := st.rb
    unfold InBounds; omega
  have hXP : ∀ x ∈ X, x ∉ P := fun x hx => (st.unc x ((hXU x).mp hx).1).1
  have hXQ : ∀ x ∈ X, x ∉ Q := fun x hx => (st.unc x ((hXU x).mp hx).1).2
  have uncU : ∀ v, Uncov r U' v → Uncov r U v := fun v ⟨h1, h2⟩ => ⟨h1, hU' h2⟩
  by_cases hP : [a, b] <:+: P
  · simp only [spliceE, ite_t hP]
    obtain ⟨hP', hmem, hkeep, hXin⟩ := splice_edgeC st.pp hP hX hXn hXb hXP
    refine ⟨⟨hP', st.pq, ?_, ?_, ?_, fun y hy => st.Ub y (hU' hy), st.rb⟩, Or.inl hXin, ?_⟩
    · intro v hv hq
      rcases (hmem v).mp hv with h | h
      · exact st.disj v h hq
      · exact hXQ v h hq
    · intro v hv hn
      by_cases hu : Uncov r U v
      · exact Or.inl ((hmem v).mpr (Or.inr ((hXU v).mpr ⟨hu, hn⟩)))
      · rcases st.cov v hv hu with h | h
        · exact Or.inl ((hmem v).mpr (Or.inl h))
        · exact Or.inr h
    · intro v hv
      refine ⟨fun h => ?_, (st.unc v (uncU v hv)).2⟩
      rcases (hmem v).mp h with h | h
      · exact (st.unc v (uncU v hv)).1 h
      · exact ((hXU v).mp h).2 hv
    · intro u v hne hne' huv
      rcases huv with (h | h) | h
      · exact Or.inl (Or.inl (hkeep u v h hne))
      · exact Or.inl (Or.inr (hkeep v u h (fun ⟨h1, h2⟩ => hne' ⟨h2, h1⟩)))
      · exact Or.inr h
  · have hQ : [a, b] <:+: Q := hab.resolve_left hP
    simp only [spliceE, ite_f hP]
    obtain ⟨hQ', hmem, hkeep, hXin⟩ := splice_edgeC st.pq hQ hX hXn hXb hXQ
    refine ⟨⟨st.pp, hQ', ?_, ?_, ?_, fun y hy => st.Ub y (hU' hy), st.rb⟩, Or.inr hXin, ?_⟩
    · intro v hv hq
      rcases (hmem v).mp hq with h | h
      · exact st.disj v hv h
      · exact hXP v h hv
    · intro v hv hn
      by_cases hu : Uncov r U v
      · exact Or.inr ((hmem v).mpr (Or.inr ((hXU v).mpr ⟨hu, hn⟩)))
      · rcases st.cov v hv hu with h | h
        · exact Or.inl h
        · exact Or.inr ((hmem v).mpr (Or.inl h))
    · intro v hv
      refine ⟨(st.unc v (uncU v hv)).1, fun h => ?_⟩
      rcases (hmem v).mp h with h | h
      · exact (st.unc v (uncU v hv)).2 h
      · exact ((hXU v).mp h).2 hv
    · intro u v hne hne' huv
      rcases huv with h | (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl (hkeep u v h hne))
      · exact Or.inr (Or.inr (hkeep v u h (fun ⟨h1, h2⟩ => hne' ⟨h2, h1⟩)))

/-! ### Absorb -/

theorem PState.absorb_coreC {W h r : ℕ} {s0 t0 s1 t1 : Coord} {U : Finset ℕ} {P Q : List Coord}
    {y y' : ℕ} (st : PState W h r s0 t0 s1 t1 U P Q) (hy : y ∈ U) {a b : Coord} {X : List Coord}
    (hab : [a, b] <:+: P ∨ [a, b] <:+: Q) (hX : chainAdjacent (a :: (X ++ [b])) = true)
    (hXn : X.Nodup) (hXset : ∀ v, v ∈ X ↔ (v = (r + 1, y) ∨ v = (r + 2, y)))
    (hmidX : [(r + 1, y), (r + 2, y)] <:+: X ∨ [(r + 2, y), (r + 1, y)] <:+: X)
    (ha : a.2 = y') (hb : b.2 = y') :
    PState W h r s0 t0 s1 t1 (U.erase y) (spliceE P Q a b X).1 (spliceE P Q a b X).2 ∧
      Mid r (spliceE P Q a b X).1 (spliceE P Q a b X).2 y ∧
      ∀ z, z ≠ y' → Mid r P Q z → Mid r (spliceE P Q a b X).1 (spliceE P Q a b X).2 z := by
  obtain ⟨st', hXin, hkeep⟩ := st.spliceC hab hX hXn
    (fun v => (hXset v).trans (uncov_erase_iff hy v).symm) (Finset.erase_subset _ _)
  refine ⟨st', mid_of_X hXin hmidX, fun z hz hm => ?_⟩
  unfold Mid at hm ⊢
  have h1 : ¬((r + 1, z) = a ∧ (r + 2, z) = b) := fun ⟨h, _⟩ => hz (by rw [← ha, ← h])
  have h2 : ¬((r + 1, z) = b ∧ (r + 2, z) = a) := fun ⟨h, _⟩ => hz (by rw [← hb, ← h])
  exact hkeep _ _ h1 h2 hm

/-- Cover column `y` by a detour of the middle edge of column `y'`. -/
def absorbE (r y y' : ℕ) (P Q : List Coord) : List Coord × List Coord :=
  if [(r + 1, y'), (r + 2, y')] <:+: P ∨ [(r + 1, y'), (r + 2, y')] <:+: Q then
    spliceE P Q (r + 1, y') (r + 2, y') [(r + 1, y), (r + 2, y)]
  else spliceE P Q (r + 2, y') (r + 1, y') [(r + 2, y), (r + 1, y)]

theorem PState.absorbC {W h r : ℕ} {s0 t0 s1 t1 : Coord} {U : Finset ℕ} {P Q : List Coord}
    {y y' : ℕ} (st : PState W h r s0 t0 s1 t1 U P Q) (hy : y ∈ U)
    (hadj : y' + 1 = y ∨ y + 1 = y') (hmid : Mid r P Q y') :
    PState W h r s0 t0 s1 t1 (U.erase y) (absorbE r y y' P Q).1 (absorbE r y y' P Q).2 ∧
      Mid r (absorbE r y y' P Q).1 (absorbE r y y' P Q).2 y ∧
      ∀ z, z ≠ y' → Mid r P Q z → Mid r (absorbE r y y' P Q).1 (absorbE r y y' P Q).2 z := by
  have hc1 : chainAdjacent ((r + 1, y') :: ([(r + 1, y), (r + 2, y)] ++ [(r + 2, y')])) = true := by
    simp [chainAdjacent_cons_cons, adjacentB, Adjacent]; omega
  have hc2 : chainAdjacent ((r + 2, y') :: ([(r + 2, y), (r + 1, y)] ++ [(r + 1, y')])) = true := by
    simp [chainAdjacent_cons_cons, adjacentB, Adjacent]; omega
  have hn1 : [(r + 1, y), (r + 2, y)].Nodup := by simp
  have hn2 : [(r + 2, y), (r + 1, y)].Nodup := by simp
  have hs1 : ∀ v, v ∈ [(r + 1, y), (r + 2, y)] ↔ (v = (r + 1, y) ∨ v = (r + 2, y)) := by simp
  have hs2 : ∀ v, v ∈ [(r + 2, y), (r + 1, y)] ↔ (v = (r + 1, y) ∨ v = (r + 2, y)) := by
    intro v; simp; tauto
  unfold absorbE
  by_cases hf : [(r + 1, y'), (r + 2, y')] <:+: P ∨ [(r + 1, y'), (r + 2, y')] <:+: Q
  · rw [ite_t hf]
    exact st.absorb_coreC hy hf hc1 hn1 hs1 (Or.inl ⟨[], [], rfl⟩) rfl rfl
  · rw [ite_f hf]
    have hb : [(r + 2, y'), (r + 1, y')] <:+: P ∨ [(r + 2, y'), (r + 1, y')] <:+: Q := by
      unfold Mid Used at hmid
      rcases hmid with (hm | hm) | (hm | hm)
      · exact absurd (Or.inl hm) hf
      · exact Or.inl hm
      · exact absurd (Or.inr hm) hf
      · exact Or.inr hm
    exact st.absorb_coreC hy hb hc2 hn2 hs2 (Or.inr ⟨[], [], rfl⟩) rfl rfl

/-! ### Flip -/

theorem PState.flip_coreC {W h r : ℕ} {s0 t0 s1 t1 : Coord} {U : Finset ℕ} {P Q : List Coord}
    {y : ℕ} (st : PState W h r s0 t0 s1 t1 U P Q) (hy : y ∈ U) (hy1 : y + 1 ∈ U)
    {a b : Coord} {X : List Coord}
    (hab : [a, b] <:+: P ∨ [a, b] <:+: Q) (hX : chainAdjacent (a :: (X ++ [b])) = true)
    (hXn : X.Nodup)
    (hXset : ∀ v, v ∈ X ↔
      (v = (r + 1, y) ∨ v = (r + 2, y) ∨ v = (r + 2, y + 1) ∨ v = (r + 1, y + 1)))
    (hm0 : [(r + 1, y), (r + 2, y)] <:+: X ∨ [(r + 2, y), (r + 1, y)] <:+: X)
    (hm1 : [(r + 1, y + 1), (r + 2, y + 1)] <:+: X ∨ [(r + 2, y + 1), (r + 1, y + 1)] <:+: X)
    (ha : a.1 = r) (hb : b.1 = r) :
    PState W h r s0 t0 s1 t1 ((U.erase y).erase (y + 1)) (spliceE P Q a b X).1 (spliceE P Q a b X).2 ∧
      Mid r (spliceE P Q a b X).1 (spliceE P Q a b X).2 y ∧
      Mid r (spliceE P Q a b X).1 (spliceE P Q a b X).2 (y + 1) ∧
      ∀ z, Mid r P Q z → Mid r (spliceE P Q a b X).1 (spliceE P Q a b X).2 z := by
  obtain ⟨st', hXin, hkeep⟩ := st.spliceC hab hX hXn
    (fun v => (hXset v).trans (uncov_erase2_iff hy hy1 v).symm)
    ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
  refine ⟨st', mid_of_X hXin hm0, mid_of_X hXin hm1, fun z hm => ?_⟩
  unfold Mid at hm ⊢
  have h1 : ¬((r + 1, z) = a ∧ (r + 2, z) = b) := fun ⟨h, _⟩ => by
    have := congrArg Prod.fst h; simp at this; omega
  have h2 : ¬((r + 1, z) = b ∧ (r + 2, z) = a) := fun ⟨h, _⟩ => by
    have := congrArg Prod.fst h; simp at this; omega
  exact hkeep _ _ h1 h2 hm

/-- Cover columns `y, y + 1` by a detour of the row-`r` edge between them. -/
def flipE (r y : ℕ) (P Q : List Coord) : List Coord × List Coord :=
  if [(r, y), (r, y + 1)] <:+: P ∨ [(r, y), (r, y + 1)] <:+: Q then
    spliceE P Q (r, y) (r, y + 1) [(r + 1, y), (r + 2, y), (r + 2, y + 1), (r + 1, y + 1)]
  else spliceE P Q (r, y + 1) (r, y) [(r + 1, y + 1), (r + 2, y + 1), (r + 2, y), (r + 1, y)]

theorem PState.flipC {W h r : ℕ} {s0 t0 s1 t1 : Coord} {U : Finset ℕ} {P Q : List Coord}
    {y : ℕ} (st : PState W h r s0 t0 s1 t1 U P Q) (hy : y ∈ U) (hy1 : y + 1 ∈ U)
    (hu : Used P (r, y) (r, y + 1) ∨ Used Q (r, y) (r, y + 1)) :
    PState W h r s0 t0 s1 t1 ((U.erase y).erase (y + 1)) (flipE r y P Q).1 (flipE r y P Q).2 ∧
      Mid r (flipE r y P Q).1 (flipE r y P Q).2 y ∧ Mid r (flipE r y P Q).1 (flipE r y P Q).2 (y + 1) ∧
      ∀ z, Mid r P Q z → Mid r (flipE r y P Q).1 (flipE r y P Q).2 z := by
  have hc1 : chainAdjacent ((r, y) :: ([(r + 1, y), (r + 2, y), (r + 2, y + 1), (r + 1, y + 1)]
      ++ [(r, y + 1)])) = true := by
    simp [chainAdjacent_cons_cons, adjacentB, Adjacent]
  have hc2 : chainAdjacent ((r, y + 1) :: ([(r + 1, y + 1), (r + 2, y + 1), (r + 2, y), (r + 1, y)]
      ++ [(r, y)])) = true := by
    simp [chainAdjacent_cons_cons, adjacentB, Adjacent]
  have hn1 : [(r + 1, y), (r + 2, y), (r + 2, y + 1), (r + 1, y + 1)].Nodup := by simp
  have hn2 : [(r + 1, y + 1), (r + 2, y + 1), (r + 2, y), (r + 1, y)].Nodup := by simp
  have hs1 : ∀ v, v ∈ [(r + 1, y), (r + 2, y), (r + 2, y + 1), (r + 1, y + 1)] ↔
      (v = (r + 1, y) ∨ v = (r + 2, y) ∨ v = (r + 2, y + 1) ∨ v = (r + 1, y + 1)) := by simp
  have hs2 : ∀ v, v ∈ [(r + 1, y + 1), (r + 2, y + 1), (r + 2, y), (r + 1, y)] ↔
      (v = (r + 1, y) ∨ v = (r + 2, y) ∨ v = (r + 2, y + 1) ∨ v = (r + 1, y + 1)) := by
    intro v; simp; tauto
  unfold flipE
  by_cases hf : [(r, y), (r, y + 1)] <:+: P ∨ [(r, y), (r, y + 1)] <:+: Q
  · rw [ite_t hf]
    exact st.flip_coreC hy hy1 hf hc1 hn1 hs1 (Or.inl ⟨[], _, rfl⟩) (Or.inr ⟨[_, _], [], rfl⟩) rfl rfl
  · rw [ite_f hf]
    have hb : [(r, y + 1), (r, y)] <:+: P ∨ [(r, y + 1), (r, y)] <:+: Q := by
      unfold Used at hu
      rcases hu with (hm | hm) | (hm | hm)
      · exact absurd (Or.inl hm) hf
      · exact Or.inl hm
      · exact absurd (Or.inr hm) hf
      · exact Or.inr hm
    exact st.flip_coreC hy hy1 hb hc2 hn2 hs2 (Or.inr ⟨[_, _], [], rfl⟩) (Or.inl ⟨[], _, rfl⟩) rfl rfl

/-! ### Sweeps -/

/-- Cover the uncovered columns below `L`, from the middle edge of column `L` down. -/
def sweepLeftE (r : ℕ) : ℕ → Finset ℕ → List Coord → List Coord → List Coord × List Coord
  | 0, _, P, Q => (P, Q)
  | L + 1, U, P, Q =>
    if L ∈ U then sweepLeftE r L (U.erase L) (absorbE r L (L + 1) P Q).1 (absorbE r L (L + 1) P Q).2
    else sweepLeftE r L U P Q

theorem PState.sweepLeftC {W h r : ℕ} {s0 t0 s1 t1 : Coord} :
    ∀ (L : ℕ) (U : Finset ℕ) (P Q : List Coord), PState W h r s0 t0 s1 t1 U P Q →
      L ∉ U → Mid r P Q L → (∀ z, z < L → z ∉ U → Mid r P Q z) →
      PState W h r s0 t0 s1 t1 (U.filter (L < ·)) (sweepLeftE r L U P Q).1 (sweepLeftE r L U P Q).2 ∧
        ∀ z, L < z → Mid r P Q z → Mid r (sweepLeftE r L U P Q).1 (sweepLeftE r L U P Q).2 z
  | 0, U, P, Q, st, hL, _, _ => by
    refine ⟨st.congrU ?_, fun _ _ h => h⟩
    ext z
    simp only [Finset.mem_filter]
    constructor
    · intro hz; exact ⟨hz, Nat.pos_of_ne_zero (fun h => hL (h ▸ hz))⟩
    · exact fun h => h.1
  | L + 1, U, P, Q, st, hL, hm, hbelow => by
    by_cases hLU : L ∈ U
    · simp only [sweepLeftE, ite_t hLU]
      obtain ⟨st1, hm1, hkeep1⟩ := st.absorbC (y' := L + 1) hLU (Or.inr rfl) hm
      obtain ⟨st2, hkeep2⟩ := PState.sweepLeftC L (U.erase L) _ _ st1
        (Finset.notMem_erase _ _) hm1
        (fun z hz hzU => hkeep1 z (by omega)
          (hbelow z (by omega) (fun h => hzU (Finset.mem_erase.mpr ⟨by omega, h⟩))))
      refine ⟨st2.congrU ?_, fun z hz h => hkeep2 z (by omega) (hkeep1 z (by omega) h)⟩
      ext z
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨hne, hz⟩, hlt⟩
        refine ⟨hz, ?_⟩
        rcases Nat.lt_or_ge (L + 1) z with h | h
        · exact h
        · exact absurd (show z = L + 1 by omega) (fun he => hL (he ▸ hz))
      · rintro ⟨hz, hlt⟩
        exact ⟨⟨by omega, hz⟩, by omega⟩
    · simp only [sweepLeftE, ite_f hLU]
      obtain ⟨st2, hkeep2⟩ := PState.sweepLeftC L U P Q st hLU
        (hbelow L (by omega) hLU) (fun z hz hzU => hbelow z (by omega) hzU)
      refine ⟨st2.congrU ?_, fun z hz h => hkeep2 z (by omega) h⟩
      ext z
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hz, hlt⟩
        refine ⟨hz, ?_⟩
        rcases Nat.lt_or_ge (L + 1) z with h | h
        · exact h
        · exact absurd (show z = L + 1 by omega) (fun he => hL (he ▸ hz))
      · rintro ⟨hz, hlt⟩
        exact ⟨hz, by omega⟩

/-- Cover the uncovered columns above `R`, from the middle edge of column `R` up. -/
def sweepRightE (r h : ℕ) : ℕ → ℕ → Finset ℕ → List Coord → List Coord → List Coord × List Coord
  | 0, _, _, P, Q => (P, Q)
  | n + 1, R, U, P, Q =>
    if R + 1 ∈ U then
      sweepRightE r h n (R + 1) (U.erase (R + 1)) (absorbE r (R + 1) R P Q).1 (absorbE r (R + 1) R P Q).2
    else if R + 1 < h then sweepRightE r h n (R + 1) U P Q
    else (P, Q)

theorem PState.sweepRightC {W h r : ℕ} {s0 t0 s1 t1 : Coord} :
    ∀ (n R : ℕ) (U : Finset ℕ) (P Q : List Coord), h - R = n →
      PState W h r s0 t0 s1 t1 U P Q →
      R ∉ U → Mid r P Q R → (∀ z, R < z → z < h → z ∉ U → Mid r P Q z) →
      PState W h r s0 t0 s1 t1 (U.filter (· < R)) (sweepRightE r h n R U P Q).1
          (sweepRightE r h n R U P Q).2 ∧
        ∀ z, z < R → Mid r P Q z → Mid r (sweepRightE r h n R U P Q).1 (sweepRightE r h n R U P Q).2 z
  | 0, R, U, P, Q, hn, st, hR, _, _ => by
    refine ⟨st.congrU ?_, fun _ _ h => h⟩
    ext z
    simp only [Finset.mem_filter]
    constructor
    · intro hz; exact ⟨hz, by have := st.Ub z hz; omega⟩
    · exact fun h => h.1
  | n + 1, R, U, P, Q, hn, st, hR, hm, habove => by
    have hfilt : ∀ (V : Finset ℕ), R ∉ V → V.filter (· < R + 1) = V.filter (· < R) := by
      intro V hV
      ext z
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hz, hlt⟩
        refine ⟨hz, ?_⟩
        rcases Nat.lt_or_ge z R with h | h
        · exact h
        · exact absurd (show z = R by omega) (fun he => hV (he ▸ hz))
      · rintro ⟨hz, hlt⟩
        exact ⟨hz, by omega⟩
    by_cases hRU : R + 1 ∈ U
    · simp only [sweepRightE, ite_t hRU]
      obtain ⟨st1, hm1, hkeep1⟩ := st.absorbC (y' := R) hRU (Or.inl rfl) hm
      obtain ⟨st2, hkeep2⟩ := PState.sweepRightC n (R + 1) (U.erase (R + 1)) _ _
        (by omega) st1 (Finset.notMem_erase _ _) hm1
        (fun z hz hzh hzU => hkeep1 z (by omega)
          (habove z (by omega) hzh (fun h => hzU (Finset.mem_erase.mpr ⟨by omega, h⟩))))
      refine ⟨st2.congrU ?_, fun z hz h => hkeep2 z (by omega) (hkeep1 z (by omega) h)⟩
      rw [hfilt _ (fun h => hR (Finset.mem_of_mem_erase h))]
      ext z
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨-, hz⟩, hlt⟩; exact ⟨hz, hlt⟩
      · rintro ⟨hz, hlt⟩; exact ⟨⟨by omega, hz⟩, hlt⟩
    · simp only [sweepRightE, ite_f hRU]
      by_cases hlast : R + 1 < h
      · simp only [ite_t hlast]
        obtain ⟨st2, hkeep2⟩ := PState.sweepRightC n (R + 1) U P Q (by omega) st hRU
          (habove (R + 1) (by omega) hlast hRU)
          (fun z hz hzh hzU => habove z (by omega) hzh hzU)
        exact ⟨st2.congrU (hfilt U hR), fun z hz h => hkeep2 z (by omega) h⟩
      · simp only [ite_f hlast]
        refine ⟨st.congrU ?_, fun _ _ h => h⟩
        ext z
        simp only [Finset.mem_filter]
        constructor
        · intro hz
          refine ⟨hz, ?_⟩
          have := st.Ub z hz
          rcases Nat.lt_or_ge z R with h | h
          · exact h
          · exact absurd (show z = R by omega) (fun he => hR (he ▸ hz))
        · exact fun h => h.1

/-! ### The seed and the whole construction -/

instance (p q : List Coord) (r y : ℕ) : Decidable (Cross p q r y) := by
  unfold Cross Used; infer_instance

/-- The condition of `seed_or_flip` at position `R`. -/
def SeedAt (h : ℕ) (p q : List Coord) (r R : ℕ) : Prop :=
  ((R = 0 ∨ Cross p q r (R - 1)) ∧ (R = h ∨ Cross p q r R)) ∨
    (1 ≤ R ∧ R < h ∧ ¬ Cross p q r (R - 1) ∧ ¬ Cross p q r R ∧
      (Used p (r, R - 1) (r, R) ∨ Used q (r, R - 1) (r, R)))

instance (h : ℕ) (p q : List Coord) (r R : ℕ) : Decidable (SeedAt h p q r R) := by
  unfold SeedAt Used; infer_instance

/-- The construction of `band_extension`, as a function. -/
def bandExtE (I : Inst) (r : ℕ) (p q : List Coord) : List Coord × List Coord :=
  let U0 := (Finset.range I.h).filter (fun y => ¬ Cross p q r y)
  let P0 := stretch r p
  let Q0 := stretch r q
  match (List.range (I.h + 1)).find? (fun R => decide (SeedAt I.h p q r R)) with
  | none => (P0, Q0)
  | some R =>
    if (R = 0 ∨ Cross p q r (R - 1)) ∧ (R = I.h ∨ Cross p q r R) then
      if R = 0 then sweepRightE r I.h (I.h - 0) 0 U0 P0 Q0
      else if R = I.h then sweepLeftE r (R - 1) U0 P0 Q0
      else
        sweepRightE r I.h (I.h - R) R (U0.filter (R - 1 < ·)) (sweepLeftE r (R - 1) U0 P0 Q0).1
          (sweepLeftE r (R - 1) U0 P0 Q0).2
    else
      sweepRightE r I.h (I.h - (R - 1 + 1)) (R - 1 + 1)
        (((U0.erase (R - 1)).erase (R - 1 + 1)).filter (R - 1 < ·))
        (sweepLeftE r (R - 1) ((U0.erase (R - 1)).erase (R - 1 + 1)) (flipE r (R - 1) P0 Q0).1
          (flipE r (R - 1) P0 Q0).2).1
        (sweepLeftE r (R - 1) ((U0.erase (R - 1)).erase (R - 1 + 1)) (flipE r (R - 1) P0 Q0).1
          (flipE r (R - 1) P0 Q0).2).2

/-- **Band extension, computed.** -/
theorem bandExtE_sol {I : Inst} {p q : List Coord} {r : ℕ} (hsol : IsSolution I p q) (hr : r < I.w)
    (hfree : LineFree I r) :
    IsSolution (I.insertAt r) (bandExtE I r p q).1 (bandExtE I r p q).2 := by
  have hh : 0 < I.h := by
    have hs0 : I.s0 ∈ p := List.mem_of_mem_head? hsol.1.1
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) (hsol.1.2.2.2.1 _ hs0).2
  set U0 := (Finset.range I.h).filter (fun y => ¬ Cross p q r y) with hU0
  have st0 : PState (I.w + 2) I.h r (shiftAt r I.s0) (shiftAt r I.t0) (shiftAt r I.s1)
      (shiftAt r I.t1) U0 (stretch r p) (stretch r q) := by
    have h0 := init_state hsol hr
    convert h0 using 2
  have midC : ∀ y, Cross p q r y → Mid r (stretch r p) (stretch r q) y := by
    intro y hc
    rcases hc with hc | hc
    · exact Or.inl (used_stretch_cross hc)
    · exact Or.inr (used_stretch_cross hc)
  have notU : ∀ z, z < I.h → z ∉ U0 → Cross p q r z := by
    intro z hz hzU
    by_contra hc
    exact hzU (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hz, hc⟩)
  have inU : ∀ z, z ∈ U0 → z < I.h ∧ ¬ Cross p q r z := by
    intro z hz
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hz
    exact ⟨Finset.mem_range.mp h1, h2⟩
  have finish : ∀ P Q, PState (I.w + 2) I.h r (shiftAt r I.s0) (shiftAt r I.t0)
      (shiftAt r I.s1) (shiftAt r I.t1) ∅ P Q → IsSolution (I.insertAt r) P Q := by
    intro P Q st
    exact ⟨st.pp, st.pq, st.disj, fun v hv => st.cov v hv (fun ⟨_, h⟩ => by simp at h)⟩
  -- the seed found by the search
  obtain ⟨R0, hR0h, hR0⟩ := seed_or_flip hsol hr hfree hh
  have hR0' : SeedAt I.h p q r R0 := hR0
  have hfind : ∃ R, (List.range (I.h + 1)).find? (fun R => decide (SeedAt I.h p q r R)) = some R := by
    cases hf : (List.range (I.h + 1)).find? (fun R => decide (SeedAt I.h p q r R)) with
    | some R => exact ⟨R, rfl⟩
    | none =>
      rw [List.find?_eq_none] at hf
      exact absurd (decide_eq_true hR0') (hf R0 (List.mem_range.mpr (by omega)))
  obtain ⟨R, hf⟩ := hfind
  have hRmem := List.mem_of_find?_eq_some hf
  have hRh : R ≤ I.h := by have := List.mem_range.mp hRmem; omega
  have hcase : SeedAt I.h p q r R := by
    have := List.find?_some hf
    simpa using this
  unfold bandExtE
  simp only [hf]
  rw [← hU0]
  by_cases hc1 : (R = 0 ∨ Cross p q r (R - 1)) ∧ (R = I.h ∨ Cross p q r R)
  · rw [ite_t hc1]
    obtain ⟨hl, hrt⟩ := hc1
    by_cases hR0 : R = 0
    · subst hR0
      rw [ite_t rfl]
      have hc0 : Cross p q r 0 := hrt.resolve_left (by omega)
      obtain ⟨st', -⟩ := PState.sweepRightC (I.h - 0) 0 U0 _ _ rfl st0
        (fun h => (inU 0 h).2 hc0) (midC 0 hc0)
        (fun z _ hzh hzU => midC z (notU z hzh hzU))
      exact finish _ _ (st'.congrU (by ext z; simp))
    · rw [ite_f hR0]
      have hcL : Cross p q r (R - 1) := hl.resolve_left hR0
      obtain ⟨st1, keep1⟩ := PState.sweepLeftC (R - 1) U0 _ _ st0
        (fun h => (inU _ h).2 hcL) (midC _ hcL)
        (fun z hz hzU => midC z (notU z (by omega) hzU))
      by_cases hRh' : R = I.h
      · rw [ite_t hRh']
        refine finish _ _ (st1.congrU ?_)
        ext z
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hz
        have := (inU z hz).1
        omega
      · rw [ite_f hRh']
        have hcR : Cross p q r R := hrt.resolve_left hRh'
        obtain ⟨st2, -⟩ := PState.sweepRightC (I.h - R) R (U0.filter (R - 1 < ·)) _ _
          rfl st1 (fun h => (inU R (Finset.mem_filter.mp h).1).2 hcR)
          (keep1 R (by omega) (midC R hcR))
          (fun z hz hzh hzU => keep1 z (by omega)
            (midC z (notU z hzh (fun h => hzU (Finset.mem_filter.mpr ⟨h, by omega⟩)))))
        refine finish _ _ (st2.congrU ?_)
        ext z
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        rintro ⟨_, h1⟩ h2
        omega
  · rw [ite_f hc1]
    have hflip := hcase.resolve_left hc1
    obtain ⟨h1, hRlt, hnc1, hnc, hu⟩ := hflip
    obtain ⟨y, rfl⟩ : ∃ y, R = y + 1 := ⟨R - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hnc1 hu ⊢
    have hy : y ∈ U0 := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hnc1⟩
    have hy1 : y + 1 ∈ U0 := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hRlt, hnc⟩
    have hu' : Used (stretch r p) (r, y) (r, y + 1) ∨ Used (stretch r q) (r, y) (r, y + 1) := by
      rcases hu with hu | hu
      · exact Or.inl (used_stretch_row hu)
      · exact Or.inr (used_stretch_row hu)
    obtain ⟨st1, m1, m2, keep1⟩ := st0.flipC hy hy1 hu'
    have outU1 : ∀ z, z ≠ y → z ≠ y + 1 → z ∉ (U0.erase y).erase (y + 1) → z ∉ U0 := by
      intro z h1 h2 hz hz0
      exact hz (Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, hz0⟩⟩)
    obtain ⟨st2, keep2⟩ := PState.sweepLeftC y _ _ _ st1
      (fun h => Finset.notMem_erase y U0 (Finset.mem_of_mem_erase h)) m1
      (fun z hz hzU => keep1 z (midC z (notU z (by omega)
        (outU1 z (by omega) (by omega) hzU))))
    obtain ⟨st3, -⟩ := PState.sweepRightC (I.h - (y + 1)) (y + 1) _ _ _ rfl st2
      (fun h => Finset.notMem_erase (y + 1) _ (Finset.mem_filter.mp h).1)
      (keep2 (y + 1) (by omega) m2)
      (fun z hz hzh hzU => keep2 z (by omega) (keep1 z (midC z (notU z hzh
        (outU1 z (by omega) (by omega) (fun h => hzU (Finset.mem_filter.mpr ⟨h, by omega⟩)))))))
    refine finish _ _ (st3.congrU ?_)
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.notMem_empty, iff_false, not_and]
    rintro ⟨_, h1⟩ h2
    omega

end ZZN

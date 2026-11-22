/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Timed.ThinNC

@[expose] public section

/-!
# A non-crossing matching is determined by its opening and closing places

`M` is a matching on places: symmetric, each place has at most one partner, no place is its own
partner, and two different pairs never interleave (`Mtch`). Place `k` opens if its partner is
larger, closes if smaller. For a pair `p < q`, every place strictly between them is matched inside
`(p, q)`. So for `p < k < q` the closing places in `(p, k]` are at most the opening ones, and in
`(p, q]` they exceed them by one: `q` is the first place after `p` where the closing places
outnumber the opening ones. Two matchings with the same opening and closing places are equal
(`match_eq`).
-/

namespace ZZN.T

open Classical

/-- A non-crossing matching on places. -/
structure Mtch (M : ℕ → ℕ → Prop) : Prop where
  symm : ∀ p q, M p q → M q p
  func : ∀ p q q', M p q → M p q' → q = q'
  irr : ∀ p, ¬ M p p
  nc : ∀ p q u v, M p q → M u v → p ≠ u → p ≠ v → ¬ Cross p q u v

/-- Place `k` opens a pair. -/
def Op (M : ℕ → ℕ → Prop) (k : ℕ) : Prop := ∃ q, k < q ∧ M k q

/-- Place `k` closes a pair. -/
def Cl (M : ℕ → ℕ → Prop) (k : ℕ) : Prop := ∃ q, q < k ∧ M k q

section
variable {M : ℕ → ℕ → Prop}

/-- The partner of a place inside a pair lies inside the pair. -/
lemma partner_in (hM : Mtch M) {p q i j : ℕ} (hpq : M p q) (hlt : p < q) (hi : p < i) (hiq : i < q)
    (hij : M i j) : p < j ∧ j < q := by
  have hjp : j ≠ p := by
    rintro rfl
    have := hM.func _ _ _ (hM.symm _ _ hij) hpq; omega
  have hjq : j ≠ q := by
    rintro rfl
    have := hM.func _ _ _ (hM.symm _ _ hij) (hM.symm _ _ hpq); omega
  have hc := hM.nc p q i j hpq hij (by omega) (Ne.symm hjp)
  unfold Cross sep at hc
  omega

/-- The partner of a closing place. -/
noncomputable def pcl (M : ℕ → ℕ → Prop) (i : ℕ) : ℕ := if h : Cl M i then h.choose else 0

/-- The partner of an opening place. -/
noncomputable def pop (M : ℕ → ℕ → Prop) (i : ℕ) : ℕ := if h : Op M i then h.choose else 0

lemma pcl_spec {i : ℕ} (h : Cl M i) : pcl M i < i ∧ M i (pcl M i) := by
  unfold pcl; simp only [h, ↓reduceDIte]; exact h.choose_spec

lemma pop_spec {i : ℕ} (h : Op M i) : i < pop M i ∧ M i (pop M i) := by
  unfold pop; simp only [h, ↓reduceDIte]; exact h.choose_spec

lemma not_op_cl (hM : Mtch M) {k : ℕ} (h1 : Op M k) (h2 : Cl M k) : False := by
  obtain ⟨q, hq, hkq⟩ := h1
  obtain ⟨q', hq', hkq'⟩ := h2
  have := hM.func _ _ _ hkq hkq'; omega

/-- Closing places of `(p, k]` inside a pair map into opening places of `(p, k]`. -/
lemma card_cl_le (hM : Mtch M) {p q : ℕ} (hpq : M p q) (hlt : p < q) {k : ℕ} (hk : k < q) :
    ((Finset.Ioc p k).filter (Cl M)).card ≤ ((Finset.Ioc p k).filter (Op M)).card := by
  apply Finset.card_le_card_of_injOn (pcl M)
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_ofPred_eq] at hi ⊢
    obtain ⟨⟨h1, h2⟩, hc⟩ := hi
    obtain ⟨s1, s2⟩ := pcl_spec hc
    have hin := partner_in hM hpq hlt h1 (by omega) s2
    exact ⟨⟨hin.1, by omega⟩, ⟨i, s1, hM.symm _ _ s2⟩⟩
  · intro i hi i' hi' h
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hi hi'
    have a1 := (pcl_spec hi.2).2
    have a2 := (pcl_spec hi'.2).2
    rw [h] at a1
    exact hM.func _ _ _ (hM.symm _ _ a1) (hM.symm _ _ a2)

/-- Inside a pair, opening and closing places are equally many. -/
lemma card_inner (hM : Mtch M) {p q : ℕ} (hpq : M p q) (hlt : p < q) :
    ((Finset.Ioo p q).filter (Cl M)).card = ((Finset.Ioo p q).filter (Op M)).card := by
  apply le_antisymm
  · apply Finset.card_le_card_of_injOn (pcl M)
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_Ioo, Set.mem_ofPred_eq] at hi ⊢
      obtain ⟨⟨h1, h2⟩, hc⟩ := hi
      obtain ⟨s1, s2⟩ := pcl_spec hc
      have hin := partner_in hM hpq hlt h1 h2 s2
      exact ⟨hin, ⟨i, s1, hM.symm _ _ s2⟩⟩
    · intro i hi i' hi' h
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hi hi'
      have a1 := (pcl_spec hi.2).2
      have a2 := (pcl_spec hi'.2).2
      rw [h] at a1
      exact hM.func _ _ _ (hM.symm _ _ a1) (hM.symm _ _ a2)
  · apply Finset.card_le_card_of_injOn (pop M)
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_Ioo, Set.mem_ofPred_eq] at hi ⊢
      obtain ⟨⟨h1, h2⟩, hc⟩ := hi
      obtain ⟨s1, s2⟩ := pop_spec hc
      have hin := partner_in hM hpq hlt h1 h2 s2
      exact ⟨hin, ⟨i, s1, hM.symm _ _ s2⟩⟩
    · intro i hi i' hi' h
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hi hi'
      have a1 := (pop_spec hi.2).2
      have a2 := (pop_spec hi'.2).2
      rw [h] at a1
      exact hM.func _ _ _ (hM.symm _ _ a1) (hM.symm _ _ a2)

/-- In `(p, q]` the closing places exceed the opening ones by one. -/
lemma card_pair (hM : Mtch M) {p q : ℕ} (hpq : M p q) (hlt : p < q) :
    ((Finset.Ioc p q).filter (Cl M)).card = ((Finset.Ioc p q).filter (Op M)).card + 1 := by
  have hcq : Cl M q := ⟨p, hlt, hM.symm _ _ hpq⟩
  have hoq : ¬ Op M q := fun h => not_op_cl hM h hcq
  rw [← Finset.Ioo_insert_right hlt, Finset.filter_insert, Finset.filter_insert]
  simp only [hcq, hoq, ↓reduceIte]
  rw [Finset.card_insert_of_notMem (by simp), card_inner hM hpq hlt]

/-- **Equal opening and closing places give equal matchings.** -/
theorem match_eq {M M' : ℕ → ℕ → Prop} (hM : Mtch M) (hM' : Mtch M') (hop : ∀ k, Op M k ↔ Op M' k)
    (hcl : ∀ k, Cl M k ↔ Cl M' k) {p q : ℕ} (h : M p q) : M' p q := by
  have fo : ∀ s : Finset ℕ, s.filter (Op M) = s.filter (Op M') := fun s => Finset.filter_congr (fun k _ => hop k)
  have fc : ∀ s : Finset ℕ, s.filter (Cl M) = s.filter (Cl M') := fun s => Finset.filter_congr (fun k _ => hcl k)
  have main : ∀ p q, p < q → M p q → M' p q := by
    intro p q hlt h
    obtain ⟨q', hq', h'⟩ := (hop p).mp ⟨q, hlt, h⟩
    rcases lt_trichotomy q q' with hl | rfl | hl
    · have a := card_cl_le hM' h' hq' hl
      have b := card_pair hM h hlt
      rw [fo, fc] at b; omega
    · exact h'
    · have a := card_cl_le hM h hlt hl
      have b := card_pair hM' h' hq'
      rw [← fo, ← fc] at b; omega
  rcases lt_trichotomy p q with hl | rfl | hl
  · exact main p q hl h
  · exact absurd h (hM.irr p)
  · exact hM'.symm _ _ (main q p hl (hM.symm _ _ h))

end

end ZZN.T

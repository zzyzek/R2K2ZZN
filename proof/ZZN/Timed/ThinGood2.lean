/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Timed.ThinCount2
public import ZZN.Thin.Sound
public import ZZN.Constr.ThinWit

@[expose] public section

/-!
# Reachable states satisfy `Good2`

Every state the plug DP reaches keeps its pieces sorted with `lo ≤ hi` (`fold_SInv`): pieces are
only erased or inserted by `insSorted (mkP x y)`. Under the realizability invariant `W` no plug
code is an end of two pieces (`plugDisj_of_W`): the code names one boundary edge (`desc_inj`), so
the two pieces would share its processed cell.
-/

namespace ZZN.T

open ZZN ZZN.Thin GridHam

/-! ### Sorted pieces with `lo ≤ hi` -/

/-- The structural invariant: pieces sorted, each with `lo ≤ hi`. -/
def SInv (s : St) : Prop := s.1.Pairwise (· ≤ ·) ∧ ∀ z ∈ s.1, lo z ≤ hi z

lemma mem_insSorted (x : ℕ) : ∀ (l : List ℕ) (z : ℕ), z ∈ insSorted x l ↔ z = x ∨ z ∈ l
  | [], z => by simp [insSorted]
  | y :: l, z => by
    unfold insSorted
    split_ifs
    · simp
    · simp only [List.mem_cons, mem_insSorted x l z]; tauto

lemma insSorted_pairwise (x : ℕ) : ∀ l : List ℕ, l.Pairwise (· ≤ ·) → (insSorted x l).Pairwise (· ≤ ·)
  | [], _ => by simp [insSorted]
  | y :: l, h => by
    unfold insSorted
    have h' := List.pairwise_cons.mp h
    split_ifs with hxy
    · refine List.Pairwise.cons (fun z hz => ?_) h
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hxy
      · exact le_trans hxy (h'.1 z hz)
    · refine List.Pairwise.cons (fun z hz => ?_) (insSorted_pairwise x l h'.2)
      rcases (mem_insSorted x l z).mp hz with rfl | hz
      · omega
      · exact h'.1 z hz

lemma lo_mkP (x y : ℕ) : lo (mkP x y) = min x y := by
  unfold mkP lo; split_ifs <;> simp [Nat.unpair_pair] <;> omega

lemma hi_mkP (x y : ℕ) : hi (mkP x y) = max x y := by
  unfold mkP hi; split_ifs <;> simp [Nat.unpair_pair] <;> omega

lemma restK_sublist (ps : List ℕ) (pu pl : Option ℕ) : (restK ps pu pl).Sublist ps := by
  unfold restK
  split_ifs
  · exact ((ps.erase_sublist).erase _).trans (ps.erase_sublist)
  · exact ps.erase_sublist
  · exact ps.erase_sublist
  · exact List.Sublist.refl _

lemma closeP_SInv {a b x y : ℕ} {rest : List ℕ} {dn : ℕ} {s' : St}
    (h : closeP a b x y rest dn = some s') (hr : SInv (rest, dn)) : SInv s' := by
  obtain ⟨hp, hl⟩ := hr
  unfold closeP at h
  split_ifs at h
  · cases h; exact ⟨hp, hl⟩
  · cases h
    refine ⟨insSorted_pairwise _ rest hp, fun z hz => ?_⟩
    rcases (mem_insSorted _ rest z).mp hz with rfl | hz
    · rw [lo_mkP, hi_mkP]; omega
    · exact hl z hz

lemma stepCell_SInv {a b : ℕ} {e : Option ℕ} {r c : ℕ} {s s' : St}
    (h : s' ∈ stepCell a b e r c s) (hs : SInv s) : SInv s' := by
  have hrest : SInv (restK s.1 (puOf s r c) (plOf b s c), s.2) :=
    ⟨hs.1.sublist (restK_sublist _ _ _),
      fun z hz => hs.2 z ((restK_sublist _ _ _).subset hz)⟩
  rw [ZZN.Thin.stepCell_eq] at h
  split_ifs at h
  · simp at h
  · simp at h
  · rw [List.mem_filterMap] at h
    obtain ⟨outs, -, ho⟩ := h
    split at ho
    · exact closeP_SInv ho hrest
    · cases ho

/-- **Every reached state is sorted, with `lo ≤ hi`.** -/
theorem fold_SInv (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) :
    ∀ n, ∀ s ∈ (List.range n).foldl (stageF a b tm) [([], 0)], SInv s := by
  intro n
  induction n with
  | zero => intro s hs; rw [List.mem_singleton.mp hs]; exact ⟨List.Pairwise.nil, by simp⟩
  | succ n ih =>
    intro s hs
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hs
    unfold stageF stage at hs
    rw [List.mem_filter, mem_normS, List.mem_flatMap] at hs
    obtain ⟨⟨s0, h0, h1⟩, -⟩ := hs
    exact stepCell_SInv h1 (ih s0 h0)

/-! ### Plug codes are not shared -/

section
variable {a b : ℕ} {J : Inst}

/-- **Under `W`, no plug code is an end of two pieces.** -/
theorem plugDisj_of_W {n : ℕ} (hn : n ≤ a * b) {s : St} (hW : W a b J n s) : PlugDisj b s.1 := by
  obtain ⟨sg, dp, hnd, -, hseg, -, hall, -⟩ := hW
  have hflat : (s.1.flatMap sg).Nodup := (List.nodup_append.mp hall).1
  have endcell : ∀ z ∈ s.1, ∀ e, (lo z = e ∨ hi z = e) →
      ∃ u ∈ sg z, prI a b n u ∧ EndOK a b J n e u := by
    intro z hz e he
    obtain ⟨-, -, -, hp, u, v, hu, hv, eu, ev⟩ := hseg z hz
    have hum : u ∈ sg z := List.mem_of_mem_head? hu
    have hvm : v ∈ sg z := List.mem_of_mem_getLast? hv
    rcases he with rfl | rfl
    · exact ⟨u, hum, hp u hum, eu⟩
    · exact ⟨v, hvm, hp v hvm, ev⟩
  intro z hz z' hz' e he hze hz'e
  obtain ⟨u, hu, pu, eu⟩ := endcell z hz e hze
  obtain ⟨u', hu', pu', eu'⟩ := endcell z' hz' e hz'e
  have hlt : e < a + 2 * b + 1 := by omega
  obtain ⟨y, hy, hadj, hd⟩ := plug_of pu eu hlt
  obtain ⟨y', hy', hadj', hd'⟩ := plug_of pu' eu' hlt
  obtain ⟨huu, -⟩ := desc_inj hn pu hy hadj pu' hy' hadj' (hd.trans hd'.symm)
  subst huu
  exact flatMap_unique hnd hflat hz hz' hu hu'

/-- `W` gives `lo ≠ hi`. -/
theorem lo_ne_hi_of_W {n : ℕ} {s : St} (hW : W a b J n s) : ∀ z ∈ s.1, lo z ≠ hi z := by
  obtain ⟨sg, dp, -, -, hseg, -⟩ := hW
  exact fun z hz => (hseg z hz).1

end

end ZZN.T

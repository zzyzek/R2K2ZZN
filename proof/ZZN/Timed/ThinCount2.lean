/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Timed.ThinCount
public import Mathlib.Data.List.Sort

@[expose] public section

/-!
# Counting DP states by their plug map

A reachable state has more structure than `Good` records: its pieces are sorted, each piece has
`lo < hi`, and no plug code is an end of two pieces (`Good2`). Such a state is determined by its
colour mask, by whether it holds the piece joining the two endpoint codes, and by the map sending
each plug code `j ≤ b` to the other end of the piece using it. So a duplicate-free list of such
states has at most `Nst b = 8 (b + 5) ^ (b + 1)` entries (`card_good2`).
-/

namespace ZZN.T

open ZZN ZZN.Thin GridHam

/-- No plug code is an end of two different pieces. -/
def PlugDisj (b : ℕ) (ps : List ℕ) : Prop :=
  ∀ z ∈ ps, ∀ z' ∈ ps, ∀ e, e ≤ b → (lo z = e ∨ hi z = e) → (lo z' = e ∨ hi z' = e) → z = z'

/-- A reachable state: `Good`, pieces sorted with `lo < hi`, and plug codes not shared. -/
def Good2 (a b : ℕ) (s : St) : Prop :=
  Good a b s ∧ s.1.Pairwise (· ≤ ·) ∧ (∀ z ∈ s.1, lo z < hi z) ∧ PlugDisj b s.1

/-- The piece of `ps` using plug code `j`, if any. -/
def pieceAt (ps : List ℕ) (j : ℕ) : Option ℕ := ps.find? (fun z => lo z == j || hi z == j)

/-- The digit of plug `j`: `0` if no piece uses it, else one more than the compressed other end. -/
def plugVal (a b : ℕ) (ps : List ℕ) (j : ℕ) : ℕ :=
  match pieceAt ps j with
  | none => 0
  | some z => 1 + cmpE a b (if lo z = j then hi z else lo z)

/-- The piece joining the two endpoint codes. -/
def tPiece (a b : ℕ) : ℕ := Nat.pair (termE a b 0) (termE a b 1)

/-- Code of a state. -/
def scode2 (a b : ℕ) (s : St) : ℕ :=
  s.2 + 4 * ((if tPiece a b ∈ s.1 then 1 else 0) +
    2 * lcode (b + 4) ((List.range (b + 1)).map (plugVal a b s.1)))

/-- The other end of piece `z` at plug `j`. -/
def otherAt (z j : ℕ) : ℕ := if lo z = j then hi z else lo z

lemma goodEnd_other {a b z : ℕ} (h : GoodEnd a b (lo z) ∧ GoodEnd a b (hi z)) (j : ℕ) :
    GoodEnd a b (otherAt z j) := by
  unfold otherAt; split_ifs; exacts [h.2, h.1]

lemma plugVal_some {a b : ℕ} {ps : List ℕ} {j z : ℕ} (h : pieceAt ps j = some z) :
    plugVal a b ps j = 1 + cmpE a b (otherAt z j) := by
  unfold plugVal otherAt; rw [h]

lemma plugVal_none {a b : ℕ} {ps : List ℕ} {j : ℕ} (h : pieceAt ps j = none) :
    plugVal a b ps j = 0 := by
  unfold plugVal; rw [h]

lemma plugVal_lt {a b : ℕ} {ps : List ℕ} (he : ∀ z ∈ ps, GoodEnd a b (lo z) ∧ GoodEnd a b (hi z))
    (j : ℕ) : plugVal a b ps j < b + 4 := by
  cases h : pieceAt ps j with
  | none => rw [plugVal_none h]; omega
  | some z =>
    rw [plugVal_some h]
    have := cmpE_lt (goodEnd_other (he z (List.mem_of_find?_eq_some h)) j)
    omega

lemma scode2_lt {a b : ℕ} {s : St} (hs : Good2 a b s) : scode2 a b s < Nst b := by
  obtain ⟨⟨-, h4, he⟩, -⟩ := hs
  have h1 := lcode_lt (b + 4) ((List.range (b + 1)).map (plugVal a b s.1)) (fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact plugVal_lt he j)
  simp only [List.length_map, List.length_range] at h1
  have e : (b + 4 + 1) ^ (b + 1) = (b + 5) ^ (b + 1) := by ring_nf
  rw [e] at h1
  unfold scode2 Nst
  split_ifs <;> omega

/-- A piece with `lo < hi` is determined by its two ends. -/
lemma piece_eq {z z' : ℕ} (h1 : lo z = lo z') (h2 : hi z = hi z') : z = z' := by
  have : Nat.unpair z = Nat.unpair z' := Prod.ext h1 h2
  rw [← Nat.pair_unpair z, ← Nat.pair_unpair z', this]

lemma termE_lt (a b : ℕ) : termE a b 0 < termE a b 1 := by unfold termE; omega

/-- A piece with no plug end is the piece joining the endpoint codes. -/
lemma noplug_piece {a b z : ℕ} (he : GoodEnd a b (lo z) ∧ GoodEnd a b (hi z)) (hlt : lo z < hi z)
    (hl : ¬ lo z ≤ b) (hh : ¬ hi z ≤ b) : z = tPiece a b := by
  have hl' : lo z = termE a b 0 ∨ lo z = termE a b 1 := he.1.resolve_left hl
  have hh' : hi z = termE a b 0 ∨ hi z = termE a b 1 := he.2.resolve_left hh
  have ht := termE_lt a b
  have e1 : lo z = termE a b 0 := by rcases hl' with h | h <;> rcases hh' with h' | h' <;> omega
  have e2 : hi z = termE a b 1 := by rcases hl' with h | h <;> rcases hh' with h' | h' <;> omega
  apply piece_eq
  · rw [e1]; simp [tPiece, lo]
  · rw [e2]; simp [tPiece, hi]

lemma pieceAt_some {ps : List ℕ} {j z : ℕ} (hz : z ∈ ps) (hj : lo z = j ∨ hi z = j) :
    ∃ z', pieceAt ps j = some z' ∧ z' ∈ ps ∧ (lo z' = j ∨ hi z' = j) := by
  unfold pieceAt
  cases h : ps.find? (fun z => lo z == j || hi z == j) with
  | none =>
    rw [List.find?_eq_none] at h
    have := h z hz
    simp at this; omega
  | some z' =>
    have hm := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    simp only [Bool.or_eq_true, beq_iff_eq] at hp
    exact ⟨z', rfl, hm, hp⟩

/-- From equal plug digits, a piece of `s` using plug `j` is a piece of `s'`. -/
lemma mem_of_plugVal {a b : ℕ} {s s' : St} (hs : Good2 a b s) (hs' : Good2 a b s') {z j : ℕ}
    (hz : z ∈ s.1) (hjb : j ≤ b) (hj : lo z = j ∨ hi z = j)
    (hv : plugVal a b s.1 j = plugVal a b s'.1 j) : z ∈ s'.1 := by
  obtain ⟨⟨-, -, he⟩, -, hlt, hd⟩ := hs
  obtain ⟨⟨-, -, he'⟩, -, hlt', hd'⟩ := hs'
  obtain ⟨z1, h1, hm1, hj1⟩ := pieceAt_some hz hj
  have hz1 : z1 = z := hd z1 hm1 z hz j hjb hj1 hj
  subst hz1
  rw [plugVal_some h1] at hv
  cases h2 : pieceAt s'.1 j with
  | none => rw [plugVal_none h2] at hv; omega
  | some z2 =>
    rw [plugVal_some h2] at hv
    have hm2 : z2 ∈ s'.1 := List.mem_of_find?_eq_some h2
    have hj2 : lo z2 = j ∨ hi z2 = j := by
      have hp := List.find?_some h2
      simp only [Bool.or_eq_true, beq_iff_eq] at hp
      exact hp
    have l1 := hlt z1 hm1
    have l2 := hlt' z2 hm2
    have key : otherAt z1 j = otherAt z2 j :=
      cmpE_inj (goodEnd_other (he z1 hm1) j) (goodEnd_other (he' z2 hm2) j) (by omega)
    unfold otherAt at key
    have : z1 = z2 := by
      apply piece_eq <;> split_ifs at key <;> omega
    rw [this]; exact hm2

lemma mem_of_scode2 {a b : ℕ} {s s' : St} (hs : Good2 a b s) (hs' : Good2 a b s')
    (h : scode2 a b s = scode2 a b s') {z : ℕ} (hz : z ∈ s.1) : z ∈ s'.1 := by
  have hs0 := hs
  have hs1 := hs'
  obtain ⟨⟨-, h4, he⟩, -, hlt, -⟩ := hs
  obtain ⟨⟨-, h4', he'⟩, -, -, -⟩ := hs'
  unfold scode2 at h
  have hfl : (if tPiece a b ∈ s.1 then 1 else 0) + 2 * lcode (b + 4) ((List.range (b + 1)).map (plugVal a b s.1)) =
      (if tPiece a b ∈ s'.1 then 1 else 0) + 2 * lcode (b + 4) ((List.range (b + 1)).map (plugVal a b s'.1)) := by
    omega
  have hl : lcode (b + 4) ((List.range (b + 1)).map (plugVal a b s.1)) =
      lcode (b + 4) ((List.range (b + 1)).map (plugVal a b s'.1)) := by
    split_ifs at hfl <;> omega
  have hf : (tPiece a b ∈ s.1) ↔ (tPiece a b ∈ s'.1) := by
    constructor <;> intro hm <;> by_contra hn
    · simp only [hm, hn, ↓reduceIte] at hfl; omega
    · simp only [hm, hn, ↓reduceIte] at hfl; omega
  have hvals := lcode_inj (b + 4) _ _
    (fun x hx => by obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx; exact plugVal_lt he j)
    (fun x hx => by obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx; exact plugVal_lt he' j) hl
  have hv : ∀ j, j ≤ b → plugVal a b s.1 j = plugVal a b s'.1 j := by
    intro j hj
    have := congrArg (fun l => l[j]?) hvals
    simp only [List.getElem?_map, List.getElem?_range (by omega : j < b + 1), Option.map_some,
      Option.some.injEq] at this
    exact this
  by_cases hlo : lo z ≤ b
  · exact mem_of_plugVal hs0 hs1 hz hlo (Or.inl rfl) (hv _ hlo)
  · by_cases hhi : hi z ≤ b
    · exact mem_of_plugVal hs0 hs1 hz hhi (Or.inr rfl) (hv _ hhi)
    · have := noplug_piece (he z hz) (hlt z hz) hlo hhi
      subst this
      exact hf.mp hz

lemma scode2_inj {a b : ℕ} {s s' : St} (hs : Good2 a b s) (hs' : Good2 a b s')
    (h : scode2 a b s = scode2 a b s') : s = s' := by
  have hm : ∀ z, z ∈ s.1 ↔ z ∈ s'.1 := fun z =>
    ⟨fun hz => mem_of_scode2 hs hs' h hz, fun hz => mem_of_scode2 hs' hs h.symm hz⟩
  obtain ⟨⟨hn, h4, -⟩, hsort, -, -⟩ := hs
  obtain ⟨⟨hn', h4', -⟩, hsort', -, -⟩ := hs'
  have hp : s.1.Perm s'.1 := (List.perm_ext_iff_of_nodup hn hn').mpr hm
  have e1 : s.1 = s'.1 := List.Perm.eq_of_pairwise' hsort hsort' hp
  have e2 : s.2 = s'.2 := by
    unfold scode2 at h
    rw [e1] at h
    omega
  exact Prod.ext e1 e2

/-- **A duplicate-free list of reachable states has at most `Nst b` entries.** -/
theorem card_good2 {a b : ℕ} (S : List St) (hn : S.Nodup) (hg : ∀ s ∈ S, Good2 a b s) :
    S.length ≤ Nst b := by
  have hmap : (S.map (scode2 a b)).Nodup :=
    List.Nodup.map_on (fun x hx y hy h => scode2_inj (hg x hx) (hg y hy) h) hn
  have := nodup_len_le (Nst b) _ hmap (fun x hx => by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
    exact scode2_lt (hg s hs))
  simpa using this

end ZZN.T

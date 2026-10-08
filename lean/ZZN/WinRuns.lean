-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.WinCheck
import ZZN.Defs

/-!
# Runs of a path inside a set of cells

A **run** of a path `L` in a predicate `P` is a maximal interval `[st, en]` of indices whose cells
all satisfy `P`. Used for the window certificates: the pieces of the inside DP are the runs of the
solution paths in the processed cells.
-/

namespace ZZN.Win

open GridHam

def nth (L : List Coord) (j : ℕ) : Coord := L.getD j (0, 0)

structure IsRun (P : Coord → Prop) (L : List Coord) (st en : ℕ) : Prop where
  le : st ≤ en
  lt : en < L.length
  all : ∀ j, st ≤ j → j ≤ en → P (nth L j)
  left : st = 0 ∨ ¬ P (nth L (st - 1))
  right : en + 1 = L.length ∨ ¬ P (nth L (en + 1))

theorem nth_eq {L : List Coord} {j : ℕ} (h : j < L.length) : nth L j = L[j] := by
  unfold nth; rw [List.getD_eq_getElem _ _ h]

theorem nth_mem {L : List Coord} {j : ℕ} (h : j < L.length) : nth L j ∈ L := by
  rw [nth_eq h]; exact List.getElem_mem h

theorem nth_inj {L : List Coord} (hn : L.Nodup) {i j : ℕ} (hi : i < L.length) (hj : j < L.length)
    (h : nth L i = nth L j) : i = j := by
  rw [nth_eq hi, nth_eq hj] at h
  exact (List.Nodup.getElem_inj_iff hn).mp h

/-- Two runs sharing an index are equal. -/
theorem run_unique {P : Coord → Prop} {L : List Coord} {st en st' en' j : ℕ} (h : IsRun P L st en)
    (h' : IsRun P L st' en') (h1 : st ≤ j) (h2 : j ≤ en) (h3 : st' ≤ j) (h4 : j ≤ en') :
    st = st' ∧ en = en' := by
  constructor
  · rcases Nat.lt_trichotomy st st' with c | c | c
    · rcases h'.left with e | e
      · omega
      · exact absurd (h.all (st' - 1) (by omega) (by omega)) e
    · exact c
    · rcases h.left with e | e
      · omega
      · exact absurd (h'.all (st - 1) (by omega) (by omega)) e
  · rcases Nat.lt_trichotomy en en' with c | c | c
    · rcases h.right with e | e
      · have := h'.lt; omega
      · exact absurd (h'.all (en + 1) (by omega) (by omega)) e
    · exact c
    · rcases h'.right with e | e
      · have := h.lt; omega
      · exact absurd (h.all (en' + 1) (by omega) (by omega)) e

theorem run_left_ext {P : Coord → Prop} [DecidablePred P] {L : List Coord} :
    ∀ j, P (nth L j) → ∃ st, st ≤ j ∧ (∀ k, st ≤ k → k ≤ j → P (nth L k)) ∧ (st = 0 ∨ ¬ P (nth L (st - 1)))
  | 0, h => ⟨0, le_refl _, fun k _ hk => by rw [show k = 0 by omega]; exact h, Or.inl rfl⟩
  | j + 1, h => by
    by_cases hp : P (nth L j)
    · obtain ⟨st, h1, h2, h3⟩ := run_left_ext j hp
      refine ⟨st, by omega, fun k hk hk' => ?_, h3⟩
      rcases Nat.lt_or_ge k (j + 1) with c | c
      · exact h2 k hk (by omega)
      · rw [show k = j + 1 by omega]; exact h
    · exact ⟨j + 1, le_refl _, fun k hk hk' => by rw [show k = j + 1 by omega]; exact h, Or.inr hp⟩

theorem run_right_ext {P : Coord → Prop} [DecidablePred P] {L : List Coord} :
    ∀ d j, L.length = j + 1 + d → P (nth L j) →
      ∃ en, j ≤ en ∧ en < L.length ∧ (∀ k, j ≤ k → k ≤ en → P (nth L k)) ∧
        (en + 1 = L.length ∨ ¬ P (nth L (en + 1)))
  | 0, j, hl, h => ⟨j, le_refl _, by omega, fun k hk hk' => by rw [show k = j by omega]; exact h,
      Or.inl (by omega)⟩
  | d + 1, j, hl, h => by
    by_cases hp : P (nth L (j + 1))
    · obtain ⟨en, h1, h2, h3, h4⟩ := run_right_ext d (j + 1) (by omega) hp
      refine ⟨en, by omega, h2, fun k hk hk' => ?_, h4⟩
      rcases Nat.lt_or_ge j k with c | c
      · exact h3 k (by omega) hk'
      · rw [show k = j by omega]; exact h
    · exact ⟨j, le_refl _, by omega, fun k hk hk' => by rw [show k = j by omega]; exact h, Or.inr hp⟩

/-- Every index in `P` lies in a run. -/
theorem run_exists {P : Coord → Prop} [DecidablePred P] {L : List Coord} {j : ℕ} (hj : j < L.length)
    (h : P (nth L j)) : ∃ st en, IsRun P L st en ∧ st ≤ j ∧ j ≤ en := by
  obtain ⟨st, h1, h2, h3⟩ := run_left_ext j h
  obtain ⟨en, e1, e2, e3, e4⟩ := run_right_ext (L.length - j - 1) j (by omega) h
  refine ⟨st, en, ⟨by omega, e2, fun k hk hk' => ?_, h3, e4⟩, h1, e1⟩
  rcases Nat.lt_or_ge k j with c | c
  · exact h2 k hk (by omega)
  · exact e3 k c hk'

/-! ### Adding one cell -/

section Add

variable {P : Coord → Prop} {L : List Coord} {j0 : ℕ}

/-- A run away from the new cell stays a run. -/
theorem run_keep (hn : L.Nodup) (hj : j0 < L.length) {st en : ℕ} (h : IsRun P L st en)
    (h1 : en + 1 ≠ j0) (h2 : st ≠ j0 + 1) :
    IsRun (fun y => P y ∨ y = nth L j0) L st en := by
  refine ⟨h.le, h.lt, fun k a b => Or.inl (h.all k a b), ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos st with z | z
    · exact Or.inl z
    · rcases h.left with e | e
      · exact Or.inl e
      · have := h.lt; have := h.le
        exact Or.inr (fun c => c.elim e (fun c => h2 (by have := nth_inj hn (by omega) hj c; omega)))
  · rcases Nat.lt_or_ge (en + 1) L.length with d | d
    · rcases h.right with e | e
      · exact Or.inl e
      · exact Or.inr (fun c => c.elim e (fun c => h1 (nth_inj hn d hj c)))
    · exact Or.inl (by have := h.lt; omega)

/-- A run of the enlarged predicate that misses the new cell is an old run. -/
theorem run_back (hn : L.Nodup) (hj : j0 < L.length) (_hx : ¬ P (nth L j0)) {st en : ℕ}
    (h : IsRun (fun y => P y ∨ y = nth L j0) L st en) (hm : ¬ (st ≤ j0 ∧ j0 ≤ en)) :
    IsRun P L st en ∧ en + 1 ≠ j0 ∧ st ≠ j0 + 1 := by
  have ne : ∀ k, k < L.length → k ≠ j0 → nth L k ≠ nth L j0 := fun k hk hne e => hne (nth_inj hn hk hj e)
  have hst : st ≠ j0 + 1 := by
    intro e
    rcases h.left with c | c
    · omega
    · exact c (Or.inr (by rw [show st - 1 = j0 by omega]))
  have hen : en + 1 ≠ j0 := by
    intro e
    rcases h.right with c | c
    · omega
    · exact c (Or.inr (by rw [e]))
  refine ⟨⟨h.le, h.lt, fun k a b => ?_, ?_, ?_⟩, hen, hst⟩
  · rcases h.all k a b with c | c
    · exact c
    · exact absurd c (ne k (by have := h.lt; omega) (by omega))
  · rcases h.left with c | c
    · exact Or.inl c
    · exact Or.inr (fun d => c (Or.inl d))
  · rcases h.right with c | c
    · exact Or.inl c
    · exact Or.inr (fun d => c (Or.inl d))

/-- How a run of the enlarged predicate starts at the new cell: either there, or where the old run
ending just before it starts. -/
def LeftOK (P : Coord → Prop) (L : List Coord) (j0 s : ℕ) : Prop :=
  (s = j0 ∧ (j0 = 0 ∨ ¬ P (nth L (j0 - 1)))) ∨ (s < j0 ∧ IsRun P L s (j0 - 1))

def RightOK (P : Coord → Prop) (L : List Coord) (j0 e : ℕ) : Prop :=
  (e = j0 ∧ (j0 + 1 = L.length ∨ ¬ P (nth L (j0 + 1)))) ∨ (j0 < e ∧ IsRun P L (j0 + 1) e)

theorem leftOK_exists [DecidablePred P] (hj : j0 < L.length) (hx : ¬ P (nth L j0)) :
    ∃ s, LeftOK P L j0 s := by
  by_cases h : j0 = 0 ∨ ¬ P (nth L (j0 - 1))
  · exact ⟨j0, Or.inl ⟨rfl, h⟩⟩
  · push Not at h
    obtain ⟨st, en, hr, h1, h2⟩ := run_exists (P := P) (L := L) (j := j0 - 1) (by omega) h.2
    have : en = j0 - 1 := by
      by_contra c
      exact hx (by have := hr.all j0 (by omega) (by omega); exact this)
    subst this
    exact ⟨st, Or.inr ⟨by omega, hr⟩⟩

theorem rightOK_exists [DecidablePred P] (hj : j0 < L.length) (hx : ¬ P (nth L j0)) :
    ∃ e, RightOK P L j0 e := by
  by_cases h : j0 + 1 = L.length ∨ ¬ P (nth L (j0 + 1))
  · exact ⟨j0, Or.inl ⟨rfl, h⟩⟩
  · push Not at h
    obtain ⟨st, en, hr, h1, h2⟩ := run_exists (P := P) (L := L) (j := j0 + 1) (by omega) h.2
    have : st = j0 + 1 := by
      by_contra c
      exact hx (by have := hr.all j0 (by omega) (by omega); exact this)
    subst this
    exact ⟨en, Or.inr ⟨by omega, hr⟩⟩

/-- The merged run through the new cell. -/
theorem run_merge (hn : L.Nodup) (hj : j0 < L.length) {s e : ℕ}
    (hs : LeftOK P L j0 s) (he : RightOK P L j0 e) :
    IsRun (fun y => P y ∨ y = nth L j0) L s e := by
  have ne : ∀ k, k < L.length → k ≠ j0 → nth L k ≠ nth L j0 := fun k hk hne e => hne (nth_inj hn hk hj e)
  have hs' : s ≤ j0 := by rcases hs with ⟨rfl, -⟩ | ⟨h, -⟩ <;> omega
  have he' : j0 ≤ e ∧ e < L.length := by
    rcases he with ⟨rfl, -⟩ | ⟨h, hr⟩
    · exact ⟨le_refl _, hj⟩
    · exact ⟨by omega, hr.lt⟩
  refine ⟨by omega, he'.2, fun k a b => ?_, ?_, ?_⟩
  · rcases Nat.lt_trichotomy k j0 with c | c | c
    · rcases hs with ⟨rfl, -⟩ | ⟨-, hr⟩
      · omega
      · exact Or.inl (hr.all k a (by omega))
    · exact Or.inr (by rw [c])
    · rcases he with ⟨rfl, -⟩ | ⟨-, hr⟩
      · omega
      · exact Or.inl (hr.all k (by omega) b)
  · rcases Nat.eq_zero_or_pos s with z | z
    · exact Or.inl z
    · rcases hs with ⟨hs0, c⟩ | ⟨h, hr⟩
      · rcases c with c | c
        · exact Or.inl (by omega)
        · rw [hs0]; exact Or.inr (fun d => d.elim c (ne _ (by omega) (by omega)))
      · rcases hr.left with c | c
        · exact Or.inl c
        · exact Or.inr (fun d => d.elim c (ne _ (by omega) (by omega)))
  · rcases he with ⟨he0, c⟩ | ⟨h, hr⟩
    · rcases c with c | c
      · exact Or.inl (by omega)
      · rcases Nat.lt_or_ge (j0 + 1) L.length with d | d
        · rw [he0]; exact Or.inr (fun f => f.elim c (ne _ d (by omega)))
        · exact Or.inl (by omega)
    · rcases hr.right with c | c
      · exact Or.inl c
      · have := hr.lt
        rcases Nat.lt_or_ge (e + 1) L.length with d | d
        · exact Or.inr (fun f => f.elim c (ne _ d (by omega)))
        · exact Or.inl (by omega)

/-- On another path (without the new cell), runs are unchanged. -/
theorem run_other {M : List Coord} {x : Coord} (hx : x ∉ M) {st en : ℕ} :
    IsRun (fun y => P y ∨ y = x) M st en ↔ IsRun P M st en := by
  have key : ∀ k, k < M.length → ((P (nth M k) ∨ nth M k = x) ↔ P (nth M k)) := fun k hk =>
    ⟨fun h => h.elim id (fun e => absurd (e ▸ nth_mem hk) hx), Or.inl⟩
  constructor
  · intro h
    refine ⟨h.le, h.lt, fun k a b => (key k (by have := h.lt; omega)).mp (h.all k a b), ?_, ?_⟩
    · rcases h.left with c | c
      · exact Or.inl c
      · exact Or.inr (fun d => c (Or.inl d))
    · rcases h.right with c | c
      · exact Or.inl c
      · exact Or.inr (fun d => c (Or.inl d))
  · intro h
    refine ⟨h.le, h.lt, fun k a b => Or.inl (h.all k a b), ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos st with z | z
      · exact Or.inl z
      · rcases h.left with c | c
        · exact Or.inl c
        · have := h.lt; have := h.le
          exact Or.inr (fun d => c ((key _ (by omega)).mp d))
    · rcases Nat.lt_or_ge (en + 1) M.length with z | z
      · rcases h.right with c | c
        · exact Or.inl c
        · exact Or.inr (fun d => c ((key _ z).mp d))
      · exact Or.inl (by have := h.lt; omega)

end Add

end ZZN.Win

-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.WinDP
import ZZN.WinComb

/-!
# Window certificates: the outside data of a solution

The window is `k × k` at the top-left corner. Edges of a solution path that leave the window are
its **crossings**; each uses an exit slot.
-/

namespace ZZN.Win

open GridHam

/-! ### Exit edges and slots -/

/-- The slot of the exit edge from window cell `u` to outside cell `v`. -/
def slotOf (k : ℕ) (u v : Coord) : ℕ := if v = (u.1, u.2 + 1) then u.1 else k + (k - 1 - u.2)

/-- An edge from a window cell to an adjacent outside cell. -/
def ExitEdge (k : ℕ) (u v : Coord) : Prop := u.1 < k ∧ u.2 < k ∧ ¬ (v.1 < k ∧ v.2 < k) ∧ Adjacent u v

theorem exitEdge_cases {k : ℕ} {u v : Coord} (h : ExitEdge k u v) :
    (u.2 + 1 = k ∧ v = (u.1, k)) ∨ (u.1 + 1 = k ∧ v = (k, u.2)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v
  unfold Adjacent at h4
  simp only [Prod.mk.injEq] at *
  omega

theorem slotOf_lt {k : ℕ} {u v : Coord} (h : ExitEdge k u v) : slotOf k u v < 2 * k := by
  have := h.1; have := h.2.1
  unfold slotOf; split_ifs <;> omega

theorem exitCell_slot {k : ℕ} {u v : Coord} (h : ExitEdge k u v) : exitCell k k (slotOf k u v) = v := by
  have h1 := h.1; have h2 := h.2.1
  obtain ⟨u1, u2⟩ := u
  simp only at h1 h2
  rcases exitEdge_cases h with ⟨e, rfl⟩ | ⟨e, rfl⟩ <;> simp only at e <;>
    simp only [slotOf, exitCell, Prod.mk.injEq, true_and] <;> split_ifs <;> (try simp only [Prod.mk.injEq, true_and, and_true]) <;> omega

/-- The window cell of a slot. -/
def inCell (k s : ℕ) : Coord := if s < k then (s, k - 1) else (k - 1, k - 1 - (s - k))

theorem inCell_slot {k : ℕ} {u v : Coord} (h : ExitEdge k u v) : inCell k (slotOf k u v) = u := by
  have h1 := h.1; have h2 := h.2.1
  obtain ⟨u1, u2⟩ := u
  simp only at h1 h2
  rcases exitEdge_cases h with ⟨e, rfl⟩ | ⟨e, rfl⟩ <;> simp only at e <;>
    simp only [slotOf, inCell, Prod.mk.injEq, true_and] <;> split_ifs <;> (try simp only [Prod.mk.injEq, true_and]) <;> omega

/-- A slot determines its exit edge. -/
theorem slot_inj {k : ℕ} {u v u' v' : Coord} (h : ExitEdge k u v) (h' : ExitEdge k u' v')
    (e : slotOf k u v = slotOf k u' v') : u = u' ∧ v = v' := by
  refine ⟨by rw [← inCell_slot h, ← inCell_slot h', e], by rw [← exitCell_slot h, ← exitCell_slot h', e]⟩

/-- The end code of an exit edge. -/
theorem desc_exit {k : ℕ} {u v : Coord} (h : ExitEdge k u v) : desc k k u v = exitE k (slotOf k u v) := by
  rcases exitEdge_cases h with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · have : ((u.1, k) : Coord) = (u.1, u.2 + 1) := by rw [e]
    rw [this, desc_right, ite_eq_right (by omega)]
    unfold slotOf; rw [ite_eq_left rfl]
  · have : ((k, u.2) : Coord) = (u.1 + 1, u.2) := by rw [e]
    rw [this, desc_down, ite_eq_right (by omega)]
    unfold slotOf; rw [ite_eq_right (by simp only [Prod.mk.injEq]; omega)]

/-- At the last stage, every boundary edge is an exit edge. -/
theorem bd_exit {k : ℕ} {u v : Coord} (hu : prI k k (k * k) u) (hv : ¬ prI k k (k * k) v) (h : Adjacent u v) :
    ExitEdge k u v := by
  rw [prI_all] at hu hv
  exact ⟨hu.1, hu.2, hv, h⟩

/-! ### Crossings -/

def inWb (k : ℕ) (x : Coord) : Bool := decide (x.1 < k) && decide (x.2 < k)

theorem inWb_iff {k : ℕ} {x : Coord} : inWb k x = true ↔ x.1 < k ∧ x.2 < k := by
  unfold inWb; simp

/-- Index `j` of `L` is a crossing: the window status changes between `j` and `j + 1`. -/
def IsCross (k : ℕ) (L : List Coord) (j : ℕ) : Prop :=
  j + 1 < L.length ∧ inWb k (nth L j) ≠ inWb k (nth L (j + 1))

/-- The exit edge of a crossing: window cell first. -/
def crossEdge (k : ℕ) (L : List Coord) (j : ℕ) : Coord × Coord :=
  if inWb k (nth L j) then (nth L j, nth L (j + 1)) else (nth L (j + 1), nth L j)

def crossSlot (k : ℕ) (L : List Coord) (j : ℕ) : ℕ := slotOf k (crossEdge k L j).1 (crossEdge k L j).2

section Cross

variable {k : ℕ} {L : List Coord}

theorem cross_exit (hc : chainAdjacent L = true) {j : ℕ} (h : IsCross k L j) :
    ExitEdge k (crossEdge k L j).1 (crossEdge k L j).2 := by
  obtain ⟨h1, h2⟩ := h
  have ad := chain_nth hc h1
  unfold crossEdge
  by_cases hw : inWb k (nth L j) = true
  · rw [ite_eq_left hw]
    have hw' : inWb k (nth L (j + 1)) = false := by
      cases e : inWb k (nth L (j + 1)) <;> simp_all
    exact ⟨(inWb_iff.mp hw).1, (inWb_iff.mp hw).2, fun c => by rw [inWb_iff.mpr c] at hw'; simp at hw', ad⟩
  · rw [ite_eq_right hw]
    have hw' : inWb k (nth L (j + 1)) = true := by
      cases e : inWb k (nth L (j + 1)) <;> simp_all
    exact ⟨(inWb_iff.mp hw').1, (inWb_iff.mp hw').2, fun c => hw (inWb_iff.mpr c), adj_symm ad⟩

theorem crossSlot_lt (hc : chainAdjacent L = true) {j : ℕ} (h : IsCross k L j) : crossSlot k L j < 2 * k :=
  slotOf_lt (cross_exit hc h)

end Cross

section Ends

variable {k : ℕ} {J : Inst} {p q : List Coord}

/-- **Crossings are unique per slot**: two crossings (of either path) with the same slot are the
same crossing. -/
theorem cross_unique (hS : IsSolution J p q) {L L' : List Coord} {col col' : ℕ} (hL : PathC p q L col)
    (hL' : PathC p q L' col') {j j' : ℕ} (h : IsCross k L j) (h' : IsCross k L' j')
    (e : crossSlot k L j = crossSlot k L' j') : L = L' ∧ col = col' ∧ j = j' := by
  obtain ⟨n, c, -⟩ := pathC_facts hS hL
  obtain ⟨n', c', -⟩ := pathC_facts hS hL'
  obtain ⟨eu, ev⟩ := slot_inj (cross_exit c h) (cross_exit c' h') e
  have hj := h.1; have hj' := h'.1
  -- the window cell of the edge lies on both paths
  have mu : (crossEdge k L j).1 ∈ L := by
    unfold crossEdge; split_ifs <;> exact nth_mem (by omega)
  have mu' : (crossEdge k L' j').1 ∈ L' := by
    unfold crossEdge; split_ifs <;> exact nth_mem (by omega)
  rw [eu] at mu
  obtain ⟨rfl, rfl⟩ := pathC_same hS hL hL' mu mu'
  refine ⟨rfl, rfl, ?_⟩
  have ni := fun {i i' : ℕ} (hi : i < L.length) (hi' : i' < L.length) (e : nth L i = nth L i') => nth_inj n hi hi' e
  unfold crossEdge at eu ev
  split_ifs at eu ev with g1 g2 g2
  · exact ni (by omega) (by omega) eu
  · have := ni (by omega) (by omega) eu; have := ni (by omega) (by omega) ev; omega
  · have := ni (by omega) (by omega) eu; have := ni (by omega) (by omega) ev; omega
  · have := ni (by omega) (by omega) eu; omega

end Ends

/-! ### Window runs end at crossings -/

section RunCross

variable {k : ℕ} {L : List Coord}

theorem prI_all' {y : Coord} : prI k k (k * k) y ↔ inWb k y = true := by
  rw [prI_all, inWb_iff]

theorem runL_cross (hc : chainAdjacent L = true) {st en : ℕ} (h : IsRun (prI k k (k * k)) L st en)
    (h0 : st ≠ 0) (col : ℕ) :
    IsCross k L (st - 1) ∧ crossEdge k L (st - 1) = (nth L st, nth L (st - 1)) ∧
      endL k k col L st = exitE k (crossSlot k L (st - 1)) := by
  obtain ⟨b1, b2, b3⟩ := endL_bd hc h h0
  rw [prI_all'] at b1 b2
  have hlt := h.lt; have hle := h.le
  have e1 : st - 1 + 1 = st := by omega
  have cr : IsCross k L (st - 1) := ⟨by omega, by rw [e1, b1]; simpa using b2⟩
  have ce : crossEdge k L (st - 1) = (nth L st, nth L (st - 1)) := by
    unfold crossEdge; rw [ite_eq_right (by simpa using b2), e1]
  refine ⟨cr, ce, ?_⟩
  unfold endL crossSlot; rw [ite_eq_right h0, ce]
  have ee := cross_exit hc cr
  rw [ce] at ee
  exact desc_exit ee

theorem runR_cross (hc : chainAdjacent L = true) {st en : ℕ} (h : IsRun (prI k k (k * k)) L st en)
    (h0 : en + 1 ≠ L.length) (col : ℕ) :
    IsCross k L en ∧ crossEdge k L en = (nth L en, nth L (en + 1)) ∧
      endR k k col L en = exitE k (crossSlot k L en) := by
  obtain ⟨b1, b2, b3⟩ := endR_bd hc h h0
  rw [prI_all'] at b1 b2
  have hlt := h.lt
  have cr : IsCross k L en := ⟨by omega, by rw [b1]; simpa using b2⟩
  have ce : crossEdge k L en = (nth L en, nth L (en + 1)) := by
    unfold crossEdge; rw [ite_eq_left b1]
  refine ⟨cr, ce, ?_⟩
  unfold endR crossSlot; rw [ite_eq_right h0, ce]
  have ee := cross_exit hc cr
  rw [ce] at ee
  exact desc_exit ee

/-- A crossing borders a window run: ending at it (leaving the window) or starting after it
(entering). -/
theorem cross_run {j : ℕ} (h : IsCross k L j) :
    (inWb k (nth L j) = true ∧ ∃ st, IsRun (prI k k (k * k)) L st j) ∨
      (inWb k (nth L j) = false ∧ ∃ en, IsRun (prI k k (k * k)) L (j + 1) en) := by
  obtain ⟨h1, h2⟩ := h
  by_cases hw : inWb k (nth L j) = true
  · left
    refine ⟨hw, ?_⟩
    obtain ⟨st, en, hr, s1, s2⟩ := run_exists (P := prI k k (k * k)) (L := L) (j := j) (by omega) (prI_all'.mpr hw)
    have : en = j := by
      by_contra ne
      have := hr.all (j + 1) (by omega) (by omega)
      rw [prI_all'] at this
      exact h2 (by rw [hw, this])
    subst this; exact ⟨st, hr⟩
  · right
    have hw' : inWb k (nth L (j + 1)) = true := by
      cases e : inWb k (nth L (j + 1)) <;> simp_all
    refine ⟨by simpa using hw, ?_⟩
    obtain ⟨st, en, hr, s1, s2⟩ := run_exists (P := prI k k (k * k)) (L := L) (j := j + 1) h1 (prI_all'.mpr hw')
    have : st = j + 1 := by
      by_contra ne
      have := hr.all j (by omega) (by omega)
      rw [prI_all'] at this
      exact hw this
    subst this; exact ⟨en, hr⟩

end RunCross

/-! ### The used slots and their pieces -/

section Used

variable {k : ℕ} {J : Inst} {p q : List Coord} {s : St}

theorem exitE_lt_term {k x : ℕ} (hx : x < 2 * k) : exitE k x < k + 2 * k + 1 := by unfold exitE; omega

/-- A piece of the final state with an exit end comes from a crossing with that slot. -/
theorem piece_exit (hk : k ≤ 8) (hS : IsSolution J p q) (hinv : Inv k k (k * k) p q s) {z sl : ℕ}
    (hz : z ∈ s.1) (hsl : sl < 2 * k) (he : hasEnd (exitE k sl) z = true) :
    ∃ L col st en, PathC p q L col ∧ IsRun (prI k k (k * k)) L st en ∧ z = runCode k k col L st en ∧
      ((st ≠ 0 ∧ crossSlot k L (st - 1) = sl ∧ IsCross k L (st - 1)) ∨
        (en + 1 ≠ L.length ∧ crossSlot k L en = sl ∧ IsCross k L en)) := by
  obtain ⟨L, col, st, en, hp, hr, -, rfl⟩ := (hinv.2.1 z).mp hz
  obtain ⟨-, cL, colL⟩ := pathC_facts hS hp
  obtain ⟨l1, l2⟩ := end_lt32 hk hk colL cL hr
  unfold runCode at he
  rw [hasEnd_mkP l1 l2] at he
  refine ⟨L, col, st, en, hp, hr, rfl, ?_⟩
  have T : ∀ c, termE k k c = k + 2 * k + 1 + c := fun c => rfl
  have xs := exitE_lt_term hsl
  rcases he with e | e
  · rcases endL_cases cL hr col with ⟨-, d⟩ | ⟨h0, -, -⟩
    · rw [d, T] at e; omega
    obtain ⟨cr, -, d⟩ := runL_cross cL hr h0 col
    rw [d] at e; unfold exitE at e
    exact Or.inl ⟨h0, by omega, cr⟩
  · rcases endR_cases cL hr col with ⟨-, d⟩ | ⟨h0, -, -⟩
    · rw [d, T] at e; omega
    obtain ⟨cr, -, d⟩ := runR_cross cL hr h0 col
    rw [d] at e; unfold exitE at e
    exact Or.inr ⟨h0, by omega, cr⟩

/-- **The used slots are the slots of the crossings.** -/
theorem used_iff (hk : k ≤ 8) (hS : IsSolution J p q) (hinv : Inv k k (k * k) p q s) (sl : ℕ) :
    sl ∈ usedOf k k s ↔ ∃ L col j, PathC p q L col ∧ IsCross k L j ∧ crossSlot k L j = sl := by
  unfold usedOf
  rw [List.mem_filter, List.mem_range, List.any_eq_true]
  constructor
  · rintro ⟨hsl, z, hz, he⟩
    obtain ⟨L, col, st, en, hp, -, -, h | h⟩ := piece_exit hk hS hinv hz (by omega) he
    · exact ⟨L, col, _, hp, h.2.2, h.2.1⟩
    · exact ⟨L, col, _, hp, h.2.2, h.2.1⟩
  · rintro ⟨L, col, j, hp, hc, rfl⟩
    obtain ⟨-, cL, -⟩ := pathC_facts hS hp
    refine ⟨by have := crossSlot_lt cL hc; omega, ?_⟩
    have hj := hc.1
    rcases cross_run hc with ⟨hw, st, hr⟩ | ⟨hw, en, hr⟩
    · obtain ⟨-, -, d⟩ := runR_cross cL hr (by omega) col
      refine ⟨_, (hinv.2.1 _).mpr ⟨L, col, st, j, hp, hr, fun c => by omega, rfl⟩, ?_⟩
      obtain ⟨l1, l2⟩ := end_lt32 hk hk (pathC_facts hS hp).2.2 cL hr
      unfold runCode; rw [hasEnd_mkP l1 l2]; exact Or.inr d
    · obtain ⟨-, -, d⟩ := runL_cross cL hr (by omega) col
      refine ⟨_, (hinv.2.1 _).mpr ⟨L, col, j + 1, en, hp, hr, fun c => by omega, rfl⟩, ?_⟩
      obtain ⟨l1, l2⟩ := end_lt32 hk hk (pathC_facts hS hp).2.2 cL hr
      unfold runCode; rw [hasEnd_mkP l1 l2]
      left; simpa using d

/-- **The piece at a crossing**: unique, and its other end is the far end of the window run. -/
theorem cross_piece (hk : k ≤ 8) (hS : IsSolution J p q) (hinv : Inv k k (k * k) p q s)
    {L : List Coord} {col j : ℕ} (hp : PathC p q L col) (hc : IsCross k L j) :
    ∃ z, z ∈ s.1 ∧ hasEnd (exitE k (crossSlot k L j)) z = true ∧
      (∀ z' ∈ s.1, hasEnd (exitE k (crossSlot k L j)) z' = true → z' = z) ∧
      ((inWb k (nth L j) = true ∧ ∃ st, IsRun (prI k k (k * k)) L st j ∧
          other (exitE k (crossSlot k L j)) z = endL k k col L st) ∨
        (inWb k (nth L j) = false ∧ ∃ en, IsRun (prI k k (k * k)) L (j + 1) en ∧
          other (exitE k (crossSlot k L j)) z = endR k k col L en)) := by
  obtain ⟨-, cL, colL⟩ := pathC_facts hS hp
  have hj := hc.1
  have hsl := crossSlot_lt cL hc
  -- any piece with this exit end is the run at this crossing
  have uniq : ∀ z' ∈ s.1, hasEnd (exitE k (crossSlot k L j)) z' = true →
      ∃ st en, IsRun (prI k k (k * k)) L st en ∧ z' = runCode k k col L st en ∧
        ((st ≠ 0 ∧ st - 1 = j) ∨ (en + 1 ≠ L.length ∧ en = j)) := by
    intro z' hz' he
    obtain ⟨L', col', st', en', hp', hr', rfl, h | h⟩ := piece_exit hk hS hinv hz' hsl he
    · obtain ⟨rfl, rfl, e⟩ := cross_unique hS hp' hp h.2.2 hc h.2.1
      exact ⟨st', en', hr', rfl, Or.inl ⟨h.1, e⟩⟩
    · obtain ⟨rfl, rfl, e⟩ := cross_unique hS hp' hp h.2.2 hc h.2.1
      exact ⟨st', en', hr', rfl, Or.inr ⟨h.1, e⟩⟩
  rcases cross_run hc with ⟨hw, st, hr⟩ | ⟨hw, en, hr⟩
  · obtain ⟨l1, l2⟩ := end_lt32 hk hk colL cL hr
    obtain ⟨-, -, d⟩ := runR_cross cL hr (by omega) col
    refine ⟨runCode k k col L st j, (hinv.2.1 _).mpr ⟨L, col, st, j, hp, hr, fun c => by omega, rfl⟩,
      by unfold runCode; rw [hasEnd_mkP l1 l2]; exact Or.inr d, fun z' hz' he => ?_,
      Or.inl ⟨hw, st, hr, by unfold runCode; rw [← d]; exact other_mkP_r l1 l2⟩⟩
    obtain ⟨st', en', hr', rfl, h | h⟩ := uniq z' hz' he
    · exfalso
      have := hr'.all (j + 1) (by omega) (by have := hr'.le; omega)
      rw [prI_all'] at this
      exact hc.2 (by rw [hw, this])
    · obtain ⟨e1, -⟩ := run_unique hr' hr (by have := hr'.le; omega) (by omega) hr.le (le_refl _)
      rw [e1, h.2]
  · obtain ⟨l1, l2⟩ := end_lt32 hk hk colL cL hr
    obtain ⟨-, -, d⟩ := runL_cross cL hr (by omega) col
    simp only [Nat.add_sub_cancel] at d
    refine ⟨runCode k k col L (j + 1) en, (hinv.2.1 _).mpr ⟨L, col, j + 1, en, hp, hr, fun c => by omega, rfl⟩,
      by unfold runCode; rw [hasEnd_mkP l1 l2]; exact Or.inl d, fun z' hz' he => ?_,
      Or.inr ⟨hw, en, hr, by unfold runCode; rw [← d]; exact other_mkP_l l1 l2⟩⟩
    obtain ⟨st', en', hr', rfl, h | h⟩ := uniq z' hz' he
    · obtain ⟨-, e2⟩ := run_unique hr' hr (by omega) (by have := hr'.le; omega) (le_refl _) hr.le
      rw [e2, show st' = j + 1 by omega]
    · exfalso
      have := hr'.all j (by have := hr'.le; omega) (by omega)
      rw [prI_all'] at this
      rw [this] at hw; exact absurd hw (by simp)

/-- The node of an inside-link end: an exit's node, or a terminal code. -/
def endNode (k : ℕ) (F : FSpec) (s : St) (v : ℕ) : ℕ :=
  if isExit k k v then (usedOf k k s).idxOf (v - (k + 1)) else mOf k k F s + colE k k v

/-- **The inside link of a crossing's node.** -/
theorem linkOf_cross (hk : k ≤ 8) (hS : IsSolution J p q) (hinv : Inv k k (k * k) p q s) {F : FSpec}
    {L : List Coord} {col j : ℕ} (hp : PathC p q L col) (hc : IsCross k L j) :
    ∃ v, linkOf k k F s ((usedOf k k s).idxOf (crossSlot k L j)) = some (endNode k F s v) ∧
      ((inWb k (nth L j) = true ∧ ∃ st, IsRun (prI k k (k * k)) L st j ∧ v = endL k k col L st) ∨
        (inWb k (nth L j) = false ∧ ∃ en, IsRun (prI k k (k * k)) L (j + 1) en ∧ v = endR k k col L en)) := by
  obtain ⟨-, cL, colL⟩ := pathC_facts hS hp
  obtain ⟨z, hz, he, hu, hv⟩ := cross_piece hk hS hinv hp hc
  have mem : crossSlot k L j ∈ usedOf k k s := (used_iff hk hS hinv _).mpr ⟨L, col, j, hp, hc, rfl⟩
  have lt := List.idxOf_lt_length_iff.mpr mem
  have gd : (usedOf k k s).getD ((usedOf k k s).idxOf (crossSlot k L j)) 0 = crossSlot k L j := by
    rw [List.getD_eq_getElem _ _ lt]; exact List.getElem_idxOf lt
  have fz : s.1.find? (hasEnd (exitE k (crossSlot k L j))) = some z := find_unique hz he hu
  refine ⟨other (exitE k (crossSlot k L j)) z, ?_, ?_⟩
  · unfold linkOf
    rw [ite_eq_left lt, gd, fz]
    dsimp only
    unfold endNode
    -- the far end is an exit or a terminal
    have ft : isExit k k (other (exitE k (crossSlot k L j)) z) = true ∨
        isTerm k k (other (exitE k (crossSlot k L j)) z) = true := by
      rcases hv with ⟨-, st, hr, e⟩ | ⟨-, en, hr, e⟩
      · rw [e]
        rcases endL_cases cL hr col with ⟨-, d⟩ | ⟨h0, -, -⟩
        · right; rw [d]; unfold isTerm termE; simp
        · obtain ⟨cr, -, d⟩ := runL_cross cL hr h0 col
          left; rw [d]; have := crossSlot_lt cL cr; unfold isExit exitE; simp; omega
      · rw [e]
        rcases endR_cases cL hr col with ⟨-, d⟩ | ⟨h0, -, -⟩
        · right; rw [d]; unfold isTerm termE; simp
        · obtain ⟨cr, -, d⟩ := runR_cross cL hr h0 col
          left; rw [d]; have := crossSlot_lt cL cr; unfold isExit exitE; simp; omega
    split_ifs with h1 h2
    · rfl
    · rfl
    · exfalso; rcases ft with f | f <;> simp_all
  · rcases hv with ⟨hw, st, hr, e⟩ | ⟨hw, en, hr, e⟩
    · exact Or.inl ⟨hw, st, hr, e⟩
    · exact Or.inr ⟨hw, en, hr, e⟩

end Used

/-! ### The crossing list of a path -/

section CI

variable {k : ℕ} {L : List Coord}

/-- The crossings of `L`, in order. -/
def CI (k : ℕ) (L : List Coord) : List ℕ :=
  (List.range (L.length - 1)).filter fun j => inWb k (nth L j) != inWb k (nth L (j + 1))

theorem mem_CI {j : ℕ} : j ∈ CI k L ↔ IsCross k L j := by
  unfold CI IsCross
  rw [List.mem_filter, List.mem_range]
  simp only [bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

theorem CI_sorted : (CI k L).Pairwise (· < ·) := List.pairwise_lt_range.filter _

/-- The status is constant along a stretch without crossings. -/
theorem status_const {a : ℕ} : ∀ b, a ≤ b → b < L.length → (∀ j, a ≤ j → j < b → ¬ IsCross k L j) →
    inWb k (nth L b) = inWb k (nth L a)
  | 0, hab, _, _ => by rw [show a = 0 by omega]
  | b + 1, hab, hb, h => by
    rcases Nat.eq_or_lt_of_le hab with e | e
    · rw [e]
    · have ih := status_const b (by omega) (by omega) (fun j h1 h2 => h j h1 (by omega))
      have nc := h b (by omega) (by omega)
      unfold IsCross at nc
      push Not at nc
      rw [← ih, nc (by omega)]

theorem CI_get_lt {i i' : ℕ} (hi' : i' < (CI k L).length) (h : i < i') :
    (CI k L).getD i 0 < (CI k L).getD i' 0 := by
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi']
  exact List.pairwise_iff_getElem.mp CI_sorted i i' (by omega) hi' h

theorem CI_mem {i : ℕ} (hi : i < (CI k L).length) : IsCross k L ((CI k L).getD i 0) := by
  rw [← mem_CI, List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _

/-- No crossing between consecutive crossings. -/
theorem CI_gap {i j : ℕ} (hi : i + 1 < (CI k L).length) (h1 : (CI k L).getD i 0 < j)
    (h2 : j < (CI k L).getD (i + 1) 0) : ¬ IsCross k L j := by
  intro hc
  obtain ⟨t, ht, e⟩ := List.getElem_of_mem (mem_CI.mpr hc)
  rw [← List.getD_eq_getElem _ 0 ht] at e
  rcases Nat.lt_trichotomy t i with c | c | c
  · have := CI_get_lt (k := k) (L := L) (i' := i) (by omega) c; omega
  · subst c; omega
  · rcases Nat.lt_or_ge (i + 1) t with d | d
    · have := CI_get_lt ht d; omega
    · have : t = i + 1 := by omega
      subst this; omega

theorem CI_before {j : ℕ} (_hne : 0 < (CI k L).length) (h : j < (CI k L).getD 0 0) : ¬ IsCross k L j := by
  intro hc
  obtain ⟨t, ht, e⟩ := List.getElem_of_mem (mem_CI.mpr hc)
  rw [← List.getD_eq_getElem _ 0 ht] at e
  rcases Nat.eq_zero_or_pos t with c | c
  · subst c; omega
  · have := CI_get_lt ht c; omega

theorem CI_after {j : ℕ} (hne : 0 < (CI k L).length) (h : (CI k L).getD ((CI k L).length - 1) 0 < j) :
    ¬ IsCross k L j := by
  intro hc
  obtain ⟨t, ht, e⟩ := List.getElem_of_mem (mem_CI.mpr hc)
  rw [← List.getD_eq_getElem _ 0 ht] at e
  rcases Nat.lt_or_ge t ((CI k L).length - 1) with c | c
  · have := CI_get_lt (k := k) (L := L) (i' := (CI k L).length - 1) (by omega) c; omega
  · rw [show t = (CI k L).length - 1 by omega] at e; omega

theorem CI_none (hne : (CI k L).length = 0) (j : ℕ) : ¬ IsCross k L j := by
  intro hc; have := mem_CI.mpr hc; rw [List.length_eq_zero_iff] at hne; rw [hne] at this; simp at this

/-- The status just after the `i`-th crossing alternates. -/
theorem status_after {i : ℕ} (hi : i < (CI k L).length) (_hL : 0 < L.length) :
    inWb k (nth L ((CI k L).getD i 0 + 1)) = (if i % 2 = 0 then !inWb k (nth L 0) else inWb k (nth L 0)) := by
  induction i with
  | zero =>
    have hc := CI_mem (L := L) hi
    have e := status_const (L := L) (a := 0) _ (Nat.zero_le _) (by have := hc.1; omega)
      (fun j _ hj => CI_before (k := k) (L := L) (by omega) hj)
    have := hc.2
    simp only [Nat.zero_mod, ↓reduceIte]
    rw [← e]
    cases h1 : inWb k (nth L ((CI k L).getD 0 0)) <;> cases h2 : inWb k (nth L ((CI k L).getD 0 0 + 1)) <;>
      simp_all
  | succ i ih =>
    have ih' := ih (by omega)
    have hc := CI_mem (L := L) hi
    have lt := CI_get_lt (L := L) hi (Nat.lt_succ_self i)
    have e := status_const (L := L) (a := (CI k L).getD i 0 + 1) _ (by omega) (by have := hc.1; omega)
      (fun j h1 h2 => CI_gap hi (by omega) h2)
    have := hc.2
    rw [← e] at ih'
    have hm : (i + 1) % 2 = 0 ↔ ¬ i % 2 = 0 := by omega
    by_cases h0 : i % 2 = 0
    · rw [ite_eq_left h0] at ih'; rw [ite_eq_right (by omega)]
      cases h1 : inWb k (nth L ((CI k L).getD (i + 1) 0)) <;> cases h2 : inWb k (nth L ((CI k L).getD (i + 1) 0 + 1)) <;>
        cases h3 : inWb k (nth L 0) <;> simp_all
    · rw [ite_eq_right h0] at ih'; rw [ite_eq_left (by omega)]
      cases h1 : inWb k (nth L ((CI k L).getD (i + 1) 0)) <;> cases h2 : inWb k (nth L ((CI k L).getD (i + 1) 0 + 1)) <;>
        cases h3 : inWb k (nth L 0) <;> simp_all

end CI

/-! ### The node chain of a path -/

/-- The outside ends along `L`: F where the path ends outside, and its crossings in order. -/
def chainOf (k : ℕ) (s : St) (L : List Coord) : List ℕ :=
  (if inWb k (nth L 0) then [] else [(usedOf k k s).length]) ++
    (CI k L).map (fun j => (usedOf k k s).idxOf (crossSlot k L j)) ++
    (if inWb k (nth L (L.length - 1)) then [] else [(usedOf k k s).length])

section Chain

variable {k : ℕ} {s : St} {L : List Coord}

def offL (k : ℕ) (L : List Coord) : ℕ := if inWb k (nth L 0) then 0 else 1
def offR (k : ℕ) (L : List Coord) : ℕ := if inWb k (nth L (L.length - 1)) then 0 else 1

theorem getD_mid {P M Q : List ℕ} {i : ℕ} (hi : i < M.length) :
    (P ++ M ++ Q).getD (P.length + i) 0 = M.getD i 0 := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi]
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
  congr 1; omega

theorem getD_lastApp {X : List ℕ} {a : ℕ} : (X ++ [a]).getD X.length 0 = a := by
  rw [List.getD_eq_getElem _ _ (by simp)]; simp

theorem pre_len : (if inWb k (nth L 0) then ([] : List ℕ) else [(usedOf k k s).length]).length = offL k L := by
  unfold offL; split_ifs <;> rfl

theorem chainOf_length : (chainOf k s L).length = offL k L + (CI k L).length + offR k L := by
  unfold chainOf offL offR; split_ifs <;> simp <;> omega

theorem chainOf_mid {i : ℕ} (hi : i < (CI k L).length) :
    (chainOf k s L).getD (offL k L + i) 0 = (usedOf k k s).idxOf (crossSlot k L ((CI k L).getD i 0)) := by
  unfold chainOf
  rw [← pre_len (s := s), getD_mid (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
    List.getElem_map, List.getD_eq_getElem _ _ hi]

theorem chainOf_first (h : offL k L = 1) : (chainOf k s L).getD 0 0 = (usedOf k k s).length := by
  have h0 : ¬ inWb k (nth L 0) = true := by intro e; simp [offL, e] at h
  simp [chainOf, h0]

theorem chainOf_last (h : offR k L = 1) :
    (chainOf k s L).getD ((chainOf k s L).length - 1) 0 = (usedOf k k s).length := by
  have h0 : ¬ inWb k (nth L (L.length - 1)) = true := by intro e; simp [offR, e] at h
  have e : chainOf k s L = ((if inWb k (nth L 0) then ([] : List ℕ) else [(usedOf k k s).length]) ++
      (CI k L).map (fun j => (usedOf k k s).idxOf (crossSlot k L j))) ++ [(usedOf k k s).length] := by
    unfold chainOf; rw [ite_eq_right h0]
  rw [e, List.length_append, List.length_singleton, Nat.add_sub_cancel]
  exact getD_lastApp

/-- The status at the end of the path. -/
theorem status_end (hL : 0 < L.length) :
    inWb k (nth L (L.length - 1)) =
      (if (CI k L).length = 0 then inWb k (nth L 0)
       else if ((CI k L).length - 1) % 2 = 0 then !inWb k (nth L 0) else inWb k (nth L 0)) := by
  by_cases h0 : (CI k L).length = 0
  · rw [ite_eq_left h0]
    exact status_const (L := L) (a := 0) _ (Nat.zero_le _) (by omega) (fun j _ _ => CI_none h0 j)
  · rw [ite_eq_right h0]
    have hi : (CI k L).length - 1 < (CI k L).length := by omega
    have hc := CI_mem (L := L) hi
    rw [← status_after hi hL]
    exact status_const (L := L) (a := (CI k L).getD ((CI k L).length - 1) 0 + 1) _ (by have := hc.1; omega)
      (by omega) (fun j h1 h2 => CI_after (by omega) (by omega))

theorem chainOf_even (hL : 0 < L.length) : (chainOf k s L).length % 2 = 0 := by
  rw [chainOf_length]
  have e := status_end (k := k) hL
  unfold offL offR
  rw [e]
  by_cases h0 : (CI k L).length = 0
  · rw [ite_eq_left h0, h0]; split_ifs <;> omega
  · rw [ite_eq_right h0]
    by_cases hp : ((CI k L).length - 1) % 2 = 0
    · rw [ite_eq_left hp]; cases hb : inWb k (nth L 0) <;> simp <;> omega
    · rw [ite_eq_right hp]; cases hb : inWb k (nth L 0) <;> simp <;> omega

end Chain

/-! ### Links along a chain -/

section Links

variable {k : ℕ} {J : Inst} {p q : List Coord} {s : St}

theorem endNode_exit {F : FSpec} {x : ℕ} (hx : x < 2 * k) :
    endNode k F s (exitE k x) = (usedOf k k s).idxOf x := by
  unfold endNode isExit exitE; rw [ite_eq_left (by simp; omega)]; congr 1; omega

theorem endNode_term {F : FSpec} {col : ℕ} : endNode k F s (termE k k col) = mOf k k F s + col := by
  unfold endNode isExit termE colE; rw [ite_eq_right (by simp; omega)]; congr 1; omega

/-- The window run between consecutive crossings, entering then leaving. -/
theorem run_between {L : List Coord} (_hL : 0 < L.length) {i : ℕ} (hi : i + 1 < (CI k L).length)
    (hw : inWb k (nth L ((CI k L).getD i 0 + 1)) = true) :
    IsRun (prI k k (k * k)) L ((CI k L).getD i 0 + 1) ((CI k L).getD (i + 1) 0) := by
  have c0 := CI_mem (k := k) (L := L) (i := i) (by omega)
  have c1 := CI_mem (k := k) (L := L) hi
  have lt := CI_get_lt (k := k) (L := L) hi (Nat.lt_succ_self i)
  have const : ∀ j, (CI k L).getD i 0 + 1 ≤ j → j ≤ (CI k L).getD (i + 1) 0 →
      inWb k (nth L j) = true := fun j h1 h2 => by
    rw [status_const (L := L) (a := (CI k L).getD i 0 + 1) j h1 (by have := c1.1; omega)
      (fun j' a b => CI_gap hi (by omega) (by omega))]
    exact hw
  refine ⟨by omega, by have := c1.1; omega, fun j h1 h2 => prI_all'.mpr (const j h1 h2), ?_, ?_⟩
  · right; rw [prI_all', Nat.add_sub_cancel]
    have := c0.2; rw [hw] at this; simpa using this
  · right; rw [prI_all']
    have := c1.2; rw [const _ (by omega) (le_refl _)] at this; simpa using this

theorem run_first {L : List Coord} (hne : 0 < (CI k L).length) (hw : inWb k (nth L 0) = true) :
    IsRun (prI k k (k * k)) L 0 ((CI k L).getD 0 0) := by
  have c0 := CI_mem (k := k) (L := L) hne
  have const : ∀ j, j ≤ (CI k L).getD 0 0 → inWb k (nth L j) = true := fun j h => by
    rw [status_const (L := L) (a := 0) j (Nat.zero_le _) (by have := c0.1; omega)
      (fun j' _ b => CI_before hne (by omega))]
    exact hw
  refine ⟨Nat.zero_le _, by have := c0.1; omega, fun j _ h2 => prI_all'.mpr (const j h2), Or.inl rfl, ?_⟩
  right; rw [prI_all']
  have := c0.2; rw [const _ (le_refl _)] at this; simpa using this

theorem run_last {L : List Coord} (hne : 0 < (CI k L).length)
    (hw : inWb k (nth L ((CI k L).getD ((CI k L).length - 1) 0 + 1)) = true) :
    IsRun (prI k k (k * k)) L ((CI k L).getD ((CI k L).length - 1) 0 + 1) (L.length - 1) := by
  have c0 := CI_mem (k := k) (L := L) (i := (CI k L).length - 1) (by omega)
  have const : ∀ j, (CI k L).getD ((CI k L).length - 1) 0 + 1 ≤ j → j < L.length →
      inWb k (nth L j) = true := fun j h1 h2 => by
    rw [status_const (L := L) (a := (CI k L).getD ((CI k L).length - 1) 0 + 1) j h1 h2
      (fun j' a b => CI_after hne (by omega))]
    exact hw
  refine ⟨by have := c0.1; omega, by have := c0.1; omega, fun j h1 h2 => prI_all'.mpr (const j h1 (by omega)),
    ?_, Or.inl (by have := c0.1; omega)⟩
  right; rw [prI_all', Nat.add_sub_cancel]
  have := c0.2; rw [hw] at this; simpa using this

/-- **The link at an entering crossing**: to the next crossing, or a terminal at the path's end. -/
theorem link_enter (hk : k ≤ 8) (hS : IsSolution J p q) (hinv : Inv k k (k * k) p q s) {F : FSpec}
    {L : List Coord} {col : ℕ} (hp : PathC p q L col) {i : ℕ} (hi : i < (CI k L).length)
    (hw : inWb k (nth L ((CI k L).getD i 0 + 1)) = true) :
    linkOf k k F s ((usedOf k k s).idxOf (crossSlot k L ((CI k L).getD i 0))) =
      some (if i + 1 < (CI k L).length then (usedOf k k s).idxOf (crossSlot k L ((CI k L).getD (i + 1) 0))
        else mOf k k F s + col) := by
  obtain ⟨-, cL, -⟩ := pathC_facts hS hp
  have hc := CI_mem (k := k) (L := L) hi
  have hL : 0 < L.length := by have := hc.1; omega
  obtain ⟨v, hv, h | h⟩ := linkOf_cross (F := F) hk hS hinv hp hc
  · exfalso; have := hc.2; rw [h.1, hw] at this; exact this rfl
  obtain ⟨-, en, hr, rfl⟩ := h
  rw [hv]
  congr 1
  split_ifs with hn
  · obtain ⟨-, e⟩ := run_unique hr (run_between hL hn hw) (le_refl _) hr.le (le_refl _)
      (by have := CI_get_lt (k := k) (L := L) hn (Nat.lt_succ_self i); omega)
    subst e
    have c1 := CI_mem (k := k) (L := L) hn
    obtain ⟨cr, -, d⟩ := runR_cross cL hr (by have := c1.1; omega) col
    rw [d, endNode_exit (crossSlot_lt cL cr)]
  · have hl : i = (CI k L).length - 1 := by omega
    have hw' := hw; rw [hl] at hw'
    obtain ⟨-, e⟩ := run_unique hr (by rw [hl]; exact run_last (by omega) hw') (le_refl _) hr.le
      (le_refl _) (by have := hc.1; omega)
    rw [e]
    unfold endR; rw [ite_eq_left (by omega)]
    exact endNode_term

/-- **The link at a leaving crossing**: to the previous crossing, or a terminal at the path's
start. -/
theorem link_leave (hk : k ≤ 8) (hS : IsSolution J p q) (hinv : Inv k k (k * k) p q s) {F : FSpec}
    {L : List Coord} {col : ℕ} (hp : PathC p q L col) {i : ℕ} (hi : i < (CI k L).length)
    (hw : inWb k (nth L ((CI k L).getD i 0)) = true) :
    linkOf k k F s ((usedOf k k s).idxOf (crossSlot k L ((CI k L).getD i 0))) =
      some (if 0 < i then (usedOf k k s).idxOf (crossSlot k L ((CI k L).getD (i - 1) 0))
        else mOf k k F s + col) := by
  obtain ⟨-, cL, -⟩ := pathC_facts hS hp
  have hc := CI_mem (k := k) (L := L) hi
  have hL : 0 < L.length := by have := hc.1; omega
  obtain ⟨v, hv, h | h⟩ := linkOf_cross (F := F) hk hS hinv hp hc
  swap
  · exfalso; rw [h.1] at hw; exact absurd hw (by simp)
  obtain ⟨-, st, hr, rfl⟩ := h
  rw [hv]
  congr 1
  split_ifs with hn
  · -- the run after the previous crossing
    have hi' : i - 1 + 1 < (CI k L).length := by omega
    have e1 : i - 1 + 1 = i := by omega
    have hw' : inWb k (nth L ((CI k L).getD (i - 1) 0 + 1)) = true := by
      have c0 := CI_mem (k := k) (L := L) (i := i - 1) (by omega)
      have lt := CI_get_lt (k := k) (L := L) hi (show i - 1 < i by omega)
      rw [status_const (L := L) (a := (CI k L).getD (i - 1) 0 + 1) ((CI k L).getD i 0) (by omega)
        (by have := hc.1; omega) (fun j' a b => CI_gap hi' (by omega) (by rw [e1]; omega))] at hw
      exact hw
    have rb := run_between hL hi' hw'
    rw [e1] at rb
    obtain ⟨e, -⟩ := run_unique hr rb hr.le (le_refl _)
      (by have := CI_get_lt (k := k) (L := L) hi (show i - 1 < i by omega); omega) (le_refl _)
    subst e
    have c0 := CI_mem (k := k) (L := L) (i := i - 1) (by omega)
    obtain ⟨cr, -, d⟩ := runL_cross cL hr (by omega) col
    rw [d, Nat.add_sub_cancel, endNode_exit (crossSlot_lt cL c0)]
  · have hz : i = 0 := by omega
    subst hz
    obtain ⟨e, -⟩ := run_unique hr (run_first (by omega) (by
      rw [← status_const (L := L) (a := 0) ((CI k L).getD 0 0) (Nat.zero_le _) (by have := hc.1; omega)
        (fun j' _ b => CI_before (by omega) b)]; exact hw)) hr.le (le_refl _) (Nat.zero_le _) (le_refl _)
    rw [e]
    unfold endL; rw [ite_eq_left rfl]
    exact endNode_term

theorem status_at_cross {L : List Coord} (hL : 0 < L.length) {i : ℕ} (hi : i < (CI k L).length) :
    inWb k (nth L ((CI k L).getD i 0)) = (if i % 2 = 0 then inWb k (nth L 0) else !inWb k (nth L 0)) := by
  have hc := CI_mem (k := k) (L := L) hi
  have := hc.2
  rw [status_after hi hL] at this
  split_ifs at this ⊢ <;> cases h : inWb k (nth L ((CI k L).getD i 0)) <;> cases h' : inWb k (nth L 0) <;> simp_all

/-- **The inside links of a path's chain.** -/
theorem chain_links (hk : k ≤ 8) (hS : IsSolution J p q) (hinv : Inv k k (k * k) p q s) {F : FSpec}
    {L : List Coord} {col : ℕ} (hp : PathC p q L col) (hL : 0 < L.length) {t : ℕ}
    (ht : 2 * t + 2 < (chainOf k s L).length) :
    linkOf k k F s ((chainOf k s L).getD (2 * t + 1) 0) = some ((chainOf k s L).getD (2 * t + 2) 0) ∧
      linkOf k k F s ((chainOf k s L).getD (2 * t + 2) 0) = some ((chainOf k s L).getD (2 * t + 1) 0) := by
  have hlen := chainOf_length (k := k) (s := s) (L := L)
  have hev := chainOf_even (k := k) (s := s) hL
  have e := status_end (k := k) hL
  -- positions 2t+1, 2t+2 are crossings i, i+1
  obtain ⟨i, hi⟩ : ∃ i, 2 * t + 1 = offL k L + i := ⟨2 * t + 1 - offL k L, by unfold offL; split_ifs <;> omega⟩
  have hir : i + 1 < (CI k L).length := by
    unfold offL at hlen hi
    unfold offR at hlen
    rw [e] at hlen
    by_cases h0 : (CI k L).length = 0
    · rw [ite_eq_left h0] at hlen; split_ifs at hlen hi <;> omega
    · rw [ite_eq_right h0] at hlen
      split_ifs at hlen hi <;> omega
  have p1 : (chainOf k s L).getD (2 * t + 1) 0 = (usedOf k k s).idxOf (crossSlot k L ((CI k L).getD i 0)) := by
    rw [hi]; exact chainOf_mid (by omega)
  have p2 : (chainOf k s L).getD (2 * t + 2) 0 = (usedOf k k s).idxOf (crossSlot k L ((CI k L).getD (i + 1) 0)) := by
    rw [show 2 * t + 2 = offL k L + (i + 1) by omega]; exact chainOf_mid hir
  -- the stretch after crossing `i` is inside the window
  have hw : inWb k (nth L ((CI k L).getD i 0 + 1)) = true := by
    rw [status_after (by omega) hL]
    unfold offL at hi
    split_ifs at hi with h0 <;> split_ifs with h1 <;> simp_all <;> omega
  have hw' : inWb k (nth L ((CI k L).getD (i + 1) 0)) = true := by
    have lt := CI_get_lt (k := k) (L := L) hir (Nat.lt_succ_self i)
    have c1 := CI_mem (k := k) (L := L) hir
    rw [status_const (L := L) (a := (CI k L).getD i 0 + 1) _ (by omega) (by have := c1.1; omega)
      (fun j' a b => CI_gap hir (by omega) b)]
    exact hw
  rw [p1, p2]
  refine ⟨?_, ?_⟩
  · rw [link_enter hk hS hinv hp (by omega) hw, ite_eq_left hir]
  · rw [link_leave hk hS hinv hp hir hw', ite_eq_left (by omega), Nat.add_sub_cancel]

/-- **The first and last nodes of a path's chain link to its colour's terminal.** -/
theorem chain_ends (hk : k ≤ 8) (hS : IsSolution J p q) (hinv : Inv k k (k * k) p q s) {F : FSpec}
    {L : List Coord} {col : ℕ} (hp : PathC p q L col) (hL : 0 < L.length)
    (hne : chainOf k s L ≠ [])
    (hFn : offL k L = 1 ∨ offR k L = 1 → linkOf k k F s (usedOf k k s).length = some (mOf k k F s + col)) :
    linkOf k k F s ((chainOf k s L).getD 0 0) = some (mOf k k F s + col) ∧
      linkOf k k F s ((chainOf k s L).getD ((chainOf k s L).length - 1) 0) = some (mOf k k F s + col) := by
  have hlen := chainOf_length (k := k) (s := s) (L := L)
  have e := status_end (k := k) hL
  have hpos : 0 < (chainOf k s L).length := List.length_pos_iff.mpr hne
  constructor
  · by_cases h1 : offL k L = 1
    · rw [chainOf_first h1]; exact hFn (Or.inl h1)
    · have h0 : offL k L = 0 := by unfold offL at h1 ⊢; split_ifs at h1 ⊢ <;> omega
      have hσ : inWb k (nth L 0) = true := by unfold offL at h0; split_ifs at h0 with h; exact h
      have hr : 0 < (CI k L).length := by
        by_contra hz
        have hz' : (CI k L).length = 0 := by omega
        unfold offR at hlen; rw [e, ite_eq_left hz', hσ] at hlen; simp at hlen; omega
      have p0 := chainOf_mid (k := k) (s := s) (L := L) hr
      rw [h0, zero_add] at p0
      rw [p0, link_leave hk hS hinv hp hr (by rw [status_at_cross hL hr]; simp [hσ]), ite_eq_right (by omega)]
  · by_cases h1 : offR k L = 1
    · rw [chainOf_last h1]; exact hFn (Or.inr h1)
    · have h0 : offR k L = 0 := by unfold offR at h1 ⊢; split_ifs at h1 ⊢ <;> omega
      have hσ : inWb k (nth L (L.length - 1)) = true := by unfold offR at h0; split_ifs at h0 with h; exact h
      have hr : 0 < (CI k L).length := by
        by_contra hz
        have hz' : (CI k L).length = 0 := by omega
        rw [e, ite_eq_left hz'] at hσ
        unfold offL at hlen; rw [hσ] at hlen; simp at hlen; omega
      have hl : (chainOf k s L).length - 1 = offL k L + ((CI k L).length - 1) := by omega
      have pl := chainOf_mid (k := k) (s := s) (L := L) (i := (CI k L).length - 1) (by omega)
      rw [← hl] at pl
      have c0 := CI_mem (k := k) (L := L) (i := (CI k L).length - 1) (by omega)
      have hw : inWb k (nth L ((CI k L).getD ((CI k L).length - 1) 0 + 1)) = true := by
        rw [← status_const (L := L) (a := (CI k L).getD ((CI k L).length - 1) 0 + 1) (L.length - 1)
          (by have := c0.1; omega) (by omega) (fun j' a b => CI_after hr (by omega))]
        exact hσ
      rw [pl, link_enter hk hS hinv hp (by omega) hw, ite_eq_right (by omega)]

end Links

end ZZN.Win

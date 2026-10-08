-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Symmetry
import GridHam.StripSplit

/-!
# Gluing pieces of a cut

A path of the left piece (`x < p`) is a path of the whole grid (`IsPath.widen`); a path of the
right piece, in local coordinates, becomes one by translating by `p` (`IsPath.translate`).
`glue_same` puts a Hamiltonian path of each piece of a same-color split together into a
solution.
-/

namespace ZZN

open GridHam

/-- A Hamiltonian path in the sense of `GridHam` is a path covering its rectangle. -/
theorem validPath_isPath {w h : ℕ} {s t : Coord} {L : List Coord} (hv : ValidPath w h s t L) :
    IsPath w h s t L ∧ ∀ v, InBounds w h v → v ∈ L := by
  obtain ⟨-, hh, hl, hn, hb, hc, hch⟩ := hv
  refine ⟨⟨hh, hl, hn, hb, hch⟩, fun v hvb => hc v ?_⟩
  exact (mem_allCoords w h v).mpr hvb

theorem IsPath.widen {w w' h : ℕ} {s t : Coord} {L : List Coord} (hp : IsPath w h s t L)
    (hw : w ≤ w') : IsPath w' h s t L := by
  obtain ⟨hh, hl, hn, hb, hc⟩ := hp
  exact ⟨hh, hl, hn, fun v hv => ⟨by have := (hb v hv).1; omega, (hb v hv).2⟩, hc⟩

/-- Translate by `p` along the first coordinate. -/
def trX (p : ℕ) (v : Coord) : Coord := (v.1 + p, v.2)

theorem trX_injective (p : ℕ) : Function.Injective (trX p) := by
  intro u v h
  simp only [trX, Prod.mk.injEq] at h
  exact Prod.ext (by omega) h.2

theorem chainAdjacent_map_trX (p : ℕ) : ∀ (l : List Coord), chainAdjacent l = true →
    chainAdjacent (l.map (trX p)) = true
  | [] => fun _ => rfl
  | [_] => fun _ => rfl
  | a :: b :: l => by
    intro hc
    rw [chainAdjacent_cons_cons, Bool.and_eq_true] at hc
    simp only [List.map_cons]
    rw [chainAdjacent_cons_cons, Bool.and_eq_true]
    refine ⟨(adjacentB_iff _ _).mpr ?_, by simpa using chainAdjacent_map_trX p (b :: l) hc.2⟩
    have := (adjacentB_iff _ _).mp hc.1
    unfold Adjacent at this ⊢
    simp only [trX]
    omega

theorem IsPath.translate {w h p : ℕ} {s t : Coord} {L : List Coord}
    (hp : IsPath w h s t L) : IsPath (w + p) h (trX p s) (trX p t) (L.map (trX p)) := by
  obtain ⟨hh, hl, hn, hb, hc⟩ := hp
  refine ⟨?_, ?_, hn.map (trX_injective p), ?_, chainAdjacent_map_trX p L hc⟩
  · rw [List.head?_map, hh]; rfl
  · rw [List.getLast?_map, hl]; rfl
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    have := hb u hu
    unfold InBounds at this ⊢
    simp only [trX]
    omega

/-- **Same-color split.** A Hamiltonian path of the left piece for one pair and of the right
piece for the other pair give a solution. -/
theorem glue_same (I : Inst) (p : ℕ) (hp : p < I.w)
    (_hs0 : I.s0.1 < p) (_ht0 : I.t0.1 < p) (hs1 : p ≤ I.s1.1) (ht1 : p ≤ I.t1.1)
    (hA : HasHamPath p I.h I.s0 I.t0)
    (hB : HasHamPath (I.w - p) I.h (I.s1.1 - p, I.s1.2) (I.t1.1 - p, I.t1.2)) :
    Solvable I := by
  obtain ⟨A, hA⟩ := hA
  obtain ⟨B, hB⟩ := hB
  obtain ⟨hApath, hAcov⟩ := validPath_isPath hA
  obtain ⟨hBpath, hBcov⟩ := validPath_isPath hB
  have e1 : trX p (I.s1.1 - p, I.s1.2) = I.s1 := by
    simp only [trX]; exact Prod.ext (by simp; omega) rfl
  have e2 : trX p (I.t1.1 - p, I.t1.2) = I.t1 := by
    simp only [trX]; exact Prod.ext (by simp; omega) rfl
  have hBt := hBpath.translate (p := p)
  rw [e1, e2, show I.w - p + p = I.w by omega] at hBt
  refine ⟨A, B.map (trX p), hApath.widen (by omega), hBt, ?_, ?_⟩
  · intro v hv hv'
    have h1 := (hApath.2.2.2.1 v hv).1
    obtain ⟨u, -, rfl⟩ := List.mem_map.mp hv'
    simp only [trX] at h1
    omega
  · intro v hv
    by_cases hx : v.1 < p
    · exact Or.inl (hAcov v ⟨hx, hv.2⟩)
    · right
      refine List.mem_map.mpr ⟨(v.1 - p, v.2), hBcov _ ⟨by simp; have := hv.1; omega, hv.2⟩, ?_⟩
      simp only [trX]
      exact Prod.ext (by simp; omega) rfl

/-- Swapping the colors. -/
def Inst.swapColors (I : Inst) : Inst := ⟨I.w, I.h, I.s1, I.t1, I.s0, I.t0⟩

theorem solvable_swapColors {I : Inst} (h : Solvable I.swapColors) : Solvable I := by
  obtain ⟨p, q, hp, hq, hd, hc⟩ := h
  exact ⟨q, p, hq, hp, fun v hv hv' => hd v hv' hv, fun v hv => (hc v hv).symm⟩

/-! ### Concatenation and the cut moves -/

/-- Two paths joined by an edge make a path. -/
theorem IsPath.append {w h : ℕ} {s a b t : Coord} {A B : List Coord}
    (hA : IsPath w h s a A) (hB : IsPath w h b t B) (hab : Adjacent a b)
    (hd : ∀ v ∈ A, v ∉ B) : IsPath w h s t (A ++ B) := by
  obtain ⟨hAh, hAl, hAn, hAb, hAc⟩ := hA
  obtain ⟨hBh, hBl, hBn, hBb, hBc⟩ := hB
  obtain ⟨A', rfl⟩ : ∃ A', A = A' ++ [a] := by
    cases A using List.reverseRecOn with
    | nil => simp at hAl
    | append_singleton A' x _ =>
      simp at hAl
      exact ⟨A', by rw [hAl]⟩
  obtain ⟨B', rfl⟩ : ∃ B', B = b :: B' := by
    cases B with
    | nil => simp at hBh
    | cons x B' => simp at hBh; exact ⟨B', by rw [hBh]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases A' with
    | nil => simpa using hAh
    | cons x A' => simpa using hAh
  · simpa using hBl
  · rw [List.nodup_append]
    exact ⟨hAn, hBn, fun x hx y hy hxy => hd x hx (hxy ▸ hy)⟩
  · intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact hAb v h
    · exact hBb v h
  · have e : (A' ++ [a]) ++ b :: B' = A' ++ a :: (b :: B') := by simp
    rw [e, chainAdjacent_append_cons, Bool.and_eq_true, chainAdjacent_cons_cons, Bool.and_eq_true]
    exact ⟨hAc, (adjacentB_iff a b).mpr hab, hBc⟩

/-- The right piece of a cut at `x = p`, in local coordinates. -/
def unX (p : ℕ) (v : Coord) : Coord := (v.1 - p, v.2)

theorem trX_unX {p : ℕ} {v : Coord} (h : p ≤ v.1) : trX p (unX p v) = v := by
  simp only [trX, unX]; exact Prod.ext (by simp; omega) rfl

/-- A solution of the right piece, carried to the whole grid: its paths live in `x ≥ p`. -/
theorem right_piece {I : Inst} {p : ℕ} {J : Inst} (hJw : J.w + p = I.w) (hJh : J.h = I.h)
    {P Q : List Coord} (hs : IsSolution J P Q) :
    IsPath I.w I.h (trX p J.s0) (trX p J.t0) (P.map (trX p)) ∧
    IsPath I.w I.h (trX p J.s1) (trX p J.t1) (Q.map (trX p)) ∧
    (∀ v ∈ P.map (trX p), v ∉ Q.map (trX p)) ∧
    (∀ v ∈ P.map (trX p) ++ Q.map (trX p), p ≤ v.1) ∧
    (∀ v, InBounds I.w I.h v → p ≤ v.1 → v ∈ P.map (trX p) ∨ v ∈ Q.map (trX p)) := by
  obtain ⟨hP, hQ, hd, hc⟩ := hs
  have tP := hP.translate (p := p)
  have tQ := hQ.translate (p := p)
  rw [hJw, hJh] at tP tQ
  refine ⟨tP, tQ, ?_, ?_, ?_⟩
  · intro v hv hv'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    obtain ⟨u', hu', he⟩ := List.mem_map.mp hv'
    exact hd u hu (trX_injective p he ▸ hu')
  · intro v hv
    rcases List.mem_append.mp hv with h | h <;>
    · obtain ⟨u, -, rfl⟩ := List.mem_map.mp h
      simp [trX]
  · intro v hv hpv
    have hb : InBounds J.w J.h (unX p v) := by
      unfold InBounds at hv ⊢; simp only [unX]; omega
    rcases hc _ hb with h | h
    · exact Or.inl (List.mem_map.mpr ⟨_, h, trX_unX hpv⟩)
    · exact Or.inr (List.mem_map.mpr ⟨_, h, trX_unX hpv⟩)

/-- A solution of the left piece is a pair of paths of the whole grid in `x < p`. -/
theorem left_piece {I : Inst} {p : ℕ} {J : Inst} (hJw : J.w = p) (hp : p ≤ I.w)
    (hJh : J.h = I.h) {P Q : List Coord} (hs : IsSolution J P Q) :
    IsPath I.w I.h J.s0 J.t0 P ∧ IsPath I.w I.h J.s1 J.t1 Q ∧ (∀ v ∈ P, v ∉ Q) ∧
    (∀ v ∈ P ++ Q, v.1 < p) ∧ (∀ v, InBounds I.w I.h v → v.1 < p → v ∈ P ∨ v ∈ Q) := by
  obtain ⟨hP, hQ, hd, hc⟩ := hs
  have wP := hP.widen (w' := I.w) (by omega)
  have wQ := hQ.widen (w' := I.w) (by omega)
  rw [hJh] at wP wQ
  refine ⟨wP, wQ, hd, ?_, ?_⟩
  · intro v hv
    rcases List.mem_append.mp hv with h | h
    · have := (hP.2.2.2.1 v h).1; omega
    · have := (hQ.2.2.2.1 v h).1; omega
  · intro v hv hvp
    exact hc v ⟨by omega, by rw [hJh]; exact hv.2⟩

/-- **2/2 cross cut.** Left piece: `s0 → (p-1, y0)` and `s1 → (p-1, y1)`. Right piece (local
coordinates): `(0, y0) → t0` and `(0, y1) → t1`. Solutions of both give a solution of `I`. -/
theorem glue_cross (I : Inst) (p y0 y1 : ℕ) (hp0 : 0 < p) (hp : p < I.w)
    (hL : Solvable ⟨p, I.h, I.s0, (p - 1, y0), I.s1, (p - 1, y1)⟩)
    (hR : Solvable ⟨I.w - p, I.h, (0, y0), unX p I.t0, (0, y1), unX p I.t1⟩)
    (ht0 : p ≤ I.t0.1) (ht1 : p ≤ I.t1.1) : Solvable I := by
  obtain ⟨PL, QL, sL⟩ := hL
  obtain ⟨PR, QR, sR⟩ := hR
  obtain ⟨aP, aQ, aD, aX, aC⟩ := left_piece (I := I) (J := ⟨p, I.h, I.s0, (p - 1, y0), I.s1, (p - 1, y1)⟩) (p := p) rfl hp.le rfl sL
  obtain ⟨bP, bQ, bD, bX, bC⟩ := right_piece (I := I) (J := ⟨I.w - p, I.h, (0, y0), unX p I.t0, (0, y1), unX p I.t1⟩) (p := p) (show I.w - p + p = I.w by omega) rfl sR
  have e0 : trX p (0, y0) = (p, y0) := by simp [trX]
  have e1 : trX p (0, y1) = (p, y1) := by simp [trX]
  dsimp only at bP bQ aP aQ
  rw [e0, trX_unX ht0] at bP
  rw [e1, trX_unX ht1] at bQ
  have sep : ∀ v ∈ PL ++ QL, ∀ u ∈ PR.map (trX p) ++ QR.map (trX p), v ≠ u := by
    intro v hv u hu he
    have := aX v hv; have := bX u hu; rw [he] at *; omega
  have adj : ∀ y, Adjacent (p - 1, y) (p, y) := fun y => by unfold Adjacent; omega
  refine ⟨PL ++ PR.map (trX p), QL ++ QR.map (trX p),
    aP.append bP (adj y0) (fun v hv hv' => sep v (by simp [hv]) v (by simp [hv']) rfl),
    aQ.append bQ (adj y1) (fun v hv hv' => sep v (by simp [hv]) v (by simp [hv']) rfl), ?_, ?_⟩
  · intro v hv hv'
    rcases List.mem_append.mp hv with h | h <;> rcases List.mem_append.mp hv' with h' | h'
    · exact aD v h h'
    · exact sep v (by simp [h]) v (by simp [h']) rfl
    · exact sep v (by simp [h']) v (by simp [h]) rfl
    · exact bD v h h'
  · intro v hv
    by_cases hx : v.1 < p
    · rcases aC v hv hx with h | h
      · exact Or.inl (List.mem_append_left _ h)
      · exact Or.inr (List.mem_append_left _ h)
    · rcases bC v hv (by omega) with h | h
      · exact Or.inl (List.mem_append_right _ h)
      · exact Or.inr (List.mem_append_right _ h)

/-- **1/3 cut.** The lone endpoint `s0` is left of `x = p`, with a Hamiltonian path of the left
piece to `(p-1, y)`. The right piece (local coordinates) has `(0, y) → t0` and `s1 → t1`. -/
theorem glue_13 (I : Inst) (p y : ℕ) (hp0 : 0 < p) (hp : p < I.w)
    (hA : HasHamPath p I.h I.s0 (p - 1, y))
    (hR : Solvable ⟨I.w - p, I.h, (0, y), unX p I.t0, unX p I.s1, unX p I.t1⟩)
    (ht0 : p ≤ I.t0.1) (hs1 : p ≤ I.s1.1) (ht1 : p ≤ I.t1.1) : Solvable I := by
  obtain ⟨A, hA⟩ := hA
  obtain ⟨hApath, hAcov⟩ := validPath_isPath hA
  have aP := hApath.widen (w' := I.w) hp.le
  obtain ⟨PR, QR, sR⟩ := hR
  obtain ⟨bP, bQ, bD, bX, bC⟩ := right_piece (I := I)
    (J := ⟨I.w - p, I.h, (0, y), unX p I.t0, unX p I.s1, unX p I.t1⟩) (p := p)
    (show I.w - p + p = I.w by omega) rfl sR
  have e0 : trX p (0, y) = (p, y) := by simp [trX]
  dsimp only at bP bQ
  rw [e0, trX_unX ht0] at bP
  rw [trX_unX hs1, trX_unX ht1] at bQ
  have aX : ∀ v ∈ A, v.1 < p := fun v hv => (hApath.2.2.2.1 v hv).1
  have sepA : ∀ v ∈ A, ∀ u ∈ PR.map (trX p) ++ QR.map (trX p), v ≠ u := by
    intro v hv u hu he
    have := aX v hv; have := bX u hu; rw [he] at *; omega
  have adj : Adjacent (p - 1, y) (p, y) := by unfold Adjacent; omega
  refine ⟨A ++ PR.map (trX p), QR.map (trX p),
    aP.append bP adj (fun v hv hv' => sepA v hv v (by simp [hv']) rfl), bQ, ?_, ?_⟩
  · intro v hv hv'
    rcases List.mem_append.mp hv with h | h
    · exact sepA v h v (by simp [hv']) rfl
    · exact bD v h hv'
  · intro v hv
    by_cases hx : v.1 < p
    · exact Or.inl (List.mem_append_left _ (hAcov v ⟨hx, hv.2⟩))
    · rcases bC v hv (by omega) with h | h
      · exact Or.inl (List.mem_append_right _ h)
      · exact Or.inr h

/-- **Excursion.** Color 0 has both endpoints left of `x = p` and makes one excursion to the
right, crossing at rows `ya` (out) and `yb` (back). Near piece: `s0 → (p-1, ya)` and
`(p-1, yb) → t0`. Far piece (local coordinates): `s1 → t1` and the excursion
`(0, ya) → (0, yb)`. -/
theorem glue_exc (I : Inst) (p ya yb : ℕ) (hp0 : 0 < p) (hp : p < I.w)
    (hN : Solvable ⟨p, I.h, I.s0, (p - 1, ya), (p - 1, yb), I.t0⟩)
    (hF : Solvable ⟨I.w - p, I.h, unX p I.s1, unX p I.t1, (0, ya), (0, yb)⟩)
    (hs1 : p ≤ I.s1.1) (ht1 : p ≤ I.t1.1) : Solvable I := by
  obtain ⟨PL, QL, sL⟩ := hN
  obtain ⟨PR, QR, sR⟩ := hF
  obtain ⟨aP, aQ, aD, aX, aC⟩ := left_piece (I := I)
    (J := ⟨p, I.h, I.s0, (p - 1, ya), (p - 1, yb), I.t0⟩) (p := p) rfl hp.le rfl sL
  obtain ⟨bP, bQ, bD, bX, bC⟩ := right_piece (I := I)
    (J := ⟨I.w - p, I.h, unX p I.s1, unX p I.t1, (0, ya), (0, yb)⟩) (p := p)
    (show I.w - p + p = I.w by omega) rfl sR
  have ea : trX p (0, ya) = (p, ya) := by simp [trX]
  have eb : trX p (0, yb) = (p, yb) := by simp [trX]
  dsimp only at aP aQ bP bQ
  rw [trX_unX hs1, trX_unX ht1] at bP
  rw [ea, eb] at bQ
  have sep : ∀ v ∈ PL ++ QL, ∀ u ∈ PR.map (trX p) ++ QR.map (trX p), v ≠ u := by
    intro v hv u hu he
    have := aX v hv; have := bX u hu; rw [he] at *; omega
  have adj1 : Adjacent (p - 1, ya) (p, ya) := by unfold Adjacent; omega
  have adj2 : Adjacent (p, yb) (p - 1, yb) := by unfold Adjacent; omega
  have h1 := aP.append bQ adj1 (fun v hv hv' => sep v (by simp [hv]) v (by simp [hv']) rfl)
  have h2 := h1.append aQ adj2 (by
    intro v hv hv'
    rcases List.mem_append.mp hv with h | h
    · exact aD v h hv'
    · exact sep v (by simp [hv']) v (by simp [h]) rfl)
  refine ⟨(PL ++ QR.map (trX p)) ++ QL, PR.map (trX p), h2, bP, ?_, ?_⟩
  · intro v hv hv'
    rcases List.mem_append.mp hv with h | h
    · rcases List.mem_append.mp h with h | h
      · exact sep v (by simp [h]) v (by simp [hv']) rfl
      · exact bD v hv' h
    · exact sep v (by simp [h]) v (by simp [hv']) rfl
  · intro v hv
    by_cases hx : v.1 < p
    · rcases aC v hv hx with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inl (by simp [h])
    · rcases bC v hv (by omega) with h | h
      · exact Or.inr h
      · exact Or.inl (by simp [h])

end ZZN

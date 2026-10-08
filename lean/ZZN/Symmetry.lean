-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Reductions

/-!
# Transposition

Swapping the two coordinates maps solutions to solutions (`solvable_transpose`).
-/

namespace ZZN

open GridHam

def Inst.transpose (I : Inst) : Inst where
  w  := I.h
  h  := I.w
  s0 := I.s0.swap
  t0 := I.t0.swap
  s1 := I.s1.swap
  t1 := I.t1.swap

theorem Inst.transpose_transpose (I : Inst) : I.transpose.transpose = I := by
  cases I; simp [Inst.transpose]

theorem adjacent_swap {u v : Coord} (h : Adjacent u v) : Adjacent u.swap v.swap := by
  unfold Adjacent at h ⊢
  simp only [Prod.fst_swap, Prod.snd_swap]
  tauto

theorem chainAdjacent_map_swap : ∀ (l : List Coord), chainAdjacent l = true →
    chainAdjacent (l.map Prod.swap) = true
  | [] => fun _ => rfl
  | [_] => fun _ => rfl
  | a :: b :: l => by
    intro hc
    rw [chainAdjacent_cons_cons, Bool.and_eq_true] at hc
    simp only [List.map_cons]
    rw [chainAdjacent_cons_cons, Bool.and_eq_true]
    refine ⟨(adjacentB_iff _ _).mpr (adjacent_swap ((adjacentB_iff _ _).mp hc.1)), ?_⟩
    have := chainAdjacent_map_swap (b :: l) hc.2
    simpa using this

theorem IsPath.swap {w h : ℕ} {s t : Coord} {l : List Coord} (hp : IsPath w h s t l) :
    IsPath h w s.swap t.swap (l.map Prod.swap) := by
  obtain ⟨hh, hl, hn, hb, hc⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, chainAdjacent_map_swap l hc⟩
  · rw [List.head?_map, hh]; rfl
  · rw [List.getLast?_map, hl]; rfl
  · exact hn.map Prod.swap_injective
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    have := hb u hu
    unfold InBounds at this ⊢
    simp only [Prod.fst_swap, Prod.snd_swap]
    exact ⟨this.2, this.1⟩

theorem solvable_transpose {I : Inst} (hS : Solvable I) : Solvable I.transpose := by
  obtain ⟨p, q, hp, hq, hd, hc⟩ := hS
  refine ⟨p.map Prod.swap, q.map Prod.swap, hp.swap, hq.swap, ?_, ?_⟩
  · intro v hv hv'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    obtain ⟨u', hu', he⟩ := List.mem_map.mp hv'
    exact hd u hu (Prod.swap_injective he ▸ hu')
  · intro v hv
    have hb : InBounds I.w I.h v.swap := by
      unfold InBounds at hv ⊢
      exact ⟨hv.2, hv.1⟩
    rcases hc v.swap hb with h | h
    · exact Or.inl (List.mem_map.mpr ⟨v.swap, h, Prod.swap_swap v⟩)
    · exact Or.inr (List.mem_map.mpr ⟨v.swap, h, Prod.swap_swap v⟩)

theorem solvable_transpose_iff {I : Inst} : Solvable I.transpose ↔ Solvable I :=
  ⟨fun h => I.transpose_transpose ▸ solvable_transpose h, solvable_transpose⟩

/-! ### Reflection and path reversal -/

/-- Reflect the x-axis: `x ↦ w - 1 - x`. -/
def reflX (w : ℕ) (v : Coord) : Coord := (w - 1 - v.1, v.2)

def Inst.reflectX (I : Inst) : Inst where
  w  := I.w
  h  := I.h
  s0 := reflX I.w I.s0
  t0 := reflX I.w I.t0
  s1 := reflX I.w I.s1
  t1 := reflX I.w I.t1

theorem chainAdjacent_map_of {f : Coord → Coord} (hf : ∀ u v, Adjacent u v → Adjacent (f u) (f v)) :
    ∀ (l : List Coord), chainAdjacent l = true → chainAdjacent (l.map f) = true
  | [] => fun _ => rfl
  | [_] => fun _ => rfl
  | a :: b :: l => by
    intro hc
    rw [chainAdjacent_cons_cons, Bool.and_eq_true] at hc
    simp only [List.map_cons]
    rw [chainAdjacent_cons_cons, Bool.and_eq_true]
    refine ⟨(adjacentB_iff _ _).mpr (hf _ _ ((adjacentB_iff _ _).mp hc.1)), ?_⟩
    have := chainAdjacent_map_of hf (b :: l) hc.2
    simpa using this

/-- A map of the grid to itself that is a bijection on cells and preserves adjacency carries
solutions to solutions. -/
theorem solvable_map {I J : Inst} (f : Coord → Coord)
    (hinj : ∀ u v, InBounds I.w I.h u → InBounds I.w I.h v → f u = f v → u = v)
    (hb : ∀ v, InBounds I.w I.h v → InBounds J.w J.h (f v))
    (hsurj : ∀ v, InBounds J.w J.h v → ∃ u, InBounds I.w I.h u ∧ f u = v)
    (hadj : ∀ u v, Adjacent u v → InBounds I.w I.h u → InBounds I.w I.h v → Adjacent (f u) (f v))
    (e0 : f I.s0 = J.s0) (e1 : f I.t0 = J.t0) (e2 : f I.s1 = J.s1) (e3 : f I.t1 = J.t1)
    (hS : Solvable I) : Solvable J := by
  obtain ⟨p, q, hp, hq, hd, hc⟩ := hS
  have path : ∀ {s t : Coord} {L : List Coord}, IsPath I.w I.h s t L →
      IsPath J.w J.h (f s) (f t) (L.map f) := by
    intro s t L hL
    obtain ⟨hh, hl, hn, hbL, hch⟩ := hL
    refine ⟨by rw [List.head?_map, hh]; rfl, by rw [List.getLast?_map, hl]; rfl, ?_,
      fun v hv => by obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv; exact hb u (hbL u hu), ?_⟩
    · refine List.Nodup.map_on (fun x hx y hy h => hinj x y (hbL x hx) (hbL y hy) h) hn
    · -- adjacency is only needed for in-bounds cells, which all cells of `L` are
      have : ∀ (l : List Coord), (∀ v ∈ l, InBounds I.w I.h v) → chainAdjacent l = true →
          chainAdjacent (l.map f) = true := by
        intro l
        induction l with
        | nil => intro _ _; rfl
        | cons a l ih =>
          intro hbl hcl
          cases l with
          | nil => rfl
          | cons b l =>
            rw [chainAdjacent_cons_cons, Bool.and_eq_true] at hcl
            simp only [List.map_cons]
            rw [chainAdjacent_cons_cons, Bool.and_eq_true]
            refine ⟨(adjacentB_iff _ _).mpr (hadj _ _ ((adjacentB_iff _ _).mp hcl.1)
              (hbl a (by simp)) (hbl b (by simp))), ?_⟩
            have := ih (fun v hv => hbl v (List.mem_cons_of_mem _ hv)) hcl.2
            simpa using this
      exact this L hbL hch
  refine ⟨p.map f, q.map f, e0 ▸ e1 ▸ path hp, e2 ▸ e3 ▸ path hq, ?_, ?_⟩
  · intro v hv hv'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    obtain ⟨u', hu', he⟩ := List.mem_map.mp hv'
    have := hinj u' u (hp.2.2.2.1 _ (by exact hu) |> fun _ => hq.2.2.2.1 u' hu')
      (hp.2.2.2.1 u hu) he
    exact hd u hu (this ▸ hu')
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := hsurj v hv
    rcases hc u hu with h | h
    · exact Or.inl (List.mem_map_of_mem h)
    · exact Or.inr (List.mem_map_of_mem h)

theorem solvable_reflectX {I : Inst} (hS : Solvable I) : Solvable I.reflectX := by
  refine solvable_map (reflX I.w) ?_ ?_ ?_ ?_ rfl rfl rfl rfl hS
  · intro u v hu hv h
    obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v
    simp only [reflX, Prod.mk.injEq] at h
    have := hu.1; have := hv.1
    simp only at *
    exact Prod.ext (by omega) h.2
  · intro v hv
    exact ⟨by simp [reflX, Inst.reflectX]; have := hv.1; omega, hv.2⟩
  · intro v hv
    refine ⟨reflX I.w v, ⟨by simp [reflX]; have := hv.1; simp [Inst.reflectX] at this; omega, hv.2⟩, ?_⟩
    obtain ⟨v1, v2⟩ := v
    have := hv.1
    simp only [reflX, Inst.reflectX] at this ⊢
    exact Prod.ext (by simp; omega) rfl
  · intro u v h hu hv
    unfold Adjacent at h ⊢
    have := hu.1; have := hv.1
    simp only [reflX]
    omega

/-- Undo a reflection (the endpoints lie in the grid). -/
theorem solvable_of_reflectX {I : Inst} (hb : ∀ e ∈ [I.s0, I.t0, I.s1, I.t1], e.1 < I.w)
    (h : Solvable I.reflectX) : Solvable I := by
  have h2 := solvable_reflectX h
  have back : ∀ e ∈ [I.s0, I.t0, I.s1, I.t1], reflX I.w (reflX I.w e) = e := by
    intro e he
    have := hb e he
    obtain ⟨e1, e2⟩ := e
    simp only [reflX] at this ⊢
    exact Prod.ext (by simp; omega) rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at back
  have e : I.reflectX.reflectX = I := by
    cases I
    simp only [Inst.reflectX] at back ⊢
    rw [back.1, back.2.1, back.2.2.1, back.2.2.2]
  exact e ▸ h2

end ZZN

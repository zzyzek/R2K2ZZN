-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Glue

/-!
# Strips: adding two endpoint-free lines at the edge

`strip2`: if `I` is solvable and its lines have length `h ≥ 5`, then the instance with two more
lines `x = w, w+1` (same endpoints) is solvable. The last line may hold endpoints: since `h ≥ 5`,
some cell of the last line is not an endpoint, and it has a path edge along the line, which seeds
the construction of `BandExtension.lean` (flip, then sweeps).
-/

namespace ZZN

open GridHam Classical

/-- Widen by `k` lines at the edge `x = w`, keeping the endpoints. -/
def Inst.widen (I : Inst) (k : ℕ) : Inst := ⟨I.w + k, I.h, I.s0, I.t0, I.s1, I.t1⟩

theorem shiftAt_of_le {r : ℕ} {v : Coord} (h : v.1 ≤ r) : shiftAt r v = v := by
  simp [shiftAt, h]

/-- Five cells cannot all be endpoints. -/
theorem exists_free_cell (I : Inst) (x : ℕ) :
    ∃ y, y < 5 ∧ (x, y) ≠ I.s0 ∧ (x, y) ≠ I.t0 ∧ (x, y) ≠ I.s1 ∧ (x, y) ≠ I.t1 := by
  by_contra H
  push Not at H
  let E : Finset Coord := {I.s0, I.t0, I.s1, I.t1}
  let F : Finset Coord := (Finset.range 5).image (fun y => (x, y))
  have hsub : F ⊆ E := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hc
    have := H y (Finset.mem_range.mp hy)
    simp only [E, Finset.mem_insert, Finset.mem_singleton]
    by_cases a : (x, y) = I.s0
    · exact Or.inl a
    by_cases b : (x, y) = I.t0
    · exact Or.inr (Or.inl b)
    by_cases c : (x, y) = I.s1
    · exact Or.inr (Or.inr (Or.inl c))
    exact Or.inr (Or.inr (Or.inr (this a b c)))
  have h1 : F.card = 5 := by
    rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
    simp
  have h2 : E.card ≤ 4 := Finset.card_le_four
  have := Finset.card_le_card hsub
  omega

theorem strip2 (I : Inst) (h5 : 5 ≤ I.h) (hS : Solvable I) : Solvable (I.widen 2) := by
  obtain ⟨p, q, hsol⟩ := hS
  have hw : 0 < I.w := by
    have hs0 : I.s0 ∈ p := List.mem_of_mem_head? hsol.1.1
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) (hsol.1.2.2.2.1 _ hs0).1
  set r := I.w - 1 with hr
  have hrw : r < I.w := by omega
  have noCross : ∀ y, ¬ Cross p q r y := by
    intro y hc
    have hin : ∀ {L : List Coord} {s t : Coord}, IsPath I.w I.h s t L →
        ¬ Used L (r, y) (r + 1, y) := by
      intro L s t hL hu
      have := (hL.2.2.2.1 _ hu.mem_right).1
      simp only at this
      omega
    rcases hc with hc | hc
    · exact hin hsol.1 hc
    · exact hin hsol.2.1 hc
  set U0 := (Finset.range I.h).filter (fun y => ¬ Cross p q r y) with hU0
  have hU0' : ∀ z, z ∈ U0 ↔ z < I.h := by
    intro z
    simp only [hU0, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.1, fun h => ⟨h, noCross z⟩⟩
  have st0 := init_state hsol hrw
  -- a seed edge along the last line
  obtain ⟨y0, hy05, f0, f1, f2, f3⟩ := exists_free_cell I r
  have seed : ∃ y, y + 1 < I.h ∧
      (Used (stretch r p) (r, y) (r, y + 1) ∨ Used (stretch r q) (r, y) (r, y + 1)) := by
    obtain ⟨hp, hq, -, hcov⟩ := hsol
    have edge : ∃ y', (y' + 1 = y0 ∨ y0 + 1 = y') ∧ y' < I.h ∧
        (Used p (r, y0) (r, y') ∨ Used q (r, y0) (r, y')) := by
      rcases hcov (r, y0) ⟨hrw, by omega⟩ with hv | hv
      · obtain ⟨y', a, b, u⟩ := exists_row_edge hp hv (Ne.symm f0) (Ne.symm f1)
          (fun h => noCross y0 (Or.inl h))
        exact ⟨y', a, b, Or.inl u⟩
      · obtain ⟨y', a, b, u⟩ := exists_row_edge hq hv (Ne.symm f2) (Ne.symm f3)
          (fun h => noCross y0 (Or.inr h))
        exact ⟨y', a, b, Or.inr u⟩
    obtain ⟨y', hadj, hy', hu⟩ := edge
    rcases hadj with e | e
    · subst e
      refine ⟨y', by omega, ?_⟩
      rcases hu with u | u
      · exact Or.inl (used_stretch_row u.symm)
      · exact Or.inr (used_stretch_row u.symm)
    · subst e
      refine ⟨y0, hy', ?_⟩
      rcases hu with u | u
      · exact Or.inl (used_stretch_row u)
      · exact Or.inr (used_stretch_row u)
  obtain ⟨y, hy, hu⟩ := seed
  have hyU : y ∈ U0 := (hU0' y).mpr (by omega)
  have hy1U : y + 1 ∈ U0 := (hU0' (y + 1)).mpr hy
  obtain ⟨P1, Q1, st1, m1, m2, -⟩ := st0.flip hyU hy1U hu
  have gone : ∀ z, z < I.h → z ≠ y → z ≠ y + 1 → z ∈ (U0.erase y).erase (y + 1) := by
    intro z hz h1 h2
    exact Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, (hU0' z).mpr hz⟩⟩
  obtain ⟨P2, Q2, st2, keep2⟩ := PState.sweepLeft y _ P1 Q1 st1
    (fun h => Finset.notMem_erase y U0 (Finset.mem_of_mem_erase h)) m1
    (fun z hz hzU => absurd (gone z (by omega) (by omega) (by omega)) hzU)
  obtain ⟨P3, Q3, st3, -⟩ := PState.sweepRight (I.h - (y + 1)) (y + 1) _ P2 Q2 rfl st2
    (fun h => Finset.notMem_erase (y + 1) _ (Finset.mem_filter.mp h).1)
    (keep2 (y + 1) (by omega) m2)
    (fun z hz hzh hzU => absurd (Finset.mem_filter.mpr ⟨gone z hzh (by omega) (by omega),
      by omega⟩) hzU)
  have hend : ∀ e, InBounds I.w I.h e → shiftAt r e = e := fun e he => shiftAt_of_le (by
    have := he.1; omega)
  have bs0 := hsol.1.2.2.2.1 _ (List.mem_of_mem_head? hsol.1.1)
  have bt0 := hsol.1.2.2.2.1 _ (List.mem_of_mem_getLast? hsol.1.2.1)
  have bs1 := hsol.2.1.2.2.2.1 _ (List.mem_of_mem_head? hsol.2.1.1)
  have bt1 := hsol.2.1.2.2.2.1 _ (List.mem_of_mem_getLast? hsol.2.1.2.1)
  rw [hend _ bs0, hend _ bt0, hend _ bs1, hend _ bt1] at st3
  refine ⟨P3, Q3, st3.pp, st3.pq, st3.disj, fun v hv => st3.cov v hv ?_⟩
  rintro ⟨_, h⟩
  simp only [Finset.mem_filter, Finset.mem_erase] at h
  omega

/-- Strips of any even width. -/
theorem strip_even (I : Inst) (h5 : 5 ≤ I.h) : ∀ k, Solvable I → Solvable (I.widen (2 * k))
  | 0, hS => by simpa [Inst.widen] using hS
  | k + 1, hS => by
    have := strip2 (I.widen (2 * k)) h5 (strip_even I h5 k hS)
    simpa [Inst.widen, Nat.mul_succ, Nat.add_assoc] using this

/-! ### Odd widths: a 3-wide snake -/

/-- Column `x`, rows `a + n` down to `a`. -/
def colSeg (x a : ℕ) : ℕ → List Coord
  | 0 => [(x, a)]
  | n + 1 => (x, a + n + 1) :: colSeg x a n

/-- Columns `x+1, x+2`, rows `0 … 2m-1`, as a snake: row `2i` left to right, row `2i+1` back. -/
def snake (x : ℕ) : ℕ → List Coord
  | 0 => []
  | m + 1 => snake x m ++ [(x + 1, 2 * m), (x + 2, 2 * m), (x + 2, 2 * m + 1), (x + 1, 2 * m + 1)]

theorem colSeg_head (x a n : ℕ) : (colSeg x a n).head? = some (x, a + n) := by
  cases n <;> simp [colSeg]; omega

theorem colSeg_getLast (x a : ℕ) : ∀ n, (colSeg x a n).getLast? = some (x, a)
  | 0 => rfl
  | n + 1 => by
    have := colSeg_getLast x a n
    cases n <;> simp_all [colSeg, List.getLast?_cons_cons]

theorem mem_colSeg {x a : ℕ} {v : Coord} : ∀ {n}, v ∈ colSeg x a n ↔ v.1 = x ∧ a ≤ v.2 ∧ v.2 ≤ a + n
  | 0 => by
    obtain ⟨v1, v2⟩ := v
    simp [colSeg]; omega
  | n + 1 => by
    obtain ⟨v1, v2⟩ := v
    have ih := @mem_colSeg x a (v1, v2) n
    simp only [colSeg, List.mem_cons, Prod.mk.injEq] at ih ⊢
    rw [ih]; omega

theorem colSeg_chain (x a : ℕ) : ∀ n, chainAdjacent (colSeg x a n) = true
  | 0 => rfl
  | n + 1 => by
    have ih := colSeg_chain x a n
    cases n with
    | zero => simp [colSeg, chainAdjacent_cons_cons, adjacentB, Adjacent]
    | succ n =>
      simp only [colSeg] at ih ⊢
      rw [chainAdjacent_cons_cons, Bool.and_eq_true]
      exact ⟨by simp [adjacentB, Adjacent]; omega, ih⟩

theorem colSeg_nodup (x a : ℕ) : ∀ n, (colSeg x a n).Nodup
  | 0 => by simp [colSeg]
  | n + 1 => by
    refine List.nodup_cons.mpr ⟨fun h => ?_, colSeg_nodup x a n⟩
    have := (mem_colSeg.mp h).2.2
    simp at this

theorem mem_snake {x : ℕ} {v : Coord} : ∀ {m}, v ∈ snake x m ↔
    (v.1 = x + 1 ∨ v.1 = x + 2) ∧ v.2 < 2 * m
  | 0 => by simp [snake]
  | m + 1 => by
    obtain ⟨v1, v2⟩ := v
    have ih := @mem_snake x (v1, v2) m
    simp only [snake, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at ih ⊢
    rw [ih]; omega

theorem snake_nodup (x : ℕ) : ∀ m, (snake x m).Nodup
  | 0 => by simp [snake]
  | m + 1 => by
    simp only [snake]
    rw [List.nodup_append]
    refine ⟨snake_nodup x m, by simp, ?_⟩
    rintro ⟨u1, u2⟩ hu ⟨v1, v2⟩ hv huv
    simp only [Prod.mk.injEq] at huv
    obtain ⟨rfl, rfl⟩ := huv
    have := (mem_snake.mp hu).2
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hv this
    omega

theorem snake_getLast (x m : ℕ) : (snake x (m + 1)).getLast? = some (x + 1, 2 * m + 1) := by
  simp [snake]

theorem snake_head (x : ℕ) : ∀ m, (snake x (m + 1)).head? = some (x + 1, 0)
  | 0 => by simp [snake]
  | m + 1 => by
    have ih := snake_head x m
    rw [show snake x (m + 2) = snake x (m + 1) ++ _ from rfl, List.head?_append, ih]
    rfl

theorem chainAdjacent_append_of {A B : List Coord} {a b : Coord} (hA : chainAdjacent A = true)
    (hB : chainAdjacent B = true) (ha : A.getLast? = some a) (hb : B.head? = some b)
    (hab : Adjacent a b) : chainAdjacent (A ++ B) = true := by
  obtain ⟨A', rfl⟩ : ∃ A', A = A' ++ [a] := by
    cases A using List.reverseRecOn with
    | nil => simp at ha
    | append_singleton A' z _ => simp at ha; exact ⟨A', by rw [ha]⟩
  obtain ⟨B', rfl⟩ : ∃ B', B = b :: B' := by
    cases B with
    | nil => simp at hb
    | cons z B' => simp at hb; exact ⟨B', by rw [hb]⟩
  have e : (A' ++ [a]) ++ b :: B' = A' ++ a :: (b :: B') := by simp
  rw [e, chainAdjacent_append_cons, Bool.and_eq_true, chainAdjacent_cons_cons, Bool.and_eq_true]
  exact ⟨hA, (adjacentB_iff a b).mpr hab, hB⟩

theorem snake_chain (x : ℕ) : ∀ m, chainAdjacent (snake x m) = true
  | 0 => rfl
  | m + 1 => by
    cases m with
    | zero => simp [snake, chainAdjacent_cons_cons, adjacentB, Adjacent]
    | succ m =>
      refine chainAdjacent_append_of (snake_chain x (m + 1)) ?_ (snake_getLast x m) rfl ?_
      · simp [chainAdjacent_cons_cons, adjacentB, Adjacent]
      · unfold Adjacent; omega

theorem chainAdjacent_reverse : ∀ (l : List Coord), chainAdjacent l = true →
    chainAdjacent l.reverse = true
  | [] => fun _ => rfl
  | [_] => fun _ => rfl
  | a :: b :: l => by
    intro hc
    rw [chainAdjacent_cons_cons, Bool.and_eq_true] at hc
    have ih := chainAdjacent_reverse (b :: l) hc.2
    rw [List.reverse_cons]
    have hadj := (adjacentB_iff a b).mp hc.1
    refine chainAdjacent_append_of ih rfl (show ((b :: l).reverse).getLast? = some b by simp) rfl ?_
    unfold Adjacent at hadj ⊢
    omega

/-- The 3-wide block `x = w, w+1, w+2` (rows `0 … h-1`, `h` even), as a path from `(w, y)` to
`(w, y+1)`. -/
def block3 (w h y : ℕ) : List Coord :=
  colSeg w 0 y ++ snake w (h / 2) ++ colSeg w (y + 1) (h - 2 - y)

theorem mem_block3 {w h y : ℕ} (hh : h % 2 = 0) (hy : y + 2 ≤ h) {v : Coord} :
    v ∈ block3 w h y ↔ w ≤ v.1 ∧ v.1 ≤ w + 2 ∧ v.2 < h := by
  obtain ⟨v1, v2⟩ := v
  simp only [block3, List.mem_append, mem_colSeg, mem_snake]
  omega

theorem block3_nodup {w h y : ℕ} (_hh : h % 2 = 0) (_hy : y + 2 ≤ h) : (block3 w h y).Nodup := by
  unfold block3
  rw [List.nodup_append, List.nodup_append]
  refine ⟨⟨colSeg_nodup _ _ _, snake_nodup _ _, ?_⟩, colSeg_nodup _ _ _, ?_⟩
  · rintro u hu v hv rfl
    have a := mem_colSeg.mp hu
    have b := mem_snake.mp hv
    omega
  · rintro u hu v hv rfl
    have b := mem_colSeg.mp hv
    rcases List.mem_append.mp hu with hu | hu
    · have a := mem_colSeg.mp hu; omega
    · have a := mem_snake.mp hu; omega

theorem block3_chain {w h y : ℕ} (hw : 1 ≤ w) (hh : h % 2 = 0) (hy : y + 2 ≤ h) :
    chainAdjacent ((w - 1, y) :: (block3 w h y ++ [(w - 1, y + 1)])) = true := by
  obtain ⟨m, rfl⟩ : ∃ m, h = 2 * (m + 1) := ⟨h / 2 - 1, by omega⟩
  have hm : 2 * (m + 1) / 2 = m + 1 := by omega
  have c1 : chainAdjacent ([(w - 1, y)] ++ colSeg w 0 y) = true :=
    chainAdjacent_append_of rfl (colSeg_chain _ _ _)
      (show [(w - 1, y)].getLast? = some (w - 1, y) from rfl) (colSeg_head _ _ _)
      (by unfold Adjacent; omega)
  have c2 : chainAdjacent (([(w - 1, y)] ++ colSeg w 0 y) ++ snake w (m + 1)) = true :=
    chainAdjacent_append_of c1 (snake_chain _ _)
      (by rw [List.getLast?_append_of_ne_nil _ (by cases y <;> simp [colSeg])]; exact colSeg_getLast _ _ _)
      (snake_head _ _) (by unfold Adjacent; omega)
  have c3 : chainAdjacent ((([(w - 1, y)] ++ colSeg w 0 y) ++ snake w (m + 1)) ++
      colSeg w (y + 1) (2 * (m + 1) - 2 - y)) = true :=
    chainAdjacent_append_of c2 (colSeg_chain _ _ _)
      (by rw [List.getLast?_append_of_ne_nil _ (by simp [snake])]; exact snake_getLast _ _)
      (colSeg_head _ _ _) (by unfold Adjacent; omega)
  have c4 := chainAdjacent_append_of c3 (show chainAdjacent [(w - 1, y + 1)] = true from rfl)
      (by rw [List.getLast?_append_of_ne_nil _ (by cases (2 * (m + 1) - 2 - y) <;> simp [colSeg])]
          exact colSeg_getLast _ _ _)
      rfl (by unfold Adjacent; omega)
  simpa [block3, hm] using c4

/-- **Odd strips.** Adding a 3-wide endpoint-free strip, when the line length is even. -/
theorem strip3 (I : Inst) (h5 : 5 ≤ I.h) (heven : I.h % 2 = 0) (hS : Solvable I) :
    Solvable (I.widen 3) := by
  obtain ⟨p, q, hsol⟩ := hS
  have hw : 0 < I.w := by
    have hs0 : I.s0 ∈ p := List.mem_of_mem_head? hsol.1.1
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) (hsol.1.2.2.2.1 _ hs0).1
  set r := I.w - 1 with hr
  have hrw : r < I.w := by omega
  obtain ⟨hp, hq, hdisj, hcov⟩ := hsol
  have noUse : ∀ {L : List Coord} {s t : Coord} {y : ℕ}, IsPath I.w I.h s t L →
      ¬ Used L (r, y) (r + 1, y) := by
    intro L s t y hL hu
    have := (hL.2.2.2.1 _ hu.mem_right).1
    simp only at this
    omega
  obtain ⟨y0, hy05, f0, f1, f2, f3⟩ := exists_free_cell I r
  have edge : ∃ y', (y' + 1 = y0 ∨ y0 + 1 = y') ∧ y' < I.h ∧
      (Used p (r, y0) (r, y') ∨ Used q (r, y0) (r, y')) := by
    rcases hcov (r, y0) ⟨hrw, by omega⟩ with hv | hv
    · obtain ⟨y', a, b, u⟩ := exists_row_edge hp hv (Ne.symm f0) (Ne.symm f1) (noUse hp)
      exact ⟨y', a, b, Or.inl u⟩
    · obtain ⟨y', a, b, u⟩ := exists_row_edge hq hv (Ne.symm f2) (Ne.symm f3) (noUse hq)
      exact ⟨y', a, b, Or.inr u⟩
  obtain ⟨y, hy, hu⟩ : ∃ y, y + 1 < I.h ∧ (Used p (r, y) (r, y + 1) ∨ Used q (r, y) (r, y + 1)) := by
    obtain ⟨y', hadj, hy', hu⟩ := edge
    rcases hadj with e | e
    · subst e
      exact ⟨y', by omega, by rcases hu with u | u; exact Or.inl u.symm; exact Or.inr u.symm⟩
    · subst e
      exact ⟨y0, hy', hu⟩
  set X := block3 I.w I.h y with hX
  have hXn : X.Nodup := block3_nodup heven (by omega)
  have hXmem : ∀ v, v ∈ X ↔ I.w ≤ v.1 ∧ v.1 ≤ I.w + 2 ∧ v.2 < I.h := fun v =>
    mem_block3 heven (by omega)
  have hXb : ∀ v ∈ X, InBounds (I.w + 3) I.h v := fun v hv => by
    have := (hXmem v).mp hv; unfold InBounds; omega
  have hc : chainAdjacent ((r, y) :: (X ++ [(r, y + 1)])) = true := by
    rw [hr]; exact block3_chain (by omega) heven (by omega)
  have hc' : chainAdjacent ((r, y + 1) :: (X.reverse ++ [(r, y)])) = true := by
    have := chainAdjacent_reverse _ hc
    simpa using this
  have fresh : ∀ {L : List Coord} {s t : Coord}, IsPath I.w I.h s t L → ∀ x ∈ X, x ∉ L := by
    intro L s t hL x hx hxL
    have := (hL.2.2.2.1 x hxL).1
    have := ((hXmem x).mp hx).1
    omega
  have freshR : ∀ {L : List Coord} {s t : Coord}, IsPath I.w I.h s t L → ∀ x ∈ X.reverse, x ∉ L :=
    fun hL x hx => fresh hL x (List.mem_reverse.mp hx)
  have wp := hp.widen (w' := I.w + 3) (by omega)
  have wq := hq.widen (w' := I.w + 3) (by omega)
  -- splice the block into the edge, in whichever path and direction it is used
  have finish : ∀ (P Q : List Coord), IsPath (I.w + 3) I.h I.s0 I.t0 P →
      IsPath (I.w + 3) I.h I.s1 I.t1 Q → (∀ v ∈ P, v ∉ Q) →
      (∀ v, v ∈ P ∨ v ∈ Q ↔ v ∈ p ∨ v ∈ q ∨ v ∈ X) → Solvable (I.widen 3) := by
    intro P Q hP hQ hd hm
    refine ⟨P, Q, hP, hQ, hd, fun v hv => (hm v).mpr ?_⟩
    by_cases hx : v.1 < I.w
    · rcases hcov v ⟨hx, hv.2⟩ with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ((hXmem v).mpr ⟨by omega, by have := hv.1; simp [Inst.widen] at this; omega, hv.2⟩))
  rcases hu with (h | h) | (h | h)
  · obtain ⟨l1, l2, rfl⟩ := infix_pair_iff.mp h
    refine finish _ q (wp.splice hc hXn hXb (fresh hp)) wq ?_ ?_
    · intro v hv hvq
      rcases (mem_splice _ _ _ _ _ _).mp hv with h | h
      · exact hdisj v h hvq
      · exact fresh hq v h hvq
    · intro v; rw [mem_splice]; try tauto
  · obtain ⟨l1, l2, rfl⟩ := infix_pair_iff.mp h
    refine finish _ q (wp.splice hc' (List.nodup_reverse.mpr hXn)
      (fun x hx => hXb x (List.mem_reverse.mp hx)) (freshR hp)) wq ?_ ?_
    · intro v hv hvq
      rcases (mem_splice _ _ _ _ _ _).mp hv with h | h
      · exact hdisj v h hvq
      · exact freshR hq v h hvq
    · intro v; rw [mem_splice, List.mem_reverse]; try tauto
  · obtain ⟨l1, l2, rfl⟩ := infix_pair_iff.mp h
    refine finish p _ wp (wq.splice hc hXn hXb (fresh hq)) ?_ ?_
    · intro v hv hvq
      rcases (mem_splice _ _ _ _ _ _).mp hvq with h | h
      · exact hdisj v hv h
      · exact fresh hp v h hv
    · intro v; rw [mem_splice]; try tauto
  · obtain ⟨l1, l2, rfl⟩ := infix_pair_iff.mp h
    refine finish p _ wp (wq.splice hc' (List.nodup_reverse.mpr hXn)
      (fun x hx => hXb x (List.mem_reverse.mp hx)) (freshR hq)) ?_ ?_
    · intro v hv hvq
      rcases (mem_splice _ _ _ _ _ _).mp hvq with h | h
      · exact hdisj v hv h
      · exact freshR hp v h hv
    · intro v; rw [mem_splice, List.mem_reverse]; try tauto

/-- **Strips of any width `k ≥ 2`** with even area of the added block (`k` even, or `h` even). -/
theorem strip_any (I : Inst) (h5 : 5 ≤ I.h) (k : ℕ) (hk : 2 ≤ k) (harea : (k * I.h) % 2 = 0)
    (hS : Solvable I) : Solvable (I.widen k) := by
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simpa [two_mul] using strip_even I h5 j hS
  · have heven : I.h % 2 = 0 := by
      rcases Nat.even_or_odd I.h with ⟨i, hi⟩ | ⟨i, hi⟩
      · omega
      · rw [hi] at harea
        have : ((2 * j + 1) * (2 * i + 1)) % 2 = 1 := by
          rw [Nat.mul_mod]; simp [Nat.add_mod]
        omega
    have h3 := strip3 I h5 heven hS
    have := strip_even (I.widen 3) h5 (j - 1) h3
    have e : (I.widen 3).widen (2 * (j - 1)) = I.widen (2 * j + 1) := by
      simp only [Inst.widen, Inst.mk.injEq, and_true]; omega
    rw [e] at this
    exact this

end ZZN

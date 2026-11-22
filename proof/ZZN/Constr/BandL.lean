/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Constr.Band

@[expose] public section

/-!
# Band extension in one pass

`bandExtE` covers the uncovered rows of the new band one at a time: each absorb finds an edge in
a path and splices two cells into it, which costs the length of the path. This file describes the
same result as one pass over each path. Each covered row `a` of the band (a row crossed by a
path, or a row of the flip) is an *anchor*; the sweeps attach to it a run of `K a` uncovered rows,
below it if `a < R` and above it otherwise (`R` the seed). The pass `extL` stretches the path and
inserts, at the crossing edge of each anchor, the U-shaped detour `Gf`/`Gb` through its run.

`planLeft`/`planRight` run the sweeps of `bandExtE` on the counts `K` only. The main theorem
`bandExtL_eq` says that `bandExtL`, the pass with the planned counts, equals `bandExtE` for a
solution with line `r` free.
-/

namespace ZZN

open GridHam

/-! ### Detours -/

/-- Row `j` steps from `a`, upwards if `up`. -/
def runRow (a : ℕ) (up : Bool) (j : ℕ) : ℕ := if up then a + j else a - j

/-- The cells of the middle edge of anchor `a` with its run of `k` rows, entered from column
`r + 1` and left from column `r + 2`. -/
def Gf (r a k : ℕ) (up : Bool) : List Coord :=
  (List.range (k + 1)).map (fun i => (r + 1, runRow a up i)) ++
    (List.range (k + 1)).reverse.map (fun i => (r + 2, runRow a up i))

/-- The same, entered from column `r + 2`. -/
def Gb (r a k : ℕ) (up : Bool) : List Coord :=
  (List.range (k + 1)).map (fun i => (r + 2, runRow a up i)) ++
    (List.range (k + 1)).reverse.map (fun i => (r + 1, runRow a up i))

theorem Gf_split (r a k : ℕ) (up : Bool) :
    ∃ C D, Gf r a k up = C ++ (r + 1, runRow a up k) :: (r + 2, runRow a up k) :: D ∧
      Gf r a (k + 1) up = C ++ (r + 1, runRow a up k) :: (r + 1, runRow a up (k + 1)) ::
        (r + 2, runRow a up (k + 1)) :: (r + 2, runRow a up k) :: D := by
  refine ⟨(List.range k).map (fun i => (r + 1, runRow a up i)),
    (List.range k).reverse.map (fun i => (r + 2, runRow a up i)), ?_, ?_⟩
  · simp [Gf, List.range_succ]
  · simp [Gf, List.range_succ]

theorem Gb_split (r a k : ℕ) (up : Bool) :
    ∃ C D, Gb r a k up = C ++ (r + 2, runRow a up k) :: (r + 1, runRow a up k) :: D ∧
      Gb r a (k + 1) up = C ++ (r + 2, runRow a up k) :: (r + 2, runRow a up (k + 1)) ::
        (r + 1, runRow a up (k + 1)) :: (r + 1, runRow a up k) :: D := by
  refine ⟨(List.range k).map (fun i => (r + 2, runRow a up i)),
    (List.range k).reverse.map (fun i => (r + 1, runRow a up i)), ?_, ?_⟩
  · simp [Gb, List.range_succ]
  · simp [Gb, List.range_succ]

@[simp] theorem Gf_zero (r a : ℕ) (up : Bool) : Gf r a 0 up = [(r + 1, a), (r + 2, a)] := by
  simp [Gf, runRow]

@[simp] theorem Gb_zero (r a : ℕ) (up : Bool) : Gb r a 0 up = [(r + 2, a), (r + 1, a)] := by
  simp [Gb, runRow]

/-! ### The pass -/

/-- What the pass inserts between consecutive old cells `x, y`: the detour of a crossing edge,
the flip at rows `R - 1, R` when `fl`, or nothing. -/
def insK (r : ℕ) (K : ℕ → ℕ) (R : ℕ) (fl : Bool) (x y : Coord) : List Coord :=
  if x.1 = r ∧ y.1 = r + 1 ∧ x.2 = y.2 then Gf r x.2 (K x.2) (decide (R ≤ x.2))
  else if x.1 = r + 1 ∧ y.1 = r ∧ x.2 = y.2 then Gb r x.2 (K x.2) (decide (R ≤ x.2))
  else if fl = true ∧ x = (r, R - 1) ∧ y = (r, R) then
    Gf r (R - 1) (K (R - 1)) false ++ Gb r R (K R) true
  else if fl = true ∧ x = (r, R) ∧ y = (r, R - 1) then
    Gf r R (K R) true ++ Gb r (R - 1) (K (R - 1)) false
  else []

/-- The stretched path with the detours inserted. -/
def extL (r : ℕ) (K : ℕ → ℕ) (R : ℕ) (fl : Bool) : List Coord → List Coord
  | [] => []
  | [a] => [shiftAt r a]
  | a :: b :: l => shiftAt r a :: (insK r K R fl a b ++ extL r K R fl (b :: l))

theorem extL_append (r : ℕ) (K : ℕ → ℕ) (R : ℕ) (fl : Bool) (s t : Coord) :
    ∀ (L1 L2 : List Coord), extL r K R fl (L1 ++ s :: t :: L2) =
      extL r K R fl (L1 ++ [s]) ++ insK r K R fl s t ++ extL r K R fl (t :: L2)
  | [], L2 => by simp [extL]
  | [x], L2 => by simp [extL]
  | x :: y :: L1, L2 => by
    have ih := extL_append r K R fl s t (y :: L1) L2
    simp only [List.cons_append] at ih ⊢
    simp only [extL, ih, List.cons_append, List.append_assoc]

theorem extL_congr (r : ℕ) {K K' : ℕ → ℕ} (R : ℕ) (fl : Bool) :
    ∀ (l : List Coord), (∀ x y, [x, y] <:+: l → insK r K R fl x y = insK r K' R fl x y) →
      extL r K R fl l = extL r K' R fl l
  | [], _ => rfl
  | [_], _ => rfl
  | x :: y :: l, h => by
    simp only [extL]
    rw [h x y ⟨[], l, rfl⟩, extL_congr r R fl (y :: l) (fun u v huv => h u v (huv.trans
      (List.suffix_cons x (y :: l)).isInfix))]

/-- With no runs and no flip, the pass is `stretch`. -/
theorem extL_zero (r R : ℕ) : ∀ l, extL r (fun _ => 0) R false l = stretch r l
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    simp only [extL, stretch, extL_zero r R (b :: l)]
    congr 2
    unfold insK gap
    split_ifs <;> simp_all

/-! ### Inserting at the unique occurrence of an edge -/

theorem insB_nodup (u v : Coord) (X B : List Coord) :
    ∀ (A : List Coord), (A ++ u :: v :: B).Nodup → insB u v X (A ++ u :: v :: B) = A ++ u :: (X ++ v :: B)
  | [], _ => by simp [insB]
  | [x], hn => by
    have hx : x ≠ u := by
      intro h; subst h; simp at hn
    simp [insB, hx]
  | x :: y :: A, hn => by
    have hx : x ≠ u := by
      intro h; subst h; simp at hn
    have ih := insB_nodup u v X B (y :: A) (List.Nodup.of_cons (by simpa using hn))
    simp only [List.cons_append] at ih ⊢
    rw [insB, ite_f (fun h => hx h.1), ih]

theorem nodup_split {L1 L2 : List Coord} {s t : Coord} (h : (L1 ++ s :: t :: L2).Nodup) :
    s ∉ L1 ∧ t ∉ L1 ∧ s ≠ t ∧ s ∉ L2 ∧ t ∉ L2 := by
  rw [List.nodup_append] at h
  obtain ⟨_, h2, h3⟩ := h
  simp only [List.nodup_cons, List.mem_cons, not_or] at h2
  refine ⟨fun hs => h3 _ hs _ (by simp) rfl, fun ht => h3 _ ht _ (by simp) rfl, h2.1.1, h2.1.2,
    h2.2.1⟩

/-- A consecutive pair of a list lies in it. -/
theorem mem_of_infix_pair {l : List Coord} {x y : Coord} (h : [x, y] <:+: l) : x ∈ l ∧ y ∈ l :=
  ⟨h.subset (by simp), h.subset (by simp)⟩

/-- The pair `s, t` (in either order) is not a consecutive pair of the parts of a duplicate-free
list around one occurrence of it. -/
theorem pair_avoid {L1 L2 : List Coord} {s t : Coord} (h : (L1 ++ s :: t :: L2).Nodup) {x y : Coord}
    (hxy : [x, y] <:+: L1 ++ [s] ∨ [x, y] <:+: t :: L2) :
    ¬((x = s ∧ y = t) ∨ (x = t ∧ y = s)) := by
  obtain ⟨hs1, ht1, hst, hs2, ht2⟩ := nodup_split h
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rcases hxy with hxy | hxy
  · have := (mem_of_infix_pair hxy).2; simp at this; tauto
  · have := (mem_of_infix_pair hxy).1; simp at this; tauto
  · have := (mem_of_infix_pair hxy).1; simp at this; tauto
  · have := (mem_of_infix_pair hxy).2; simp at this; tauto

/-! ### Changing one count -/

/-- The insertion between `x, y` reads the count of anchor `a`. -/
def DepOn (r R : ℕ) (fl : Bool) (a : ℕ) (x y : Coord) : Prop :=
  (x.1 = r ∧ y.1 = r + 1 ∧ x.2 = y.2 ∧ x.2 = a) ∨ (x.1 = r + 1 ∧ y.1 = r ∧ x.2 = y.2 ∧ x.2 = a) ∨
    (fl = true ∧ (a = R - 1 ∨ a = R) ∧ ((x = (r, R - 1) ∧ y = (r, R)) ∨ (x = (r, R) ∧ y = (r, R - 1))))

theorem insK_update (r : ℕ) (K : ℕ → ℕ) (R : ℕ) (fl : Bool) (a n : ℕ) {x y : Coord}
    (h : ¬ DepOn r R fl a x y) : insK r K R fl x y = insK r (Function.update K a n) R fl x y := by
  unfold DepOn at h
  unfold insK
  split_ifs with h1 h2 h3 h4
  · rw [Function.update_of_ne (fun e => h (Or.inl ⟨h1.1, h1.2.1, h1.2.2, e⟩))]
  · rw [Function.update_of_ne (fun e => h (Or.inr (Or.inl ⟨h2.1, h2.2.1, h2.2.2, e⟩)))]
  · rw [Function.update_of_ne (fun e => h (Or.inr (Or.inr ⟨h3.1, Or.inl e.symm, Or.inl h3.2⟩))),
      Function.update_of_ne (fun e => h (Or.inr (Or.inr ⟨h3.1, Or.inr e.symm, Or.inl h3.2⟩)))]
  · rw [Function.update_of_ne (fun e => h (Or.inr (Or.inr ⟨h4.1, Or.inr e.symm, Or.inr h4.2⟩))),
      Function.update_of_ne (fun e => h (Or.inr (Or.inr ⟨h4.1, Or.inl e.symm, Or.inr h4.2⟩)))]
  · rfl

/-- One step of the pass: the count of anchor `a` grows by one, and its source edge `s, t`
occurs once in the duplicate-free list `l`. The pass changes only inside that edge. -/
theorem extL_step (r : ℕ) (K : ℕ → ℕ) (R : ℕ) (fl : Bool) (a : ℕ) {L1 L2 : List Coord}
    {s t u v : Coord} {A B X : List Coord}
    (hn : (L1 ++ s :: t :: L2).Nodup)
    (hdep : ∀ x y, [x, y] <:+: L1 ++ s :: t :: L2 → DepOn r R fl a x y →
      (x = s ∧ y = t) ∨ (x = t ∧ y = s))
    (h0 : insK r K R fl s t = A ++ u :: v :: B)
    (h1 : insK r (Function.update K a (K a + 1)) R fl s t = A ++ u :: (X ++ v :: B)) :
    ∃ E1 E2, extL r K R fl (L1 ++ s :: t :: L2) = E1 ++ u :: v :: E2 ∧
      extL r (Function.update K a (K a + 1)) R fl (L1 ++ s :: t :: L2) = E1 ++ u :: (X ++ v :: E2) := by
  have c1 : extL r K R fl (L1 ++ [s]) = extL r (Function.update K a (K a + 1)) R fl (L1 ++ [s]) :=
    extL_congr r R fl _ (fun x y hxy => insK_update r K R fl a _
      (fun hd => pair_avoid hn (Or.inl hxy) (hdep x y (hxy.trans
        ⟨[], t :: L2, by simp⟩) hd)))
  have c2 : extL r K R fl (t :: L2) = extL r (Function.update K a (K a + 1)) R fl (t :: L2) :=
    extL_congr r R fl _ (fun x y hxy => insK_update r K R fl a _
      (fun hd => pair_avoid hn (Or.inr hxy) (hdep x y (hxy.trans
        ⟨L1 ++ [s], [], by simp⟩) hd)))
  refine ⟨extL r K R fl (L1 ++ [s]) ++ A, B ++ extL r K R fl (t :: L2), ?_, ?_⟩
  · rw [extL_append, h0]; simp
  · rw [extL_append, h1, ← c1, ← c2]; simp

/-- A list none of whose cells is `s` or `t` is not changed. -/
theorem extL_other (r : ℕ) (K : ℕ → ℕ) (R : ℕ) (fl : Bool) (a : ℕ) {m : List Coord} {s t : Coord}
    (hdep : ∀ x y, [x, y] <:+: m → DepOn r R fl a x y → (x = s ∧ y = t) ∨ (x = t ∧ y = s))
    (hs : s ∉ m) :
    extL r K R fl m = extL r (Function.update K a (K a + 1)) R fl m :=
  extL_congr r R fl _ (fun x y hxy => insK_update r K R fl a _ (fun hd => by
    have hm := mem_of_infix_pair hxy
    rcases hdep x y hxy hd with ⟨rfl, -⟩ | ⟨-, rfl⟩
    · exact hs hm.1
    · exact hs hm.2))

/-! ### One absorb -/

theorem no_rev_pair {l : List Coord} {u v : Coord} (hn : l.Nodup) (h1 : [u, v] <:+: l)
    (h2 : [v, u] <:+: l) : False :=
  pred_ne_succ hn h1 h2 rfl

/-- The shape of the insertion at the source edge of an anchor, before and after its count grows:
the middle edge of the deepest row `y'` gets the two cells of the next row `y`. -/
def Grows (r y y' : ℕ) (G G' : List Coord) : Prop :=
  ∃ A B, (G = A ++ (r + 1, y') :: (r + 2, y') :: B ∧
      G' = A ++ (r + 1, y') :: ([(r + 1, y), (r + 2, y)] ++ (r + 2, y') :: B)) ∨
    (G = A ++ (r + 2, y') :: (r + 1, y') :: B ∧
      G' = A ++ (r + 2, y') :: ([(r + 2, y), (r + 1, y)] ++ (r + 1, y') :: B))

section
variable {W h r : ℕ} {s0 t0 s1 t1 : Coord} {U : Finset ℕ} {P Q p q : List Coord}

/-- **One absorb is one count.** If the paths are the pass with counts `K`, and the source edge
`s, t` of anchor `a` (the only pair whose insertion reads `K a`) lies in `p` or `q`, then
absorbing row `y` from the middle edge of row `y'` gives the pass with `K a` one larger. -/
theorem absorb_ext (st : PState W h r s0 t0 s1 t1 U P Q) {K : ℕ → ℕ} {R : ℕ} {fl : Bool}
    {a y y' : ℕ} {s t : Coord}
    (hP : P = extL r K R fl p) (hQ : Q = extL r K R fl q)
    (hp : p.Nodup) (hq : q.Nodup) (hdisj : ∀ v ∈ p, v ∉ q)
    (hst : [s, t] <:+: p ∨ [s, t] <:+: q)
    (hdep : ∀ x z, ([x, z] <:+: p ∨ [x, z] <:+: q) → DepOn r R fl a x z →
      (x = s ∧ z = t) ∨ (x = t ∧ z = s))
    (hg : Grows r y y' (insK r K R fl s t) (insK r (Function.update K a (K a + 1)) R fl s t)) :
    Mid r P Q y' ∧ absorbE r y y' P Q = (extL r (Function.update K a (K a + 1)) R fl p,
      extL r (Function.update K a (K a + 1)) R fl q) := by
  have hPn : P.Nodup := st.pp.2.2.1
  have hQn : Q.Nodup := st.pq.2.2.1
  obtain ⟨A, B, hg⟩ := hg
  rcases hst with hs | hs
  · obtain ⟨L1, L2, rfl⟩ := infix_pair_iff.mp hs
    have hsq : s ∉ q := hdisj s (by simp)
    have eQ := extL_other r K R fl a (m := q) (fun x z h => hdep x z (Or.inr h)) hsq
    rcases hg with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · obtain ⟨E1, E2, e0, e1⟩ := extL_step r K R fl a hp (fun x z h => hdep x z (Or.inl h)) h0 h1
      have hin : [(r + 1, y'), (r + 2, y')] <:+: P := by
        rw [hP, e0]; exact ⟨E1, E2, by simp⟩
      refine ⟨Or.inl (Or.inl hin), ?_⟩
      unfold absorbE spliceE
      rw [ite_t (Or.inl hin), ite_t hin, ← eQ, ← hQ, e1]
      congr 1
      rw [hP, e0] at hPn ⊢
      exact insB_nodup _ _ _ _ _ hPn
    · obtain ⟨E1, E2, e0, e1⟩ := extL_step r K R fl a hp (fun x z h => hdep x z (Or.inl h)) h0 h1
      have hin : [(r + 2, y'), (r + 1, y')] <:+: P := by
        rw [hP, e0]; exact ⟨E1, E2, by simp⟩
      have hnot : ¬([(r + 1, y'), (r + 2, y')] <:+: P ∨ [(r + 1, y'), (r + 2, y')] <:+: Q) := by
        rintro (h | h)
        · exact no_rev_pair hPn h hin
        · exact st.disj _ (mem_of_infix_pair hin).2 (mem_of_infix_pair h).1
      refine ⟨Or.inl (Or.inr hin), ?_⟩
      unfold absorbE spliceE
      rw [ite_f hnot, ite_t hin, ← eQ, ← hQ, e1]
      congr 1
      rw [hP, e0] at hPn ⊢
      exact insB_nodup _ _ _ _ _ hPn
  · obtain ⟨L1, L2, rfl⟩ := infix_pair_iff.mp hs
    have hsp : s ∉ p := fun h => hdisj s h (by simp)
    have eP := extL_other r K R fl a (m := p) (fun x z h => hdep x z (Or.inl h)) hsp
    rcases hg with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · obtain ⟨E1, E2, e0, e1⟩ := extL_step r K R fl a hq (fun x z h => hdep x z (Or.inr h)) h0 h1
      have hin : [(r + 1, y'), (r + 2, y')] <:+: Q := by
        rw [hQ, e0]; exact ⟨E1, E2, by simp⟩
      have hnP : ¬ [(r + 1, y'), (r + 2, y')] <:+: P := fun h =>
        st.disj _ (mem_of_infix_pair h).1 (mem_of_infix_pair hin).1
      refine ⟨Or.inr (Or.inl hin), ?_⟩
      unfold absorbE spliceE
      rw [ite_t (Or.inr hin), ite_f hnP, ← eP, ← hP, e1]
      congr 1
      rw [hQ, e0] at hQn ⊢
      exact insB_nodup _ _ _ _ _ hQn
    · obtain ⟨E1, E2, e0, e1⟩ := extL_step r K R fl a hq (fun x z h => hdep x z (Or.inr h)) h0 h1
      have hin : [(r + 2, y'), (r + 1, y')] <:+: Q := by
        rw [hQ, e0]; exact ⟨E1, E2, by simp⟩
      have hnot : ¬([(r + 1, y'), (r + 2, y')] <:+: P ∨ [(r + 1, y'), (r + 2, y')] <:+: Q) := by
        rintro (h | h)
        · exact st.disj _ (mem_of_infix_pair h).1 (mem_of_infix_pair hin).2
        · exact no_rev_pair hQn h hin
      have hnP : ¬ [(r + 2, y'), (r + 1, y')] <:+: P := fun h =>
        st.disj _ (mem_of_infix_pair h).1 (mem_of_infix_pair hin).1
      refine ⟨Or.inr (Or.inr hin), ?_⟩
      unfold absorbE spliceE
      rw [ite_f hnot, ite_f hnP, ← eP, ← hP, e1]
      congr 1
      rw [hQ, e0] at hQn ⊢
      exact insB_nodup _ _ _ _ _ hQn

end

/-! ### The source shapes -/

section
variable {r R : ℕ} {fl : Bool} {K : ℕ → ℕ}

theorem grows_crossF (a : ℕ) :
    Grows r (runRow a (decide (R ≤ a)) (K a + 1)) (runRow a (decide (R ≤ a)) (K a))
      (insK r K R fl (r, a) (r + 1, a)) (insK r (Function.update K a (K a + 1)) R fl (r, a) (r + 1, a)) := by
  obtain ⟨C, D, e0, e1⟩ := Gf_split r a (K a) (decide (R ≤ a))
  refine ⟨C, D, Or.inl ⟨?_, ?_⟩⟩
  · unfold insK; rw [ite_t (by simp)]; exact e0
  · unfold insK; rw [ite_t (by simp)]; simp only [Function.update_self]; rw [e1]; simp

theorem grows_crossB (a : ℕ) :
    Grows r (runRow a (decide (R ≤ a)) (K a + 1)) (runRow a (decide (R ≤ a)) (K a))
      (insK r K R fl (r + 1, a) (r, a)) (insK r (Function.update K a (K a + 1)) R fl (r + 1, a) (r, a)) := by
  obtain ⟨C, D, e0, e1⟩ := Gb_split r a (K a) (decide (R ≤ a))
  have hn : ¬((r + 1, a).1 = r ∧ (r, a).1 = r + 1 ∧ (r + 1, a).2 = (r, a).2) := by simp
  refine ⟨C, D, Or.inr ⟨?_, ?_⟩⟩
  · unfold insK; rw [ite_f hn, ite_t (by simp)]; exact e0
  · unfold insK; rw [ite_f hn, ite_t (by simp)]; simp only [Function.update_self]; rw [e1]; simp

theorem grows_flipF_lo (hR : 1 ≤ R) (hfl : fl = true) :
    Grows r (runRow (R - 1) false (K (R - 1) + 1)) (runRow (R - 1) false (K (R - 1)))
      (insK r K R fl (r, R - 1) (r, R))
      (insK r (Function.update K (R - 1) (K (R - 1) + 1)) R fl (r, R - 1) (r, R)) := by
  obtain ⟨C, D, e0, e1⟩ := Gf_split r (R - 1) (K (R - 1)) false
  have n1 : ¬((r, R - 1).1 = r ∧ (r, R).1 = r + 1 ∧ (r, R - 1).2 = (r, R).2) := by simp
  have n2 : ¬((r, R - 1).1 = r + 1 ∧ (r, R).1 = r ∧ (r, R - 1).2 = (r, R).2) := by simp
  have hR' : R ≠ R - 1 := by omega
  refine ⟨C, D ++ Gb r R (K R) true, Or.inl ⟨?_, ?_⟩⟩
  · unfold insK; rw [ite_f n1, ite_f n2, ite_t ⟨hfl, rfl, rfl⟩, e0]; simp
  · unfold insK; rw [ite_f n1, ite_f n2, ite_t ⟨hfl, rfl, rfl⟩]
    simp only [Function.update_self, Function.update_of_ne hR']; rw [e1]; simp

theorem grows_flipF_hi (hR : 1 ≤ R) (hfl : fl = true) :
    Grows r (runRow R true (K R + 1)) (runRow R true (K R))
      (insK r K R fl (r, R - 1) (r, R))
      (insK r (Function.update K R (K R + 1)) R fl (r, R - 1) (r, R)) := by
  obtain ⟨C, D, e0, e1⟩ := Gb_split r R (K R) true
  have n1 : ¬((r, R - 1).1 = r ∧ (r, R).1 = r + 1 ∧ (r, R - 1).2 = (r, R).2) := by simp
  have n2 : ¬((r, R - 1).1 = r + 1 ∧ (r, R).1 = r ∧ (r, R - 1).2 = (r, R).2) := by simp
  have hR' : R - 1 ≠ R := by omega
  refine ⟨Gf r (R - 1) (K (R - 1)) false ++ C, D, Or.inr ⟨?_, ?_⟩⟩
  · unfold insK; rw [ite_f n1, ite_f n2, ite_t ⟨hfl, rfl, rfl⟩, e0]; simp
  · unfold insK; rw [ite_f n1, ite_f n2, ite_t ⟨hfl, rfl, rfl⟩]
    simp only [Function.update_self, Function.update_of_ne hR']; rw [e1]; simp

theorem grows_flipB_hi (hR : 1 ≤ R) (hfl : fl = true) :
    Grows r (runRow R true (K R + 1)) (runRow R true (K R))
      (insK r K R fl (r, R) (r, R - 1))
      (insK r (Function.update K R (K R + 1)) R fl (r, R) (r, R - 1)) := by
  obtain ⟨C, D, e0, e1⟩ := Gf_split r R (K R) true
  have n1 : ¬((r, R).1 = r ∧ (r, R - 1).1 = r + 1 ∧ (r, R).2 = (r, R - 1).2) := by simp
  have n2 : ¬((r, R).1 = r + 1 ∧ (r, R - 1).1 = r ∧ (r, R).2 = (r, R - 1).2) := by simp
  have n3 : ¬(fl = true ∧ (r, R) = (r, R - 1) ∧ (r, R - 1) = (r, R)) := by
    rintro ⟨-, h, -⟩; simp at h; omega
  have hR' : R - 1 ≠ R := by omega
  refine ⟨C, D ++ Gb r (R - 1) (K (R - 1)) false, Or.inl ⟨?_, ?_⟩⟩
  · unfold insK; rw [ite_f n1, ite_f n2, ite_f n3, ite_t ⟨hfl, rfl, rfl⟩, e0]; simp
  · unfold insK; rw [ite_f n1, ite_f n2, ite_f n3, ite_t ⟨hfl, rfl, rfl⟩]
    simp only [Function.update_self, Function.update_of_ne hR']; rw [e1]; simp

theorem grows_flipB_lo (hR : 1 ≤ R) (hfl : fl = true) :
    Grows r (runRow (R - 1) false (K (R - 1) + 1)) (runRow (R - 1) false (K (R - 1)))
      (insK r K R fl (r, R) (r, R - 1))
      (insK r (Function.update K (R - 1) (K (R - 1) + 1)) R fl (r, R) (r, R - 1)) := by
  obtain ⟨C, D, e0, e1⟩ := Gb_split r (R - 1) (K (R - 1)) false
  have n1 : ¬((r, R).1 = r ∧ (r, R - 1).1 = r + 1 ∧ (r, R).2 = (r, R - 1).2) := by simp
  have n2 : ¬((r, R).1 = r + 1 ∧ (r, R - 1).1 = r ∧ (r, R).2 = (r, R - 1).2) := by simp
  have n3 : ¬(fl = true ∧ (r, R) = (r, R - 1) ∧ (r, R - 1) = (r, R)) := by
    rintro ⟨-, h, -⟩; simp at h; omega
  have hR' : R ≠ R - 1 := by omega
  refine ⟨Gf r R (K R) true ++ C, D, Or.inr ⟨?_, ?_⟩⟩
  · unfold insK; rw [ite_f n1, ite_f n2, ite_f n3, ite_t ⟨hfl, rfl, rfl⟩, e0]; simp
  · unfold insK; rw [ite_f n1, ite_f n2, ite_f n3, ite_t ⟨hfl, rfl, rfl⟩]
    simp only [Function.update_self, Function.update_of_ne hR']; rw [e1]; simp

end

/-! ### Anchors -/

section
variable {W h r : ℕ} {s0 t0 s1 t1 : Coord} {U : Finset ℕ} {P Q p q : List Coord}

/-- Row `a` is covered: crossed by a path, or one of the two flip rows. -/
def Cov (p q : List Coord) (r R : ℕ) (fl : Bool) (a : ℕ) : Prop :=
  Cross p q r a ∨ (fl = true ∧ (a = R - 1 ∨ a = R))

theorem cross_of_pair {x z : Coord} {a : ℕ} (hxz : [x, z] <:+: p ∨ [x, z] <:+: q)
    (h : (x = (r, a) ∧ z = (r + 1, a)) ∨ (x = (r + 1, a) ∧ z = (r, a))) : Cross p q r a := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hxz with hxz | hxz
  · exact Or.inl (Or.inl hxz)
  · exact Or.inr (Or.inl hxz)
  · exact Or.inl (Or.inr hxz)
  · exact Or.inr (Or.inr hxz)

theorem depOn_cells {R : ℕ} {fl : Bool} {a : ℕ} {x z : Coord} (hd : DepOn r R fl a x z) :
    ((x = (r, a) ∧ z = (r + 1, a)) ∨ (x = (r + 1, a) ∧ z = (r, a))) ∨
      (fl = true ∧ (a = R - 1 ∨ a = R) ∧ ((x = (r, R - 1) ∧ z = (r, R)) ∨ (x = (r, R) ∧ z = (r, R - 1)))) := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨z1, z2⟩ := z
  unfold DepOn at hd
  simp only [Prod.mk.injEq] at hd ⊢
  rcases hd with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | h
  · left; left; exact ⟨⟨h1, h4⟩, h2, by omega⟩
  · left; right; exact ⟨⟨h1, h4⟩, h2, by omega⟩
  · right; exact h

/-- **Absorbing at an anchor.** -/
theorem absorb_anchor (st : PState W h r s0 t0 s1 t1 U P Q) {K : ℕ → ℕ} {R : ℕ} {fl : Bool} {a : ℕ}
    (hP : P = extL r K R fl p) (hQ : Q = extL r K R fl q)
    (hp : p.Nodup) (hq : q.Nodup) (hdisj : ∀ v ∈ p, v ∉ q)
    (hflc : fl = true → 1 ≤ R ∧ ¬ Cross p q r (R - 1) ∧ ¬ Cross p q r R ∧
      (Used p (r, R - 1) (r, R) ∨ Used q (r, R - 1) (r, R)))
    (hcov : Cov p q r R fl a) :
    Mid r P Q (runRow a (decide (R ≤ a)) (K a)) ∧
      absorbE r (runRow a (decide (R ≤ a)) (K a + 1)) (runRow a (decide (R ≤ a)) (K a)) P Q =
        (extL r (Function.update K a (K a + 1)) R fl p, extL r (Function.update K a (K a + 1)) R fl q) := by
  rcases hcov with hc | ⟨hfl, ha⟩
  · -- a crossed row
    have hnf : ¬(fl = true ∧ (a = R - 1 ∨ a = R)) := by
      rintro ⟨hfl, ha⟩
      obtain ⟨-, h1, h2, -⟩ := hflc hfl
      rcases ha with rfl | rfl
      · exact h1 hc
      · exact h2 hc
    have hdep : ∀ x z, ([x, z] <:+: p ∨ [x, z] <:+: q) → DepOn r R fl a x z →
        ((x = (r, a) ∧ z = (r + 1, a)) ∨ (x = (r + 1, a) ∧ z = (r, a))) := by
      intro x z _ hd
      rcases depOn_cells hd with h | ⟨hfl, ha, -⟩
      · exact h
      · exact absurd ⟨hfl, ha⟩ hnf
    rcases hc with (h | h) | (h | h)
    · exact absorb_ext st hP hQ hp hq hdisj (Or.inl h) hdep (grows_crossF a)
    · exact absorb_ext st hP hQ hp hq hdisj (Or.inl h)
        (fun x z hxz hd => (hdep x z hxz hd).symm) (grows_crossB a)
    · exact absorb_ext st hP hQ hp hq hdisj (Or.inr h) hdep (grows_crossF a)
    · exact absorb_ext st hP hQ hp hq hdisj (Or.inr h)
        (fun x z hxz hd => (hdep x z hxz hd).symm) (grows_crossB a)
  · -- a flip row
    obtain ⟨hR1, hnc1, hnc2, hu⟩ := hflc hfl
    have hdep : ∀ x z, ([x, z] <:+: p ∨ [x, z] <:+: q) → DepOn r R fl a x z →
        ((x = (r, R - 1) ∧ z = (r, R)) ∨ (x = (r, R) ∧ z = (r, R - 1))) := by
      intro x z hxz hd
      rcases depOn_cells hd with h | ⟨-, -, h⟩
      · have := cross_of_pair hxz h
        rcases ha with rfl | rfl
        · exact absurd this hnc1
        · exact absurd this hnc2
      · exact h
    have dlo : decide (R ≤ R - 1) = false := by simp; omega
    have dhi : decide (R ≤ R) = true := by simp
    rcases ha with rfl | rfl
    · rw [dlo]
      rcases hu with (h | h) | (h | h)
      · exact absorb_ext st hP hQ hp hq hdisj (Or.inl h) hdep (grows_flipF_lo hR1 hfl)
      · exact absorb_ext st hP hQ hp hq hdisj (Or.inl h)
          (fun x z hxz hd => (hdep x z hxz hd).symm) (grows_flipB_lo hR1 hfl)
      · exact absorb_ext st hP hQ hp hq hdisj (Or.inr h) hdep (grows_flipF_lo hR1 hfl)
      · exact absorb_ext st hP hQ hp hq hdisj (Or.inr h)
          (fun x z hxz hd => (hdep x z hxz hd).symm) (grows_flipB_lo hR1 hfl)
    · rw [dhi]
      rcases hu with (h | h) | (h | h)
      · exact absorb_ext st hP hQ hp hq hdisj (Or.inl h) hdep (grows_flipF_hi hR1 hfl)
      · exact absorb_ext st hP hQ hp hq hdisj (Or.inl h)
          (fun x z hxz hd => (hdep x z hxz hd).symm) (grows_flipB_hi hR1 hfl)
      · exact absorb_ext st hP hQ hp hq hdisj (Or.inr h) hdep (grows_flipF_hi hR1 hfl)
      · exact absorb_ext st hP hQ hp hq hdisj (Or.inr h)
          (fun x z hxz hd => (hdep x z hxz hd).symm) (grows_flipB_hi hR1 hfl)

end

/-! ### The sweeps on the counts -/

/-- `sweepLeftE` on the counts: `c` is the anchor whose run ends at row `L`. -/
def planLeft : ℕ → Finset ℕ → (ℕ → ℕ) → ℕ → (ℕ → ℕ)
  | 0, _, K, _ => K
  | L + 1, U, K, c =>
    if L ∈ U then planLeft L (U.erase L) (Function.update K c (K c + 1)) c
    else planLeft L U K L

/-- `sweepRightE` on the counts. -/
def planRight (h : ℕ) : ℕ → ℕ → Finset ℕ → (ℕ → ℕ) → ℕ → (ℕ → ℕ)
  | 0, _, _, K, _ => K
  | n + 1, R0, U, K, c =>
    if R0 + 1 ∈ U then planRight h n (R0 + 1) (U.erase (R0 + 1)) (Function.update K c (K c + 1)) c
    else if R0 + 1 < h then planRight h n (R0 + 1) U K (R0 + 1)
    else K

section
variable {W h r : ℕ} {s0 t0 s1 t1 : Coord} {p q : List Coord}

theorem sweepLeft_ext {R : ℕ} {fl : Bool} (hp : p.Nodup) (hq : q.Nodup) (hdisj : ∀ v ∈ p, v ∉ q)
    (hflc : fl = true → 1 ≤ R ∧ ¬ Cross p q r (R - 1) ∧ ¬ Cross p q r R ∧
      (Used p (r, R - 1) (r, R) ∨ Used q (r, R - 1) (r, R))) :
    ∀ (L : ℕ) (U : Finset ℕ) (P Q : List Coord) (K : ℕ → ℕ) (c : ℕ),
      PState W h r s0 t0 s1 t1 U P Q → P = extL r K R fl p → Q = extL r K R fl q →
      Cov p q r R fl c → c < R → c - K c = L → K c ≤ c → L ∉ U →
      (∀ z, z < L → z ∉ U → Cov p q r R fl z) → (∀ z, z < L → K z = 0) →
      sweepLeftE r L U P Q = (extL r (planLeft L U K c) R fl p, extL r (planLeft L U K c) R fl q)
  | 0, U, P, Q, K, c, _, hP, hQ, _, _, _, _, _, _, _ => by
    simp [sweepLeftE, planLeft, hP, hQ]
  | L + 1, U, P, Q, K, c, st, hP, hQ, hc, hcR, hdeep, hKc, hLU, hbelow, hzero => by
    have dc : decide (R ≤ c) = false := by simp; omega
    by_cases hL : L ∈ U
    · obtain ⟨hmid, habs⟩ := absorb_anchor st hP hQ hp hq hdisj hflc hc
      rw [dc] at hmid habs
      have e1 : runRow c false (K c) = L + 1 := by simp [runRow]; omega
      have e2 : runRow c false (K c + 1) = L := by simp [runRow]; omega
      rw [e1] at hmid
      rw [e1, e2] at habs
      obtain ⟨st1, -, -⟩ := st.absorbC (y' := L + 1) hL (Or.inr rfl) hmid
      simp only [sweepLeftE, planLeft, ite_t hL]
      rw [habs] at st1 ⊢
      exact sweepLeft_ext hp hq hdisj hflc L (U.erase L) _ _ _ c st1 rfl rfl hc hcR
        (by simp only [Function.update_self]; omega) (by simp only [Function.update_self]; omega)
        (Finset.notMem_erase _ _)
        (fun z hz hzU => hbelow z (by omega) (fun h => hzU (Finset.mem_erase.mpr ⟨by omega, h⟩)))
        (fun z hz => by rw [Function.update_of_ne (by omega)]; exact hzero z (by omega))
    · simp only [sweepLeftE, planLeft, ite_f hL]
      exact sweepLeft_ext hp hq hdisj hflc L U P Q K L st hP hQ (hbelow L (by omega) hL) (by omega)
        (by rw [hzero L (by omega)]; omega) (by rw [hzero L (by omega)]; omega) hL
        (fun z hz hzU => hbelow z (by omega) hzU) (fun z hz => hzero z (by omega))

theorem sweepRight_ext {R : ℕ} {fl : Bool} (hp : p.Nodup) (hq : q.Nodup) (hdisj : ∀ v ∈ p, v ∉ q)
    (hflc : fl = true → 1 ≤ R ∧ ¬ Cross p q r (R - 1) ∧ ¬ Cross p q r R ∧
      (Used p (r, R - 1) (r, R) ∨ Used q (r, R - 1) (r, R))) :
    ∀ (n R0 : ℕ) (U : Finset ℕ) (P Q : List Coord) (K : ℕ → ℕ) (c : ℕ),
      PState W h r s0 t0 s1 t1 U P Q → P = extL r K R fl p → Q = extL r K R fl q →
      Cov p q r R fl c → R ≤ c → c + K c = R0 → R0 ∉ U →
      (∀ z, R0 < z → z < h → z ∉ U → Cov p q r R fl z) → (∀ z, R0 < z → K z = 0) →
      sweepRightE r h n R0 U P Q =
        (extL r (planRight h n R0 U K c) R fl p, extL r (planRight h n R0 U K c) R fl q)
  | 0, R0, U, P, Q, K, c, _, hP, hQ, _, _, _, _, _, _ => by
    simp [sweepRightE, planRight, hP, hQ]
  | n + 1, R0, U, P, Q, K, c, st, hP, hQ, hc, hcR, hdeep, hRU, habove, hzero => by
    have dc : decide (R ≤ c) = true := by simp; omega
    by_cases hR1 : R0 + 1 ∈ U
    · obtain ⟨hmid, habs⟩ := absorb_anchor st hP hQ hp hq hdisj hflc hc
      rw [dc] at hmid habs
      have e1 : runRow c true (K c) = R0 := by simp [runRow]; omega
      have e2 : runRow c true (K c + 1) = R0 + 1 := by simp [runRow]; omega
      rw [e1] at hmid
      rw [e1, e2] at habs
      obtain ⟨st1, -, -⟩ := st.absorbC (y' := R0) hR1 (Or.inl rfl) hmid
      simp only [sweepRightE, planRight, ite_t hR1]
      rw [habs] at st1 ⊢
      exact sweepRight_ext hp hq hdisj hflc n (R0 + 1) (U.erase (R0 + 1)) _ _ _ c st1 rfl rfl hc hcR
        (by simp only [Function.update_self]; omega) (Finset.notMem_erase _ _)
        (fun z hz hzh hzU => habove z (by omega) hzh
          (fun h => hzU (Finset.mem_erase.mpr ⟨by omega, h⟩)))
        (fun z hz => by rw [Function.update_of_ne (by omega)]; exact hzero z (by omega))
    · simp only [sweepRightE, planRight, ite_f hR1]
      by_cases hlast : R0 + 1 < h
      · simp only [ite_t hlast]
        exact sweepRight_ext hp hq hdisj hflc n (R0 + 1) U P Q K (R0 + 1) st hP hQ
          (habove (R0 + 1) (by omega) hlast hR1) (by omega) (by rw [hzero (R0 + 1) (by omega)])
          hR1 (fun z hz hzh hzU => habove z (by omega) hzh hzU) (fun z hz => hzero z (by omega))
      · simp only [ite_f hlast, hP, hQ]

end

/-! ### The flip -/

theorem insK_fl (r : ℕ) (K : ℕ → ℕ) (R : ℕ) {x z : Coord}
    (h : ¬((x = (r, R - 1) ∧ z = (r, R)) ∨ (x = (r, R) ∧ z = (r, R - 1)))) :
    insK r K R false x z = insK r K R true x z := by
  unfold insK
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp_all

theorem extL_fl_congr (r : ℕ) (K : ℕ → ℕ) (R : ℕ) (l : List Coord)
    (h : ∀ x z, [x, z] <:+: l → ¬((x = (r, R - 1) ∧ z = (r, R)) ∨ (x = (r, R) ∧ z = (r, R - 1)))) :
    extL r K R false l = extL r K R true l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    match l, ih, h with
    | [], _, _ => rfl
    | b :: l, ih, h =>
      simp only [extL]
      rw [insK_fl r K R (h a b ⟨[], l, rfl⟩), ih (fun x z hxz => h x z (hxz.trans
        (List.suffix_cons a (b :: l)).isInfix))]

theorem extL_snoc (r : ℕ) (K : ℕ → ℕ) (R : ℕ) (fl : Bool) (s : Coord) :
    ∀ L1 : List Coord, ∃ E, extL r K R fl (L1 ++ [s]) = E ++ [shiftAt r s]
  | [] => ⟨[], rfl⟩
  | [x] => ⟨[shiftAt r x] ++ insK r K R fl x s, by simp [extL]⟩
  | x :: y :: L1 => by
    obtain ⟨E, hE⟩ := extL_snoc r K R fl s (y :: L1)
    refine ⟨shiftAt r x :: (insK r K R fl x y ++ E), ?_⟩
    simp only [List.cons_append] at hE ⊢
    simp [extL, hE]

theorem extL_cons_head (r : ℕ) (K : ℕ → ℕ) (R : ℕ) (fl : Bool) (t : Coord) (L2 : List Coord) :
    ∃ E, extL r K R fl (t :: L2) = shiftAt r t :: E := by
  cases L2 with
  | nil => exact ⟨[], rfl⟩
  | cons b l => exact ⟨_, rfl⟩

theorem insK_flip_false (r : ℕ) (K : ℕ → ℕ) (R : ℕ) (y1 y2 : ℕ) :
    insK r K R false (r, y1) (r, y2) = [] := by
  unfold insK; simp

/-- The pass with the flip on, on a list holding the flip edge once. -/
theorem extL_flip_split (r : ℕ) (K : ℕ → ℕ) (R : ℕ) {L1 L2 : List Coord} {y1 y2 : ℕ}
    (hn : (L1 ++ (r, y1) :: (r, y2) :: L2).Nodup)
    (hfe : ((y1 = R - 1 ∧ y2 = R) ∨ (y1 = R ∧ y2 = R - 1))) :
    ∃ E1 E2, extL r K R false (L1 ++ (r, y1) :: (r, y2) :: L2) = E1 ++ (r, y1) :: (r, y2) :: E2 ∧
      extL r K R true (L1 ++ (r, y1) :: (r, y2) :: L2) =
        E1 ++ (r, y1) :: (insK r K R true (r, y1) (r, y2) ++ (r, y2) :: E2) := by
  have avoid : ∀ x z, ([x, z] <:+: L1 ++ [(r, y1)] ∨ [x, z] <:+: (r, y2) :: L2) →
      ¬((x = (r, R - 1) ∧ z = (r, R)) ∨ (x = (r, R) ∧ z = (r, R - 1))) := by
    intro x z hxz hf
    apply pair_avoid hn hxz
    rcases hfe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
  have c1 := extL_fl_congr r K R (L1 ++ [(r, y1)]) (fun x z h => avoid x z (Or.inl h))
  have c2 := extL_fl_congr r K R ((r, y2) :: L2) (fun x z h => avoid x z (Or.inr h))
  obtain ⟨E1, h1⟩ := extL_snoc r K R false (r, y1) L1
  obtain ⟨E2, h2⟩ := extL_cons_head r K R false (r, y2) L2
  have sh1 : shiftAt r (r, y1) = (r, y1) := by simp [shiftAt]
  have sh2 : shiftAt r (r, y2) = (r, y2) := by simp [shiftAt]
  refine ⟨E1, E2, ?_, ?_⟩
  · rw [extL_append, h1, h2, insK_flip_false, sh1, sh2]; simp
  · rw [extL_append, ← c1, ← c2, h1, h2, sh1, sh2]; simp

section
variable {W h r : ℕ} {s0 t0 s1 t1 : Coord} {U : Finset ℕ} {p q : List Coord}

/-- **The flip is the pass with the flip on.** -/
theorem flip_ext (y : ℕ) (st : PState W h r s0 t0 s1 t1 U (extL r (fun _ => 0) (y + 1) false p)
      (extL r (fun _ => 0) (y + 1) false q))
    (hp : p.Nodup) (hq : q.Nodup) (hdisj : ∀ v ∈ p, v ∉ q)
    (hu : Used p (r, y) (r, y + 1) ∨ Used q (r, y) (r, y + 1)) :
    flipE r y (extL r (fun _ => 0) (y + 1) false p) (extL r (fun _ => 0) (y + 1) false q) =
      (extL r (fun _ => 0) (y + 1) true p, extL r (fun _ => 0) (y + 1) true q) := by
  set P := extL r (fun _ => 0) (y + 1) false p with hP
  set Q := extL r (fun _ => 0) (y + 1) false q with hQ
  have hPn : P.Nodup := st.pp.2.2.1
  have hQn : Q.Nodup := st.pq.2.2.1
  have hy : y + 1 - 1 = y := by omega
  have insF : insK r (fun _ => 0) (y + 1) true (r, y) (r, y + 1) =
      [(r + 1, y), (r + 2, y), (r + 2, y + 1), (r + 1, y + 1)] := by
    unfold insK; simp [Gf, Gb, runRow]
  have insB' : insK r (fun _ => 0) (y + 1) true (r, y + 1) (r, y) =
      [(r + 1, y + 1), (r + 2, y + 1), (r + 2, y), (r + 1, y)] := by
    unfold insK; simp [Gf, Gb, runRow]
  have fe1 : ((y = y + 1 - 1 ∧ y + 1 = y + 1) ∨ (y = y + 1 ∧ y + 1 = y + 1 - 1)) := by omega
  have fe2 : ((y + 1 = y + 1 - 1 ∧ y = y + 1) ∨ (y + 1 = y + 1 ∧ y = y + 1 - 1)) := by omega
  have otherl : ∀ (m : List Coord) (y1 y2 : ℕ), (r, y1) ∉ m →
      ((y1 = y ∧ y2 = y + 1) ∨ (y1 = y + 1 ∧ y2 = y)) →
      extL r (fun _ => 0) (y + 1) false m = extL r (fun _ => 0) (y + 1) true m := by
    intro m y1 y2 hm hy12
    refine extL_fl_congr r _ (y + 1) m (fun x z hxz hf => ?_)
    have hmem := mem_of_infix_pair hxz
    rw [hy] at hf
    rcases hy12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      first | exact hm hmem.1 | exact hm hmem.2
  unfold flipE spliceE
  rcases hu with (h | h) | (h | h)
  · obtain ⟨L1, L2, rfl⟩ := infix_pair_iff.mp h
    obtain ⟨E1, E2, e0, e1⟩ := extL_flip_split r (fun _ => 0) (y + 1) hp fe1
    have hin : [(r, y), (r, y + 1)] <:+: P := by rw [hP, e0]; exact ⟨E1, E2, by simp⟩
    rw [ite_t (Or.inl hin), ite_t hin, hQ, otherl q y (y + 1) (hdisj _ (by simp)) (Or.inl ⟨rfl, rfl⟩)]
    congr 1
    rw [hP, e0] at hPn ⊢
    rw [e1, insB_nodup _ _ _ _ _ hPn, insF]
  · obtain ⟨L1, L2, rfl⟩ := infix_pair_iff.mp h
    obtain ⟨E1, E2, e0, e1⟩ := extL_flip_split r (fun _ => 0) (y + 1) hp fe2
    have hin : [(r, y + 1), (r, y)] <:+: P := by rw [hP, e0]; exact ⟨E1, E2, by simp⟩
    have hnot : ¬([(r, y), (r, y + 1)] <:+: P ∨ [(r, y), (r, y + 1)] <:+: Q) := by
      rintro (h | h)
      · exact no_rev_pair hPn h hin
      · exact st.disj _ (mem_of_infix_pair hin).2 (mem_of_infix_pair h).1
    rw [ite_f hnot, ite_t hin, hQ, otherl q (y + 1) y (hdisj _ (by simp)) (Or.inr ⟨rfl, rfl⟩)]
    congr 1
    rw [hP, e0] at hPn ⊢
    rw [e1, insB_nodup _ _ _ _ _ hPn, insB']
  · obtain ⟨L1, L2, rfl⟩ := infix_pair_iff.mp h
    obtain ⟨E1, E2, e0, e1⟩ := extL_flip_split r (fun _ => 0) (y + 1) hq fe1
    have hin : [(r, y), (r, y + 1)] <:+: Q := by rw [hQ, e0]; exact ⟨E1, E2, by simp⟩
    have hnP : ¬ [(r, y), (r, y + 1)] <:+: P := fun h =>
      st.disj _ (mem_of_infix_pair h).1 (mem_of_infix_pair hin).1
    rw [ite_t (Or.inr hin), ite_f hnP, hP,
      otherl p y (y + 1) (fun h => hdisj _ h (by simp)) (Or.inl ⟨rfl, rfl⟩)]
    congr 1
    rw [hQ, e0] at hQn ⊢
    rw [e1, insB_nodup _ _ _ _ _ hQn, insF]
  · obtain ⟨L1, L2, rfl⟩ := infix_pair_iff.mp h
    obtain ⟨E1, E2, e0, e1⟩ := extL_flip_split r (fun _ => 0) (y + 1) hq fe2
    have hin : [(r, y + 1), (r, y)] <:+: Q := by rw [hQ, e0]; exact ⟨E1, E2, by simp⟩
    have hnot : ¬([(r, y), (r, y + 1)] <:+: P ∨ [(r, y), (r, y + 1)] <:+: Q) := by
      rintro (h | h)
      · exact st.disj _ (mem_of_infix_pair h).1 (mem_of_infix_pair hin).2
      · exact no_rev_pair hQn h hin
    have hnP : ¬ [(r, y + 1), (r, y)] <:+: P := fun h =>
      st.disj _ (mem_of_infix_pair h).1 (mem_of_infix_pair hin).1
    rw [ite_f hnot, ite_f hnP, hP,
      otherl p (y + 1) y (fun h => hdisj _ h (by simp)) (Or.inr ⟨rfl, rfl⟩)]
    congr 1
    rw [hQ, e0] at hQn ⊢
    rw [e1, insB_nodup _ _ _ _ _ hQn, insB']

end

/-! ### The whole band -/

theorem planLeft_above : ∀ (L : ℕ) (U : Finset ℕ) (K : ℕ → ℕ) (c z : ℕ), L ≤ c → c < z →
    planLeft L U K c z = K z
  | 0, _, _, _, _, _, _ => rfl
  | L + 1, U, K, c, z, hLc, hcz => by
    simp only [planLeft]
    split_ifs
    · rw [planLeft_above L _ _ c z (by omega) hcz, Function.update_of_ne (by omega)]
    · exact planLeft_above L U K L z le_rfl (by omega)

/-- Both paths through the pass. -/
def extP (r : ℕ) (K : ℕ → ℕ) (R : ℕ) (fl : Bool) (p q : List Coord) : List Coord × List Coord :=
  (extL r K R fl p, extL r K R fl q)

/-- **Band extension in one pass**: the seed and the sweeps of `bandExtE` run on the counts,
then one pass over each path. -/
def bandExtL (I : Inst) (r : ℕ) (p q : List Coord) : List Coord × List Coord :=
  let U0 := (Finset.range I.h).filter (fun y => ¬ Cross p q r y)
  match (List.range (I.h + 1)).find? (fun R => decide (SeedAt I.h p q r R)) with
  | none => (stretch r p, stretch r q)
  | some R =>
    if (R = 0 ∨ Cross p q r (R - 1)) ∧ (R = I.h ∨ Cross p q r R) then
      if R = 0 then extP r (planRight I.h (I.h - 0) 0 U0 (fun _ => 0) 0) R false p q
      else if R = I.h then extP r (planLeft (R - 1) U0 (fun _ => 0) (R - 1)) R false p q
      else extP r (planRight I.h (I.h - R) R (U0.filter (R - 1 < ·))
        (planLeft (R - 1) U0 (fun _ => 0) (R - 1)) R) R false p q
    else
      extP r (planRight I.h (I.h - (R - 1 + 1)) (R - 1 + 1)
        (((U0.erase (R - 1)).erase (R - 1 + 1)).filter (R - 1 < ·))
        (planLeft (R - 1) ((U0.erase (R - 1)).erase (R - 1 + 1)) (fun _ => 0) (R - 1)) (R - 1 + 1))
        R true p q

/-- **The one-pass band extension equals `bandExtE`** on a solution with line `r` free. -/
theorem bandExtL_eq {I : Inst} {p q : List Coord} {r : ℕ} (hsol : IsSolution I p q) (hr : r < I.w)
    (hfree : LineFree I r) : bandExtL I r p q = bandExtE I r p q := by
  have hh : 0 < I.h := by
    have hs0 : I.s0 ∈ p := List.mem_of_mem_head? hsol.1.1
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) (hsol.1.2.2.2.1 _ hs0).2
  have hp : p.Nodup := hsol.1.2.2.1
  have hq : q.Nodup := hsol.2.1.2.2.1
  have hdisj : ∀ v ∈ p, v ∉ q := hsol.2.2.1
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
  have z0 : ∀ R', stretch r p = extL r (fun _ => 0) R' false p := fun R' => (extL_zero r R' p).symm
  have z0q : ∀ R', stretch r q = extL r (fun _ => 0) R' false q := fun R' => (extL_zero r R' q).symm
  unfold bandExtE bandExtL
  simp only [hf]
  rw [← hU0]
  by_cases hc1 : (R = 0 ∨ Cross p q r (R - 1)) ∧ (R = I.h ∨ Cross p q r R)
  · rw [ite_t hc1, ite_t hc1]
    obtain ⟨hl, hrt⟩ := hc1
    have hflc : false = true → 1 ≤ R ∧ ¬ Cross p q r (R - 1) ∧ ¬ Cross p q r R ∧
        (Used p (r, R - 1) (r, R) ∨ Used q (r, R - 1) (r, R)) := by simp
    by_cases hR0 : R = 0
    · subst hR0
      rw [ite_t rfl, ite_t rfl]
      have hc0 : Cross p q r 0 := hrt.resolve_left (by omega)
      rw [sweepRight_ext hp hq hdisj hflc (I.h - 0) 0 U0 _ _ (fun _ => 0) 0 st0 (z0 0) (z0q 0)
        (Or.inl hc0) le_rfl rfl (fun h => (inU 0 h).2 hc0)
        (fun z _ hzh hzU => Or.inl (notU z hzh hzU)) (fun _ _ => rfl)]
      rfl
    · rw [ite_f hR0, ite_f hR0]
      have hcL : Cross p q r (R - 1) := hl.resolve_left hR0
      have eL := sweepLeft_ext hp hq hdisj hflc (R - 1) U0 _ _ (fun _ => 0) (R - 1) st0 (z0 R)
        (z0q R) (Or.inl hcL) (by omega) rfl (Nat.zero_le _) (fun h => (inU _ h).2 hcL)
        (fun z hz hzU => Or.inl (notU z (by omega) hzU)) (fun _ _ => rfl)
      by_cases hRh' : R = I.h
      · rw [ite_t hRh', ite_t hRh', eL]
        rfl
      · rw [ite_f hRh', ite_f hRh']
        have hcR : Cross p q r R := hrt.resolve_left hRh'
        obtain ⟨st1, -⟩ := PState.sweepLeftC (R - 1) U0 _ _ st0
          (fun h => (inU _ h).2 hcL) (midC _ hcL)
          (fun z hz hzU => midC z (notU z (by omega) hzU))
        rw [eL] at st1 ⊢
        rw [sweepRight_ext hp hq hdisj hflc (I.h - R) R (U0.filter (R - 1 < ·)) _ _ _ R st1 rfl rfl
          (Or.inl hcR) le_rfl (by rw [planLeft_above _ _ _ _ _ le_rfl (by omega), Nat.add_zero])
          (fun h => (inU R (Finset.mem_filter.mp h).1).2 hcR)
          (fun z hz hzh hzU => Or.inl (notU z hzh (fun h => hzU (Finset.mem_filter.mpr ⟨h, by omega⟩))))
          (fun z hz => by rw [planLeft_above _ _ _ _ _ le_rfl (by omega)])]
        rfl
  · rw [ite_f hc1, ite_f hc1]
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
    have hflc : true = true → 1 ≤ y + 1 ∧ ¬ Cross p q r (y + 1 - 1) ∧ ¬ Cross p q r (y + 1) ∧
        (Used p (r, y + 1 - 1) (r, y + 1) ∨ Used q (r, y + 1 - 1) (r, y + 1)) := by
      intro _; simp only [Nat.add_sub_cancel]; exact ⟨by omega, hnc1, hnc, hu⟩
    have eF : flipE r y (stretch r p) (stretch r q) =
        (extL r (fun _ => 0) (y + 1) true p, extL r (fun _ => 0) (y + 1) true q) := by
      have := flip_ext (p := p) (q := q) y (by rw [← z0, ← z0q]; exact st0) hp hq hdisj hu
      rw [← z0, ← z0q] at this; exact this
    have outU1 : ∀ z, z ≠ y → z ≠ y + 1 → z ∉ (U0.erase y).erase (y + 1) → z ∉ U0 := by
      intro z h1 h2 hz hz0
      exact hz (Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, hz0⟩⟩)
    obtain ⟨st2, keep2⟩ := PState.sweepLeftC y _ _ _ st1
      (fun h => Finset.notMem_erase y U0 (Finset.mem_of_mem_erase h)) m1
      (fun z hz hzU => keep1 z (midC z (notU z (by omega)
        (outU1 z (by omega) (by omega) hzU))))
    rw [eF] at st1 st2 ⊢
    have covy : Cov p q r (y + 1) true y := Or.inr ⟨rfl, Or.inl (by omega)⟩
    have covy1 : Cov p q r (y + 1) true (y + 1) := Or.inr ⟨rfl, Or.inr rfl⟩
    have eL := sweepLeft_ext hp hq hdisj hflc y _ _ _ (fun _ => 0) y st1 rfl rfl covy (by omega) rfl
      (Nat.zero_le _) (fun h => Finset.notMem_erase y U0 (Finset.mem_of_mem_erase h))
      (fun z hz hzU => Or.inl (notU z (by omega) (outU1 z (by omega) (by omega) hzU))) (fun _ _ => rfl)
    rw [eL] at st2 ⊢
    rw [sweepRight_ext hp hq hdisj hflc (I.h - (y + 1)) (y + 1) _ _ _ _ (y + 1) st2 rfl rfl covy1 le_rfl
      (by rw [planLeft_above _ _ _ _ _ le_rfl (by omega), Nat.add_zero])
      (fun h => Finset.notMem_erase (y + 1) _ (Finset.mem_filter.mp h).1)
      (fun z hz hzh hzU => Or.inl (notU z hzh
        (outU1 z (by omega) (by omega) (fun h => hzU (Finset.mem_filter.mpr ⟨h, by omega⟩)))))
      (fun z hz => by rw [planLeft_above _ _ _ _ _ le_rfl (by omega)])]
    rfl

end ZZN

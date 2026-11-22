/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Constr.EdgeBlock

@[expose] public section

/-!
# The wide band: inserting `2j` lines after a free line in one pass

`insMany G L` walks `L` once and inserts the list `G a b` between each consecutive pair `a, b`.
If the inserted lists are fresh, pairwise disjoint and each closes a chain `a, G a b, b`, the
result is a path through `L` and all inserted cells (`insMany_nodup`, `insMany_chain`,
`mem_insMany`).

The wide band applies this to a solution with its cells right of the free line `r` shifted by
`2j`. At a crossing edge in row `y` it inserts a column snake over the `2j` new columns and the
rows `y` and the uncovered rows attached to `y`. Rows below the seed `R` attach to the nearest
crossing row above them, rows above `R` to the nearest one below. In the flip case the vertical
edge `(r, R - 1) – (r, R)` takes two snakes, one per row group.
-/

namespace ZZN

open GridHam

/-! ### Inserting between consecutive cells -/

/-- Insert `G a b` between each consecutive pair `a, b` of the list. -/
def insMany (G : Coord → Coord → List Coord) : List Coord → List Coord
  | a :: b :: l => a :: (G a b ++ insMany G (b :: l))
  | l => l

section
variable (G : Coord → Coord → List Coord)

theorem insMany_cons (b : Coord) : ∀ l : List Coord, ∃ t, insMany G (b :: l) = b :: t
  | [] => ⟨[], rfl⟩
  | c :: l => ⟨G b c ++ insMany G (c :: l), rfl⟩

theorem insMany_head : ∀ l : List Coord, (insMany G l).head? = l.head?
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

theorem insMany_getLast : ∀ l : List Coord, (insMany G l).getLast? = l.getLast?
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    have ih := insMany_getLast (b :: l)
    obtain ⟨t, ht⟩ := insMany_cons G b l
    rw [ht] at ih
    rw [insMany, ht, ← List.cons_append, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _), ih,
      List.getLast?_cons_cons]

theorem mem_insMany : ∀ (l : List Coord) (v : Coord),
    v ∈ insMany G l ↔ v ∈ l ∨ ∃ a b, [a, b] <:+: l ∧ v ∈ G a b
  | [], v => by simp [insMany]
  | [x], v => by
    simp only [insMany, List.mem_singleton]
    constructor
    · exact Or.inl
    · rintro (h | ⟨a, b, hab, -⟩)
      · exact h
      · exfalso
        obtain ⟨s, t, he⟩ := infix_pair_iff.mp hab
        have := congrArg List.length he
        simp at this
        omega
  | a :: b :: l, v => by
    rw [insMany, List.mem_cons, List.mem_append, mem_insMany (b :: l) v]
    constructor
    · rintro (h | h | h | ⟨a', b', hab, hv⟩)
      · exact Or.inl (h ▸ List.mem_cons_self)
      · exact Or.inr ⟨a, b, ⟨[], l, rfl⟩, h⟩
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr ⟨a', b', hab.trans (List.suffix_cons a _).isInfix, hv⟩
    · rintro (h | ⟨a', b', hab, hv⟩)
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
      · obtain ⟨s, t, he⟩ := infix_pair_iff.mp hab
        cases s with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at he
          obtain ⟨rfl, rfl, -⟩ := he
          exact Or.inr (Or.inl hv)
        | cons z s =>
          simp only [List.cons_append, List.cons.injEq] at he
          exact Or.inr (Or.inr (Or.inr ⟨a', b', infix_pair_iff.mpr ⟨s, t, he.2⟩, hv⟩))

theorem insMany_chain : ∀ (l : List Coord),
    (∀ a b, [a, b] <:+: l → chainAdjacent (a :: (G a b ++ [b])) = true) →
    chainAdjacent (insMany G l) = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    have ih := insMany_chain (b :: l)
      (fun a' b' hab => h a' b' (hab.trans (List.suffix_cons a _).isInfix))
    obtain ⟨t, ht⟩ := insMany_cons G b l
    rw [ht] at ih
    rw [insMany, ht, ← List.cons_append, chainAdjacent_append_cons, Bool.and_eq_true]
    exact ⟨by simpa using h a b ⟨[], l, rfl⟩, ih⟩

theorem insMany_nodup : ∀ (l : List Coord), l.Nodup →
    (∀ a b, [a, b] <:+: l → (G a b).Nodup ∧ ∀ x ∈ G a b, x ∉ l) →
    (∀ a b a' b', [a, b] <:+: l → [a', b'] <:+: l → a ≠ a' → ∀ x ∈ G a b, x ∉ G a' b') →
    (insMany G l).Nodup
  | [], h, _, _ => h
  | [_], h, _, _ => h
  | a :: b :: l, hn, hG, hd => by
    have sub : ∀ {a' b'}, [a', b'] <:+: b :: l → [a', b'] <:+: a :: b :: l :=
      fun hab => hab.trans (List.suffix_cons a _).isInfix
    have h0 : [a, b] <:+: a :: b :: l := ⟨[], l, rfl⟩
    have ih := insMany_nodup (b :: l) (List.nodup_cons.mp hn).2
      (fun a' b' hab => ⟨(hG a' b' (sub hab)).1,
        fun x hx hxl => (hG a' b' (sub hab)).2 x hx (List.mem_cons_of_mem _ hxl)⟩)
      (fun a1 b1 a2 b2 h1 h2 hne => hd a1 b1 a2 b2 (sub h1) (sub h2) hne)
    have ha : a ∉ b :: l := (List.nodup_cons.mp hn).1
    have pairMem : ∀ {a' b'}, [a', b'] <:+: b :: l → a' ∈ b :: l :=
      fun hab => hab.subset (by simp)
    rw [insMany, List.nodup_cons, List.nodup_append]
    refine ⟨?_, (hG a b h0).1, ih, ?_⟩
    · rw [List.mem_append, mem_insMany]
      rintro (h | h | ⟨a', b', hab, hx⟩)
      · exact (hG a b h0).2 a h List.mem_cons_self
      · exact ha h
      · exact (hG a' b' (sub hab)).2 a hx List.mem_cons_self
    · intro x hx y hy hxy
      subst hxy
      rcases (mem_insMany G _ x).mp hy with h | ⟨a', b', hab, hx'⟩
      · exact (hG a b h0).2 x hx (List.mem_cons_of_mem _ h)
      · exact hd a b a' b' h0 (sub hab) (fun e => ha (e ▸ pairMem hab)) x hx hx'

end

/-! ### Rows attached to an anchor -/

/-- The rows `a - 1, a - 2, …` below `a`, while `cv` is false. -/
def runDn (cv : ℕ → Bool) : ℕ → List ℕ
  | 0 => []
  | n + 1 => if cv n then [] else n :: runDn cv n

/-- The rows `y, y + 1, …`, at most `k` of them, while `cv` is false. -/
def runUpF (cv : ℕ → Bool) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, y => if cv y then [] else y :: runUpF cv k (y + 1)

/-- The rows `a + 1, a + 2, …` below `h`, while `cv` is false. -/
def runUp (cv : ℕ → Bool) (h a : ℕ) : List ℕ := runUpF cv (h - (a + 1)) (a + 1)

section
variable {cv : ℕ → Bool}

theorem mem_runDn : ∀ {a y : ℕ}, y ∈ runDn cv a ↔ y < a ∧ ∀ z, y ≤ z → z < a → cv z = false
  | 0, y => by simp [runDn]
  | n + 1, y => by
    unfold runDn
    split_ifs with hc
    · simp only [List.not_mem_nil, false_iff, not_and]
      intro hy hz
      have := hz n (by omega) (by omega)
      rw [hc] at this; simp at this
    · rw [List.mem_cons, mem_runDn]
      constructor
      · rintro (rfl | ⟨hy, hz⟩)
        · refine ⟨by omega, fun z h1 h2 => ?_⟩
          obtain rfl : z = y := by omega
          simpa using hc
        · refine ⟨by omega, fun z h1 h2 => ?_⟩
          by_cases e : z = n
          · subst e; simpa using hc
          · exact hz z h1 (by omega)
      · rintro ⟨hy, hz⟩
        by_cases e : y = n
        · exact Or.inl e
        · exact Or.inr ⟨by omega, fun z h1 h2 => hz z h1 (by omega)⟩

theorem mem_runUpF : ∀ {k y x : ℕ}, x ∈ runUpF cv k y ↔
    y ≤ x ∧ x < y + k ∧ ∀ z, y ≤ z → z ≤ x → cv z = false
  | 0, y, x => by simp [runUpF]; omega
  | k + 1, y, x => by
    unfold runUpF
    split_ifs with hc
    · simp only [List.not_mem_nil, false_iff, not_and]
      intro hy _ hz
      have := hz y le_rfl hy
      rw [hc] at this; simp at this
    · rw [List.mem_cons, mem_runUpF]
      constructor
      · rintro (rfl | ⟨hy, hk, hz⟩)
        · refine ⟨le_rfl, by omega, fun z h1 h2 => ?_⟩
          obtain rfl : z = x := by omega
          simpa using hc
        · refine ⟨by omega, by omega, fun z h1 h2 => ?_⟩
          by_cases e : z = y
          · subst e; simpa using hc
          · exact hz z (by omega) h2
      · rintro ⟨hy, hk, hz⟩
        by_cases e : x = y
        · exact Or.inl e
        · exact Or.inr ⟨by omega, by omega, fun z h1 h2 => hz z (by omega) h2⟩

theorem mem_runUp {h a x : ℕ} : x ∈ runUp cv h a ↔
    a < x ∧ x < h ∧ ∀ z, a < z → z ≤ x → cv z = false := by
  unfold runUp
  rw [mem_runUpF]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, by omega, fun z a1 a2 => h3 z (by omega) a2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, by omega, fun z a1 a2 => h3 z (by omega) a2⟩

theorem steps_runDn : ∀ a, Steps (a :: runDn cv a)
  | 0 => trivial
  | n + 1 => by
    unfold runDn
    split_ifs
    · trivial
    · exact ⟨Or.inr rfl, steps_runDn n⟩

theorem steps_runUpF : ∀ k a, Steps (a :: runUpF cv k (a + 1))
  | 0, _ => trivial
  | k + 1, a => by
    unfold runUpF
    split_ifs
    · trivial
    · exact ⟨Or.inl rfl, steps_runUpF k (a + 1)⟩

theorem nodup_runDn {a : ℕ} : (a :: runDn cv a).Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  have : ∀ a, (a :: runDn cv a).Pairwise (· > ·) := by
    intro a
    induction a with
    | zero => simp [runDn]
    | succ n ih =>
      unfold runDn
      split_ifs
      · simp
      · refine List.Pairwise.cons (fun z hz => ?_) ih
        rcases List.mem_cons.mp hz with rfl | hz
        · omega
        · have := (mem_runDn.mp hz).1; omega
  exact (this a).imp (fun h => Nat.ne_of_gt h)

theorem nodup_runUp {h a : ℕ} : (a :: runUp cv h a).Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  have : ∀ k a, (a :: runUpF cv k (a + 1)).Pairwise (· < ·) := by
    intro k
    induction k with
    | zero => intro a; simp [runUpF]
    | succ k ih =>
      intro a
      unfold runUpF
      split_ifs
      · simp
      · refine List.Pairwise.cons (fun z hz => ?_) (ih (a + 1))
        rcases List.mem_cons.mp hz with rfl | hz
        · omega
        · have := (mem_runUpF.mp hz).1; omega
  exact (this _ a).imp (fun h => Nat.ne_of_lt h)

end

/-! ### The wide band -/

/-- Shift the cells right of line `r` by `W`. -/
def shW (r W : ℕ) (v : Coord) : Coord := if v.1 ≤ r then v else (v.1 + W, v.2)

/-- The instance with `W` lines inserted after line `x = r`. -/
def Inst.insertW (I : Inst) (r W : ℕ) : Inst :=
  ⟨I.w + W, I.h, shW r W I.s0, shW r W I.t0, shW r W I.s1, shW r W I.t1⟩

/-- The rows attached to the anchor `a`: below it if `a < R`, above it otherwise. -/
def attW (cv : ℕ → Bool) (h R a : ℕ) : List ℕ := if a < R then runDn cv a else runUp cv h a

/-- The anchor row `a` and its attached rows. -/
def grpW (cv : ℕ → Bool) (h R a : ℕ) : List ℕ := a :: attW cv h R a

/-- The snake over the new columns `r + 1 … r + 2j` and the rows of anchor `a`, from `(r + 1, a)`
to `(r + 2j, a)`. -/
def snW (r j h R : ℕ) (cv : ℕ → Bool) (a : ℕ) : List Coord := colSnake (r + 1) (grpW cv h R a) j

/-- The flip block, from `(r + 1, R - 1)` to `(r + 1, R)`. -/
def flipW (r j h R : ℕ) (cv : ℕ → Bool) : List Coord :=
  snW r j h R cv (R - 1) ++ (snW r j h R cv R).reverse

/-- What to insert between consecutive shifted cells `u, v`. -/
def GW (r j h R : ℕ) (flip : Bool) (cv : ℕ → Bool) (u v : Coord) : List Coord :=
  if u.1 = r ∧ v.1 = r + 2 * j + 1 ∧ u.2 = v.2 then snW r j h R cv u.2
  else if u.1 = r + 2 * j + 1 ∧ v.1 = r ∧ u.2 = v.2 then (snW r j h R cv u.2).reverse
  else if flip = true ∧ u = (r, R - 1) ∧ v = (r, R) then flipW r j h R cv
  else if flip = true ∧ u = (r, R) ∧ v = (r, R - 1) then (flipW r j h R cv).reverse
  else []

/-- **The wide band**: shift, then insert in one pass. -/
def wideExt (r j h R : ℕ) (flip : Bool) (cv : ℕ → Bool) (L : List Coord) : List Coord :=
  insMany (GW r j h R flip cv) (L.map (shW r (2 * j)))

section
variable {cv : ℕ → Bool} {r j h R : ℕ}

theorem steps_grpW (a : ℕ) : Steps (grpW cv h R a) := by
  unfold grpW attW
  split_ifs
  · exact steps_runDn a
  · exact steps_runUpF _ a

theorem nodup_grpW (a : ℕ) : (grpW cv h R a).Nodup := by
  unfold grpW attW
  split_ifs
  · exact nodup_runDn
  · exact nodup_runUp

/-- Attached rows are not covered. -/
theorem attW_cv {a x : ℕ} (hx : x ∈ attW cv h R a) : cv x = false := by
  unfold attW at hx
  split_ifs at hx
  · exact (mem_runDn.mp hx).2 x le_rfl (mem_runDn.mp hx).1
  · exact (mem_runUp.mp hx).2.2 x (mem_runUp.mp hx).1 le_rfl

theorem attW_lt {a x : ℕ} (ha : a < h) (hx : x ∈ attW cv h R a) : x < h := by
  unfold attW at hx
  split_ifs at hx
  · have := (mem_runDn.mp hx).1; omega
  · exact (mem_runUp.mp hx).2.1

/-- **Groups of distinct covered anchors are disjoint.** -/
theorem grpW_disj {a a' x : ℕ} (ha : cv a = true) (ha' : cv a' = true) (hne : a ≠ a')
    (hx : x ∈ grpW cv h R a) (hx' : x ∈ grpW cv h R a') : False := by
  unfold grpW at hx hx'
  rcases List.mem_cons.mp hx with rfl | hx <;> rcases List.mem_cons.mp hx' with rfl | hx'
  · exact hne rfl
  · rw [attW_cv hx'] at ha; simp at ha
  · rw [attW_cv hx] at ha'; simp at ha'
  · unfold attW at hx hx'
    split_ifs at hx hx' with h1 h2 h2
    · obtain ⟨y1, z1⟩ := mem_runDn.mp hx
      obtain ⟨y2, z2⟩ := mem_runDn.mp hx'
      rcases Nat.lt_or_gt_of_ne hne with l | l
      · rw [z2 a (by omega) l] at ha; simp at ha
      · rw [z1 a' (by omega) l] at ha'; simp at ha'
    · have := (mem_runDn.mp hx).1; have := (mem_runUp.mp hx').1; omega
    · have := (mem_runUp.mp hx).1; have := (mem_runDn.mp hx').1; omega
    · obtain ⟨y1, -, z1⟩ := mem_runUp.mp hx
      obtain ⟨y2, -, z2⟩ := mem_runUp.mp hx'
      rcases Nat.lt_or_gt_of_ne hne with l | l
      · rw [z1 a' l (by omega)] at ha'; simp at ha'
      · rw [z2 a l (by omega)] at ha; simp at ha

/-- **Every uncovered row is attached to a covered anchor**, when the rows next to `R` are
covered (or walls). -/
theorem exists_anchor (hR : R ≤ h) (hlo : R = 0 ∨ cv (R - 1) = true) (hhi : R = h ∨ cv R = true)
    {y : ℕ} (hy : y < h) (hc : cv y = false) :
    ∃ a, cv a = true ∧ a < h ∧ y ∈ attW cv h R a := by
  by_cases hyR : y < R
  · have hR1 : cv (R - 1) = true := hlo.resolve_left (by omega)
    have hne : y ≠ R - 1 := fun e => by rw [e, hR1] at hc; simp at hc
    have hex : ∃ z, y < z ∧ cv z = true := ⟨R - 1, by omega, hR1⟩
    classical
    let a := Nat.find hex
    have ha : y < a ∧ cv a = true := Nat.find_spec hex
    have haR : a ≤ R - 1 := Nat.find_min' hex ⟨by omega, hR1⟩
    refine ⟨a, ha.2, by omega, ?_⟩
    unfold attW
    rw [ite_t (show a < R by omega), mem_runDn]
    refine ⟨ha.1, fun z h1 h2 => ?_⟩
    by_cases e : z = y
    · subst e; exact hc
    · have := Nat.find_min hex h2
      simp only [not_and, Bool.not_eq_true] at this
      exact this (by omega)
  · have hRh : R < h := by omega
    have hR : cv R = true := hhi.resolve_left (by omega)
    have hex : ∃ k, k ≤ y ∧ cv (y - k) = true := ⟨y - R, by omega, by
      rw [show y - (y - R) = R by omega]; exact hR⟩
    classical
    let k := Nat.find hex
    have hk : k ≤ y ∧ cv (y - k) = true := Nat.find_spec hex
    have hkR : k ≤ y - R := Nat.find_min' hex ⟨by omega, by
      rw [show y - (y - R) = R by omega]; exact hR⟩
    have hk0 : k ≠ 0 := by
      intro e
      have := hk.2
      rw [e, Nat.sub_zero, hc] at this; simp at this
    refine ⟨y - k, hk.2, by omega, ?_⟩
    unfold attW
    rw [ite_f (show ¬ y - k < R by omega), mem_runUp]
    refine ⟨by omega, hy, fun z h1 h2 => ?_⟩
    have := Nat.find_min hex (show y - z < k by omega)
    simp only [not_and, Bool.not_eq_true] at this
    rw [show z = y - (y - z) by omega]
    exact this (by omega)

theorem mem_snW {a : ℕ} {v : Coord} :
    v ∈ snW r j h R cv a ↔ r + 1 ≤ v.1 ∧ v.1 < r + 1 + 2 * j ∧ v.2 ∈ grpW cv h R a :=
  mem_colSnake

theorem snW_head (a : ℕ) (hj : 0 < j) : (snW r j h R cv a).head? = some (r + 1, a) :=
  colSnake_head rfl j hj

theorem snW_last (a : ℕ) (hj : 0 < j) : (snW r j h R cv a).getLast? = some (r + 2 * j, a) := by
  rw [snW, colSnake_last rfl j hj]
  congr 2
  omega

theorem snW_chain (a : ℕ) : chainAdjacent (snW r j h R cv a) = true :=
  colSnake_chain (steps_grpW a) (List.cons_ne_nil _ _) j

theorem snW_nodup (a : ℕ) : (snW r j h R cv a).Nodup := colSnake_nodup (nodup_grpW a) j

theorem snW_ne_nil (a : ℕ) (hj : 0 < j) : snW r j h R cv a ≠ [] := by
  intro he
  have := snW_head (cv := cv) (r := r) (h := h) (R := R) a hj
  rw [he] at this; simp at this

/-- The snake closes the crossing `(r, y) – (r + 2j + 1, y)`. -/
theorem snW_cross_chain (y : ℕ) (hj : 0 < j) :
    chainAdjacent ((r, y) :: (snW r j h R cv y ++ [(r + 2 * j + 1, y)])) = true := by
  have c1 : chainAdjacent ([(r, y)] ++ snW r j h R cv y) = true :=
    chainAdjacent_append_of (a := (r, y)) (b := (r + 1, y)) rfl (snW_chain y) rfl
      (snW_head y hj) (Or.inr ⟨rfl, Or.inl rfl⟩)
  have c2 := chainAdjacent_append_of (a := (r + 2 * j, y)) (b := (r + 2 * j + 1, y)) c1
    (show chainAdjacent [(r + 2 * j + 1, y)] = true from rfl)
    (by rw [List.getLast?_append_of_ne_nil _ (snW_ne_nil y hj)]; exact snW_last y hj) rfl
    (Or.inr ⟨rfl, Or.inl rfl⟩)
  simpa using c2

/-- The flip block closes the step `(r, R - 1) – (r, R)`. -/
theorem flipW_chain (hj : 0 < j) (hR : 1 ≤ R) :
    chainAdjacent ((r, R - 1) :: (flipW r j h R cv ++ [(r, R)])) = true := by
  have c1 : chainAdjacent ([(r, R - 1)] ++ snW r j h R cv (R - 1)) = true :=
    chainAdjacent_append_of (a := (r, R - 1)) (b := (r + 1, R - 1)) rfl (snW_chain _) rfl
      (snW_head _ hj) (Or.inr ⟨rfl, Or.inl rfl⟩)
  have c2 : chainAdjacent (([(r, R - 1)] ++ snW r j h R cv (R - 1)) ++
      (snW r j h R cv R).reverse) = true :=
    chainAdjacent_append_of (a := (r + 2 * j, R - 1)) (b := (r + 2 * j, R)) c1
      (chainAdjacent_reverse _ (snW_chain R))
      (by rw [List.getLast?_append_of_ne_nil _ (snW_ne_nil _ hj)]; exact snW_last _ hj)
      (by rw [List.head?_reverse]; exact snW_last R hj)
      (Or.inl ⟨rfl, Or.inl (by omega)⟩)
  have c3 := chainAdjacent_append_of (a := (r + 1, R)) (b := (r, R)) c2
    (show chainAdjacent [(r, R)] = true from rfl)
    (by
      rw [List.getLast?_append_of_ne_nil _ (by
        rw [Ne, List.reverse_eq_nil_iff]; exact snW_ne_nil R hj)]
      rw [List.getLast?_reverse]; exact snW_head R hj)
    rfl (Or.inr ⟨rfl, Or.inr rfl⟩)
  simpa [flipW] using c3

theorem flipW_nodup (h1 : cv (R - 1) = true) (h2 : cv R = true) (hR : 1 ≤ R) :
    (flipW r j h R cv).Nodup := by
  unfold flipW
  rw [List.nodup_append]
  refine ⟨snW_nodup _, List.nodup_reverse.mpr (snW_nodup _), ?_⟩
  intro x hx y hy hxy
  subst hxy
  rw [List.mem_reverse] at hy
  exact grpW_disj h1 h2 (by omega) (mem_snW.mp hx).2.2 (mem_snW.mp hy).2.2

end

/-! ### Shifted pairs -/

theorem not_pair_rev {l : List Coord} {x z : Coord} (hn : l.Nodup) (h1 : [x, z] <:+: l)
    (h2 : [z, x] <:+: l) : False :=
  pred_ne_succ hn h1 h2 rfl

theorem infix_map_pair {f : Coord → Coord} {L : List Coord} {u v : Coord}
    (h : [u, v] <:+: L.map f) : ∃ a b, [a, b] <:+: L ∧ f a = u ∧ f b = v := by
  obtain ⟨s, t, he⟩ := infix_pair_iff.mp h
  obtain ⟨L1, L2, rfl, -, h2⟩ := List.map_eq_append_iff.mp he
  cases L2 with
  | nil => simp at h2
  | cons a L2 =>
    cases L2 with
    | nil => simp at h2
    | cons b l =>
      simp only [List.map_cons, List.cons.injEq] at h2
      exact ⟨a, b, infix_pair_iff.mpr ⟨L1, l, rfl⟩, h2.1, h2.2.1⟩

section
variable {r W : ℕ}

theorem shW_le {v : Coord} (h : v.1 ≤ r) : shW r W v = v := by simp [shW, h]

theorem shW_gt {v : Coord} (h : r < v.1) : shW r W v = (v.1 + W, v.2) := by
  simp [shW, show ¬ v.1 ≤ r by omega]

theorem shW_inj {u v : Coord} (h : shW r W u = shW r W v) : u = v := by
  obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v
  unfold shW at h
  simp only at h
  split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> exact Prod.ext (by simp; omega) h.2

theorem shW_out (v : Coord) : (shW r W v).1 ≤ r ∨ r + W < (shW r W v).1 := by
  unfold shW
  split_ifs with hh
  · exact Or.inl hh
  · right; show r + W < v.1 + W; omega

theorem shW_snd (v : Coord) : (shW r W v).2 = v.2 := by unfold shW; split_ifs <;> rfl

theorem shW_adj {a b : Coord} (hab : Adjacent a b) (n1 : ¬ (a.1 = r ∧ b.1 = r + 1))
    (n2 : ¬ (a.1 = r + 1 ∧ b.1 = r)) : Adjacent (shW r W a) (shW r W b) := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  unfold Adjacent at hab ⊢
  simp only at hab n1 n2
  unfold shW
  split_ifs <;> simp only <;> omega

/-- A shifted cell sits on line `r` only if the cell does. -/
theorem shW_eq_r {a : Coord} {y : ℕ} : shW r W a = (r, y) ↔ a = (r, y) := by
  obtain ⟨a1, a2⟩ := a
  unfold shW
  split_ifs with h
  · rfl
  · simp only [Prod.mk.injEq]; constructor <;> rintro ⟨h1, h2⟩ <;> omega

theorem shW_eq_far {a : Coord} {y : ℕ} : shW r W a = (r + W + 1, y) ↔ a = (r + 1, y) := by
  obtain ⟨a1, a2⟩ := a
  unfold shW
  split_ifs with h
  · simp only [Prod.mk.injEq]; constructor <;> rintro ⟨h1, h2⟩ <;> omega
  · simp only [Prod.mk.injEq]; constructor <;> rintro ⟨h1, h2⟩ <;> omega

end

section
variable {cv : ℕ → Bool} {r j h R : ℕ} {flip : Bool}

/-- The crossing pairs and the flip pairs, in shifted form, and what `GW` inserts there. -/
theorem GW_fwd (y : ℕ) :
    GW r j h R flip cv (r, y) (r + 2 * j + 1, y) = snW r j h R cv y := by
  unfold GW; rw [ite_t ⟨rfl, rfl, rfl⟩]

theorem GW_bwd (y : ℕ) :
    GW r j h R flip cv (r + 2 * j + 1, y) (r, y) = (snW r j h R cv y).reverse := by
  unfold GW
  rw [ite_f (fun h => by simp only at h; omega), ite_t ⟨rfl, rfl, rfl⟩]

/-- **What `GW` inserts at a shifted step**: nothing, a crossing snake, or the flip block. -/
theorem GW_cases {a b : Coord} (hab : Adjacent a b) :
    (∃ y, a = (r, y) ∧ b = (r + 1, y) ∧
      GW r j h R flip cv (shW r (2 * j) a) (shW r (2 * j) b) = snW r j h R cv y) ∨
    (∃ y, a = (r + 1, y) ∧ b = (r, y) ∧
      GW r j h R flip cv (shW r (2 * j) a) (shW r (2 * j) b) = (snW r j h R cv y).reverse) ∨
    (flip = true ∧ a = (r, R - 1) ∧ b = (r, R) ∧
      GW r j h R flip cv (shW r (2 * j) a) (shW r (2 * j) b) = flipW r j h R cv) ∨
    (flip = true ∧ a = (r, R) ∧ b = (r, R - 1) ∧ R - 1 ≠ R ∧
      GW r j h R flip cv (shW r (2 * j) a) (shW r (2 * j) b) = (flipW r j h R cv).reverse) ∨
    (¬ (a.1 = r ∧ b.1 = r + 1) ∧ ¬ (a.1 = r + 1 ∧ b.1 = r) ∧
      GW r j h R flip cv (shW r (2 * j) a) (shW r (2 * j) b) = []) := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  by_cases c1 : a1 = r ∧ b1 = r + 1
  · obtain ⟨rfl, rfl⟩ := c1
    have e : a2 = b2 := by unfold Adjacent at hab; simp only at hab; omega
    subst e
    refine Or.inl ⟨a2, rfl, rfl, ?_⟩
    rw [shW_le (by simp), shW_gt (show a1 < a1 + 1 by simp)]
    simp only
    rw [show a1 + 1 + 2 * j = a1 + 2 * j + 1 by omega]
    exact GW_fwd a2
  by_cases c2 : a1 = r + 1 ∧ b1 = r
  · obtain ⟨rfl, rfl⟩ := c2
    have e : a2 = b2 := by unfold Adjacent at hab; simp only at hab; omega
    subst e
    refine Or.inr (Or.inl ⟨a2, rfl, rfl, ?_⟩)
    rw [shW_gt (show b1 < b1 + 1 by simp), shW_le (by simp)]
    simp only
    rw [show b1 + 1 + 2 * j = b1 + 2 * j + 1 by omega]
    exact GW_bwd a2
  -- not a crossing: the first two branches of `GW` do not fire
  have n12 : ∀ u v : Coord, u = shW r (2 * j) (a1, a2) → v = shW r (2 * j) (b1, b2) →
      ¬ (u.1 = r ∧ v.1 = r + 2 * j + 1 ∧ u.2 = v.2) ∧
      ¬ (u.1 = r + 2 * j + 1 ∧ v.1 = r ∧ u.2 = v.2) := by
    rintro u v rfl rfl
    unfold Adjacent at hab
    simp only at hab c1 c2
    unfold shW
    constructor <;> split_ifs <;> simp only <;> omega
  obtain ⟨n1, n2⟩ := n12 _ _ rfl rfl
  by_cases f1 : flip = true ∧ (a1, a2) = (r, R - 1) ∧ (b1, b2) = (r, R)
  · obtain ⟨hf, ea, eb⟩ := f1
    refine Or.inr (Or.inr (Or.inl ⟨hf, ea, eb, ?_⟩))
    unfold GW
    rw [ite_f n1, ite_f n2, ite_t ⟨hf, shW_eq_r.mpr ea, shW_eq_r.mpr eb⟩]
  by_cases f2 : flip = true ∧ (a1, a2) = (r, R) ∧ (b1, b2) = (r, R - 1)
  · obtain ⟨hf, ea, eb⟩ := f2
    have hR : R - 1 ≠ R := by
      intro e
      rw [e] at eb
      rw [← eb] at ea
      unfold Adjacent at hab
      simp only [Prod.mk.injEq] at ea
      omega
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hf, ea, eb, hR, ?_⟩)))
    unfold GW
    rw [ite_f n1, ite_f n2, ite_f (fun h => by
        rw [shW_eq_r] at h; rw [ea] at h; simp only [Prod.mk.injEq] at h; omega),
      ite_t ⟨hf, shW_eq_r.mpr ea, shW_eq_r.mpr eb⟩]
  refine Or.inr (Or.inr (Or.inr (Or.inr ⟨c1, c2, ?_⟩)))
  unfold GW
  rw [ite_f n1, ite_f n2]
  rw [ite_f (fun h => f1 ⟨h.1, shW_eq_r.mp h.2.1, shW_eq_r.mp h.2.2⟩),
    ite_f (fun h => f2 ⟨h.1, shW_eq_r.mp h.2.1, shW_eq_r.mp h.2.2⟩)]

/-- **Each shifted step closes a chain** through what `GW` inserts. -/
theorem GW_chain (hj : 0 < j) {a b : Coord} (hab : Adjacent a b) :
    chainAdjacent (shW r (2 * j) a ::
      (GW r j h R flip cv (shW r (2 * j) a) (shW r (2 * j) b) ++ [shW r (2 * j) b])) = true := by
  rcases GW_cases (cv := cv) (r := r) (h := h) (R := R) (flip := flip) (j := j) hab with
    ⟨y, rfl, rfl, e⟩ | ⟨y, rfl, rfl, e⟩ | ⟨hf, rfl, rfl, e⟩ | ⟨hf, rfl, rfl, hR, e⟩ | ⟨n1, n2, e⟩
  · rw [e, shW_le (by simp), shW_gt (show r < r + 1 by simp)]
    simp only
    rw [show r + 1 + 2 * j = r + 2 * j + 1 by omega]
    exact snW_cross_chain y hj
  · rw [e, shW_le (show (r, y).1 ≤ r by simp), shW_gt (show r < (r + 1, y).1 by simp)]
    simp only
    rw [show r + 1 + 2 * j = r + 2 * j + 1 by omega]
    have := chainAdjacent_reverse _ (snW_cross_chain (cv := cv) (r := r) (h := h) (R := R) y hj)
    simpa using this
  · rw [e, shW_le (show (r, R - 1).1 ≤ r by simp), shW_le (show (r, R).1 ≤ r by simp)]
    by_cases hR : 1 ≤ R
    · exact flipW_chain hj hR
    · obtain rfl : R = 0 := by omega
      have := hab
      unfold Adjacent at this; simp at this
  · rw [e, shW_le (show (r, R - 1).1 ≤ r by simp), shW_le (show (r, R).1 ≤ r by simp)]
    have := chainAdjacent_reverse _ (flipW_chain (cv := cv) (h := h) (r := r) (R := R) hj (by omega))
    simpa using this
  · rw [e]
    simp only [List.nil_append, chainAdjacent_cons_cons, chainAdjacent_singleton, Bool.and_true]
    exact (adjacentB_iff _ _).mpr (shW_adj hab n1 n2)

end

/-! ### The wide band is a solution -/

/-- The seed `R`, the flip flag and the table `cv` of covered rows, for a solution `p, q` and
the line `r`. -/
structure WideOK (I : Inst) (p q : List Coord) (r R : ℕ) (flip : Bool) (cv : ℕ → Bool) : Prop where
  rw : r < I.w
  hR : R ≤ I.h
  noflip : flip = false → (R = 0 ∨ Cross p q r (R - 1)) ∧ (R = I.h ∨ Cross p q r R)
  yesflip : flip = true → 1 ≤ R ∧ R < I.h ∧ ¬ Cross p q r (R - 1) ∧ ¬ Cross p q r R ∧
    (Used p (r, R - 1) (r, R) ∨ Used q (r, R - 1) (r, R))
  cv_iff : ∀ y, cv y = true ↔ Cross p q r y ∨ (flip = true ∧ (y + 1 = R ∨ y = R))

/-- The rows a step anchors: its crossing row, or a flip row. -/
def StepAnchor (r R : ℕ) (flip : Bool) (a b : Coord) (z : ℕ) : Prop :=
  ((a = (r, z) ∧ b = (r + 1, z)) ∨ (a = (r + 1, z) ∧ b = (r, z))) ∨
  (flip = true ∧ (z + 1 = R ∨ z = R) ∧
    ((a = (r, R - 1) ∧ b = (r, R)) ∨ (a = (r, R) ∧ b = (r, R - 1))))

section
variable {I : Inst} {p q : List Coord} {r j R : ℕ} {flip : Bool} {cv : ℕ → Bool}

theorem WideOK.lo (ok : WideOK I p q r R flip cv) : R = 0 ∨ cv (R - 1) = true := by
  cases hf : flip
  · rcases (ok.noflip hf).1 with h | h
    · exact Or.inl h
    · exact Or.inr ((ok.cv_iff _).mpr (Or.inl h))
  · obtain ⟨h1, -⟩ := ok.yesflip hf
    exact Or.inr ((ok.cv_iff _).mpr (Or.inr ⟨hf, Or.inl (by omega)⟩))

theorem WideOK.hi (ok : WideOK I p q r R flip cv) : R = I.h ∨ cv R = true := by
  cases hf : flip
  · rcases (ok.noflip hf).2 with h | h
    · exact Or.inl h
    · exact Or.inr ((ok.cv_iff _).mpr (Or.inl h))
  · exact Or.inr ((ok.cv_iff _).mpr (Or.inr ⟨hf, Or.inr rfl⟩))

theorem mem_GW_step {h : ℕ} {a b x : Coord} (hab : Adjacent a b)
    (hx : x ∈ GW r j h R flip cv (shW r (2 * j) a) (shW r (2 * j) b)) :
    r + 1 ≤ x.1 ∧ x.1 < r + 1 + 2 * j ∧ ∃ z, StepAnchor r R flip a b z ∧ x.2 ∈ grpW cv h R z := by
  rcases GW_cases (cv := cv) (r := r) (h := h) (R := R) (flip := flip) (j := j) hab with
    ⟨y, rfl, rfl, e⟩ | ⟨y, rfl, rfl, e⟩ | ⟨hf, rfl, rfl, e⟩ | ⟨hf, rfl, rfl, hR, e⟩ | ⟨-, -, e⟩
  · rw [e, mem_snW] at hx
    exact ⟨hx.1, hx.2.1, y, Or.inl (Or.inl ⟨rfl, rfl⟩), hx.2.2⟩
  · rw [e, List.mem_reverse, mem_snW] at hx
    exact ⟨hx.1, hx.2.1, y, Or.inl (Or.inr ⟨rfl, rfl⟩), hx.2.2⟩
  · have hR : 1 ≤ R := by
      by_contra h0
      obtain rfl : R = 0 := by omega
      unfold Adjacent at hab; simp at hab
    rw [e, flipW, List.mem_append, List.mem_reverse, mem_snW, mem_snW] at hx
    rcases hx with hx | hx
    · exact ⟨hx.1, hx.2.1, R - 1, Or.inr ⟨hf, Or.inl (by omega), Or.inl ⟨rfl, rfl⟩⟩, hx.2.2⟩
    · exact ⟨hx.1, hx.2.1, R, Or.inr ⟨hf, Or.inr rfl, Or.inl ⟨rfl, rfl⟩⟩, hx.2.2⟩
  · rw [e, List.mem_reverse, flipW, List.mem_append, List.mem_reverse, mem_snW, mem_snW] at hx
    rcases hx with hx | hx
    · exact ⟨hx.1, hx.2.1, R - 1, Or.inr ⟨hf, Or.inl (by omega), Or.inr ⟨rfl, rfl⟩⟩, hx.2.2⟩
    · exact ⟨hx.1, hx.2.1, R, Or.inr ⟨hf, Or.inr rfl, Or.inr ⟨rfl, rfl⟩⟩, hx.2.2⟩
  · rw [e] at hx; simp at hx

/-- The crossing steps of the two paths are crossings. -/
def CrossOK (p q : List Coord) (r : ℕ) (a b : Coord) : Prop :=
  ∀ z, ((a = (r, z) ∧ b = (r + 1, z)) ∨ (a = (r + 1, z) ∧ b = (r, z))) → Cross p q r z

theorem crossOK_of {a b : Coord} (h : Used p a b ∨ Used q a b) : CrossOK p q r a b := by
  rintro z (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact h
  · rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm

theorem anchor_cv (ok : WideOK I p q r R flip cv) {a b : Coord} {z : ℕ} (hc : CrossOK p q r a b)
    (hz : StepAnchor r R flip a b z) : cv z = true := by
  rcases hz with hz | ⟨hf, hz, -⟩
  · exact (ok.cv_iff z).mpr (Or.inl (hc z hz))
  · exact (ok.cv_iff z).mpr (Or.inr ⟨hf, hz⟩)

/-- **Two steps whose inserted cells meet are the same step**, possibly reversed. -/
theorem GW_overlap (ok : WideOK I p q r R flip cv) {a b a' b' x : Coord}
    (hab : Adjacent a b) (hab' : Adjacent a' b') (hc : CrossOK p q r a b) (hc' : CrossOK p q r a' b')
    (hx : x ∈ GW r j I.h R flip cv (shW r (2 * j) a) (shW r (2 * j) b))
    (hx' : x ∈ GW r j I.h R flip cv (shW r (2 * j) a') (shW r (2 * j) b')) :
    (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  obtain ⟨-, -, z, hz, hxz⟩ := mem_GW_step hab hx
  obtain ⟨-, -, z', hz', hxz'⟩ := mem_GW_step hab' hx'
  have cz := anchor_cv ok hc hz
  have cz' := anchor_cv ok hc' hz'
  by_cases e : z = z'
  · subst e
    rcases hz with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨hf, hzR, hfl⟩ <;>
      rcases hz' with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨hf', hzR', hfl'⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exfalso
      obtain ⟨-, -, n1, n2, -⟩ := ok.yesflip hf'
      have := hc z (Or.inl ⟨rfl, rfl⟩)
      rcases hzR' with h | h
      · exact n1 (by rw [show R - 1 = z by omega]; exact this)
      · exact n2 (h ▸ this)
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exfalso
      obtain ⟨-, -, n1, n2, -⟩ := ok.yesflip hf'
      have := hc z (Or.inr ⟨rfl, rfl⟩)
      rcases hzR' with h | h
      · exact n1 (by rw [show R - 1 = z by omega]; exact this)
      · exact n2 (h ▸ this)
    · exfalso
      obtain ⟨-, -, n1, n2, -⟩ := ok.yesflip hf
      have := hc' z (Or.inl ⟨rfl, rfl⟩)
      rcases hzR with h | h
      · exact n1 (by rw [show R - 1 = z by omega]; exact this)
      · exact n2 (h ▸ this)
    · exfalso
      obtain ⟨-, -, n1, n2, -⟩ := ok.yesflip hf
      have := hc' z (Or.inr ⟨rfl, rfl⟩)
      rcases hzR with h | h
      · exact n1 (by rw [show R - 1 = z by omega]; exact this)
      · exact n2 (h ▸ this)
    · rcases hfl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hfl' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
  · exact (grpW_disj cz cz' e hxz hxz').elim

end

section
variable {I : Inst} {p q : List Coord} {r j R : ℕ} {flip : Bool} {cv : ℕ → Bool}

theorem GW_flipF {h : ℕ} (hf : flip = true) :
    GW r j h R flip cv (r, R - 1) (r, R) = flipW r j h R cv := by
  unfold GW
  rw [ite_f (fun h => by simp only at h; omega), ite_f (fun h => by simp only at h; omega),
    ite_t ⟨hf, rfl, rfl⟩]

theorem GW_flipB {h : ℕ} (hf : flip = true) (hR : 1 ≤ R) :
    GW r j h R flip cv (r, R) (r, R - 1) = (flipW r j h R cv).reverse := by
  unfold GW
  rw [ite_f (fun h => by simp only at h; omega), ite_f (fun h => by simp only at h; omega),
    ite_f (fun h => by simp only [Prod.mk.injEq] at h; omega), ite_t ⟨hf, rfl, rfl⟩]

theorem GW_nodup (ok : WideOK I p q r R flip cv) {a b : Coord} (hab : Adjacent a b) :
    (GW r j I.h R flip cv (shW r (2 * j) a) (shW r (2 * j) b)).Nodup := by
  rcases GW_cases (cv := cv) (r := r) (h := I.h) (R := R) (flip := flip) (j := j) hab with
    ⟨y, -, -, e⟩ | ⟨y, -, -, e⟩ | ⟨hf, -, -, e⟩ | ⟨hf, -, -, -, e⟩ | ⟨-, -, e⟩
  · rw [e]; exact snW_nodup y
  · rw [e]; exact List.nodup_reverse.mpr (snW_nodup y)
  · obtain ⟨h1, -⟩ := ok.yesflip hf
    rw [e]
    exact flipW_nodup ((ok.cv_iff _).mpr (Or.inr ⟨hf, Or.inl (by omega)⟩))
      ((ok.cv_iff _).mpr (Or.inr ⟨hf, Or.inr rfl⟩)) h1
  · obtain ⟨h1, -⟩ := ok.yesflip hf
    rw [e]
    exact List.nodup_reverse.mpr (flipW_nodup ((ok.cv_iff _).mpr (Or.inr ⟨hf, Or.inl (by omega)⟩))
      ((ok.cv_iff _).mpr (Or.inr ⟨hf, Or.inr rfl⟩)) h1)
  · rw [e]; exact List.nodup_nil

/-- **Each stretched path is a path** of the widened grid. -/
theorem wideExt_path (ok : WideOK I p q r R flip cv) (hj : 0 < j) {L : List Coord} {s t : Coord}
    (hL : IsPath I.w I.h s t L) (hU : ∀ u v, [u, v] <:+: L → Used p u v ∨ Used q u v) :
    IsPath (I.w + 2 * j) I.h (shW r (2 * j) s) (shW r (2 * j) t) (wideExt r j I.h R flip cv L) := by
  obtain ⟨hh, hl, hn, hb, hc⟩ := hL
  have pair : ∀ {u v}, [u, v] <:+: L.map (shW r (2 * j)) → ∃ a b, [a, b] <:+: L ∧
      shW r (2 * j) a = u ∧ shW r (2 * j) b = v ∧ Adjacent a b ∧ CrossOK p q r a b := by
    intro u v huv
    obtain ⟨a, b, hab, rfl, rfl⟩ := infix_map_pair huv
    exact ⟨a, b, hab, rfl, rfl, adjacent_of_infix hc hab, crossOK_of (hU a b hab)⟩
  have hnm : (L.map (shW r (2 * j))).Nodup := hn.map (fun _ _ e => shW_inj e)
  have band : ∀ {a b x}, [a, b] <:+: L → Adjacent a b →
      x ∈ GW r j I.h R flip cv (shW r (2 * j) a) (shW r (2 * j) b) →
      InBounds (I.w + 2 * j) I.h x ∧ r + 1 ≤ x.1 ∧ x.1 < r + 1 + 2 * j := by
    intro a b x hab hadj hx
    obtain ⟨x1, x2, z, hz, hxz⟩ := mem_GW_step hadj hx
    have hzh : z < I.h := by
      rcases hz with (⟨rfl, -⟩ | ⟨-, rfl⟩) | ⟨hf, hzR, -⟩
      · exact (hb (r, z) (hab.subset (by simp))).2
      · exact (hb (r, z) (hab.subset (by simp))).2
      · obtain ⟨-, h2, -⟩ := ok.yesflip hf; omega
    have : x.2 < I.h := by
      unfold grpW at hxz
      rcases List.mem_cons.mp hxz with e | e
      · omega
      · exact attW_lt hzh e
    have hrw := ok.rw
    exact ⟨⟨by omega, this⟩, x1, x2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [wideExt, insMany_head, List.head?_map, hh]; simp
  · rw [wideExt, insMany_getLast, List.getLast?_map, hl]; simp
  · refine insMany_nodup _ _ hnm (fun u v huv => ?_) (fun u v u' v' huv huv' hne x hx hx' => ?_)
    · obtain ⟨a, b, hab, rfl, rfl, hadj, -⟩ := pair huv
      refine ⟨GW_nodup ok hadj, fun x hx hxL => ?_⟩
      obtain ⟨-, x1, x2⟩ := band hab hadj hx
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp hxL
      rcases shW_out (r := r) (W := 2 * j) c with h | h <;> omega
    · obtain ⟨a, b, hab, rfl, rfl, hadj, hca⟩ := pair huv
      obtain ⟨a', b', hab', rfl, rfl, hadj', hca'⟩ := pair huv'
      rcases GW_overlap ok hadj hadj' hca hca' hx hx' with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
      · exact hne rfl
      · exact not_pair_rev hn hab hab'
  · intro x hx
    rcases (mem_insMany _ _ x).mp hx with h | ⟨u, v, huv, hx⟩
    · obtain ⟨c, hc', rfl⟩ := List.mem_map.mp h
      have hcb := hb c hc'
      unfold InBounds at hcb ⊢
      by_cases hh : c.1 ≤ r
      · rw [shW_le hh]; exact ⟨by omega, hcb.2⟩
      · rw [shW_gt (by omega)]; exact ⟨show c.1 + 2 * j < I.w + 2 * j by omega, hcb.2⟩
    · obtain ⟨a, b, hab, rfl, rfl, hadj, -⟩ := pair huv
      exact (band hab hadj hx).1
  · refine insMany_chain _ _ (fun u v huv => ?_)
    obtain ⟨a, b, hab, rfl, rfl, hadj, -⟩ := pair huv
    exact GW_chain hj hadj

/-- **The wide band is a solution** of the instance with `2j` lines inserted after line `r`. -/
theorem wideExt_sol (ok : WideOK I p q r R flip cv) (hj : 0 < j) (hsol : IsSolution I p q) :
    IsSolution (I.insertW r (2 * j)) (wideExt r j I.h R flip cv p) (wideExt r j I.h R flip cv q) := by
  obtain ⟨hp, hq, hd, hcov⟩ := hsol
  have Pp := wideExt_path ok hj hp (fun u v h => Or.inl (Or.inl h))
  have Pq := wideExt_path ok hj hq (fun u v h => Or.inr (Or.inl h))
  have pairOf : ∀ {L : List Coord} {s t : Coord}, IsPath I.w I.h s t L →
      (∀ u v, [u, v] <:+: L → Used p u v ∨ Used q u v) → ∀ {u v},
      [u, v] <:+: L.map (shW r (2 * j)) → ∃ a b, [a, b] <:+: L ∧ shW r (2 * j) a = u ∧ shW r (2 * j) b = v ∧ Adjacent a b ∧
        CrossOK p q r a b := by
    intro L s t hL hU u v huv
    obtain ⟨a, b, hab, rfl, rfl⟩ := infix_map_pair huv
    exact ⟨a, b, hab, rfl, rfl, adjacent_of_infix hL.2.2.2.2 hab, crossOK_of (hU a b hab)⟩
  have inW : ∀ {L : List Coord} {a b x : Coord}, [a, b] <:+: L → x ∈ GW r j I.h R flip cv (shW r (2 * j) a) (shW r (2 * j) b) →
      x ∈ wideExt r j I.h R flip cv L := by
    intro L a b x hab hx
    exact (mem_insMany _ _ x).mpr (Or.inr ⟨shW r (2 * j) a, shW r (2 * j) b, hab.map (shW r (2 * j)), hx⟩)
  refine ⟨Pp, Pq, ?_, ?_⟩
  · -- disjointness
    intro v hvp hvq
    rcases (mem_insMany _ _ v).mp hvp with h1 | ⟨u, w, huw, hx⟩ <;>
      rcases (mem_insMany _ _ v).mp hvq with h2 | ⟨u', w', huw', hx'⟩
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h1
      obtain ⟨c', hc', e⟩ := List.mem_map.mp h2
      exact hd c hc (shW_inj e ▸ hc')
    · obtain ⟨c, -, rfl⟩ := List.mem_map.mp h1
      obtain ⟨a, b, -, rfl, rfl, hadj, -⟩ := pairOf hq (fun u v h => Or.inr (Or.inl h)) huw'
      obtain ⟨x1, x2, -⟩ := mem_GW_step hadj hx'
      rcases shW_out (r := r) (W := 2 * j) c with h | h <;> omega
    · obtain ⟨c, -, rfl⟩ := List.mem_map.mp h2
      obtain ⟨a, b, -, rfl, rfl, hadj, -⟩ := pairOf hp (fun u v h => Or.inl (Or.inl h)) huw
      obtain ⟨x1, x2, -⟩ := mem_GW_step hadj hx
      rcases shW_out (r := r) (W := 2 * j) c with h | h <;> omega
    · obtain ⟨a, b, hab, rfl, rfl, hadj, hca⟩ := pairOf hp (fun u v h => Or.inl (Or.inl h)) huw
      obtain ⟨a', b', hab', rfl, rfl, hadj', hca'⟩ :=
        pairOf hq (fun u v h => Or.inr (Or.inl h)) huw'
      have ha : a ∈ p := hab.subset (by simp)
      rcases GW_overlap ok hadj hadj' hca hca' hx hx' with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hd a ha (hab'.subset (by simp))
      · exact hd a ha (hab'.subset (by simp))
  · -- coverage
    intro v hv
    obtain ⟨hv1, hv2⟩ := hv
    simp only [Inst.insertW] at hv1 hv2
    have toMap : ∀ c, InBounds I.w I.h c → shW r (2 * j) c = v →
        v ∈ wideExt r j I.h R flip cv p ∨ v ∈ wideExt r j I.h R flip cv q := by
      intro c hc e
      rcases hcov c hc with h | h
      · exact Or.inl ((mem_insMany _ _ v).mpr (Or.inl (List.mem_map.mpr ⟨c, h, e⟩)))
      · exact Or.inr ((mem_insMany _ _ v).mpr (Or.inl (List.mem_map.mpr ⟨c, h, e⟩)))
    by_cases hl : v.1 ≤ r
    · exact toMap v ⟨by have := ok.rw; omega, hv2⟩ (shW_le hl)
    by_cases hr : r + 2 * j < v.1
    · refine toMap (v.1 - 2 * j, v.2) ⟨by simp only; omega, hv2⟩ ?_
      rw [shW_gt (show r < v.1 - 2 * j by omega)]
      exact Prod.ext (show v.1 - 2 * j + 2 * j = v.1 by omega) rfl
    -- a cell of the band
    have hy : v.2 < I.h := hv2
    obtain ⟨z, cz, hzy⟩ : ∃ z, cv z = true ∧ v.2 ∈ grpW cv I.h R z := by
      cases hc : cv v.2
      · obtain ⟨a, ha, -, hya⟩ := exists_anchor ok.hR ok.lo ok.hi hy hc
        exact ⟨a, ha, List.mem_cons_of_mem _ hya⟩
      · exact ⟨v.2, hc, List.mem_cons_self⟩
    have vS : v ∈ snW r j I.h R cv z := mem_snW.mpr ⟨by omega, by omega, hzy⟩
    rcases (ok.cv_iff z).mp cz with hc | ⟨hf, hzR⟩
    · -- a crossing row
      have key : ∀ {L : List Coord}, Used L (r, z) (r + 1, z) →
          v ∈ wideExt r j I.h R flip cv L := by
        intro L hu
        rcases hu with hu | hu
        · refine inW hu ?_
          rw [show shW r (2 * j) (r, z) = (r, z) from shW_le (by simp),
            show shW r (2 * j) (r + 1, z) = (r + 2 * j + 1, z) by
              rw [shW_gt (show r < (r + 1, z).1 by simp)]; exact Prod.ext (by simp only; omega) rfl]
          rw [GW_fwd]; exact vS
        · refine inW hu ?_
          rw [show shW r (2 * j) (r, z) = (r, z) from shW_le (by simp),
            show shW r (2 * j) (r + 1, z) = (r + 2 * j + 1, z) by
              rw [shW_gt (show r < (r + 1, z).1 by simp)]; exact Prod.ext (by simp only; omega) rfl]
          rw [GW_bwd, List.mem_reverse]; exact vS
      rcases hc with hc | hc
      · exact Or.inl (key hc)
      · exact Or.inr (key hc)
    · -- a flip row
      obtain ⟨h1, -, -, -, hu⟩ := ok.yesflip hf
      have vF : v ∈ flipW r j I.h R cv := by
        rw [flipW, List.mem_append, List.mem_reverse]
        rcases hzR with e | e
        · exact Or.inl (by rw [show R - 1 = z by omega]; exact vS)
        · exact Or.inr (e ▸ vS)
      have key : ∀ {L : List Coord}, Used L (r, R - 1) (r, R) →
          v ∈ wideExt r j I.h R flip cv L := by
        intro L hu
        rcases hu with hu | hu
        · refine inW hu ?_
          rw [show shW r (2 * j) (r, R - 1) = (r, R - 1) from shW_le (by simp),
            show shW r (2 * j) (r, R) = (r, R) from shW_le (by simp), GW_flipF hf]
          exact vF
        · refine inW hu ?_
          rw [show shW r (2 * j) (r, R - 1) = (r, R - 1) from shW_le (by simp),
            show shW r (2 * j) (r, R) = (r, R) from shW_le (by simp), GW_flipB hf h1, List.mem_reverse]
          exact vF
      rcases hu with hu | hu
      · exact Or.inl (key hu)
      · exact Or.inr (key hu)

end

end ZZN

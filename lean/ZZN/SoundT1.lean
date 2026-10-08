-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Planar
import ZZN.PassT

/-!
# Soundness of T1 (perimeter alternation)

Argument: `PROOF.md` §4.7.
-/

namespace ZZN.Planar

/-! ### Walks built by appending -/

def inner (L : List Pz) : List (Pz × Pz) := L.zip L.tail

theorem cnt_append (q : Pz × Pz → Bool) (L1 L2 : List (Pz × Pz)) :
    cnt q (L1 ++ L2) = cnt q L1 + cnt q L2 := by
  unfold cnt; rw [List.map_append, List.sum_append]

theorem zip_snoc (x : Pz) : ∀ (l : List Pz) (y : Pz),
    (y :: l).zip (l ++ [x]) = (y :: l).zip l ++ [(l.getLastD y, x)]
  | [], y => by simp
  | z :: l, y => by
    simp only [List.cons_append, List.zip_cons_cons, zip_snoc x l z, List.getLastD_cons]

theorem steps_cons (y : Pz) (l : List Pz) :
    steps (y :: l) = inner (y :: l) ++ [(l.getLastD y, y)] := by
  unfold steps inner
  rw [List.rotate_cons_succ, List.rotate_zero]
  exact zip_snoc y l y

theorem inner_append (b : Pz) (B : List Pz) : ∀ (A : List Pz) (a : Pz),
    inner (a :: A ++ b :: B) = inner (a :: A) ++ [(A.getLastD a, b)] ++ inner (b :: B)
  | [], a => by simp [inner]
  | c :: A, a => by
    have ih := inner_append b B A c
    simp only [inner, List.cons_append, List.tail_cons, List.zip_cons_cons, List.getLastD_cons]
      at ih ⊢
    rw [ih]

theorem getLastD_append (b : Pz) (B : List Pz) : ∀ (A : List Pz) (a : Pz),
    (A ++ b :: B).getLastD a = B.getLastD b
  | [], a => by rw [List.nil_append, List.getLastD_cons]
  | c :: A, a => by
    rw [List.cons_append, List.getLastD_cons, getLastD_append b B A c]

/-- The steps of `A ++ B`, both nonempty: the inner steps, and the two joining steps. -/
theorem cnt_steps_append (q : Pz × Pz → Bool) (a b : Pz) (A B : List Pz) :
    cnt q (steps (a :: A ++ b :: B)) =
      cnt q (inner (a :: A)) + (q (A.getLastD a, b)).toNat + cnt q (inner (b :: B)) +
        (q (B.getLastD b, a)).toNat := by
  rw [List.cons_append, steps_cons, ← List.cons_append, inner_append, getLastD_append]
  simp only [cnt_append]
  simp [cnt]

/-! ### The frame -/

/-- The points at distance 1 outside the `R × C` grid, clockwise from `(-1, -1)`. -/
def psi (R C : ℕ) (k : ℕ) : Pz :=
  if k ≤ C + 1 then (-1, (k : ℤ) - 1)
  else if k ≤ C + R + 2 then ((k : ℤ) - C - 2, C)
  else if k ≤ 2 * C + R + 3 then (R, 2 * (C : ℤ) + R + 2 - k)
  else (2 * (C : ℤ) + 2 * R + 3 - k, -1)

def frameM (R C : ℕ) : ℕ := 2 * R + 2 * C + 4

theorem psi_adj {R C k : ℕ} (hk : k + 1 < frameM R C) : AdjZ (psi R C k) (psi R C (k + 1)) := by
  unfold psi AdjZ frameM at *
  split_ifs <;> dsimp only <;> omega

theorem psi_inj {R C k m : ℕ} (hk : k < frameM R C) (hm : m < frameM R C)
    (h : psi R C k = psi R C m) : k = m := by
  unfold psi frameM at *
  split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> omega

theorem psi_box {R C k : ℕ} (hk : k < frameM R C) :
    -1 ≤ (psi R C k).1 ∧ (psi R C k).1 ≤ R ∧ -1 ≤ (psi R C k).2 ∧ (psi R C k).2 ≤ C ∧
      ((psi R C k).1 = -1 ∨ (psi R C k).1 = R ∨ (psi R C k).2 = -1 ∨ (psi R C k).2 = C) := by
  unfold psi frameM at *
  split_ifs <;> dsimp only <;> omega

/-! ### Anchors of perimeter cells -/

/-- The frame index next to a perimeter cell. -/
def anc (R C : ℕ) (x : ℕ × ℕ) : ℕ :=
  if x.1 = 0 then x.2 + 1
  else if x.2 = C - 1 then C + 2 + x.1
  else if x.1 = R - 1 then 2 * C + R + 2 - x.2
  else 2 * C + 2 * R + 3 - x.1

/-- The face at a perimeter cell, between it and the frame. -/
def faceOf (R C : ℕ) (x : ℕ × ℕ) : Pz :=
  if x.1 = 0 then (-1, x.2)
  else if x.2 = C - 1 then (x.1, (C : ℤ) - 1)
  else if x.1 = R - 1 then ((R : ℤ) - 1, (x.2 : ℤ) - 1)
  else ((x.1 : ℤ) - 1, -1)

def cast2 (x : ℕ × ℕ) : Pz := ((x.1 : ℤ), (x.2 : ℤ))

theorem anc_range {R C : ℕ} (hR : 2 ≤ R) (hC : 2 ≤ C) {x : ℕ × ℕ} (hx : x.1 < R) (hy : x.2 < C)
    (_hp : OnPerim R C x) : 1 ≤ anc R C x ∧ anc R C x + 2 ≤ frameM R C := by
  unfold anc frameM; split_ifs <;> omega

theorem anc_adj {R C : ℕ} (hR : 2 ≤ R) (hC : 2 ≤ C) {x : ℕ × ℕ} (hx : x.1 < R) (hy : x.2 < C)
    (hp : OnPerim R C x) : AdjZ (cast2 x) (psi R C (anc R C x)) := by
  obtain ⟨a, b⟩ := x
  unfold OnPerim at hp
  simp only at hx hy hp
  unfold anc psi AdjZ cast2
  split_ifs <;> dsimp only <;> omega

theorem anc_order {R C : ℕ} (hR : 2 ≤ R) (hC : 2 ≤ C) {x y : ℕ × ℕ} (hx : x.1 < R) (hx' : x.2 < C)
    (hy : y.1 < R) (hy' : y.2 < C) (hpx : OnPerim R C x) (hpy : OnPerim R C y) :
    (perimIndex R C x).getD 0 < (perimIndex R C y).getD 0 ↔ anc R C x < anc R C y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  unfold OnPerim at hpx hpy
  simp only at hx hx' hy hy' hpx hpy
  unfold perimIndex anc
  simp only [beq_iff_eq]
  split_ifs <;> simp only [Option.getD_some, Option.getD_none] <;> omega

/-! ### Face parities at the frame -/

def isE (u v : Pz) (s : Pz × Pz) : Bool := decide (s = (u, v) ∨ s = (v, u))

theorem isE_comm (u v : Pz) : isE u v = isE v u := by
  funext s; unfold isE; simp only [or_comm]

/-- Every point of the walk lies in the box of the grid and its frame. -/
def Box (R C : ℕ) (W : List Pz) : Prop :=
  ∀ p ∈ W, -1 ≤ p.1 ∧ p.1 ≤ R ∧ -1 ≤ p.2 ∧ p.2 ≤ C

theorem mem_steps {W : List Pz} {s : Pz × Pz} (hs : s ∈ steps W) : s.1 ∈ W ∧ s.2 ∈ W := by
  refine ⟨?_, ?_⟩
  · rw [← steps_fst W]; exact List.mem_map_of_mem hs
  · rw [← List.mem_rotate (n := 1), ← steps_snd W]; exact List.mem_map_of_mem hs

theorem cnt_zero_all {q : Pz × Pz → Bool} {L : List (Pz × Pz)} (h : ∀ s ∈ L, q s = false) :
    cnt q L = 0 := by
  unfold cnt
  rw [List.sum_eq_zero_iff]
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
  rw [h s hs]; rfl

theorem par_down' (W : List Pz) {i i' : ℤ} (h : i' = i + 1) (j : ℤ) :
    par W i' j = (cnt (ray i j) (steps W) + cnt (isH (i + 1) j) (steps W)) % 2 := by
  subst h; exact par_down W i j

theorem par_right' {W : List Pz} (hW : Closed W) (i : ℤ) {j j' : ℤ} (h : j' = j + 1) :
    par W i j' = (cnt (ray i j) (steps W) + cnt (isV i (j + 1)) (steps W)) % 2 := by
  subst h; exact par_right hW i j

theorem ray_zero_top {R C : ℕ} {W : List Pz} (hB : Box R C W) (j : ℤ) :
    cnt (ray (-2) j) (steps W) = 0 := by
  apply cnt_zero_all; intro s hs
  have := hB _ (mem_steps hs).1
  unfold ray; simp only [decide_eq_false_iff_not]; omega

theorem ray_zero_left {R C : ℕ} {W : List Pz} (hB : Box R C W) (i : ℤ) :
    cnt (ray i (-2)) (steps W) = 0 := by
  apply cnt_zero_all; intro s hs
  have h1 := hB _ (mem_steps hs).1
  have h2 := hB _ (mem_steps hs).2
  unfold ray; simp only [decide_eq_false_iff_not]; omega

theorem ray_zero_right {R C : ℕ} {W : List Pz} (hB : Box R C W) (i : ℤ) {j : ℤ} (hj : (C : ℤ) ≤ j) :
    cnt (ray i j) (steps W) = 0 := by
  apply cnt_zero_all; intro s hs
  have h1 := hB _ (mem_steps hs).1
  have h2 := hB _ (mem_steps hs).2
  unfold ray; simp only [decide_eq_false_iff_not]; omega

theorem par_bottom {R C : ℕ} {W : List Pz} (hW : Closed W) (hB : Box R C W) :
    ∀ n : ℕ, par W R ((C : ℤ) - n) = 0
  | 0 => by
    unfold par; rw [ray_zero_right hB _ (by simp)]
  | n + 1 => by
    have ih := par_bottom hW hB n
    have hv : cnt (isV R ((C : ℤ) - (n + 1 : ℕ) + 1)) (steps W) = 0 := by
      apply cnt_zero_all; intro s hs
      have h1 := hB _ (mem_steps hs).1
      have h2 := hB _ (mem_steps hs).2
      unfold isV; simp only [decide_eq_false_iff_not]
      rintro (h | h) <;> rw [h] at h1 h2 <;> simp at h1 h2
    have e := par_right' hW (R : ℤ) (j := (C : ℤ) - (n + 1 : ℕ)) (j' := (C : ℤ) - n) (by push_cast; ring)
    rw [hv, ih] at e
    unfold par
    omega

theorem par_face {R C : ℕ} (hR : 2 ≤ R) (_hC : 2 ≤ C) {W : List Pz} (hW : Closed W) (hB : Box R C W)
    {x : ℕ × ℕ} (hx : x.1 < R) (hy : x.2 < C) (hp : OnPerim R C x) :
    par W (faceOf R C x).1 (faceOf R C x).2 =
      cnt (isE (psi R C (anc R C x)) (psi R C (anc R C x + 1))) (steps W) % 2 := by
  obtain ⟨a, b⟩ := x
  unfold OnPerim at hp
  simp only at hx hy hp
  unfold faceOf anc
  simp only
  by_cases h1 : a = 0
  · -- top
    simp only [h1, ↓reduceIte]
    have p1 : psi R C (b + 1) = (-1, (b : ℤ)) := by unfold psi; rw [ite_eq_left (by omega)]; push_cast; ring_nf
    have p2 : psi R C (b + 1 + 1) = (-1, (b : ℤ) + 1) := by
      unfold psi; rw [ite_eq_left (by omega)]; push_cast; ring_nf
    rw [p1, p2, show isE (-1, (b : ℤ)) (-1, (b : ℤ) + 1) = isH (-1) b from rfl,
      par_down' W (i := -2) (by norm_num), ray_zero_top hB]
    simp
  by_cases h2 : b = C - 1
  · -- right
    simp only [ite_eq_right h1, ite_eq_left h2]
    have p1 : psi R C (C + 2 + a) = ((a : ℤ), (C : ℤ)) := by
      unfold psi; rw [ite_eq_right (by omega), ite_eq_left (by omega)]; push_cast; ring_nf
    have p2 : psi R C (C + 2 + a + 1) = ((a : ℤ) + 1, (C : ℤ)) := by
      unfold psi; rw [ite_eq_right (by omega), ite_eq_left (by omega)]; push_cast; ring_nf
    rw [p1, p2, show isE ((a : ℤ), (C : ℤ)) ((a : ℤ) + 1, (C : ℤ)) = isV a C from rfl]
    have e := par_right' hW (a : ℤ) (j := (C : ℤ) - 1) (j' := C) (by ring)
    rw [show ((C : ℤ) - 1 + 1) = C by ring] at e
    have z : par W a C = 0 := by unfold par; rw [ray_zero_right hB _ le_rfl]
    rw [z] at e
    unfold par
    omega
  by_cases h3 : a = R - 1
  · -- bottom
    simp only [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]
    have p1 : psi R C (2 * C + R + 2 - b) = ((R : ℤ), (b : ℤ)) := by
      unfold psi; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]; simp only [Prod.mk.injEq, true_and]; omega
    have p2 : psi R C (2 * C + R + 2 - b + 1) = ((R : ℤ), (b : ℤ) - 1) := by
      unfold psi; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]; simp only [Prod.mk.injEq, true_and]; omega
    rw [p1, p2, isE_comm, show isE ((R : ℤ), (b : ℤ) - 1) ((R : ℤ), (b : ℤ)) = isH R ((b : ℤ) - 1) by
      unfold isE isH; simp]
    have e := par_down' W (i := (R : ℤ) - 1) (i' := R) (by ring) ((b : ℤ) - 1)
    rw [show ((R : ℤ) - 1 + 1) = R by ring] at e
    have z := par_bottom hW hB (C - b + 1)
    rw [show (C : ℤ) - ((C - b + 1 : ℕ) : ℤ) = (b : ℤ) - 1 by omega] at z
    unfold par at e z ⊢
    omega
  · -- left
    simp only [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
    have p1 : psi R C (2 * C + 2 * R + 3 - a) = ((a : ℤ), -1) := by
      unfold psi; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]; simp only [Prod.mk.injEq, and_true]; omega
    have p2 : psi R C (2 * C + 2 * R + 3 - a + 1) = ((a : ℤ) - 1, -1) := by
      unfold psi; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]; simp only [Prod.mk.injEq, and_true]; omega
    rw [p1, p2, isE_comm, show isE ((a : ℤ) - 1, -1) ((a : ℤ), -1) = isV ((a : ℤ) - 1) (-1) by
      unfold isE isV; simp]
    have e := par_right' hW ((a : ℤ) - 1) (j := -2) (j' := -1) (by norm_num)
    rw [ray_zero_left hB, show ((-2 : ℤ) + 1) = -1 by norm_num] at e
    rw [e]
    simp

/-! ### The connector along the frame -/

theorem inner_map (f : ℕ → Pz) : ∀ (L : List ℕ),
    inner (L.map f) = (L.zip L.tail).map (fun m => (f m.1, f m.2))
  | [] => rfl
  | [_] => rfl
  | x :: y :: L => by
    have ih := inner_map f (y :: L)
    simp only [inner, List.map_cons, List.tail_cons, List.zip_cons_cons] at ih ⊢
    rw [ih]

theorem zip_range' : ∀ (n lo : ℕ),
    (List.range' lo (n + 1)).zip (List.range' (lo + 1) n) = (List.range' lo n).map (fun m => (m, m + 1))
  | 0, lo => by simp
  | n + 1, lo => by
    have ih := zip_range' n (lo + 1)
    simp only [List.range'_succ, List.zip_cons_cons, List.map_cons] at ih ⊢
    rw [ih]

theorem sum_ind_range' (k : ℕ) : ∀ (n lo : ℕ),
    ((List.range' lo n).map fun m => (decide (m = k)).toNat).sum =
      if lo ≤ k ∧ k < lo + n then 1 else 0
  | 0, lo => by simp
  | n + 1, lo => by
    rw [List.range'_succ, List.map_cons, List.sum_cons, sum_ind_range' k n (lo + 1)]
    by_cases h : lo = k
    · subst h; simp
    · simp only [h, decide_false, Bool.toNat_false, zero_add]
      split_ifs <;> omega

/-- The frame edge at index `k` is crossed once by the connector from `lo` to `hi` iff
`lo ≤ k < hi`. -/
theorem cnt_conn {R C lo hi k : ℕ} (hhi : hi + 1 < frameM R C) (hk : k + 1 < frameM R C) :
    cnt (isE (psi R C k) (psi R C (k + 1))) (inner ((List.range' lo (hi - lo + 1)).map (psi R C))) =
      if lo ≤ k ∧ k < hi then 1 else 0 := by
  have ht : (List.range' lo (hi - lo + 1)).tail = List.range' (lo + 1) (hi - lo) := by
    rw [List.range'_succ, List.tail_cons]
  rw [inner_map, ht, zip_range']
  unfold cnt
  rw [List.map_map]
  have e : ∀ m ∈ List.range' lo (hi - lo),
      ((fun s => (isE (psi R C k) (psi R C (k + 1)) s).toNat) ∘ fun m : ℕ × ℕ => (psi R C m.1, psi R C m.2))
        (m, m + 1) = (decide (m = k)).toNat := by
    intro m hm
    rw [List.mem_range'_1] at hm
    have hm' : m + 1 < frameM R C := by omega
    simp only [Function.comp]
    congr 1
    unfold isE
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Prod.mk.injEq]
    constructor
    · rintro (⟨h1, -⟩ | ⟨h1, h2⟩)
      · exact psi_inj (by omega) (by omega) h1
      · have := psi_inj (by omega) (by omega) h1
        have := psi_inj (by omega) (by omega) h2
        omega
    · rintro rfl; exact Or.inl ⟨rfl, rfl⟩
  rw [List.map_map, List.map_congr_left (f := ((fun s => (isE (psi R C k) (psi R C (k + 1)) s).toNat) ∘
    fun m : ℕ × ℕ => (psi R C m.1, psi R C m.2)) ∘ fun m => (m, m + 1))
    (g := fun m => (decide (m = k)).toNat) e, sum_ind_range']
  split_ifs <;> omega

/-! ### The T1 core -/

theorem adj_cast {u v : ℕ × ℕ} (h : GridHam.Adjacent u v) : AdjZ (cast2 u) (cast2 v) := by
  obtain ⟨a, b⟩ := u
  obtain ⟨c, d⟩ := v
  unfold GridHam.Adjacent at h
  unfold AdjZ cast2
  simp only at h ⊢
  omega

theorem chainZ_cast : ∀ (L : List (ℕ × ℕ)), GridHam.chainAdjacent L = true → ChainZ (L.map cast2)
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: L, h => by
    rw [ZZN.chainAdjacent_cons_cons, Bool.and_eq_true] at h
    exact ⟨adj_cast ((ZZN.adjacentB_iff a b).mp h.1), chainZ_cast (b :: L) h.2⟩

theorem inner_adj : ∀ (L : List Pz), ChainZ L → ∀ s ∈ inner L, AdjZ s.1 s.2
  | [], _ => by simp [inner]
  | [_], _ => by simp [inner]
  | a :: b :: L, h => by
    intro s hs
    simp only [inner, List.tail_cons, List.zip_cons_cons, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact h.1
    · exact inner_adj (b :: L) h.2 s hs

theorem mem_inner {L : List Pz} {s : Pz × Pz} (h : s ∈ inner L) : s.1 ∈ L ∧ s.2 ∈ L := by
  unfold inner at h
  exact ⟨List.of_mem_zip h |>.1, List.mem_of_mem_tail (List.of_mem_zip h).2⟩

theorem steps_append_mem {a b : Pz} {A B : List Pz} {s : Pz × Pz} (h : s ∈ steps (a :: A ++ b :: B)) :
    s ∈ inner (a :: A) ∨ s = (A.getLastD a, b) ∨ s ∈ inner (b :: B) ∨ s = (B.getLastD b, a) := by
  rw [List.cons_append, steps_cons, ← List.cons_append, inner_append, getLastD_append] at h
  simp only [List.mem_append, List.mem_singleton] at h
  tauto

theorem getLastD_map {α β : Type} (f : α → β) : ∀ (L : List α) (x : α),
    (L.map f).getLastD (f x) = f (L.getLastD x)
  | [], _ => rfl
  | y :: L, x => by simp only [List.map_cons, List.getLastD_cons, getLastD_map f L y]

theorem getLastD_range' : ∀ (n lo : ℕ), (List.range' (lo + 1) n).getLastD lo = lo + n
  | 0, lo => rfl
  | n + 1, lo => by
    rw [List.range'_succ, List.getLastD_cons, getLastD_range' n (lo + 1)]; omega

theorem getLastD_of_getLast? : ∀ {L : List (ℕ × ℕ)} {x y : ℕ × ℕ}, (x :: L).getLast? = some y →
    L.getLastD x = y
  | [], x, y, h => by simpa using h
  | z :: L, x, y, h => by
    rw [List.getLastD_cons]
    exact getLastD_of_getLast? (by simpa using h)

theorem cast_ne_psi {R C m : ℕ} (hm : m < frameM R C) {u : ℕ × ℕ} (hu1 : u.1 < R) (hu2 : u.2 < C) :
    cast2 u ≠ psi R C m := by
  intro h
  have := psi_box (R := R) (C := C) hm
  rw [← h] at this
  unfold cast2 at this
  simp only at this
  omega

theorem cast2_inj {u v : ℕ × ℕ} (h : cast2 u = cast2 v) : u = v := by
  obtain ⟨a, b⟩ := u; obtain ⟨c, d⟩ := v
  unfold cast2 at h; simp only [Prod.mk.injEq, Nat.cast_inj] at h
  rw [h.1, h.2]

theorem face_parP {R C : ℕ} {W : List Pz} (hW : Closed W) {x : ℕ × ℕ} (hx : x.1 < R) (hy : x.2 < C)
    (hp : OnPerim R C x) (hn : cast2 x ∉ W) :
    par W (faceOf R C x).1 (faceOf R C x).2 = parP W (cast2 x) % 2 := by
  obtain ⟨f1, f2, f3⟩ := faces_around hW hn
  obtain ⟨a, b⟩ := x
  unfold OnPerim at hp
  simp only at hx hy hp
  have hpp : parP W (cast2 (a, b)) % 2 = parP W (cast2 (a, b)) := by unfold parP par; omega
  rw [hpp]
  unfold faceOf cast2 at *
  simp only at f1 f2 f3 ⊢
  split_ifs with h1 h2 h3
  · rw [← f1, h1]; simp
  · rw [h2, show ((C - 1 : ℕ) : ℤ) = (C : ℤ) - 1 by omega]; rfl
  · rw [← f2, h3, show ((R - 1 : ℕ) : ℤ) = (R : ℤ) - 1 by omega]
  · have hb : b = 0 := by omega
    rw [← f3, hb]; simp

/-- **T1 core.** A path `A` from `xh` to `xl` (anchors `lo < hi`) and a disjoint path `Q` from `c` to
`d`, all four ends on the perimeter: `c` and `d` are on the same side of the frame arc `lo … hi`. -/
theorem t1_core {R C : ℕ} (hR : 2 ≤ R) (hC : 2 ≤ C) {A Q : List (ℕ × ℕ)}
    (hAc : GridHam.chainAdjacent A = true) (hQc : GridHam.chainAdjacent Q = true)
    (hAin : ∀ v ∈ A, v.1 < R ∧ v.2 < C) (hQin : ∀ v ∈ Q, v.1 < R ∧ v.2 < C)
    (hdis : ∀ v ∈ A, v ∉ Q) {xh xl c d : ℕ × ℕ}
    (hAh : A.head? = some xh) (hAl : A.getLast? = some xl)
    (hQh : Q.head? = some c) (hQl : Q.getLast? = some d)
    (pxh : OnPerim R C xh) (pxl : OnPerim R C xl) (pc : OnPerim R C c) (pd : OnPerim R C d)
    (hlt : anc R C xl < anc R C xh) :
    (if anc R C xl ≤ anc R C c ∧ anc R C c < anc R C xh then 1 else 0) =
      (if anc R C xl ≤ anc R C d ∧ anc R C d < anc R C xh then 1 else 0) := by
  set lo := anc R C xl
  set hi := anc R C xh
  obtain ⟨A0, rfl⟩ : ∃ A0, A = xh :: A0 := by
    cases A with
    | nil => simp at hAh
    | cons y A0 => simp at hAh; exact ⟨A0, by rw [hAh]⟩
  have inb := fun {v} (hv : v ∈ xh :: A0) => hAin v hv
  have bh := inb List.mem_cons_self
  have hlast : A0.getLastD xh = xl := getLastD_of_getLast? hAl
  have bl : xl.1 < R ∧ xl.2 < C := inb (List.mem_of_getLast? hAl)
  have hc_mem : c ∈ Q := List.mem_of_mem_head? hQh
  have hd_mem : d ∈ Q := List.mem_of_getLast? hQl
  have bc := hQin c hc_mem
  have bd := hQin d hd_mem
  obtain ⟨rh1, rh2⟩ := anc_range hR hC bh.1 bh.2 pxh
  obtain ⟨rl1, rl2⟩ := anc_range hR hC bl.1 bl.2 pxl
  -- the closed walk: the path, then the frame from `lo` up to `hi`
  have hconn : (List.range' lo (hi - lo + 1)).map (psi R C) =
      psi R C lo :: (List.range' (lo + 1) (hi - lo)).map (psi R C) := by
    simp only [List.range'_succ, List.map_cons]
  set W : List Pz := cast2 xh :: A0.map cast2 ++ psi R C lo :: (List.range' (lo + 1) (hi - lo)).map (psi R C)
    with hWe
  have lastA : (A0.map cast2).getLastD (cast2 xh) = cast2 xl := by rw [getLastD_map, hlast]
  have lastC : ((List.range' (lo + 1) (hi - lo)).map (psi R C)).getLastD (psi R C lo) = psi R C hi := by
    rw [getLastD_map, getLastD_range']; congr 1; omega
  have adjSym : ∀ {u v : Pz}, AdjZ u v → AdjZ v u := by
    intro u v h; unfold AdjZ at h ⊢; omega
  have hW : Closed W := by
    intro s hs
    rcases steps_append_mem hs with h | h | h | h
    · exact inner_adj _ (by have := chainZ_cast _ hAc; simpa using this) s h
    · rw [h, lastA]; exact anc_adj hR hC bl.1 bl.2 pxl
    · rw [← hconn, inner_map, show (List.range' lo (hi - lo + 1)).tail = List.range' (lo + 1) (hi - lo) by
        rw [List.range'_succ, List.tail_cons], zip_range'] at h
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp h
      obtain ⟨m', hm', he⟩ := List.mem_map.mp hm
      rw [← he]
      rw [List.mem_range'_1] at hm'
      exact psi_adj (by omega)
    · rw [h, lastC]; exact adjSym (anc_adj hR hC bh.1 bh.2 pxh)
  have hB : Box R C W := by
    intro p hp
    simp only [hWe, List.mem_append, List.mem_cons, List.mem_map] at hp
    rcases hp with (rfl | ⟨v, hv, rfl⟩) | (rfl | ⟨m, hm, rfl⟩)
    · unfold cast2; simp only; omega
    · have := inb (List.mem_cons_of_mem _ hv); unfold cast2; simp only; omega
    · have := psi_box (R := R) (C := C) (k := lo) (by omega); omega
    · rw [List.mem_range'_1] at hm
      have := psi_box (R := R) (C := C) (k := m) (by omega); omega
  have hQW : ∀ p ∈ Q.map cast2, p ∉ W := by
    intro p hp hpW
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
    have bv := hQin v hv
    simp only [hWe, List.mem_append, List.mem_cons, List.mem_map] at hpW
    rcases hpW with (h | ⟨u, hu, he⟩) | (h | ⟨m, hm, he⟩)
    · exact hdis xh List.mem_cons_self (cast2_inj h ▸ hv)
    · exact hdis u (List.mem_cons_of_mem _ hu) (cast2_inj he ▸ hv)
    · exact cast_ne_psi (by omega) bv.1 bv.2 h
    · rw [List.mem_range'_1] at hm
      exact cast_ne_psi (by omega) bv.1 bv.2 he.symm
  have hcd : parP W (cast2 c) = parP W (cast2 d) :=
    parP_chain hW (Q.map cast2) (chainZ_cast Q hQc) hQW _ (List.mem_map_of_mem hc_mem) _
      (List.mem_map_of_mem hd_mem)
  -- the count at a perimeter cell of `Q`
  have count : ∀ x ∈ Q, OnPerim R C x →
      cnt (isE (psi R C (anc R C x)) (psi R C (anc R C x + 1))) (steps W) =
        if lo ≤ anc R C x ∧ anc R C x < hi then 1 else 0 := by
    intro x hx px
    have bx := hQin x hx
    obtain ⟨rx1, rx2⟩ := anc_range hR hC bx.1 bx.2 px
    set k := anc R C x
    have off : ∀ u : ℕ × ℕ, u.1 < R → u.2 < C → ∀ t : Pz × Pz, (t.1 = cast2 u ∨ t.2 = cast2 u) →
        isE (psi R C k) (psi R C (k + 1)) t = false := by
      intro u h1 h2 t ht
      unfold isE
      simp only [decide_eq_false_iff_not, not_or]
      obtain ⟨t1, t2⟩ := t
      have n1 := cast_ne_psi (R := R) (C := C) (m := k) (by omega) h1 h2
      have n2 := cast_ne_psi (R := R) (C := C) (m := k + 1) (by omega) h1 h2
      simp only [Prod.mk.injEq] at ht ⊢
      rcases ht with rfl | rfl
      · exact ⟨fun h => n1 h.1, fun h => n2 h.1⟩
      · exact ⟨fun h => n2 h.2, fun h => n1 h.2⟩
    rw [hWe, cnt_steps_append, lastA, lastC, ← hconn, cnt_conn (by omega) (by omega)]
    have z1 : cnt (isE (psi R C k) (psi R C (k + 1))) (inner (cast2 xh :: A0.map cast2)) = 0 := by
      apply cnt_zero_all
      intro t ht
      have h1 := (mem_inner ht).1
      simp only [List.mem_cons, List.mem_map] at h1
      rcases h1 with h1 | ⟨u, hu, h1⟩
      · exact off xh bh.1 bh.2 t (Or.inl h1)
      · have := inb (List.mem_cons_of_mem _ hu)
        exact off u this.1 this.2 t (Or.inl h1.symm)
    rw [z1, off xl bl.1 bl.2 _ (Or.inl rfl), off xh bh.1 bh.2 _ (Or.inr rfl)]
    simp
  have fc := face_parP hW bc.1 bc.2 pc (hQW _ (List.mem_map_of_mem hc_mem))
  have fd := face_parP hW bd.1 bd.2 pd (hQW _ (List.mem_map_of_mem hd_mem))
  rw [par_face hR hC hW hB bc.1 bc.2 pc, count c hc_mem pc] at fc
  rw [par_face hR hC hW hB bd.1 bd.2 pd, count d hd_mem pd] at fd
  rw [hcd] at fc
  split_ifs at fc fd ⊢ <;> omega

end ZZN.Planar

namespace ZZN

open Planar

theorem crosses_congr {k0 k1 k2 k3 m0 m1 m2 m3 : ℕ}
    (e02 : k0 < k2 ↔ m0 < m2) (e20 : k2 < k0 ↔ m2 < m0) (e12 : k1 < k2 ↔ m1 < m2)
    (e21 : k2 < k1 ↔ m2 < m1) (e03 : k0 < k3 ↔ m0 < m3) (e30 : k3 < k0 ↔ m3 < m0)
    (e13 : k1 < k3 ↔ m1 < m3) (e31 : k3 < k1 ↔ m3 < m1) :
    Crosses k0 k1 k2 k3 ↔ Crosses m0 m1 m2 m3 := by
  unfold Crosses
  rw [e02, e20, e12, e21, e03, e30, e13, e31]

/-- **T1 is sound**: on a solvable instance, the endpoints never alternate around the perimeter. -/
theorem t1_sound {I : Inst} (hwf : I.WellFormed) (hR : 2 ≤ I.w) (hC : 2 ≤ I.h) (hS : Solvable I) :
    t1Fires I.w I.h [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)] = false := by
  obtain ⟨b0, b1, b2, b3, d1, d2, d3, d4, d5, d6⟩ := hwf
  obtain ⟨p, q, hp, hq, hd, -⟩ := hS
  by_contra hf
  rw [Bool.not_eq_false] at hf
  unfold t1Fires at hf
  simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, List.zip_cons_cons, List.zip_nil_right] at hf
  obtain ⟨⟨s0p, t0p, s1p, t1p⟩, halt⟩ := hf
  unfold GridHam.InBounds at b0 b1 b2 b3
  rw [perimIndex_isSome b0.1 b0.2] at s0p
  rw [perimIndex_isSome b1.1 b1.2] at t0p
  rw [perimIndex_isSome b2.1 b2.2] at s1p
  rw [perimIndex_isSome b3.1 b3.2] at t1p
  have PI := fun {x y : ℕ × ℕ} (hx : x.1 < I.w ∧ x.2 < I.h) (hy : y.1 < I.w ∧ y.2 < I.h) hpx hpy (hxy : x ≠ y) =>
    perimIndex_inj (R := I.w) (C := I.h) hR hC hx.1 hx.2 hy.1 hy.2 hpx hpy hxy
  rw [alt_cross (PI b0 b1 s0p t0p d1) (PI b0 b2 s0p s1p d2) (PI b0 b3 s0p t1p d3) (PI b1 b2 t0p s1p d4)
    (PI b1 b3 t0p t1p d5) (PI b2 b3 s1p t1p d6)] at halt
  -- pass to the anchors
  have O := fun {x y : ℕ × ℕ} (hx : x.1 < I.w ∧ x.2 < I.h) (hy : y.1 < I.w ∧ y.2 < I.h) hpx hpy =>
    anc_order (R := I.w) (C := I.h) hR hC hx.1 hx.2 hy.1 hy.2 hpx hpy
  have o := fun {x y : ℕ × ℕ} (hx : x.1 < I.w ∧ x.2 < I.h) (hy : y.1 < I.w ∧ y.2 < I.h) hpx hpy =>
    O hx hy hpx hpy
  rw [crosses_congr (o b0 b2 s0p s1p) (o b2 b0 s1p s0p) (o b1 b2 t0p s1p) (o b2 b1 s1p t0p)
    (o b0 b3 s0p t1p) (o b3 b0 t1p s0p) (o b1 b3 t0p t1p) (o b3 b1 t1p t0p)] at halt
  -- anchors of distinct perimeter cells differ
  have AI : ∀ {x y : ℕ × ℕ}, x.1 < I.w ∧ x.2 < I.h → y.1 < I.w ∧ y.2 < I.h → OnPerim I.w I.h x →
      OnPerim I.w I.h y → x ≠ y → anc I.w I.h x ≠ anc I.w I.h y := by
    intro x y hx hy hpx hpy hxy he
    have o1 := O hx hy hpx hpy
    have o2 := O hy hx hpy hpx
    have := PI hx hy hpx hpy hxy
    omega
  have a01 := AI b0 b1 s0p t0p d1
  have a02 := AI b0 b2 s0p s1p d2
  have a03 := AI b0 b3 s0p t1p d3
  have a12 := AI b1 b2 t0p s1p d4
  have a13 := AI b1 b3 t0p t1p d5
  have hr := hp.reverse
  obtain ⟨rph, rpl, -, rpin, rpc⟩ := hr
  obtain ⟨hph, hpl, -, hpin, hpc⟩ := hp
  obtain ⟨hqh, hql, -, hqin, hqc⟩ := hq
  have hQin : ∀ v ∈ q, v.1 < I.w ∧ v.2 < I.h := fun v hv => hqin v hv
  unfold Crosses at halt
  rcases Nat.lt_or_gt_of_ne a01 with hlt | hlt
  · -- the path runs from the lower anchor: reverse it
    have core := t1_core hR hC rpc hqc (fun v hv => rpin v hv) hQin
      (fun v hv => hd v (List.mem_reverse.mp hv)) rph rpl hqh hql t0p s0p s1p t1p hlt
    split_ifs at core <;> omega
  · have core := t1_core hR hC hpc hqc (fun v hv => hpin v hv) hQin hd hph hpl hqh hql s0p t0p s1p t1p hlt
    split_ifs at core <;> omega

end ZZN

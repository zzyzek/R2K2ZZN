/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.StripExtend
public import ZZN.Constr.Band
public import ZZN.Symmetry

@[expose] public section

/-!
# Widening at an edge by a block, in one splice

`edgeBlock w h y k` is a path through the block of columns `w … w + 2k - 1` (rows `0 … h - 1`)
from `(w, y)` to `(w, y + 1)`: a column snake over the rows `y, y - 1, …, 0`, then one over the
rows `y + 1, …, h - 1`, walked back. Spliced into a path edge `(w - 1, y) – (w - 1, y + 1)` on the
last line, it turns a solution of `I` into one of `I.widen (2 k)`, in time linear in the paths and
the block.
-/

namespace ZZN

open GridHam

/-! ### Column snakes -/

/-- The cells of column `x` in the rows of `A`, in order. -/
def colRun (x : ℕ) (A : List ℕ) : List Coord := A.map fun y => (x, y)

/-- `k` pairs of columns from `x`: the first of each pair walks `A`, the second walks it back. -/
def colSnake (x : ℕ) (A : List ℕ) : ℕ → List Coord
  | 0 => []
  | k + 1 => colSnake x A k ++ (colRun (x + 2 * k) A ++ colRun (x + 2 * k + 1) A.reverse)

/-- Consecutive entries differ by one. -/
def Steps : List ℕ → Prop
  | a :: b :: l => (a + 1 = b ∨ b + 1 = a) ∧ Steps (b :: l)
  | _ => True

theorem steps_reverse : ∀ A : List ℕ, Steps A → Steps A.reverse
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: l, ⟨h1, h2⟩ => by
    have ih := steps_reverse (b :: l) h2
    rw [List.reverse_cons]
    -- appending `a` after the reversed tail ending in `b`
    have key : ∀ (L : List ℕ) (c : ℕ), Steps L → L.getLast? = some b → (c + 1 = b ∨ b + 1 = c) →
        Steps (L ++ [c]) := by
      intro L c
      induction L with
      | nil => intro _ h; simp at h
      | cons x L ihL =>
        intro hs hl hc
        cases L with
        | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hl
          subst hl
          exact ⟨by omega, trivial⟩
        | cons y L =>
          exact ⟨hs.1, ihL hs.2 (by simpa using hl) hc⟩
    exact key _ a ih (by simp) (by omega)

theorem colRun_chain (x : ℕ) : ∀ A : List ℕ, Steps A → chainAdjacent (colRun x A) = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, ⟨h1, h2⟩ => by
    have ih := colRun_chain x (b :: l) h2
    simp only [colRun, List.map_cons] at ih ⊢
    rw [chainAdjacent_cons_cons, Bool.and_eq_true]
    refine ⟨?_, ih⟩
    simp [adjacentB, Adjacent]; omega

theorem mem_colRun {x : ℕ} {A : List ℕ} {v : Coord} : v ∈ colRun x A ↔ v.1 = x ∧ v.2 ∈ A := by
  obtain ⟨v1, v2⟩ := v
  simp only [colRun, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨y, hy, rfl, rfl⟩; exact ⟨rfl, hy⟩
  · rintro ⟨rfl, hy⟩; exact ⟨v2, hy, rfl, rfl⟩

theorem mem_colSnake {x : ℕ} {A : List ℕ} {v : Coord} :
    ∀ {k}, v ∈ colSnake x A k ↔ x ≤ v.1 ∧ v.1 < x + 2 * k ∧ v.2 ∈ A
  | 0 => by simp [colSnake]; omega
  | k + 1 => by
    rw [colSnake, List.mem_append, List.mem_append, mem_colSnake, mem_colRun, mem_colRun,
      List.mem_reverse]
    constructor
    · rintro ((⟨h1, h2, h3⟩) | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> refine ⟨by omega, by omega, ‹_›⟩
    · rintro ⟨h1, h2, h3⟩
      by_cases h : v.1 < x + 2 * k
      · exact Or.inl ⟨h1, h, h3⟩
      · by_cases h' : v.1 = x + 2 * k
        · exact Or.inr (Or.inl ⟨h', h3⟩)
        · exact Or.inr (Or.inr ⟨by omega, h3⟩)

theorem colSnake_nodup {x : ℕ} {A : List ℕ} (hA : A.Nodup) : ∀ k, (colSnake x A k).Nodup
  | 0 => List.nodup_nil
  | k + 1 => by
    have runN : ∀ c (B : List ℕ), B.Nodup → (colRun c B).Nodup := fun c B hB =>
      List.Nodup.map (fun a b h => by simpa using h) hB
    rw [colSnake, List.nodup_append, List.nodup_append]
    refine ⟨colSnake_nodup hA k, ⟨runN _ _ hA, runN _ _ (List.nodup_reverse.mpr hA), ?_⟩, ?_⟩
    · intro u hu v hv he
      subst he
      have := (mem_colRun.mp hu).1; have := (mem_colRun.mp hv).1; omega
    · intro u hu v hv he
      subst he
      have := (mem_colSnake.mp hu).2.1
      rcases List.mem_append.mp hv with hv | hv <;> have := (mem_colRun.mp hv).1 <;> omega

theorem colSnake_head {x : ℕ} {A : List ℕ} {a : ℕ} (hA : A.head? = some a) :
    ∀ k, 0 < k → (colSnake x A k).head? = some (x, a)
  | 0, h => absurd h (by omega)
  | 1, _ => by
    obtain ⟨l, rfl⟩ : ∃ l, A = a :: l := by
      cases A with
      | nil => simp at hA
      | cons b l => simp at hA; exact ⟨l, by rw [hA]⟩
    simp [colSnake, colRun]
  | k + 2, _ => by
    rw [colSnake, List.head?_append, colSnake_head hA (k + 1) (by omega)]; rfl

theorem colSnake_last {x : ℕ} {A : List ℕ} {a : ℕ} (hA : A.head? = some a) :
    ∀ k, 0 < k → (colSnake x A k).getLast? = some (x + 2 * k - 1, a)
  | 0, h => absurd h (by omega)
  | k + 1, _ => by
    obtain ⟨l, rfl⟩ : ∃ l, A = a :: l := by
      cases A with
      | nil => simp at hA
      | cons b l => simp at hA; exact ⟨l, by rw [hA]⟩
    rw [colSnake, List.getLast?_append, List.getLast?_append]
    simp [colRun, List.getLast?_reverse]
    omega

theorem colSnake_chain {x : ℕ} {A : List ℕ} (hA : Steps A) (hne : A ≠ []) :
    ∀ k, chainAdjacent (colSnake x A k) = true
  | 0 => rfl
  | k + 1 => by
    obtain ⟨a, l, rfl⟩ : ∃ a l, A = a :: l := by
      cases A with
      | nil => exact absurd rfl hne
      | cons b l => exact ⟨b, l, rfl⟩
    have hhead : (a :: l).head? = some a := rfl
    have c1 := colRun_chain (x + 2 * k) (a :: l) hA
    have c2 := colRun_chain (x + 2 * k + 1) (a :: l).reverse (steps_reverse _ hA)
    obtain ⟨z, hzl⟩ : ∃ z, (a :: l).getLast? = some z := ⟨_, List.getLast?_eq_some_getLast (List.cons_ne_nil a l)⟩
    have hz1 : (colRun (x + 2 * k) (a :: l)).getLast? = some (x + 2 * k, z) := by
      rw [colRun, List.getLast?_map, hzl]; rfl
    have hz2 : (colRun (x + 2 * k + 1) (a :: l).reverse).head? = some (x + 2 * k + 1, z) := by
      rw [colRun, List.head?_map, List.head?_reverse, hzl]; rfl
    have c12 : chainAdjacent (colRun (x + 2 * k) (a :: l) ++ colRun (x + 2 * k + 1) (a :: l).reverse)
        = true :=
      chainAdjacent_append_of c1 c2 hz1 hz2 (by unfold Adjacent; omega)
    rw [colSnake]
    cases k with
    | zero => simpa [colSnake] using c12
    | succ k =>
      refine chainAdjacent_append_of (colSnake_chain hA hne (k + 1)) c12
        (colSnake_last hhead (k + 1) (by omega))
        (show (colRun (x + 2 * (k + 1)) (a :: l) ++ colRun (x + 2 * (k + 1) + 1) (a :: l).reverse).head?
          = some (x + 2 * (k + 1), a) by simp [colRun]) ?_
      unfold Adjacent; omega

theorem colSnake_ne_nil {x : ℕ} {A : List ℕ} {a : ℕ} (hA : A.head? = some a) {k : ℕ} (hk : 0 < k) :
    colSnake x A k ≠ [] := by
  intro he
  have := colSnake_head (x := x) hA k hk
  rw [he] at this
  simp at this

/-! ### The edge block -/

/-- Rows `y, y - 1, …, 0`. -/
def rowsDown (y : ℕ) : List ℕ := (List.range (y + 1)).reverse

/-- Rows `y + 1, …, h - 1`. -/
def rowsUp (y h : ℕ) : List ℕ := (List.range (h - (y + 1))).map (· + (y + 1))

/-- The block of columns `w … w + 2k - 1`, from `(w, y)` to `(w, y + 1)`. -/
def edgeBlock (w h y k : ℕ) : List Coord :=
  colSnake w (rowsDown y) k ++ (colSnake w (rowsUp y h) k).reverse

theorem steps_rowsDown (y : ℕ) : Steps (rowsDown y) := by
  have : ∀ n, Steps (List.range n) := by
    intro n
    induction n with
    | zero => trivial
    | succ n ih =>
      rw [List.range_succ]
      cases n with
      | zero => trivial
      | succ n =>
        have key : ∀ (L : List ℕ) (c : ℕ), Steps L → L.getLast? = some n → Steps (L ++ [c + n + 1 - c]) := by
          intro L c
          induction L with
          | nil => intro _ h; simp at h
          | cons x L ihL =>
            intro hs hl
            cases L with
            | nil =>
              simp only [List.getLast?_singleton, Option.some.injEq] at hl
              subst hl
              exact ⟨by omega, trivial⟩
            | cons y L => exact ⟨hs.1, ihL hs.2 (by simpa using hl)⟩
        have := key (List.range (n + 1)) 0 ih (by simp [List.getLast?_range])
        simpa using this
  exact steps_reverse _ (this (y + 1))

theorem steps_rowsUp (y h : ℕ) : Steps (rowsUp y h) := by
  unfold rowsUp
  generalize h - (y + 1) = n
  induction n with
  | zero => trivial
  | succ n ih =>
    rw [List.range_succ, List.map_append]
    cases n with
    | zero => trivial
    | succ n =>
      have key : ∀ (L : List ℕ), Steps L → L.getLast? = some (n + (y + 1)) →
          Steps (L ++ [n + 1 + (y + 1)]) := by
        intro L
        induction L with
        | nil => intro _ h; simp at h
        | cons x L ihL =>
          intro hs hl
          cases L with
          | nil =>
            simp only [List.getLast?_singleton, Option.some.injEq] at hl
            subst hl
            exact ⟨by omega, trivial⟩
          | cons z L => exact ⟨hs.1, ihL hs.2 (by simpa using hl)⟩
      simpa using key _ ih (by simp [List.getLast?_map, List.getLast?_range])

theorem length_rowsUp (y h : ℕ) : (rowsUp y h).length = h - (y + 1) := by simp [rowsUp]

theorem mem_edgeBlock {w h y k : ℕ} (hy : y + 1 < h) {v : Coord} :
    v ∈ edgeBlock w h y k ↔ w ≤ v.1 ∧ v.1 < w + 2 * k ∧ v.2 < h := by
  unfold edgeBlock rowsDown rowsUp
  rw [List.mem_append, List.mem_reverse, mem_colSnake, mem_colSnake]
  simp only [List.mem_reverse, List.mem_range, List.mem_map]
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, z, hz, he⟩) <;> omega
  · rintro ⟨h1, h2, h3⟩
    by_cases hv : v.2 < y + 1
    · exact Or.inl ⟨h1, h2, hv⟩
    · exact Or.inr ⟨h1, h2, v.2 - (y + 1), by omega, by omega⟩

theorem edgeBlock_nodup {w h y k : ℕ} : (edgeBlock w h y k).Nodup := by
  unfold edgeBlock
  rw [List.nodup_append]
  refine ⟨colSnake_nodup (List.nodup_reverse.mpr List.nodup_range) k,
    List.nodup_reverse.mpr (colSnake_nodup ((List.nodup_range).map (fun a b h => by omega)) k), ?_⟩
  intro u hu v hv he
  subst he
  rw [List.mem_reverse] at hv
  have a := (mem_colSnake.mp hu).2.2
  have b := (mem_colSnake.mp hv).2.2
  simp only [rowsDown, rowsUp, List.mem_reverse, List.mem_range, List.mem_map] at a b
  obtain ⟨z, -, hz⟩ := b
  omega

/-- **The block joins `(w - 1, y)` to `(w - 1, y + 1)`.** -/
theorem edgeBlock_chain {w h y k : ℕ} (hw : 1 ≤ w) (hy : y + 1 < h) (hk : 0 < k) :
    chainAdjacent ((w - 1, y) :: (edgeBlock w h y k ++ [(w - 1, y + 1)])) = true := by
  have hd : (rowsDown y).head? = some y := by simp [rowsDown, List.head?_reverse, List.getLast?_range]
  have hu : (rowsUp y h).head? = some (y + 1) := by
    unfold rowsUp
    obtain ⟨n, hn⟩ : ∃ n, h - (y + 1) = n + 1 := ⟨h - (y + 1) - 1, by omega⟩
    rw [hn, List.head?_map]
    have : (List.range (n + 1)).head? = some 0 := by simp [List.head?_range]
    rw [this]; simp
  have cD := colSnake_chain (x := w) (steps_rowsDown y) (by simp [rowsDown]) k
  have cU := colSnake_chain (x := w) (steps_rowsUp y h)
    (by intro he; have := congrArg List.length he; rw [length_rowsUp] at this; simp at this; omega) k
  have cUr := chainAdjacent_reverse _ cU
  have c1 : chainAdjacent ([(w - 1, y)] ++ colSnake w (rowsDown y) k) = true :=
    chainAdjacent_append_of (a := (w - 1, y)) (b := (w, y)) rfl cD rfl (colSnake_head hd k hk)
      (Or.inr ⟨rfl, Or.inl (by omega)⟩)
  have c2 : chainAdjacent (([(w - 1, y)] ++ colSnake w (rowsDown y) k) ++
      (colSnake w (rowsUp y h) k).reverse) = true :=
    chainAdjacent_append_of c1 cUr
      (by rw [List.getLast?_append_of_ne_nil _ (colSnake_ne_nil hd hk)]
          exact colSnake_last hd k hk)
      (by rw [List.head?_reverse]; exact colSnake_last hu k hk) (by unfold Adjacent; omega)
  have c3 := chainAdjacent_append_of c2 (show chainAdjacent [(w - 1, y + 1)] = true from rfl)
    (by
      rw [List.getLast?_append_of_ne_nil _ (by
        rw [Ne, List.reverse_eq_nil_iff]; exact colSnake_ne_nil hu hk)]
      rw [List.getLast?_reverse]; exact colSnake_head hu k hk)
    rfl (by unfold Adjacent; omega)
  simpa [edgeBlock] using c3

/-! ### The lift -/

/-- `u, v` is a step along the line `r` (a vertical edge on it). -/
def vertAt (r : ℕ) (u v : Coord) : Bool := u.1 = r ∧ v.1 = r ∧ (u.2 + 1 = v.2 ∨ v.2 + 1 = u.2)

/-- The first step of `L` along the line `r`. -/
def findV (r : ℕ) : List Coord → Option (Coord × Coord)
  | u :: v :: l => if vertAt r u v then some (u, v) else findV r (v :: l)
  | _ => none

theorem findV_some {r : ℕ} : ∀ {L : List Coord} {a b : Coord}, findV r L = some (a, b) →
    [a, b] <:+: L ∧ vertAt r a b = true
  | u :: v :: l, a, b, h => by
    unfold findV at h
    split_ifs at h with hv
    · cases h; exact ⟨⟨[], l, rfl⟩, hv⟩
    · obtain ⟨hi, hv'⟩ := findV_some h
      exact ⟨hi.trans (List.suffix_cons u _).isInfix, hv'⟩
  | [], _, _, h => by simp [findV] at h
  | [_], _, _, h => by simp [findV] at h

theorem findV_none {r : ℕ} : ∀ {L : List Coord}, findV r L = none →
    ∀ a b, [a, b] <:+: L → vertAt r a b = false
  | u :: v :: l, h, a, b, hab => by
    unfold findV at h
    split_ifs at h with hv
    obtain ⟨l₁, l₂, he⟩ := infix_pair_iff.mp hab
    cases l₁ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl, -⟩ := he
      simpa using hv
    | cons z l₁ =>
      simp only [List.cons_append, List.cons.injEq] at he
      exact findV_none h a b (infix_pair_iff.mpr ⟨l₁, l₂, he.2⟩)
  | [], _, a, b, hab => by
    obtain ⟨l₁, l₂, he⟩ := infix_pair_iff.mp hab
    simp at he
  | [_], _, a, b, hab => by
    obtain ⟨l₁, l₂, he⟩ := infix_pair_iff.mp hab
    cases l₁ with
    | nil => simp at he
    | cons z l₁ => simp at he

/-- The block for the edge `a – b` on the line `w - 1`, walked from `a` to `b`. -/
def blkE (w h k : ℕ) (a b : Coord) : List Coord :=
  if a.2 < b.2 then edgeBlock w h a.2 k else (edgeBlock w h b.2 k).reverse

theorem mem_blkE {w h k : ℕ} {a b : Coord} (hab : a.2 + 1 = b.2 ∨ b.2 + 1 = a.2)
    (ha : a.2 < h) (hb : b.2 < h) {v : Coord} :
    v ∈ blkE w h k a b ↔ w ≤ v.1 ∧ v.1 < w + 2 * k ∧ v.2 < h := by
  unfold blkE
  split_ifs with hl
  · exact mem_edgeBlock (by omega)
  · rw [List.mem_reverse]; exact mem_edgeBlock (by omega)

theorem blkE_nodup {w h k : ℕ} {a b : Coord} : (blkE w h k a b).Nodup := by
  unfold blkE
  split_ifs
  · exact edgeBlock_nodup
  · exact List.nodup_reverse.mpr edgeBlock_nodup

theorem blkE_chain {w h k : ℕ} {a b : Coord} (hw : 1 ≤ w) (hk : 0 < k)
    (hv : vertAt (w - 1) a b = true) (ha : a.2 < h) (hb : b.2 < h) :
    chainAdjacent (a :: (blkE w h k a b ++ [b])) = true := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [vertAt, decide_eq_true_eq] at hv
  obtain ⟨rfl, rfl, hv⟩ := hv
  unfold blkE
  simp only
  split_ifs with hl
  · obtain rfl : b2 = a2 + 1 := by omega
    exact edgeBlock_chain hw (by omega) hk
  · obtain rfl : a2 = b2 + 1 := by omega
    have := chainAdjacent_reverse _ (edgeBlock_chain (w := w) (h := h) (y := b2) (k := k) hw (by omega) hk)
    simpa using this

/-- **The right edge lift**: splice the block of the new columns `w … w + 2k - 1` into the first
step along the line `w - 1`, of `p` if it has one, else of `q`. -/
def edgeLift (w h k : ℕ) (p q : List Coord) : List Coord × List Coord :=
  match findV (w - 1) p with
  | some (a, b) => (insB a b (blkE w h k a b) p, q)
  | none =>
    match findV (w - 1) q with
    | some (a, b) => (p, insB a b (blkE w h k a b) q)
    | none => (p, q)

/-- A solution uses a step along its last line, when the lines have length at least 5. -/
theorem exists_vert {I : Inst} {p q : List Coord} (h5 : 5 ≤ I.h) (hsol : IsSolution I p q) :
    ∃ a b, ([a, b] <:+: p ∨ [a, b] <:+: q) ∧ vertAt (I.w - 1) a b = true := by
  have hw : 0 < I.w := by
    have hs0 : I.s0 ∈ p := List.mem_of_mem_head? hsol.1.1
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) (hsol.1.2.2.2.1 _ hs0).1
  set r := I.w - 1 with hr
  have hrw : r < I.w := by omega
  obtain ⟨hp, hq, -, hcov⟩ := hsol
  have noUse : ∀ {L : List Coord} {s t : Coord} {y : ℕ}, IsPath I.w I.h s t L →
      ¬ Used L (r, y) (r + 1, y) := by
    intro L s t y hL hu
    have := (hL.2.2.2.1 _ hu.mem_right).1
    simp only at this
    omega
  obtain ⟨y0, hy05, f0, f1, f2, f3⟩ := exists_free_cell I r
  have mk : ∀ {L : List Coord} {y'}, (y' + 1 = y0 ∨ y0 + 1 = y') → Used L (r, y0) (r, y') →
      ∃ a b, [a, b] <:+: L ∧ vertAt r a b = true := by
    intro L y' hadj hu
    rcases hu with hu | hu
    · exact ⟨_, _, hu, by simp [vertAt]; omega⟩
    · exact ⟨_, _, hu, by simp [vertAt]; omega⟩
  rcases hcov (r, y0) ⟨hrw, by omega⟩ with hv | hv
  · obtain ⟨y', a, -, u⟩ := exists_row_edge hp hv (Ne.symm f0) (Ne.symm f1) (noUse hp)
    obtain ⟨a', b', hi, hvt⟩ := mk a u
    exact ⟨a', b', Or.inl hi, hvt⟩
  · obtain ⟨y', a, -, u⟩ := exists_row_edge hq hv (Ne.symm f2) (Ne.symm f3) (noUse hq)
    obtain ⟨a', b', hi, hvt⟩ := mk a u
    exact ⟨a', b', Or.inr hi, hvt⟩

/-- **The right edge lift is a solution** of the instance widened by `2k` lines. -/
theorem edgeLift_sol {I : Inst} {p q : List Coord} {k : ℕ} (h5 : 5 ≤ I.h) (hk : 0 < k)
    (hsol : IsSolution I p q) :
    IsSolution (I.widen (2 * k)) (edgeLift I.w I.h k p q).1 (edgeLift I.w I.h k p q).2 := by
  have hw : 1 ≤ I.w := by
    have hs0 : I.s0 ∈ p := List.mem_of_mem_head? hsol.1.1
    have := (hsol.1.2.2.2.1 _ hs0).1
    omega
  obtain ⟨hp, hq, hdisj, hcov⟩ := hsol
  have wp := hp.widen (w' := I.w + 2 * k) (by omega)
  have wq := hq.widen (w' := I.w + 2 * k) (by omega)
  -- facts about the block for a step `a – b` of a path along the last line
  have blk : ∀ {L : List Coord} {s t a b : Coord}, IsPath I.w I.h s t L → [a, b] <:+: L →
      vertAt (I.w - 1) a b = true →
      chainAdjacent (a :: (blkE I.w I.h k a b ++ [b])) = true ∧
      (∀ v, v ∈ blkE I.w I.h k a b ↔ I.w ≤ v.1 ∧ v.1 < I.w + 2 * k ∧ v.2 < I.h) := by
    intro L s t a b hL hab hv
    have ha := (hL.2.2.2.1 a (hab.subset (by simp))).2
    have hb := (hL.2.2.2.1 b (hab.subset (by simp))).2
    have hv' := hv
    simp only [vertAt, decide_eq_true_eq] at hv'
    exact ⟨blkE_chain hw hk hv ha hb, fun v => mem_blkE hv'.2.2 ha hb⟩
  have fresh : ∀ {L : List Coord} {s t : Coord} {X : List Coord}, IsPath I.w I.h s t L →
      (∀ v, v ∈ X ↔ I.w ≤ v.1 ∧ v.1 < I.w + 2 * k ∧ v.2 < I.h) → ∀ x ∈ X, x ∉ L := by
    intro L s t X hL hX x hx hxL
    have := (hL.2.2.2.1 x hxL).1
    have := ((hX x).mp hx).1
    omega
  have bnd : ∀ {X : List Coord}, (∀ v, v ∈ X ↔ I.w ≤ v.1 ∧ v.1 < I.w + 2 * k ∧ v.2 < I.h) →
      ∀ x ∈ X, InBounds (I.w + 2 * k) I.h x := by
    intro X hX x hx
    have := (hX x).mp hx
    unfold InBounds; omega
  have cover : ∀ {X : List Coord}, (∀ v, v ∈ X ↔ I.w ≤ v.1 ∧ v.1 < I.w + 2 * k ∧ v.2 < I.h) →
      ∀ v, InBounds (I.widen (2 * k)).w (I.widen (2 * k)).h v → v ∈ p ∨ v ∈ q ∨ v ∈ X := by
    intro X hX v hv
    by_cases hx : v.1 < I.w
    · rcases hcov v ⟨hx, hv.2⟩ with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr ((hX v).mpr ⟨by omega, ?_, hv.2⟩))
      have := hv.1; simp only [Inst.widen] at this; omega
  unfold edgeLift
  rcases hfp : findV (I.w - 1) p with _ | ⟨a, b⟩
  · rcases hfq : findV (I.w - 1) q with _ | ⟨a, b⟩
    · exfalso
      obtain ⟨a, b, hab | hab, hv⟩ := exists_vert h5 ⟨hp, hq, hdisj, hcov⟩
      · rw [findV_none hfp a b hab] at hv; simp at hv
      · rw [findV_none hfq a b hab] at hv; simp at hv
    · obtain ⟨hab, hv⟩ := findV_some hfq
      obtain ⟨hc, hX⟩ := blk hq hab hv
      obtain ⟨hQ, hmem, -, -⟩ := splice_edgeC wq hab hc blkE_nodup (bnd hX) (fresh hq hX)
      refine ⟨wp, hQ, ?_, ?_⟩
      · intro v hv' hvq
        rcases (hmem v).mp hvq with h | h
        · exact hdisj v hv' h
        · exact fresh hp hX v h hv'
      · intro v hv'
        rw [hmem]
        rcases cover hX v hv' with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
  · obtain ⟨hab, hv⟩ := findV_some hfp
    obtain ⟨hc, hX⟩ := blk hp hab hv
    obtain ⟨hP, hmem, -, -⟩ := splice_edgeC wp hab hc blkE_nodup (bnd hX) (fresh hp hX)
    refine ⟨hP, wq, ?_, ?_⟩
    · intro v hv' hvq
      rcases (hmem v).mp hv' with h | h
      · exact hdisj v h hvq
      · exact fresh hq hX v h hvq
    · intro v hv'
      rw [hmem]
      rcases cover hX v hv' with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
      · exact Or.inl (Or.inr h)

/-! ### The left edge, by reflection -/

/-- A map of the grid that is a bijection on cells and keeps adjacency carries a solution to the
image of the paths. -/
theorem IsSolution.map {I J : Inst} {p q : List Coord} (f : Coord → Coord)
    (hinj : ∀ u v, InBounds I.w I.h u → InBounds I.w I.h v → f u = f v → u = v)
    (hb : ∀ v, InBounds I.w I.h v → InBounds J.w J.h (f v))
    (hsurj : ∀ v, InBounds J.w J.h v → ∃ u, InBounds I.w I.h u ∧ f u = v)
    (hadj : ∀ u v, Adjacent u v → InBounds I.w I.h u → InBounds I.w I.h v → Adjacent (f u) (f v))
    (e0 : f I.s0 = J.s0) (e1 : f I.t0 = J.t0) (e2 : f I.s1 = J.s1) (e3 : f I.t1 = J.t1)
    (hS : IsSolution I p q) : IsSolution J (p.map f) (q.map f) := by
  obtain ⟨hp, hq, hd, hc⟩ := hS
  have path : ∀ {s t : Coord} {L : List Coord}, IsPath I.w I.h s t L →
      IsPath J.w J.h (f s) (f t) (L.map f) := by
    intro s t L hL
    obtain ⟨hh, hl, hn, hbL, hch⟩ := hL
    refine ⟨by rw [List.head?_map, hh]; rfl, by rw [List.getLast?_map, hl]; rfl, ?_,
      fun v hv => by obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv; exact hb u (hbL u hu), ?_⟩
    · exact List.Nodup.map_on (fun x hx y hy h => hinj x y (hbL x hx) (hbL y hy) h) hn
    · have : ∀ (l : List Coord), (∀ v ∈ l, InBounds I.w I.h v) → chainAdjacent l = true →
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
  refine ⟨e0 ▸ e1 ▸ path hp, e2 ▸ e3 ▸ path hq, ?_, ?_⟩
  · intro v hv hv'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    obtain ⟨u', hu', he⟩ := List.mem_map.mp hv'
    have := hinj u' u (hq.2.2.2.1 u' hu') (hp.2.2.2.1 u hu) he
    exact hd u hu (this ▸ hu')
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := hsurj v hv
    rcases hc u hu with h | h
    · exact Or.inl (List.mem_map_of_mem h)
    · exact Or.inr (List.mem_map_of_mem h)

/-- Reflection across the line `x = (w - 1) / 2` is a solution map from `w × h` to `w × h`. -/
theorem IsSolution.reflect {I J : Inst} {p q : List Coord} (hw : J.w = I.w) (hh : J.h = I.h)
    (e0 : reflX I.w I.s0 = J.s0) (e1 : reflX I.w I.t0 = J.t0) (e2 : reflX I.w I.s1 = J.s1)
    (e3 : reflX I.w I.t1 = J.t1) (hS : IsSolution I p q) :
    IsSolution J (p.map (reflX I.w)) (q.map (reflX I.w)) := by
  refine IsSolution.map (reflX I.w) ?_ ?_ ?_ ?_ e0 e1 e2 e3 hS
  · intro u v hu hv h
    obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v
    simp only [ZZN.reflX, Prod.mk.injEq] at h
    have := hu.1; have := hv.1
    simp only at *
    exact Prod.ext (by omega) h.2
  · intro v hv
    exact ⟨by simp [ZZN.reflX, hw]; have := hv.1; omega, by rw [hh]; exact hv.2⟩
  · intro v hv
    have h1 := hv.1; have h2 := hv.2
    rw [hw] at h1; rw [hh] at h2
    refine ⟨ZZN.reflX I.w v, ⟨by simp [ZZN.reflX]; omega, h2⟩, ?_⟩
    obtain ⟨v1, v2⟩ := v
    simp only [ZZN.reflX] at h1 ⊢
    exact Prod.ext (by simp; omega) rfl
  · intro u v h hu hv
    unfold Adjacent at h ⊢
    have := hu.1; have := hv.1
    simp only [ZZN.reflX]
    omega

/-- Widen by `k` lines at the edge `x = 0`: the endpoints move right by `k`. -/
def Inst.widenL (I : Inst) (k : ℕ) : Inst :=
  ⟨I.w + k, I.h, (I.s0.1 + k, I.s0.2), (I.t0.1 + k, I.t0.2), (I.s1.1 + k, I.s1.2),
    (I.t1.1 + k, I.t1.2)⟩

/-- **The left edge lift**: reflect, lift at the right edge, reflect back. -/
def edgeLiftL (w h k : ℕ) (p q : List Coord) : List Coord × List Coord :=
  ((edgeLift w h k (p.map (reflX w)) (q.map (reflX w))).1.map (reflX (w + 2 * k)),
   (edgeLift w h k (p.map (reflX w)) (q.map (reflX w))).2.map (reflX (w + 2 * k)))

/-- **The left edge lift is a solution** of the instance widened by `2k` lines at `x = 0`. -/
theorem edgeLiftL_sol {I : Inst} {p q : List Coord} {k : ℕ} (h5 : 5 ≤ I.h) (hk : 0 < k)
    (hsol : IsSolution I p q) :
    IsSolution (I.widenL (2 * k)) (edgeLiftL I.w I.h k p q).1 (edgeLiftL I.w I.h k p q).2 := by
  have inb : ∀ e ∈ [I.s0, I.t0, I.s1, I.t1], e.1 < I.w := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact (hsol.1.2.2.2.1 _ (List.mem_of_mem_head? hsol.1.1)).1
    · exact (hsol.1.2.2.2.1 _ (List.mem_of_mem_getLast? hsol.1.2.1)).1
    · exact (hsol.2.1.2.2.2.1 _ (List.mem_of_mem_head? hsol.2.1.1)).1
    · exact (hsol.2.1.2.2.2.1 _ (List.mem_of_mem_getLast? hsol.2.1.2.1)).1
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at inb
  have h1 := IsSolution.reflect (I := I) (J := I.reflectX) rfl rfl rfl rfl rfl rfl hsol
  have h2 := edgeLift_sol (I := I.reflectX) (k := k) h5 hk h1
  have back : ∀ e : Coord, e.1 < I.w →
      ZZN.reflX (I.w + 2 * k) (ZZN.reflX I.w e) = (e.1 + 2 * k, e.2) := by
    intro e he
    obtain ⟨e1, e2⟩ := e
    simp only [ZZN.reflX] at he ⊢
    exact Prod.ext (by simp; omega) rfl
  exact IsSolution.reflect (I := (I.reflectX).widen (2 * k)) (J := I.widenL (2 * k)) rfl rfl (back _ inb.1)
    (back _ inb.2.1) (back _ inb.2.2.1) (back _ inb.2.2.2) h2

end ZZN

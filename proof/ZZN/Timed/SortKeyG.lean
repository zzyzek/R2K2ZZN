/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Timed.SortKeyT

@[expose] public section

/-!
# The counted sort-based duplicate removal, for any witness type

The definitions and proofs of `Timed/SortKeyT.lean` with the witness type `Wit` replaced by any
type `β`: `dedupGT` returns `dedupK Prod.fst` (`dedupGT_ret`) and on `n ≤ 2 ^ k` entries whose
states have at most `C` pieces takes at most `(n + 1) + (C + 6) n (k + 1) + 1 + n (C + 1)` steps
(`dedupGT_time`).
-/

namespace ZZN.T

open ZZN ZZN.Thin GridHam

variable {β : Type}

/-- Merge two lists sorted by state. -/
def mergeGT : List (St × β) → List (St × β) → TimeM (List (St × β))
  | [], ys => pure ys
  | xs, [] => pure xs
  | x :: xs, y :: ys => do
    let c ← ltST y.1 x.1
    if !c then do
      let r ← mergeGT xs (y :: ys)
      pure (x :: r)
    else do
      let r ← mergeGT (x :: xs) ys
      pure (y :: r)
termination_by xs ys => xs.length + ys.length
/-- Split into the entries at even and at odd positions. -/
def splitGT : List (St × β) → TimeM (List (St × β) × List (St × β))
  | [] => pure ([], [])
  | [x] => pure ([x], [])
  | x :: y :: l => do
    let p ← splitGT l
    ⟨(x :: p.1, y :: p.2), 1⟩
/-- Merge sort by state, with fuel. -/
def msortGT : ℕ → List (St × β) → TimeM (List (St × β))
  | 0, l => pure l
  | f + 1, l => do
    let n ← lengthT l
    if n ≤ 1 then pure l else do
      let p ← splitGT l
      let a ← msortGT f p.1
      let b ← msortGT f p.2
      mergeGT a b
/-- Keep the first entry of each run of equal states. -/
def dedupAdjGT : List (St × β) → TimeM (List (St × β))
  | [] => pure []
  | [x] => pure [x]
  | x :: y :: l => do
    let e ← stEqT x.1 y.1
    if e then dedupAdjGT (x :: l) else do
      let r ← dedupAdjGT (y :: l)
      pure (x :: r)
termination_by l => l.length
/-- Remove duplicate states: sort by state, keep one entry per state. -/
def dedupGT (l : List (St × β)) : TimeM (List (St × β)) := do
  let n ← lengthT l
  let s ← msortGT n l
  dedupAdjGT s

lemma mergeGT_ret : ∀ xs ys : List (St × β), (mergeGT xs ys).ret = List.merge xs ys (leK Prod.fst)
  | [], ys => by simp [mergeGT]
  | x :: xs, [] => by simp [mergeGT]
  | x :: xs, y :: ys => by
    rw [mergeGT, List.cons_merge_cons]
    simp only [ret_bind, ltST_ret, leK]
    by_cases h : ltS y.1 x.1 = true
    · simp [h, mergeGT_ret (x :: xs) ys]
    · simp [h, mergeGT_ret xs (y :: ys)]
termination_by xs ys => xs.length + ys.length

lemma splitGT_ret : ∀ l : List (St × β), (splitGT l).ret = splitK l
  | [] => rfl
  | [_] => rfl
  | x :: y :: l => by simp [splitGT, splitK, splitGT_ret l]

lemma msortGT_ret : ∀ (f : ℕ) (l : List (St × β)), (msortGT f l).ret = msortK Prod.fst f l
  | 0, l => rfl
  | f + 1, l => by
    simp only [msortGT, msortK, ret_bind, lengthT]
    split_ifs
    · rfl
    · simp [splitGT_ret, msortGT_ret f, mergeGT_ret]

lemma dedupAdjGT_ret : ∀ l : List (St × β), (dedupAdjGT l).ret = dedupAdjK Prod.fst l
  | x :: y :: l => by
    rw [dedupAdjGT, dedupAdjK]
    simp only [ret_bind, stEqT_ret]
    by_cases h : x.1 = y.1
    · simp [h, dedupAdjGT_ret (x :: l)]
    · simp [h, dedupAdjGT_ret (y :: l)]
  | [] => by simp [dedupAdjGT, dedupAdjK]
  | [_] => by simp [dedupAdjGT, dedupAdjK]
termination_by l => l.length

lemma dedupGT_ret (l : List (St × β)) : (dedupGT l).ret = dedupK Prod.fst l := by
  simp [dedupGT, dedupK, lengthT, msortGT_ret, dedupAdjGT_ret]

/-! ### Step counts -/

lemma mergeGT_time (C : ℕ) : ∀ xs ys : List (St × β), (∀ x ∈ xs ++ ys, x.1.1.length ≤ C) →
    (mergeGT xs ys).time ≤ (xs.length + ys.length) * (C + 1)
  | [], ys, _ => by simp [mergeGT]
  | x :: xs, [], _ => by simp [mergeGT]
  | x :: xs, y :: ys, h => by
    rw [mergeGT]
    have hy := h y (by simp)
    have tc := ltST_time y.1 x.1
    simp only [time_bind]
    split_ifs
    · have ih := mergeGT_time C xs (y :: ys) (fun z hz => h z (by simp at hz ⊢; tauto))
      simp only [time_bind, time_pure, List.length_cons] at ih ⊢
      nlinarith
    · have ih := mergeGT_time C (x :: xs) ys (fun z hz => h z (by simp at hz ⊢; tauto))
      simp only [time_bind, time_pure, List.length_cons] at ih ⊢
      nlinarith
termination_by xs ys => xs.length + ys.length

lemma splitGT_time : ∀ l : List (St × β), (splitGT l).time ≤ l.length
  | [] => by simp [splitGT]
  | [_] => by simp [splitGT]
  | x :: y :: l => by
    have := splitGT_time l
    simp only [splitGT, time_bind, List.length_cons]
    omega

lemma msortGT_time (C : ℕ) : ∀ (f k : ℕ) (l : List (St × β)), l.length ≤ 2 ^ k →
    (∀ x ∈ l, x.1.1.length ≤ C) → (msortGT f l).time ≤ (C + 6) * l.length * (k + 1) + 1
  | 0, _, _, _, _ => by simp [msortGT]
  | f + 1, k, l, hl, hC => by
    simp only [msortGT, time_bind, lengthT]
    split_ifs with h1
    · simp only [time_pure]
      rcases Nat.lt_or_ge l.length 1 with h0 | h0
      · omega
      · have : (C + 6) * l.length * (k + 1) ≥ 1 := by
          have : 1 ≤ (C + 6) * l.length := Nat.one_le_iff_ne_zero.mpr (by positivity)
          nlinarith
        omega
    · obtain ⟨hp, hl1, hl2⟩ := splitK_spec l
      have hk : 1 ≤ k := by
        by_contra hk0
        have : k = 0 := by omega
        subst this; simp at hl; omega
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hpow : 2 ^ (k' + 1) = 2 * 2 ^ k' := by ring
      have hs := splitGT_ret l
      have h1' : (splitGT l).ret.1.length ≤ 2 ^ k' := by rw [hs]; omega
      have h2' : (splitGT l).ret.2.length ≤ 2 ^ k' := by rw [hs]; omega
      have sub : ∀ x ∈ (splitGT l).ret.1 ++ (splitGT l).ret.2, x ∈ l := fun x hx => by
        rw [hs] at hx; exact hp.subset hx
      have c1 : ∀ x ∈ (splitGT l).ret.1, x.1.1.length ≤ C := fun x hx =>
        hC x (sub x (List.mem_append_left _ hx))
      have c2 : ∀ x ∈ (splitGT l).ret.2, x.1.1.length ≤ C := fun x hx =>
        hC x (sub x (List.mem_append_right _ hx))
      have t1 := msortGT_time C f k' _ h1' c1
      have t2 := msortGT_time C f k' _ h2' c2
      have ts := splitGT_time l
      have hm : ∀ x ∈ (msortGT f (splitGT l).ret.1).ret ++ (msortGT f (splitGT l).ret.2).ret,
          x.1.1.length ≤ C := by
        intro x hx
        rw [msortGT_ret, msortGT_ret] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact c1 x ((msortK_perm Prod.fst f _).subset hx)
        · exact c2 x ((msortK_perm Prod.fst f _).subset hx)
      have len1 : (msortGT f (splitGT l).ret.1).ret.length = (splitGT l).ret.1.length := by
        rw [msortGT_ret]; exact (msortK_perm Prod.fst f _).length_eq
      have len2 : (msortGT f (splitGT l).ret.2).ret.length = (splitGT l).ret.2.length := by
        rw [msortGT_ret]; exact (msortK_perm Prod.fst f _).length_eq
      have tm := mergeGT_time C _ _ hm
      rw [len1, len2] at tm
      have hsum : (splitGT l).ret.1.length + (splitGT l).ret.2.length = l.length := by
        rw [hs, ← List.length_append]; exact hp.length_eq
      simp only [time_bind]
      generalize (mergeGT (msortGT f (splitGT l).ret.1).ret (msortGT f (splitGT l).ret.2).ret).time = Tm at *
      generalize (msortGT f (splitGT l).ret.1).time = T1 at *
      generalize (msortGT f (splitGT l).ret.2).time = T2 at *
      generalize (splitGT l).time = Ts at *
      generalize (splitGT l).ret.1.length = n1 at *
      generalize (splitGT l).ret.2.length = n2 at *
      generalize l.length = n at *
      have e1 : (C + 6) * n1 * (k' + 1) + (C + 6) * n2 * (k' + 1) = (C + 6) * n * (k' + 1) := by
        rw [← hsum]; ring
      have e2 : (n1 + n2) * (C + 1) = n * (C + 1) := by rw [hsum]
      have e3 : (C + 6) * n * (k' + 1 + 1) = (C + 6) * n * (k' + 1) + n * (C + 1) + 5 * n := by ring
      rw [e3]
      omega

lemma dedupAdjGT_time (C : ℕ) : ∀ l : List (St × β), (∀ x ∈ l, x.1.1.length ≤ C) →
    (dedupAdjGT l).time ≤ l.length * (C + 1)
  | x :: y :: l, h => by
    rw [dedupAdjGT]
    have hx := h x (by simp)
    have te := stEqT_time x.1 y.1
    simp only [time_bind]
    split_ifs
    · have ih := dedupAdjGT_time C (x :: l) (fun z hz => h z (by simp at hz ⊢; tauto))
      simp only [List.length_cons] at ih ⊢
      nlinarith
    · have ih := dedupAdjGT_time C (y :: l) (fun z hz => h z (by simp at hz ⊢; tauto))
      simp only [time_bind, time_pure, List.length_cons] at ih ⊢
      nlinarith
  | [], _ => by simp [dedupAdjGT]
  | [_], _ => by simp [dedupAdjGT]
termination_by l => l.length

/-- **Sort-based duplicate removal**: `O(n (k + 1) C)` steps on `n ≤ 2 ^ k` entries. -/
lemma dedupGT_time (C k : ℕ) (l : List (St × β)) (hl : l.length ≤ 2 ^ k)
    (hC : ∀ x ∈ l, x.1.1.length ≤ C) :
    (dedupGT l).time ≤ (l.length + 1) + ((C + 6) * l.length * (k + 1) + 1) + l.length * (C + 1) := by
  have t1 := msortGT_time C l.length k l hl hC
  have hs : ∀ x ∈ (msortGT l.length l).ret, x.1.1.length ≤ C := fun x hx => by
    rw [msortGT_ret] at hx; exact hC x ((msortK_perm Prod.fst _ l).subset hx)
  have t2 := dedupAdjGT_time C _ hs
  rw [msortGT_ret, (msortK_perm Prod.fst _ l).length_eq] at t2
  rw [← msortGT_ret] at t2
  simp only [dedupGT, time_bind, lengthT]
  omega

end ZZN.T

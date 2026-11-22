/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.TimedStatement
public import ZZN.Thin.SortKey
public import ZZN.Timed.TimeM

@[expose] public section

/-!
# The counted sort-based duplicate removal

`dedupKT` returns `dedupK Prod.fst` (`dedupKT_ret`). On a list of `n ≤ 2 ^ k` entries whose
states have at most `C` pieces it takes at most `(n + 1) + (C + 6) n (k + 1) + 1 + n (C + 1)` steps
(`dedupKT_time`): merge sort, not the quadratic scan of `dedupKeyT`.
-/

namespace ZZN.T

open ZZN ZZN.Thin GridHam

/-! ### Equality of states -/

lemma lbeqT_ret : ∀ l m : List ℕ, (lbeqT l m).ret = decide (l = m)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: l, y :: m => by
    unfold lbeqT
    by_cases h : x = y
    · subst h; simp [lbeqT_ret l m]
    · simp [h]

lemma stEqT_ret (s t : St) : (stEqT s t).ret = decide (s = t) := by
  simp only [stEqT, ret_bind, lbeqT_ret, ret_pure]
  rw [Bool.eq_iff_iff]
  simp [Prod.ext_iff]

lemma lbeqT_time : ∀ l m : List ℕ, (lbeqT l m).time ≤ l.length
  | [], [] => by simp [lbeqT]
  | [], _ :: _ => by simp [lbeqT]
  | _ :: _, [] => by simp [lbeqT]
  | x :: l, y :: m => by
    unfold lbeqT
    split
    · simp only [time_bind, List.length_cons]; have := lbeqT_time l m; omega
    · simp

lemma lbeqT_nil_time (l : List ℕ) : (lbeqT l []).time = 0 := by
  cases l <;> rfl

lemma stEqT_time (s t : St) : (stEqT s t).time ≤ s.1.length := by
  simp only [stEqT, time_bind, time_pure]; have := lbeqT_time s.1 t.1; omega

/-! ### Return values -/

lemma ltLT_ret : ∀ l m : List ℕ, (ltLT l m).ret = ltL l m
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: l, y :: m => by
    unfold ltLT ltL
    by_cases h1 : x < y
    · simp [h1]
    · by_cases h2 : x = y
      · subst h2; simp [ltLT_ret l m]
      · simp [h1, h2]

lemma ltST_ret (s t : St) : (ltST s t).ret = ltS s t := by
  simp [ltST, ltS, ltLT_ret]

lemma mergeKT_ret : ∀ xs ys : List (St × Wit), (mergeKT xs ys).ret = List.merge xs ys (leK Prod.fst)
  | [], ys => by simp [mergeKT]
  | x :: xs, [] => by simp [mergeKT]
  | x :: xs, y :: ys => by
    rw [mergeKT, List.cons_merge_cons]
    simp only [ret_bind, ltST_ret, leK]
    by_cases h : ltS y.1 x.1 = true
    · simp [h, mergeKT_ret (x :: xs) ys]
    · simp [h, mergeKT_ret xs (y :: ys)]
termination_by xs ys => xs.length + ys.length

lemma splitKT_ret : ∀ l : List (St × Wit), (splitKT l).ret = splitK l
  | [] => rfl
  | [_] => rfl
  | x :: y :: l => by simp [splitKT, splitK, splitKT_ret l]

lemma msortKT_ret : ∀ (f : ℕ) (l : List (St × Wit)), (msortKT f l).ret = msortK Prod.fst f l
  | 0, l => rfl
  | f + 1, l => by
    simp only [msortKT, msortK, ret_bind, lengthT]
    split_ifs
    · rfl
    · simp [splitKT_ret, msortKT_ret f, mergeKT_ret]

lemma dedupAdjKT_ret : ∀ l : List (St × Wit), (dedupAdjKT l).ret = dedupAdjK Prod.fst l
  | x :: y :: l => by
    rw [dedupAdjKT, dedupAdjK]
    simp only [ret_bind, stEqT_ret]
    by_cases h : x.1 = y.1
    · simp [h, dedupAdjKT_ret (x :: l)]
    · simp [h, dedupAdjKT_ret (y :: l)]
  | [] => by simp [dedupAdjKT, dedupAdjK]
  | [_] => by simp [dedupAdjKT, dedupAdjK]
termination_by l => l.length

lemma dedupKT_ret (l : List (St × Wit)) : (dedupKT l).ret = dedupK Prod.fst l := by
  simp [dedupKT, dedupK, lengthT, msortKT_ret, dedupAdjKT_ret]

/-! ### Step counts -/

lemma ltLT_time : ∀ l m : List ℕ, (ltLT l m).time ≤ l.length
  | [], [] => by simp [ltLT]
  | [], _ :: _ => by simp [ltLT]
  | _ :: _, [] => by simp [ltLT]
  | x :: l, y :: m => by
    unfold ltLT
    have := ltLT_time l m
    split_ifs <;> simp_all

lemma ltST_time (s t : St) : (ltST s t).time ≤ s.1.length := by
  simp only [ltST, time_bind, time_pure]; have := ltLT_time s.1 t.1; omega

lemma mergeKT_time (C : ℕ) : ∀ xs ys : List (St × Wit), (∀ x ∈ xs ++ ys, x.1.1.length ≤ C) →
    (mergeKT xs ys).time ≤ (xs.length + ys.length) * (C + 1)
  | [], ys, _ => by simp [mergeKT]
  | x :: xs, [], _ => by simp [mergeKT]
  | x :: xs, y :: ys, h => by
    rw [mergeKT]
    have hy := h y (by simp)
    have tc := ltST_time y.1 x.1
    simp only [time_bind]
    split_ifs
    · have ih := mergeKT_time C xs (y :: ys) (fun z hz => h z (by simp at hz ⊢; tauto))
      simp only [time_bind, time_pure, List.length_cons] at ih ⊢
      nlinarith
    · have ih := mergeKT_time C (x :: xs) ys (fun z hz => h z (by simp at hz ⊢; tauto))
      simp only [time_bind, time_pure, List.length_cons] at ih ⊢
      nlinarith
termination_by xs ys => xs.length + ys.length

lemma splitKT_time : ∀ l : List (St × Wit), (splitKT l).time ≤ l.length
  | [] => by simp [splitKT]
  | [_] => by simp [splitKT]
  | x :: y :: l => by
    have := splitKT_time l
    simp only [splitKT, time_bind, List.length_cons]
    omega

lemma msortKT_time (C : ℕ) : ∀ (f k : ℕ) (l : List (St × Wit)), l.length ≤ 2 ^ k →
    (∀ x ∈ l, x.1.1.length ≤ C) → (msortKT f l).time ≤ (C + 6) * l.length * (k + 1) + 1
  | 0, _, _, _, _ => by simp [msortKT]
  | f + 1, k, l, hl, hC => by
    simp only [msortKT, time_bind, lengthT]
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
      have hs := splitKT_ret l
      have h1' : (splitKT l).ret.1.length ≤ 2 ^ k' := by rw [hs]; omega
      have h2' : (splitKT l).ret.2.length ≤ 2 ^ k' := by rw [hs]; omega
      have sub : ∀ x ∈ (splitKT l).ret.1 ++ (splitKT l).ret.2, x ∈ l := fun x hx => by
        rw [hs] at hx; exact hp.subset hx
      have c1 : ∀ x ∈ (splitKT l).ret.1, x.1.1.length ≤ C := fun x hx =>
        hC x (sub x (List.mem_append_left _ hx))
      have c2 : ∀ x ∈ (splitKT l).ret.2, x.1.1.length ≤ C := fun x hx =>
        hC x (sub x (List.mem_append_right _ hx))
      have t1 := msortKT_time C f k' _ h1' c1
      have t2 := msortKT_time C f k' _ h2' c2
      have ts := splitKT_time l
      have hm : ∀ x ∈ (msortKT f (splitKT l).ret.1).ret ++ (msortKT f (splitKT l).ret.2).ret,
          x.1.1.length ≤ C := by
        intro x hx
        rw [msortKT_ret, msortKT_ret] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact c1 x ((msortK_perm Prod.fst f _).subset hx)
        · exact c2 x ((msortK_perm Prod.fst f _).subset hx)
      have len1 : (msortKT f (splitKT l).ret.1).ret.length = (splitKT l).ret.1.length := by
        rw [msortKT_ret]; exact (msortK_perm Prod.fst f _).length_eq
      have len2 : (msortKT f (splitKT l).ret.2).ret.length = (splitKT l).ret.2.length := by
        rw [msortKT_ret]; exact (msortK_perm Prod.fst f _).length_eq
      have tm := mergeKT_time C _ _ hm
      rw [len1, len2] at tm
      have hsum : (splitKT l).ret.1.length + (splitKT l).ret.2.length = l.length := by
        rw [hs, ← List.length_append]; exact hp.length_eq
      simp only [time_bind]
      generalize (mergeKT (msortKT f (splitKT l).ret.1).ret (msortKT f (splitKT l).ret.2).ret).time = Tm at *
      generalize (msortKT f (splitKT l).ret.1).time = T1 at *
      generalize (msortKT f (splitKT l).ret.2).time = T2 at *
      generalize (splitKT l).time = Ts at *
      generalize (splitKT l).ret.1.length = n1 at *
      generalize (splitKT l).ret.2.length = n2 at *
      generalize l.length = n at *
      have e1 : (C + 6) * n1 * (k' + 1) + (C + 6) * n2 * (k' + 1) = (C + 6) * n * (k' + 1) := by
        rw [← hsum]; ring
      have e2 : (n1 + n2) * (C + 1) = n * (C + 1) := by rw [hsum]
      have e3 : (C + 6) * n * (k' + 1 + 1) = (C + 6) * n * (k' + 1) + n * (C + 1) + 5 * n := by ring
      rw [e3]
      omega

lemma dedupAdjKT_time (C : ℕ) : ∀ l : List (St × Wit), (∀ x ∈ l, x.1.1.length ≤ C) →
    (dedupAdjKT l).time ≤ l.length * (C + 1)
  | x :: y :: l, h => by
    rw [dedupAdjKT]
    have hx := h x (by simp)
    have te := stEqT_time x.1 y.1
    simp only [time_bind]
    split_ifs
    · have ih := dedupAdjKT_time C (x :: l) (fun z hz => h z (by simp at hz ⊢; tauto))
      simp only [List.length_cons] at ih ⊢
      nlinarith
    · have ih := dedupAdjKT_time C (y :: l) (fun z hz => h z (by simp at hz ⊢; tauto))
      simp only [time_bind, time_pure, List.length_cons] at ih ⊢
      nlinarith
  | [], _ => by simp [dedupAdjKT]
  | [_], _ => by simp [dedupAdjKT]
termination_by l => l.length

/-- **Sort-based duplicate removal**: `O(n (k + 1) C)` steps on `n ≤ 2 ^ k` entries. -/
lemma dedupKT_time (C k : ℕ) (l : List (St × Wit)) (hl : l.length ≤ 2 ^ k)
    (hC : ∀ x ∈ l, x.1.1.length ≤ C) :
    (dedupKT l).time ≤ (l.length + 1) + ((C + 6) * l.length * (k + 1) + 1) + l.length * (C + 1) := by
  have t1 := msortKT_time C l.length k l hl hC
  have hs : ∀ x ∈ (msortKT l.length l).ret, x.1.1.length ≤ C := fun x hx => by
    rw [msortKT_ret] at hx; exact hC x ((msortK_perm Prod.fst _ l).subset hx)
  have t2 := dedupAdjKT_time C _ hs
  rw [msortKT_ret, (msortK_perm Prod.fst _ l).length_eq] at t2
  rw [← msortKT_ret] at t2
  simp only [dedupKT, time_bind, lengthT]
  omega

end ZZN.T

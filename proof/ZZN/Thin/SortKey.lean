/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Statement

@[expose] public section

/-!
# Removing duplicate states by sorting

`dedupK k l` sorts `l` by the state `k x` of each entry (merge sort with `List.merge`, fuel the
length of `l`), then keeps the first entry of each run of equal states. It keeps only entries of
`l` (`dedupK_sub`), every state of `l` (`mem_dedupK_key`), and each state once (`dedupK_nodup`).
These are the three facts the plug DP uses about removing duplicates.
-/

namespace ZZN.Thin

/-! ### The order on states -/

theorem ltL_irrefl : ∀ l : List ℕ, ltL l l = false
  | [] => rfl
  | x :: l => by simp [ltL, ltL_irrefl l]

theorem ltL_trans : ∀ l m n : List ℕ, ltL l m = true → ltL m n = true → ltL l n = true
  | [], [], _, h, _ => by simp [ltL] at h
  | [], _ :: _, [], _, h => by simp [ltL] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [ltL] at h
  | _ :: _, _ :: _, [], _, h => by simp [ltL] at h
  | x :: l, y :: m, z :: n, h1, h2 => by
    simp only [ltL, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
    rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
    · left; omega
    · left; omega
    · left; omega
    · right; exact ⟨rfl, ltL_trans l m n h1 h2⟩

theorem ltL_total : ∀ l m : List ℕ, ltL l m = true ∨ l = m ∨ ltL m l = true
  | [], [] => Or.inr (Or.inl rfl)
  | [], _ :: _ => Or.inl rfl
  | _ :: _, [] => Or.inr (Or.inr rfl)
  | x :: l, y :: m => by
    simp only [ltL, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
      List.cons.injEq]
    rcases Nat.lt_trichotomy x y with h | rfl | h
    · left; left; exact h
    · rcases ltL_total l m with h | rfl | h
      · left; right; exact ⟨rfl, h⟩
      · right; left; exact ⟨rfl, rfl⟩
      · right; right; right; exact ⟨rfl, h⟩
    · right; right; left; exact h

theorem ltS_irrefl (s : St) : ltS s s = false := by
  simp [ltS, ltL_irrefl]

theorem ltS_trans (s t u : St) (h1 : ltS s t = true) (h2 : ltS t u = true) : ltS s u = true := by
  unfold ltS at h1 h2 ⊢
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
  rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
  · left; omega
  · left; omega
  · left; omega
  · right; exact ⟨e1.trans e2, ltL_trans _ _ _ h1 h2⟩

theorem ltS_total (s t : St) : ltS s t = true ∨ s = t ∨ ltS t s = true := by
  unfold ltS
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
  rcases Nat.lt_trichotomy s.2 t.2 with h | h | h
  · left; left; exact h
  · rcases ltL_total s.1 t.1 with h' | h' | h'
    · left; right; exact ⟨h, h'⟩
    · right; left; exact Prod.ext h' h
    · right; right; right; exact ⟨h.symm, h'⟩
  · right; right; left; exact h

/-! ### Sorting by key -/

section
variable {α : Type} (k : α → St)

/-- `x` may come before `y`: the state of `y` is not smaller. -/
def leK (x y : α) : Bool := !(ltS (k y) (k x))

/-- Split a list into the entries at even and at odd positions. -/
def splitK : List α → List α × List α
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: l => (x :: (splitK l).1, y :: (splitK l).2)

/-- Merge sort by state, with fuel. -/
def msortK : ℕ → List α → List α
  | 0, l => l
  | f + 1, l => if l.length ≤ 1 then l else
      List.merge (msortK f (splitK l).1) (msortK f (splitK l).2) (leK k)

/-- Keep the first entry of each run of entries with equal states. -/
def dedupAdjK : List α → List α
  | x :: y :: l => if k x = k y then dedupAdjK (x :: l) else x :: dedupAdjK (y :: l)
  | l => l
termination_by l => l.length

/-- **Remove duplicate states**: sort by state, keep one entry per state. -/
def dedupK (l : List α) : List α := dedupAdjK k (msortK k l.length l)

theorem leK_trans (x y z : α) (h1 : leK k x y = true) (h2 : leK k y z = true) : leK k x z = true := by
  unfold leK at *
  simp only [Bool.not_eq_true'] at *
  by_contra h
  simp only [Bool.not_eq_false] at h
  rcases ltS_total (k z) (k y) with h3 | h3 | h3
  · rw [h2] at h3; simp at h3
  · rw [h3] at h; rw [h1] at h; simp at h
  · have := ltS_trans _ _ _ h3 h
    rw [h1] at this; simp at this

theorem leK_total (x y : α) : (leK k x y || leK k y x) = true := by
  unfold leK
  rcases ltS_total (k x) (k y) with h | h | h
  · have : ltS (k y) (k x) = false := by
      by_contra h'; simp only [Bool.not_eq_false] at h'
      have := ltS_trans _ _ _ h h'; rw [ltS_irrefl] at this; simp at this
    simp [this]
  · simp [h, ltS_irrefl]
  · have : ltS (k x) (k y) = false := by
      by_contra h'; simp only [Bool.not_eq_false] at h'
      have := ltS_trans _ _ _ h h'; rw [ltS_irrefl] at this; simp at this
    simp [this]

theorem splitK_spec : ∀ l : List α, ((splitK l).1 ++ (splitK l).2).Perm l ∧
    (splitK l).1.length ≤ (l.length + 1) / 2 ∧ (splitK l).2.length ≤ l.length / 2
  | [] => by simp [splitK]
  | [x] => by simp [splitK]
  | x :: y :: l => by
    obtain ⟨hp, h1, h2⟩ := splitK_spec l
    refine ⟨?_, ?_, ?_⟩
    · simp only [splitK, List.cons_append]
      refine List.Perm.cons x ?_
      have : ((splitK l).1 ++ y :: (splitK l).2).Perm (y :: ((splitK l).1 ++ (splitK l).2)) :=
        List.perm_middle
      exact this.trans (List.Perm.cons y hp)
    · simp only [splitK, List.length_cons]; omega
    · simp only [splitK, List.length_cons]; omega

theorem msortK_perm : ∀ (f : ℕ) (l : List α), (msortK k f l).Perm l
  | 0, l => by simp [msortK]
  | f + 1, l => by
    unfold msortK
    split_ifs
    · exact List.Perm.refl _
    · exact (List.merge_perm_append (leK k)).trans
        (((msortK_perm f _).append (msortK_perm f _)).trans (splitK_spec l).1)

theorem msortK_sorted : ∀ (f : ℕ) (l : List α), l.length ≤ f →
    (msortK k f l).Pairwise (fun x y => leK k x y = true)
  | 0, l, h => by
    unfold msortK
    match l, h with
    | [], _ => exact List.Pairwise.nil
  | f + 1, l, h => by
    unfold msortK
    split_ifs with h1
    · match l, h1 with
      | [], _ => exact List.Pairwise.nil
      | [_], _ => exact List.pairwise_singleton _ _
    · obtain ⟨-, l1, l2⟩ := splitK_spec l
      exact List.pairwise_merge (leK_trans k) (leK_total k) _ _
        (msortK_sorted f _ (by omega)) (msortK_sorted f _ (by omega))

theorem dedupAdjK_sub : ∀ (l : List α) (x : α), x ∈ dedupAdjK k l → x ∈ l
  | x :: y :: l, z, h => by
    unfold dedupAdjK at h
    split_ifs at h
    · have := dedupAdjK_sub (x :: l) z h
      simp only [List.mem_cons] at this ⊢; tauto
    · simp only [List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · have := dedupAdjK_sub (y :: l) z h
        simp only [List.mem_cons] at this ⊢; tauto
  | [], z, h => by simp [dedupAdjK] at h
  | [x], z, h => by simpa [dedupAdjK] using h
termination_by l => l.length

theorem mem_dedupAdjK_key : ∀ (l : List α) (s : St), s ∈ (dedupAdjK k l).map k ↔ s ∈ l.map k
  | x :: y :: l, s => by
    unfold dedupAdjK
    split_ifs with h
    · rw [mem_dedupAdjK_key (x :: l) s]
      simp only [List.map_cons, List.mem_cons]
      constructor
      · rintro (h' | h'); exacts [Or.inl h', Or.inr (Or.inr h')]
      · rintro (h' | h' | h'); exacts [Or.inl h', Or.inl (h'.trans h.symm), Or.inr h']
    · simp only [List.map_cons, List.mem_cons]
      rw [mem_dedupAdjK_key (y :: l) s]
      simp
  | [], s => by simp [dedupAdjK]
  | [x], s => by simp [dedupAdjK]
termination_by l => l.length

theorem dedupAdjK_nodup : ∀ (l : List α), l.Pairwise (fun x y => leK k x y = true) →
    ((dedupAdjK k l).map k).Nodup
  | x :: y :: l, hs => by
    unfold dedupAdjK
    split_ifs with h
    · exact dedupAdjK_nodup (x :: l)
        (List.Pairwise.cons (fun z hz => List.rel_of_pairwise_cons hs (List.mem_cons_of_mem _ hz))
          (hs.of_cons.of_cons))
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, dedupAdjK_nodup (y :: l) hs.of_cons⟩
      rw [mem_dedupAdjK_key] at hm
      obtain ⟨z, hz, hzk⟩ := List.mem_map.mp hm
      -- the state of `x` is below that of `y`, and every later entry is at least `y`
      have hxy : leK k x y = true := List.rel_of_pairwise_cons hs (by simp)
      have hlt : ltS (k x) (k y) = true := by
        unfold leK at hxy
        rcases ltS_total (k x) (k y) with h' | h' | h'
        · exact h'
        · exact absurd h' h
        · simp [h'] at hxy
      rcases List.mem_cons.mp hz with rfl | hz
      · exact h hzk.symm
      · have hyz : leK k y z = true := List.rel_of_pairwise_cons hs.of_cons hz
        unfold leK at hyz
        rcases ltS_total (k y) (k z) with h' | h' | h'
        · have := ltS_trans _ _ _ hlt h'
          rw [hzk, ltS_irrefl] at this; simp at this
        · rw [h', hzk] at hlt; rw [ltS_irrefl] at hlt; simp at hlt
        · simp [h'] at hyz
  | [], _ => by simp [dedupAdjK]
  | [x], _ => by simp [dedupAdjK]
termination_by l => l.length

theorem dedupK_sub {l : List α} {x : α} (h : x ∈ dedupK k l) : x ∈ l :=
  (msortK_perm k _ l).subset (dedupAdjK_sub k _ x h)

theorem mem_dedupK_key (l : List α) (s : St) : s ∈ (dedupK k l).map k ↔ s ∈ l.map k := by
  unfold dedupK
  rw [mem_dedupAdjK_key]
  exact (msortK_perm k _ l).map k |>.mem_iff

theorem dedupK_nodup (l : List α) : ((dedupK k l).map k).Nodup :=
  dedupAdjK_nodup k _ (msortK_sorted k _ l le_rfl)

end

end ZZN.Thin

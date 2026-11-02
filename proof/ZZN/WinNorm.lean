/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.WinCheck

@[expose] public section

/-!
# Window certificates: normalising a state list keeps its members

Split from `WinDP` so that the certificate engine does not import the soundness chain.
-/

namespace ZZN.Win

/-! ### Normalisation keeps every state -/

theorem mergeS_perm : ∀ (f : ℕ) (l m : List St), (mergeS f l m).Perm (l ++ m)
  | 0, l, m => by simp [mergeS]
  | _ + 1, [], m => by simp [mergeS]
  | _ + 1, x :: l, [] => by simp [mergeS]
  | f + 1, x :: l, y :: m => by
    unfold mergeS
    split_ifs
    · exact ((mergeS_perm f (x :: l) m).cons y).trans List.perm_middle.symm
    · exact (mergeS_perm f l (y :: m)).cons x

theorem splitS_perm : ∀ l : List St, ((splitS l).1 ++ (splitS l).2).Perm l
  | [] => by simp [splitS]
  | [x] => by simp [splitS]
  | x :: y :: l => by
    have := splitS_perm l
    simp only [splitS, List.cons_append]
    refine (List.Perm.cons x ?_)
    refine (List.perm_middle).trans ?_
    exact this.cons y

theorem msortS_perm : ∀ (f : ℕ) (l : List St), (msortS f l).Perm l
  | 0, l => by simp [msortS]
  | _ + 1, [] => by simp [msortS]
  | _ + 1, [x] => by simp [msortS]
  | f + 1, x :: y :: l => by
    unfold msortS
    refine (mergeS_perm _ _ _).trans ?_
    exact ((msortS_perm f _).append (msortS_perm f _)).trans (splitS_perm _)

theorem dedupAdj_mem : ∀ (l : List St) (s : St), s ∈ dedupAdj l ↔ s ∈ l
  | [], _ => by simp [dedupAdj]
  | [x], _ => by simp [dedupAdj]
  | x :: y :: l, s => by
    unfold dedupAdj
    split_ifs with h
    · rw [dedupAdj_mem (y :: l) s]
      simp only [beq_iff_eq] at h
      subst h
      simp
    · rw [List.mem_cons, dedupAdj_mem (y :: l) s]; exact List.mem_cons.symm

theorem mem_normS {l : List St} {s : St} : s ∈ normS l ↔ s ∈ l := by
  unfold normS; rw [dedupAdj_mem, (msortS_perm _ _).mem_iff]

end ZZN.Win

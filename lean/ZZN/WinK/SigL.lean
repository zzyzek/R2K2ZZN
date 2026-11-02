-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.WinK.FastE

/-!
# Final checks for several specifications at once

`finalSigOK` decodes each final state of a bucket and checks its signature for one
specification. `finalSigOKL` decodes each state once and checks it for every specification in a
list; within one declaration the kernel shares the decoded state. It decodes and searches with the
kernel-fast helpers of `FastE`. `finalSigOKL_get` recovers the
check for each specification.
-/

namespace ZZN.WinK

open ZZN ZZN.Win

noncomputable def finalSigOKL (a b : ℕ) (arr n : ℕ) (L : List (FSpec × ℕ × ℕ)) : Bool :=
  (List.range n).all fun k =>
    let s := decD (getWD arr k)
    L.all fun q =>
      let g := sigOf a b q.1 s
      let c := sigCode g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2
      sigDec c == g && bsearchD q.2.1 c 64 0 q.2.2

theorem finalSigOKL_get {a b arr n : ℕ} {L : List (FSpec × ℕ × ℕ)} (h : finalSigOKL a b arr n L = true)
    (i : ℕ) (hi : i < L.length) : finalSigOK a b L[i].1 arr n L[i].2.1 L[i].2.2 = true := by
  simp only [finalSigOKL, decD_eq, getWD_eq, bsearchD_eq] at h
  unfold finalSigOK
  rw [List.all_eq_true] at h ⊢
  intro k hk
  exact List.all_eq_true.mp (h k hk) _ (List.getElem_mem hi)

end ZZN.WinK

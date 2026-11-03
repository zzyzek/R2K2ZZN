/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Timed.Catalogue

@[expose] public section

/-!
# The time of the counted catalogue test

`fires3T_time`: the counted catalogue test takes at most `300000 (R + C + 1)` steps. Everything is
constant-size except the edge-closure scan along one side (`edgeClosureT`) and the outer walk
of the region (`walk3T`), whose length is at most `2 (R + C)` plus a constant.
-/

namespace ZZN.T

open ZZN

/-! ### Small facts -/

lemma lfoldlT_time_le {β α : Type} (f : β → α → TimeM β) (g : β → ℕ) (A B D : ℕ)
    (hT : ∀ b x, (f b x).time ≤ A + B * g b) (hG : ∀ b x, g (f b x).ret ≤ g b + D) :
    ∀ (l : List α) (b : β), (lfoldlT f b l).time ≤ l.length * (A + B * (g b + l.length * D) + 1)
  | [], b => by simp [lfoldlT]
  | x :: l, b => by
    have ih := lfoldlT_time_le f g A B D hT hG l (f b x).ret
    have h1 := hT b x
    have h2 := hG b x
    simp only [lfoldlT, List.length_cons]
    have h3 : B * g (f b x).ret ≤ B * (g b + D) := Nat.mul_le_mul_left _ h2
    have h4 : l.length * (A + B * (g (f b x).ret + l.length * D) + 1) ≤
        l.length * (A + B * (g b + (l.length + 1) * D) + 1) := by
      apply Nat.mul_le_mul_left
      have : B * (g (f b x).ret + l.length * D) ≤ B * (g b + (l.length + 1) * D) := by
        apply Nat.mul_le_mul_left; rw [Nat.succ_mul]; omega
      omega
    have h5 : A + B * g b ≤ A + B * (g b + (l.length + 1) * D) := by
      have : B * g b ≤ B * (g b + (l.length + 1) * D) := Nat.mul_le_mul_left _ (by omega)
      omega
    rw [Nat.succ_mul]
    omega

lemma len_filter_split {γ : Type} (p : γ → Bool) :
    ∀ l : List γ, (l.filter p).length + (l.filter (fun x => !p x)).length = l.length
  | [] => rfl
  | x :: l => by
    have := len_filter_split p l
    cases h : p x <;> simp [h] <;> omega

lemma length_sortByKey : ∀ l : List (ℕ × ℕ), (sortByKey l).length = l.length
  | [] => rfl
  | x :: xs => by
    simp only [sortByKey, List.length_append, List.length_cons, List.length_nil]
    have := len_filter_split (fun y => decide (y.1 < x.1)) (sortByKey xs)
    rw [length_sortByKey xs] at this
    simp only [decide_not] at this ⊢
    omega

lemma sortByKeyT_time : ∀ l : List (ℕ × ℕ), (sortByKeyT l).time ≤ 4 * (l.length + 1) ^ 2
  | [] => by simp [sortByKeyT]
  | x :: xs => by
    have ih := sortByKeyT_time xs
    have hs : (sortByKeyT xs).ret.length = xs.length := by rw [sortByKeyT_ret, length_sortByKey]
    simp only [sortByKeyT, time_bind, lappendT, lfilterT, List.length_cons]
    have a1 := lsum_le (sortByKeyT xs).ret (fun y => (pure (decide (y.1 < x.1)) : TimeM Bool).time + 1) 1
      (fun _ _ => by simp)
    have a2 := lsum_le (sortByKeyT xs).ret
      (fun y => (pure (decide (¬ y.1 < x.1)) : TimeM Bool).time + 1) 1 (fun _ _ => by simp)
    have a3 := List.length_filter_le (fun y => ((pure (decide (y.1 < x.1)) : TimeM Bool)).ret)
      (sortByKeyT xs).ret
    simp only [List.length_append, List.length_cons, List.length_nil] at *
    rw [hs] at a1 a2 a3
    nlinarith

/-! ### Views -/

lemma atT_time (v : View) (r c : ℕ) : (atT v r c).time ≤ v.pts.length := by
  simp only [atT, time_bind, time_pure, lfindT]
  simp

lemma emptyT_time (v : View) (cells : List (ℕ × ℕ)) :
    (emptyT v cells).time ≤ cells.length * (v.pts.length + 1) := by
  apply lallT_time_le
  intro x _
  simp only [time_bind, time_pure]
  have := atT_time v x.1 x.2
  omega

lemma makeViewT_time (R C : ℕ) (f : Frame) (pts : List Pt) :
    (makeViewT R C f pts).time ≤ pts.length := by
  simp only [makeViewT, time_bind, time_pure]
  have := lmapT_time_le (fun q => (pure (f.to R C q.1, q.2) : TimeM ((ℕ × ℕ) × ℕ))) pts 0
    (fun _ _ => by simp)
  omega

lemma makeView_len (R C : ℕ) (f : Frame) (pts : List Pt) :
    (makeView R C f pts).pts.length = pts.length := by simp [makeView]

/-! ### Global checks -/

lemma lfoldlT_pure_time {β α : Type} (g : β → α → β) :
    ∀ (b : β) (l : List α), (lfoldlT (fun a x => (pure (g a x) : TimeM β)) b l).time = l.length
  | _, [] => rfl
  | b, x :: l => by
    simp only [lfoldlT, time_pure, List.length_cons, lfoldlT_pure_time g (g b x) l, ret_pure]; omega

lemma parityOkT_time (R C : ℕ) (pts : List Pt) : (parityOkT R C pts).time ≤ 2 * pts.length + 1 := by
  simp only [parityOkT, time_bind, time_pure, lsumT, lmapT]
  have := lsum_le pts (fun q => (pure (sgn q.1) : TimeM ℤ).time + 1) 1 (fun _ _ => by simp)
  simp at this ⊢; omega

lemma t1FiresT_time (R C : ℕ) (pts : List Pt) :
    (t1FiresT R C pts).time ≤ 10 * (pts.length + 1) ^ 2 := by
  simp only [t1FiresT, time_bind, time_pure, lzipT]
  have e1 := lmapT_time_le (fun q => (pure (perimIndex R C q.1) : TimeM (Option ℕ))) pts 0
    (fun _ _ => by simp)
  set idx := (lmapT (fun q => (pure (perimIndex R C q.1) : TimeM (Option ℕ))) pts).ret
  have hidx : idx.length = pts.length := by simp [idx, lmapT]
  have e2 := lallT_time_le (fun o => (pure o.isSome : TimeM Bool)) idx 0 (fun _ _ => by simp)
  have e3 := lmapT_time_le (fun o => (pure (o.getD 0) : TimeM ℕ)) idx 0 (fun _ _ => by simp)
  have e4 := lmapT_time_le (fun q => (pure q.2 : TimeM ℕ)) pts 0 (fun _ _ => by simp)
  set keys := (lmapT (fun o => (pure (o.getD 0) : TimeM ℕ)) idx).ret
  set cols := (lmapT (fun q => (pure q.2 : TimeM ℕ)) pts).ret
  have hk : keys.length = pts.length := by simp [keys, lmapT, hidx]
  have hc : cols.length = pts.length := by simp [cols, lmapT]
  have e5 := sortByKeyT_time (keys.zip cols)
  have hz : (keys.zip cols).length = pts.length := by simp [hk, hc]
  have e6 := lmapT_time_le (fun y => (pure y.2 : TimeM ℕ)) (sortByKeyT (keys.zip cols)).ret 0
    (fun _ _ => by simp)
  have hs : (sortByKeyT (keys.zip cols)).ret.length = pts.length := by
    rw [sortByKeyT_ret, length_sortByKey, hz]
  rw [hidx] at e2 e3; rw [hz] at e5; rw [hs] at e6
  simp only [hk] at *
  nlinarith

lemma t2FiresT_time (cells : List (ℕ × ℕ)) : (t2FiresT cells).time ≤ 20 * (cells.length + 1) := by
  simp only [t2FiresT, time_bind, time_pure, lfoldlT_pure_time, lgetT]
  have e1 := lmapT_time_le (fun x => (pure x.1 : TimeM ℕ)) cells 0 (fun _ _ => by simp)
  have e2 := lmapT_time_le (fun x => (pure x.2 : TimeM ℕ)) cells 0 (fun _ _ => by simp)
  simp [lmapT] at e1 e2 ⊢
  omega

lemma l1FiresT_time (R C : ℕ) (pts : List Pt) :
    (l1FiresT R C pts).time ≤ pts.length * (6 * pts.length + 15) := by
  apply le_trans (lanyT_time_le _ pts (4 * (pts.length + 2) + 4) _)
  · nlinarith
  · intro pc _
    simp only [time_bind]
    have hn : (nbrsT R C pc.1).time ≤ 4 := by
      simp only [nbrsT]
      apply le_trans (lfilterT_time_le _ _ 0 (fun _ _ => by simp)); simp
    have hl : (nbrsT R C pc.1).ret.length ≤ 4 := by
      simp only [nbrsT, lfilterT]; exact le_trans (List.length_filter_le _ _) (by simp)
    have := lallT_time_le (fun q => lanyT (fun pc' => (pure (pc'.1 == (q.1.toNat, q.2.toNat) &&
        pc'.2 != pc.2) : TimeM Bool)) pts) (nbrsT R C pc.1).ret (pts.length * 1)
      (fun q _ => lanyT_time_le _ _ 0 (fun _ _ => by simp))
    nlinarith

lemma l6FiresT_time (R C : ℕ) (pts : List Pt) : (l6FiresT R C pts).time ≤ 20 * (pts.length + 1) := by
  simp only [l6FiresT, time_bind, time_pure, lcontainsT]
  have e1 : (l6ClosuresT R C pts).time ≤ 4 * (3 * pts.length + 1) := by
    simp only [l6ClosuresT]
    refine le_trans (lfilterMapT_time_le _ _ (3 * pts.length) ?_) (by simp [cornersL])
    intro x _
    simp only [time_bind, time_pure]
    have a := lanyT_time_le (fun q => (pure (q.1 == (x.1.toNat, x.2.1.toNat)) : TimeM Bool)) pts 0
      (fun _ _ => by simp)
    have b := lfindT_time_le (fun q => (pure (q.1 == (x.1.toNat, (x.2.1 + x.2.2.2).toNat)) :
      TimeM Bool)) pts 0 (fun _ _ => by simp)
    have c := lfindT_time_le (fun q => (pure (q.1 == ((x.1 + x.2.2.1).toNat, x.2.1.toNat)) :
      TimeM Bool)) pts 0 (fun _ _ => by simp)
    omega
  have e2 : (l6ClosuresT R C pts).ret.length ≤ 4 := by
    simp only [l6ClosuresT, lfilterMapT]
    exact le_trans (List.length_filterMap_le _ _) (by simp [cornersL])
  omega

/-! ### Frame checks -/

lemma testL2T_time (v : View) : (testL2T v).time ≤ 4 * (v.pts.length + 1) := by
  simp only [testL2T, time_bind]
  have a := atT_time v 0 1; have b := atT_time v 1 0
  have c := emptyT_time v [(0, 0)]
  split <;> simp only [time_bind, time_pure] <;> simp at c <;> omega

lemma testL3T_time (v : View) : (testL3T v).time ≤ 6 * (v.pts.length + 1) := by
  simp only [testL3T, time_bind]
  have a := atT_time v 0 2; have b := atT_time v 1 1; have b2 := atT_time v 1 0
  have c := emptyT_time v [(0, 0), (0, 1)]
  split <;> simp only [time_bind, time_pure] <;> simp at c <;> omega

lemma testL4T_time (v : View) : (testL4T v).time ≤ 6 * (v.pts.length + 1) := by
  simp only [testL4T, time_bind]
  have a := atT_time v 0 0; have b := atT_time v 1 1; have b2 := atT_time v 0 2
  have c := emptyT_time v [(0, 1), (1, 0)]
  split <;> simp only [time_bind, time_pure] <;> simp at c <;> omega

lemma testL5T_time (v : View) : (testL5T v).time ≤ 7 * (v.pts.length + 1) := by
  simp only [testL5T, time_bind]
  have a := atT_time v 0 0; have b := atT_time v 0 2; have b2 := atT_time v 2 0
  have c := emptyT_time v [(0, 1), (1, 0), (1, 1)]
  split <;> simp only [time_bind, time_pure] <;> simp at c <;> omega

lemma edgeStepT_time (v : View) (k : ℕ) : (edgeStepT v k).time ≤ 4 * v.pts.length := by
  unfold edgeStepT
  split
  · simp only [time_bind]
    have a := atT_time v 0 k; have b := atT_time v 1 (k + 1); have c := atT_time v 0 (k + 3)
    have d := atT_time v 1 (k + 2)
    split <;> simp only [time_bind, time_pure] <;> omega
  · simp

lemma edgeClosureT_time (v : View) :
    (edgeClosureT v).time ≤ (v.W + 1) * (4 * v.pts.length + 2) := by
  simp only [edgeClosureT, time_bind, rangeT]
  have := lanyT_time_le (edgeStepT v) (List.range v.W) (4 * v.pts.length)
    (fun k _ => edgeStepT_time v k)
  simp only [List.length_range] at this
  nlinarith

lemma sameSetT_time (a b : List (ℕ × ℕ)) :
    (sameSetT a b).time ≤ (a.length + 1) * (b.length + 4) := by
  simp only [sameSetT, time_bind, time_pure, lengthT]
  have := lallT_time_le (fun x => lcontainsT b x) a (b.length + 1) (fun _ _ => by simp [lcontainsT])
  nlinarith

lemma corner4_lists (R C : ℕ) :
    ∀ AB ∈ (if (R * C) % 2 == 0 then CORNER4 else CORNER4_ODD), AB.1.length ≤ 2 ∧ AB.2.length ≤ 2 := by
  split <;> decide

lemma corner4_len (R C : ℕ) : (if (R * C) % 2 == 0 then CORNER4 else CORNER4_ODD).length ≤ 40 := by
  split <;> decide

lemma corner4T_time (R C : ℕ) (f : Frame) (pts : List Pt) :
    (corner4T R C f pts).time ≤ 1000 * (pts.length + 4) := by
  simp only [corner4T, time_bind]
  have a1 := lfilterT_time_le (fun q => (pure (q.2 == 0) : TimeM Bool)) pts 0 (fun _ _ => by simp)
  have a2 := lfilterT_time_le (fun q => (pure (q.2 == 1) : TimeM Bool)) pts 0 (fun _ _ => by simp)
  set F0 := (lfilterT (fun q => (pure (q.2 == 0) : TimeM Bool)) pts).ret
  set F1 := (lfilterT (fun q => (pure (q.2 == 1) : TimeM Bool)) pts).ret
  have hF0 : F0.length ≤ pts.length := by simp only [F0, lfilterT]; exact List.length_filter_le _ _
  have hF1 : F1.length ≤ pts.length := by simp only [F1, lfilterT]; exact List.length_filter_le _ _
  have a3 := lmapT_time_le (fun q => (pure (f.to R C q.1) : TimeM (ℕ × ℕ))) F0 0 (fun _ _ => by simp)
  have a4 := lmapT_time_le (fun q => (pure (f.to R C q.1) : TimeM (ℕ × ℕ))) F1 0 (fun _ _ => by simp)
  set A0 := (lmapT (fun q => (pure (f.to R C q.1) : TimeM (ℕ × ℕ))) F0).ret
  set A1 := (lmapT (fun q => (pure (f.to R C q.1) : TimeM (ℕ × ℕ))) F1).ret
  have hA0 : A0.length ≤ pts.length := by simp only [A0, lmapT, List.length_map]; exact hF0
  have hA1 : A1.length ≤ pts.length := by simp only [A1, lmapT, List.length_map]; exact hF1
  have a5 := lanyT_time_le (fun (AB : List (ℕ × ℕ) × List (ℕ × ℕ)) => do
    let x1 ← sameSetT AB.1 A0
    let x2 ← sameSetT AB.2 A1
    let x3 ← sameSetT AB.1 A1
    let x4 ← sameSetT AB.2 A0
    pure ((x1 && x2) || (x3 && x4))) (if (R * C) % 2 == 0 then CORNER4 else CORNER4_ODD)
    (12 * (pts.length + 4)) (by
      intro AB hAB
      obtain ⟨h1, h2⟩ := corner4_lists R C AB hAB
      simp only [time_bind, time_pure]
      have b1 := sameSetT_time AB.1 A0; have b2 := sameSetT_time AB.2 A1
      have b3 := sameSetT_time AB.1 A1; have b4 := sameSetT_time AB.2 A0
      nlinarith)
  have hl := corner4_len R C
  have h5 : (if (R * C % 2 == 0) = true then CORNER4 else CORNER4_ODD).length * (12 * (pts.length + 4) + 1)
      ≤ 40 * (12 * (pts.length + 4) + 1) := Nat.mul_le_mul_right _ hl
  simp only [lfilterT, lmapT, time_pure, zero_add, mul_one] at a1 a2 a3 a4 ⊢
  omega

lemma isAT_time (fp : List Pt) (A : ℕ) (x : ℕ × ℕ) : (isAT fp A x).time ≤ fp.length := by
  unfold isAT
  simpa using lanyT_time_le (fun q => (pure (q.2 == A && q.1 == x) : TimeM Bool)) fp 0
    (fun _ _ => by simp)

lemma boundaryStepT_time (H W : ℕ) (fp : List Pt) (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) (A : ℕ) :
    (boundaryStepT H W fp t A).time ≤ 4 * fp.length := by
  simp only [boundaryStepT, time_bind]
  have a := lfindT_time_le (fun q => (pure (q.2 == 1 - A && q.1 == t.2.2) : TimeM Bool)) fp 0
    (fun _ _ => by simp)
  have b := lfindT_time_le (fun q => (pure (q.2 == 1 - A && q.1 != t.2.2) : TimeM Bool)) fp 0
    (fun _ _ => by simp)
  have c := isAT_time fp A t.1; have d := isAT_time fp A t.2.1
  split <;> simp only [time_bind, time_pure] <;> omega

lemma boundary_len (R C : ℕ) :
    (if R % 2 == 1 && C % 2 == 1 then BOUNDARY3_ODD else BOUNDARY3_EVEN).length ≤ 40 := by
  split <;> decide

lemma boundaryOnlyT_time (R C : ℕ) (f : Frame) (pts : List Pt) :
    (boundaryOnlyT R C f pts).time ≤ 400 * (pts.length + 1) := by
  simp only [boundaryOnlyT, time_bind]
  have a := lmapT_time_le (fun q => (pure (f.to R C q.1, q.2) : TimeM Pt)) pts 0 (fun _ _ => by simp)
  have hfp : (lmapT (fun q => (pure (f.to R C q.1, q.2) : TimeM Pt)) pts).ret.length = pts.length := by
    simp [lmapT]
  have b := lanyT_time_le (fun t => lanyT (boundaryStepT (f.H R C) (f.W R C)
      (lmapT (fun q => (pure (f.to R C q.1, q.2) : TimeM Pt)) pts).ret t) [0, 1])
    (if R % 2 == 1 && C % 2 == 1 then BOUNDARY3_ODD else BOUNDARY3_EVEN) (2 * (4 * pts.length + 1))
    (fun t _ => by
      have := lanyT_time_le (boundaryStepT (f.H R C) (f.W R C)
        (lmapT (fun q => (pure (f.to R C q.1, q.2) : TimeM Pt)) pts).ret t) [0, 1]
        (4 * pts.length) (fun A _ => by rw [← hfp]; exact boundaryStepT_time _ _ _ t A)
      simpa using this)
  have hl := boundary_len R C
  nlinarith

lemma frameFiresT_time (R C : ℕ) (pts : List Pt) (f : Frame) :
    (frameFiresT R C pts f).time ≤ (R + C + 1) * (4 * pts.length + 2) + 2000 * (pts.length + 4) := by
  simp only [frameFiresT, time_bind, time_pure, makeViewT_ret]
  have hv := makeView_len R C f pts
  have a := makeViewT_time R C f pts
  have b2 := testL2T_time (makeView R C f pts); have b3 := testL3T_time (makeView R C f pts)
  have b4 := testL4T_time (makeView R C f pts); have b5 := testL5T_time (makeView R C f pts)
  have e := edgeClosureT_time (makeView R C f pts)
  have hW : (makeView R C f pts).W ≤ R + C := by
    simp only [makeView, Frame.W]; split <;> omega
  have g := boundaryOnlyT_time R C f pts
  have k := corner4T_time R C f pts
  rw [hv] at b2 b3 b4 b5 e
  have : ((makeView R C f pts).W + 1) * (4 * pts.length + 2) ≤ (R + C + 1) * (4 * pts.length + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-! ### The R test: rewrites -/

lemma rewritesAt_len (v : View) (rw : Rewrite) (h : rewritesAt v = some rw) :
    rw.removed.length ≤ 8 ∧ rw.moves.length ≤ 2 := by
  unfold rewritesAt at h
  dsimp only at h
  split_ifs at h <;> (cases h; decide)

lemma moveFirst_len (e : List Pt) (m : (ℕ × ℕ) × (ℕ × ℕ)) : (moveFirst e m).length = e.length := by
  unfold moveFirst; split <;> simp

lemma foldl_moveFirst_len (moves : List ((ℕ × ℕ) × (ℕ × ℕ))) :
    ∀ e : List Pt, (moves.foldl moveFirst e).length = e.length := by
  induction moves with
  | nil => intro e; rfl
  | cons m ms ih => intro e; simp [List.foldl_cons, ih, moveFirst_len]

lemma rwStep_len (R C : ℕ) (st : RWState) (f : Frame) :
    (rwStep R C st f).eff.length = st.eff.length ∧
      (rwStep R C st f).removed.length ≤ st.removed.length + 8 := by
  unfold rwStep
  split
  · simp
  · rename_i rw hrw
    have := (rewritesAt_len _ rw hrw).1
    dsimp only
    split_ifs <;> simp [foldl_moveFirst_len]; omega

lemma moveFirstT_time (e : List Pt) (m : (ℕ × ℕ) × (ℕ × ℕ)) :
    (moveFirstT e m).time ≤ 2 * e.length + 2 := by
  simp only [moveFirstT, time_bind, lfindIdxT]
  split <;> simp [lmodifyT] <;> omega

lemma rwStepT_time (R C : ℕ) (st : RWState) (f : Frame) :
    (rwStepT R C st f).time ≤ 100 + 30 * (st.removed.length + st.eff.length) := by
  simp only [rwStepT, time_bind, makeViewT_ret]
  have a := makeViewT_time R C f st.eff
  have hv := makeView_len R C f st.eff
  have b : (rewritesAtT (makeView R C f st.eff)).time ≤ 20 * st.eff.length + 14 := by
    simp only [rewritesAtT, time_bind, time_pure]
    have := atT_time (makeView R C f st.eff)
    have e1 := emptyT_time (makeView R C f st.eff)
      [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (2, 0), (3, 0)]
    have e2 := emptyT_time (makeView R C f st.eff) [(0, 1), (1, 0), (0, 2), (2, 0)]
    have e3 := emptyT_time (makeView R C f st.eff) [(0, 0), (1, 0)]
    have x1 := this 1 2; have x2 := this 2 1; have x3 := this 0 0; have x4 := this 1 1
    have x5 := this 0 1
    simp only [hv, List.length_cons, List.length_nil] at *
    omega
  rw [rewritesAtT_ret]
  cases hrw : rewritesAt (makeView R C f st.eff) with
  | none => simp only [time_pure]; omega
  | some rw =>
    obtain ⟨hr, hm⟩ := rewritesAt_len _ rw hrw
    simp only [rwApplyT, time_bind]
    have c1 := lmapT_time_le (fun x => (pure (f.back R C x) : TimeM (ℕ × ℕ))) rw.removed 0
      (fun _ _ => by simp)
    have c2 := lmapT_time_le (fun m => (pure (f.back R C m.1, f.back R C m.2) :
      TimeM ((ℕ × ℕ) × (ℕ × ℕ)))) rw.moves 0 (fun _ _ => by simp)
    set cells := (lmapT (fun x => (pure (f.back R C x) : TimeM (ℕ × ℕ))) rw.removed).ret
    set moves := (lmapT (fun m => (pure (f.back R C m.1, f.back R C m.2) :
      TimeM ((ℕ × ℕ) × (ℕ × ℕ)))) rw.moves).ret
    have hc : cells.length ≤ 8 := by simp [cells, lmapT, hr]
    have hmv : moves.length ≤ 2 := by simp [moves, lmapT, hm]
    have c3 := lanyT_time_le (fun x => lcontainsT st.removed x) cells (st.removed.length + 1)
      (fun _ _ => by simp [lcontainsT])
    have c4 := lanyT_time_le (fun m => lcontainsT st.removed m.2) moves (st.removed.length + 1)
      (fun _ _ => by simp [lcontainsT])
    have c5 := lfoldlT_time_le moveFirstT (fun e => e.length) 2 2 0 (fun e m => by have := moveFirstT_time e m; omega)
      (fun e m => by simp [moveFirstT_ret, moveFirst_len]) moves st.eff
    have h3 : cells.length * (st.removed.length + 1 + 1) ≤ 8 * (st.removed.length + 2) :=
      Nat.mul_le_mul_right _ hc
    have h4 : moves.length * (st.removed.length + 1 + 1) ≤ 2 * (st.removed.length + 2) :=
      Nat.mul_le_mul_right _ hmv
    have h5 : moves.length * (2 + 2 * (st.eff.length + moves.length * 0) + 1) ≤
        2 * (2 + 2 * st.eff.length + 1) := by
      simp only [mul_zero, add_zero]; exact Nat.mul_le_mul_right _ hmv
    split_ifs <;> simp only [time_bind, time_pure, lappendT] <;> omega

lemma rewriteAllT_time (R C : ℕ) (pts : List Pt) :
    (rewriteAllT R C pts).time ≤ 8 * (101 + 30 * (pts.length + 64)) := by
  have := lfoldlT_time_le (rwStepT R C) (fun st => st.removed.length + st.eff.length) 100 30 8
    (fun st f => rwStepT_time R C st f)
    (fun st f => by rw [rwStepT_ret]; have := rwStep_len R C st f; omega) frames ⟨pts, [], false⟩
  have hf : frames.length = 8 := by decide
  rw [hf] at this
  simp only [List.length_nil, Nat.zero_add] at this
  unfold rewriteAllT
  refine le_trans this ?_
  nlinarith

lemma rewriteAll_len_aux (R C : ℕ) :
    ∀ (fs : List Frame) (st : RWState), (fs.foldl (rwStep R C) st).eff.length = st.eff.length ∧
      (fs.foldl (rwStep R C) st).removed.length ≤ st.removed.length + 8 * fs.length
  | [], st => by simp
  | f :: fs, st => by
    have h1 := rwStep_len R C st f
    have ih := rewriteAll_len_aux R C fs (rwStep R C st f)
    simp only [List.foldl_cons, List.length_cons]
    constructor
    · rw [ih.1, h1.1]
    · omega

lemma rewriteAll_len (R C : ℕ) (pts : List Pt) :
    (rewriteAll R C pts).eff.length = pts.length ∧ (rewriteAll R C pts).removed.length ≤ 64 := by
  have := rewriteAll_len_aux R C frames ⟨pts, [], false⟩
  have hf : frames.length = 8 := by decide
  rw [hf] at this
  exact ⟨this.1, by simpa [rewriteAll] using this.2⟩

/-! ### The R test: the outer walk -/

lemma notchLen_le (R C : ℕ) (f : Frame) (removed : List (ℕ × ℕ)) (i : ℕ) :
    notchLen R C f removed i ≤ 4 := by
  unfold notchLen
  exact le_trans (List.length_filter_le _ _) (by simp)

lemma notchLenT_time (R C : ℕ) (f : Frame) (removed : List (ℕ × ℕ)) (i : ℕ) :
    (notchLenT R C f removed i).time ≤ 4 * removed.length + 18 := by
  simp only [notchLenT, time_bind, rangeT, lengthT]
  have := lfilterT_time_le (fun j => lcontainsT removed (f.back R C (i, j))) (List.range 4)
    (removed.length + 1) (fun _ _ => by simp [lcontainsT])
  have h2 := List.length_filter_le (fun j => (lcontainsT removed (f.back R C (i, j))).ret)
    (List.range 4)
  simp only [List.length_range, lfilterT] at this h2 ⊢
  omega

lemma countPosT_time (lamT : ℕ → TimeM ℕ) (c : ℕ) (h : ∀ i, (lamT i).time ≤ c) :
    (countPosT lamT).time ≤ 4 * c + 14 ∧ (countPosT lamT).ret ≤ 4 := by
  simp only [countPosT, time_bind, rangeT, lengthT, ret_bind]
  have := lfilterT_time_le (fun i => do let x ← lamT i; pure (decide (x > 0))) (List.range 4) c
    (fun i _ => by simp only [time_bind, time_pure]; have := h i; omega)
  have h2 := List.length_filter_le (fun i => (do let x ← lamT i; pure (decide (x > 0)) :
    TimeM Bool).ret) (List.range 4)
  simp only [List.length_range, lfilterT] at this h2 ⊢
  constructor <;> omega

lemma stairBlockT_time (lamT : ℕ → TimeM ℕ) (c : ℕ) (h : ∀ i, (lamT i).time ≤ c)
    (hv : ∀ i, (lamT i).ret ≤ 4) (i : ℕ) :
    (stairBlockT lamT i).time ≤ 2 * c + 14 ∧ (stairBlockT lamT i).ret.length ≤ 5 := by
  simp only [stairBlockT, time_bind, ret_bind, rangeT, lappendT]
  have a1 := h i; have a2 := h (i + 1); have v1 := hv i
  have := lmapT_time_le (fun j => (pure (i + 1, (lamT (i + 1)).ret + 1 + j) : TimeM (ℕ × ℕ)))
    (List.range ((lamT i).ret - (lamT (i + 1)).ret)) 0 (fun _ _ => by simp)
  simp only [List.length_range, lmapT, List.length_map, List.length_append, List.length_cons,
    List.length_nil] at this ⊢
  constructor <;> omega

lemma staircaseT_time (lamT : ℕ → TimeM ℕ) (c : ℕ) (h : ∀ i, (lamT i).time ≤ c)
    (hv : ∀ i, (lamT i).ret ≤ 4) :
    (staircaseT lamT).time ≤ 12 * c + 106 ∧ (staircaseT lamT).ret.length ≤ 21 := by
  obtain ⟨hk1, hk2⟩ := countPosT_time lamT c h
  have hrr : (List.range (countPosT lamT).ret).reverse.length ≤ 4 := by simp; omega
  have fm := lflatMapT_time_le (stairBlockT lamT) (List.range (countPosT lamT).ret).reverse
    (2 * c + 14) 5 (fun i _ => (stairBlockT_time lamT c h hv i).1)
    (fun i _ => (stairBlockT_time lamT c h hv i).2)
  have fl : (lflatMapT (stairBlockT lamT) (List.range (countPosT lamT).ret).reverse).ret.length ≤ 20 := by
    simp only [lflatMapT, List.length_flatMap]
    have := lsum_le (List.range (countPosT lamT).ret).reverse
      (fun i => (stairBlockT lamT i).ret.length) 5 (fun i _ => (stairBlockT_time lamT c h hv i).2)
    have : (List.range (countPosT lamT).ret).reverse.length * 5 ≤ 20 := by omega
    omega
  have hm : (List.range (countPosT lamT).ret).reverse.length * (2 * c + 14 + 5 + 1) ≤
      4 * (2 * c + 20) := Nat.mul_le_mul_right _ hrr
  simp only [staircaseT, time_bind, ret_bind, rangeT, lreverseT, lappendT, List.length_append,
    List.length_cons, List.length_nil, List.length_range]
  simp only [List.length_reverse, List.length_range] at fm hm
  constructor <;> omega

lemma stairOfT_time (R C : ℕ) (f : Frame) (removed : List (ℕ × ℕ)) :
    (stairOfT R C f removed).time ≤ 48 * removed.length + 343 ∧
      (stairOfT R C f removed).ret.length ≤ 21 := by
  obtain ⟨h1, h2⟩ := staircaseT_time (notchLenT R C f removed) (4 * removed.length + 18)
    (fun i => notchLenT_time R C f removed i) (fun i => by rw [notchLenT_ret]; exact notchLen_le _ _ _ _ _)
  simp only [stairOfT, time_bind, ret_bind]
  have := lmapT_time_le (fun x => (pure (f.back R C x) : TimeM (ℕ × ℕ)))
    (staircaseT (notchLenT R C f removed)).ret 0 (fun _ _ => by simp)
  simp only [lmapT, List.length_map] at this ⊢
  constructor <;> omega

lemma sideT_time (n lo hi : ℕ) : (sideT n lo hi).time ≤ 2 * n + 1 ∧ (sideT n lo hi).ret.length ≤ n := by
  simp only [sideT, time_bind, rangeT, ret_bind]
  have := lfilterT_time_le (fun y => (pure (decide (lo < y ∧ y + 1 + hi < n)) : TimeM Bool))
    (List.range n) 0 (fun _ _ => by simp)
  have h2 := List.length_filter_le (fun y => (pure (decide (lo < y ∧ y + 1 + hi < n)) :
    TimeM Bool).ret) (List.range n)
  simp only [List.length_range, lfilterT] at this h2 ⊢
  constructor <;> omega

lemma walkStairsT_time (R C : ℕ) (removed : List (ℕ × ℕ)) :
    (walkStairsT R C removed).time ≤ 200 * removed.length + 1500 ∧
      (walkStairsT R C removed).ret.1.length ≤ 21 ∧ (walkStairsT R C removed).ret.2.1.length ≤ 21 ∧
      (walkStairsT R C removed).ret.2.2.1.length ≤ 21 ∧ (walkStairsT R C removed).ret.2.2.2.length ≤ 21 := by
  have s1 := stairOfT_time R C frameTL removed; have s2 := stairOfT_time R C frameTR removed
  have s3 := stairOfT_time R C frameBR removed; have s4 := stairOfT_time R C frameBL removed
  simp only [walkStairsT, time_bind, ret_bind, lreverseT, time_pure, ret_pure, List.length_reverse]
  omega

lemma sideMapT_time (n lo hi : ℕ) (mk : ℕ → ℕ × ℕ) :
    (sideMapT n lo hi mk).time ≤ 3 * n + 1 ∧ (sideMapT n lo hi mk).ret.length ≤ n := by
  obtain ⟨h1, h2⟩ := sideT_time n lo hi
  have := lmapT_time_le (fun y => (pure (mk y) : TimeM (ℕ × ℕ))) (sideT n lo hi).ret 0
    (fun _ _ => by simp)
  simp only [sideMapT, time_bind, ret_bind]
  simp only [lmapT, List.length_map] at this ⊢
  constructor <;> omega

lemma walkSidesT_time (R C : ℕ) (removed : List (ℕ × ℕ)) :
    (walkSidesT R C removed).time ≤ 100 * removed.length + 10 * (R + C) + 500 ∧
      (walkSidesT R C removed).ret.1.length ≤ C ∧ (walkSidesT R C removed).ret.2.1.length ≤ R ∧
      (walkSidesT R C removed).ret.2.2.1.length ≤ C ∧ (walkSidesT R C removed).ret.2.2.2.length ≤ R := by
  have n1 := notchLenT_time R C frameTL removed 0; have n2 := notchLenT_time R C frameTR removed 0
  have n3 := notchLenT_time R C frameBR removed 0; have n4 := notchLenT_time R C frameBL removed 0
  have k1 := (countPosT_time (notchLenT R C frameTL removed) _ (notchLenT_time R C frameTL removed)).1
  have k2 := (countPosT_time (notchLenT R C frameTR removed) _ (notchLenT_time R C frameTR removed)).1
  have k3 := (countPosT_time (notchLenT R C frameBR removed) _ (notchLenT_time R C frameBR removed)).1
  have k4 := (countPosT_time (notchLenT R C frameBL removed) _ (notchLenT_time R C frameBL removed)).1
  have d1 := sideMapT_time C (notchLenT R C frameTL removed 0).ret (notchLenT R C frameTR removed 0).ret
    (fun y => (0, y))
  have d2 := sideMapT_time R (countPosT (notchLenT R C frameTR removed)).ret
    (countPosT (notchLenT R C frameBR removed)).ret (fun x => (x, C - 1))
  have d3 := sideMapT_time C (notchLenT R C frameBL removed 0).ret (notchLenT R C frameBR removed 0).ret
    (fun y => (R - 1, y))
  have d4 := sideMapT_time R (countPosT (notchLenT R C frameTL removed)).ret
    (countPosT (notchLenT R C frameBL removed)).ret (fun x => (x, 0))
  simp only [walkSidesT, time_bind, ret_bind, lreverseT, time_pure, ret_pure, List.length_reverse]
  omega

lemma walkJoinT_time (a b : List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ)) :
    (walkJoinT a b).time ≤ 7 * (a.1.length + b.1.length + a.2.1.length + b.2.1.length +
      a.2.2.1.length + b.2.2.1.length + a.2.2.2.length + 1) ∧
    (walkJoinT a b).ret.length = a.1.length + b.1.length + a.2.1.length + b.2.1.length +
      a.2.2.1.length + b.2.2.1.length + a.2.2.2.length + b.2.2.2.length := by
  simp only [walkJoinT, time_bind, ret_bind, lappendT, List.length_append]
  refine ⟨?_, ?_⟩ <;> first | omega | (simp only)

lemma walk3T_time (R C : ℕ) (removed : List (ℕ × ℕ)) :
    (walk3T R C removed).time ≤ 300 * removed.length + 30 * (R + C) + 3000 ∧
      (walk3T R C removed).ret.length ≤ 2 * (R + C) + 84 := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := walkStairsT_time R C removed
  obtain ⟨b1, b2, b3, b4, b5⟩ := walkSidesT_time R C removed
  obtain ⟨c1, c2⟩ := walkJoinT_time (walkStairsT R C removed).ret (walkSidesT R C removed).ret
  simp only [walk3T, time_bind, ret_bind]
  constructor <;> omega

lemma positionsT_time (walk : List (ℕ × ℕ)) (x : ℕ × ℕ) :
    (positionsT walk x).time ≤ 3 * walk.length + 1 ∧ (positionsT walk x).ret.length ≤ walk.length := by
  simp only [positionsT, time_bind, ret_bind, lzipIdxT]
  have := lfilterT_time_le (fun q => (pure (q.1 == x) : TimeM Bool)) walk.zipIdx 0 (fun _ _ => by simp)
  have h2 := List.length_filter_le (fun q => (pure (q.1 == x) : TimeM Bool).ret) walk.zipIdx
  have h3 := lmapT_time_le (fun q => (pure q.2 : TimeM ℕ))
    (lfilterT (fun q => (pure (q.1 == x) : TimeM Bool)) walk.zipIdx).ret 0 (fun _ _ => by simp)
  simp only [List.length_zipIdx, lfilterT, lmapT, List.length_map] at this h2 h3 ⊢
  constructor <;> omega

/-! ### The R test and the whole catalogue -/

lemma effAlt3T_time (R C : ℕ) (pts : List Pt) (hn : pts.length = 4) :
    (effAlt3T R C pts).time ≤ 100 * (R + C) + 50000 := by
  have hr := rewriteAllT_time R C pts
  obtain ⟨he, hrem⟩ := rewriteAll_len R C pts
  rw [hn] at hr he
  simp only [effAlt3T, time_bind, rewriteAllT_ret, time_pure]
  generalize rewriteAll R C pts = st at *
  have b1 := lanyT_time_le (fun q => lcontainsT st.removed q.1) st.eff (st.removed.length + 1)
    (fun _ _ => by simp [lcontainsT])
  have b2 := lmapT_time_le (fun q => (pure q.1 : TimeM (ℕ × ℕ))) st.eff 0 (fun _ _ => by simp)
  have hcs : (lmapT (fun q => (pure q.1 : TimeM (ℕ × ℕ))) st.eff).ret.length = 4 := by
    simp [lmapT, he]
  have hd : (ldedupT (lmapT (fun q => (pure q.1 : TimeM (ℕ × ℕ))) st.eff).ret).ret.length ≤ 4 := by
    simp only [ldedupT]; rw [← hcs]; exact List.Sublist.length_le (List.dedup_sublist _)
  obtain ⟨w1, w2⟩ := walk3T_time R C st.removed
  generalize walk3T R C st.removed = W at *
  have p1 := lmapT_time_le (fun q => do let p ← positionsT W.ret q.1; pure (p, q.2)) st.eff
    (3 * W.ret.length + 1) (fun q _ => by
      simp only [time_bind, time_pure]; have := (positionsT_time W.ret q.1).1; omega)
  set places := (lmapT (fun q => do let p ← positionsT W.ret q.1; pure (p, q.2)) st.eff).ret
  have hpl : places.length = 4 := by simp [places, lmapT, he]
  have hpl2 : ∀ pl ∈ places, pl.1.length ≤ W.ret.length := by
    intro pl hpl
    simp only [places, lmapT, List.mem_map, ret_bind, ret_pure] at hpl
    obtain ⟨q, _, rfl⟩ := hpl
    exact (positionsT_time W.ret q.1).2
  have p2 := lanyT_time_le (fun pl => do let m ← lengthT pl.1; pure (m != 1)) places
    (W.ret.length + 1) (fun pl hpl => by
      simp only [time_bind, time_pure, lengthT]; have := hpl2 pl hpl; omega)
  have p3 := lmapT_time_le (fun pl => (pure (pl.1.headD 0, pl.2) : TimeM (ℕ × ℕ))) places 0
    (fun _ _ => by simp)
  set keys := (lmapT (fun pl => (pure (pl.1.headD 0, pl.2) : TimeM (ℕ × ℕ))) places).ret
  have hk : keys.length = 4 := by simp [keys, lmapT, hpl]
  have p4 := sortByKeyT_time keys
  have hs : (sortByKeyT keys).ret.length = 4 := by rw [sortByKeyT_ret, length_sortByKey, hk]
  have p5 := lmapT_time_le (fun y => (pure y.2 : TimeM ℕ)) (sortByKeyT keys).ret 0 (fun _ _ => by simp)
  rw [he] at b1 b2 p1; rw [hpl] at p2 p3; rw [hk] at p4; rw [hs] at p5
  simp only [ldedupT, lengthT, hcs] at *
  have : 4 * (st.removed.length + 1 + 1) ≤ 4 * 66 := Nat.mul_le_mul_left _ (by omega)
  have : 4 * (3 * W.ret.length + 1 + 1) ≤ 4 * (3 * (2 * (R + C) + 84) + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have : 4 * (W.ret.length + 1 + 1) ≤ 4 * (2 * (R + C) + 86) := Nat.mul_le_mul_left _ (by omega)
  have : 300 * st.removed.length ≤ 300 * 64 := Nat.mul_le_mul_left _ hrem
  omega

/-- **The catalogue test takes at most `300000 (R + C + 1)` steps.** -/
theorem fires3T_time (R C : ℕ) (s0 t0 s1 t1 : ℕ × ℕ) :
    (fires3T R C s0 t0 s1 t1).time ≤ 300000 * (R + C + 1) := by
  simp only [fires3T, time_bind, time_pure]
  have a := parityOkT_time R C [(s0, 0), (t0, 0), (s1, 1), (t1, 1)]
  have b := t1FiresT_time R C [(s0, 0), (t0, 0), (s1, 1), (t1, 1)]
  have c := t2FiresT_time [s0, t0, s1, t1]
  have d := l1FiresT_time R C [(s0, 0), (t0, 0), (s1, 1), (t1, 1)]
  have e := l6FiresT_time R C [(s0, 0), (t0, 0), (s1, 1), (t1, 1)]
  have f := lanyT_time_le (frameFiresT R C [(s0, 0), (t0, 0), (s1, 1), (t1, 1)]) frames
    ((R + C + 1) * (4 * 4 + 2) + 2000 * (4 + 4))
    (fun fr _ => frameFiresT_time R C _ fr)
  have g := effAlt3T_time R C [(s0, 0), (t0, 0), (s1, 1), (t1, 1)] rfl
  have hf : frames.length = 8 := by decide
  rw [hf] at f
  simp only [List.length_cons, List.length_nil] at a b c d e
  nlinarith

end ZZN.T

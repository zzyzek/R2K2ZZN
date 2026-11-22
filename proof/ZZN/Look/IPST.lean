/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Look.IPS
public import ZZN.Timed.TimeM

@[expose] public section

/-!
# The IPS path, counted

`ipsPT` is `ipsP` (`ipsPT_ret`) with each list operation charged its length and one step per
call. `ipsPT_time`: on an acceptable problem with `w + h ≤ n` it takes at most
`100 (w + h) (w h + 1)` steps.
-/

namespace ZZN.T

open GridHam

def colEdgeT (X : ℕ) : List Coord → TimeM (Option (List Coord × Coord × Coord × List Coord))
  | a :: b :: r => do
    tick 1
    if a.1 = X ∧ b.1 = X then pure (some ([], a, b, r))
    else do
      let o ← colEdgeT X (b :: r)
      pure (o.map fun q => (a :: q.1, q.2.1, q.2.2.1, q.2.2.2))
  | _ => do tick 1; pure none

theorem colEdgeT_ret (X : ℕ) : ∀ l, (colEdgeT X l).ret = colEdge X l
  | a :: b :: r => by
    simp only [colEdgeT, colEdge, ret_bind]
    split_ifs
    · rfl
    · simp [colEdgeT_ret X (b :: r)]
  | [] => rfl
  | [_] => rfl

theorem colEdgeT_time (X : ℕ) : ∀ l, (colEdgeT X l).time ≤ l.length + 1
  | a :: b :: r => by
    simp only [colEdgeT, time_bind, time_tick]
    split_ifs
    · simp
    · have := colEdgeT_time X (b :: r)
      simp only [time_bind, time_pure, List.length_cons] at this ⊢
      omega
  | [] => by simp [colEdgeT]
  | [_] => by simp [colEdgeT]

def colSegT (c lo : ℕ) : ℕ → TimeM (List Coord)
  | 0 => do tick 1; pure [(c, lo)]
  | k + 1 => do
    tick 1
    let r ← colSegT c lo k
    pure ((c, lo + (k + 1)) :: r)

theorem colSegT_ret (c lo : ℕ) : ∀ k, (colSegT c lo k).ret = colSeg c lo k
  | 0 => rfl
  | k + 1 => by simp [colSegT, colSeg, colSegT_ret c lo k]

theorem colSegT_time (c lo : ℕ) : ∀ k, (colSegT c lo k).time = k + 1
  | 0 => rfl
  | k + 1 => by simp [colSegT, colSegT_time c lo k]; omega

def rightDetourT (w h y : ℕ) : TimeM (List Coord) := do
  let a ← colSegT w 0 y
  let b ← colSegT (w + 1) 0 (h - 1)
  let b' ← lreverseT b
  let c ← colSegT w (y + 1) (h - 1 - (y + 1))
  let bc ← lappendT b' c
  lappendT a bc

theorem rightDetourT_ret (w h y : ℕ) : (rightDetourT w h y).ret = rightDetour w h y := by
  simp [rightDetourT, rightDetour, colSegT_ret, lreverseT, lappendT]

theorem rightDetourT_time (w h y : ℕ) : (rightDetourT w h y).time ≤ 4 * h + 2 * y + 9 := by
  simp only [rightDetourT, time_bind, colSegT_time, lreverseT, lappendT, colSegT_ret,
    List.length_reverse, colSeg_length]
  omega

def stripRightPT (width height : ℕ) (p : List Coord) : TimeM (List Coord) := do
  let o ← colEdgeT (width - 3) p
  match o with
  | some (l1, a, b, l2) =>
    if b.2 = a.2 + 1 then do
      let d ← rightDetourT (width - 2) height a.2
      let m ← lappendT d (b :: l2)
      lappendT l1 (a :: m)
    else do
      let r2 ← lreverseT l2
      let r1 ← lreverseT l1
      let d ← rightDetourT (width - 2) height b.2
      let m ← lappendT d (a :: r1)
      let q ← lappendT r2 (b :: m)
      lreverseT q
  | none => pure p

theorem stripRightPT_ret (width height : ℕ) (p : List Coord) :
    (stripRightPT width height p).ret = stripRightP width height p := by
  unfold stripRightPT stripRightP
  simp only [ret_bind, colEdgeT_ret]
  rcases colEdge (width - 3) p with _ | ⟨l1, a, b, l2⟩
  · rfl
  · dsimp only
    split_ifs <;> simp [rightDetourT_ret, lappendT, lreverseT]

/-- The prime lookup with its two scans charged. -/
def primeLookupT (w h : ℕ) (s t : Coord) : TimeM (List Coord) := do
  let e ← lfindT (fun e => pure (e.1 == w && e.2.1 == h)) primeTable
  match e with
  | none => pure []
  | some e => do
    let x ← lfindT (fun x => pure (x.1 == s && x.2.1 == t)) e.2.2
    match x with
    | none => pure []
    | some x => pure x.2.2

theorem primeLookupT_ret (w h : ℕ) (s t : Coord) :
    (primeLookupT w h s t).ret = primeLookup w h s t := by
  unfold primeLookupT primeLookup
  generalize primeTable = T
  simp only [ret_bind, lfindT, ret_pure]
  cases h1 : List.find? (fun x => x.1 == w && x.2.1 == h) T with
  | none => simp only [ret_pure]
  | some e =>
    simp only [ret_bind]
    cases List.find? (fun x => x.1 == s && x.2.1 == t) e.2.2 <;> simp only [ret_pure]

set_option maxRecDepth 100000 in
theorem primeTable_entries : ∀ e ∈ primeTable, e.2.2.length ≤ 250 := by decide +kernel

theorem primeLookupT_time (w h : ℕ) (s t : Coord) : (primeLookupT w h s t).time ≤ 300 := by
  unfold primeLookupT
  simp only [time_bind]
  have h1 := lfindT_time_le (fun e : ℕ × ℕ × List (Coord × Coord × List Coord) =>
    (pure (e.1 == w && e.2.1 == h) : TimeM Bool)) primeTable 0 (fun _ _ => le_rfl)
  have hl : primeTable.length = 12 := rfl
  rw [hl] at h1
  split
  · simp only [time_pure]; omega
  · rename_i e he
    have hm := primeTable_entries e (List.mem_of_find?_eq_some (by simpa [lfindT] using he))
    simp only [time_bind]
    have h2 := lfindT_time_le (fun x : Coord × Coord × List Coord =>
      (pure (x.1 == s && x.2.1 == t) : TimeM Bool)) e.2.2 0 (fun _ _ => le_rfl)
    split <;> simp only [time_pure] <;> nlinarith

def stripLeftPT (width height : ℕ) (p : List Coord) : TimeM (List Coord) := do
  let q ← lmapT (fun v => pure (reflectX (width - 2) v)) p
  let r ← stripRightPT width height q
  lmapT (fun v => pure (reflectX width v)) r

theorem stripLeftPT_ret (width height : ℕ) (p : List Coord) :
    (stripLeftPT width height p).ret = stripLeftP width height p := by
  simp [stripLeftPT, stripLeftP, lmapT, stripRightPT_ret]

def normPT (f : ℕ → ℕ → Coord → Coord → TimeM (List Coord)) (w h : ℕ) (s t : Coord) :
    TimeM (List Coord) := do
  tick 1
  if NotPrime w h then
    if 2 ≤ s.1 then do
      let p ← f (w - 2) h (s.1 - 2, s.2) (t.1 - 2, t.2)
      stripLeftPT w h p
    else if t.1 + 2 < w then do
      let p ← f (w - 2) h s t
      stripRightPT w h p
    else do
      let a ← f 2 h s (1, rChoice s.1 s.2 h)
      let b ← f (w - 2) h (0, rChoice s.1 s.2 h) (t.1 - 2, t.2)
      let b' ← lmapT (fun v => pure (shiftX 2 v)) b
      lappendT a b'
  else primeLookupT w h s t

def stepPT (f : ℕ → ℕ → Coord → Coord → TimeM (List Coord)) (w h : ℕ) (s t : Coord) :
    TimeM (List Coord) :=
  if h ≤ w then (if s.1 ≤ t.1 then normPT f w h s t else normPT f w h t s >>= lreverseT)
  else do
    let r ← (if s.2 ≤ t.2 then normPT f h w (swapXY s) (swapXY t)
      else normPT f h w (swapXY t) (swapXY s) >>= lreverseT)
    lmapT (fun v => pure (swapXY v)) r

def ipsPT : ℕ → ℕ → ℕ → Coord → Coord → TimeM (List Coord)
  | 0, _, _, _, _ => pure []
  | n + 1, w, h, s, t => stepPT (ipsPT n) w h s t

theorem normPT_ret {f : ℕ → ℕ → Coord → Coord → TimeM (List Coord)}
    {g : ℕ → ℕ → Coord → Coord → List Coord} (hf : ∀ w h s t, (f w h s t).ret = g w h s t)
    (w h : ℕ) (s t : Coord) : (normPT f w h s t).ret = normP g w h s t := by
  unfold normPT normP
  simp only [ret_bind]
  split_ifs <;> simp [hf, stripLeftPT_ret, stripRightPT_ret, primeLookupT_ret, lmapT, lappendT]

theorem ipsPT_ret : ∀ n w h (s t : Coord), (ipsPT n w h s t).ret = ipsP n w h s t
  | 0, _, _, _, _ => rfl
  | n + 1, w, h, s, t => by
    have hf := ipsPT_ret n
    unfold ipsPT ipsP stepPT stepP
    split_ifs <;> simp [normPT_ret hf, lreverseT, lmapT]

theorem rightDetour_length_le (w h y : ℕ) : (rightDetour w h y).length ≤ y + 2 * h + 3 := by
  simp only [rightDetour, List.length_append, List.length_reverse, colSeg_length]
  omega

theorem stripRightPT_time (width height : ℕ) (p : List Coord) (hb : ∀ v ∈ p, v.2 < height) :
    (stripRightPT width height p).time ≤ 6 * p.length + 12 * height + 30 := by
  unfold stripRightPT
  simp only [time_bind]
  have hc := colEdgeT_time (width - 3) p
  rw [colEdgeT_ret]
  rcases hq : colEdge (width - 3) p with _ | ⟨l1, a, b, l2⟩
  · simp only [time_pure]; omega
  · obtain ⟨hp, -, -⟩ := colEdge_some (width - 3) p hq
    have hl : p.length = l1.length + l2.length + 2 := by rw [hp]; simp; omega
    have ha := hb a (by rw [hp]; simp)
    have hbb := hb b (by rw [hp]; simp)
    dsimp only
    split_ifs
    · simp only [time_bind, lappendT, rightDetourT_ret]
      have := rightDetourT_time (width - 2) height a.2
      have := rightDetour_length_le (width - 2) height a.2
      omega
    · simp only [time_bind, lappendT, lreverseT, rightDetourT_ret, List.length_append,
        List.length_cons, List.length_reverse]
      have := rightDetourT_time (width - 2) height b.2
      have := rightDetour_length_le (width - 2) height b.2
      omega

theorem stripRightP_length (width height : ℕ) (p : List Coord) (hb : ∀ v ∈ p, v.2 < height) :
    (stripRightP width height p).length ≤ p.length + 3 * height + 3 := by
  unfold stripRightP
  rcases hq : colEdge (width - 3) p with _ | ⟨l1, a, b, l2⟩
  · dsimp only; omega
  · obtain ⟨hp, -, -⟩ := colEdge_some (width - 3) p hq
    have hl : p.length = l1.length + l2.length + 2 := by rw [hp]; simp; omega
    have ha := hb a (by rw [hp]; simp)
    have hbb := hb b (by rw [hp]; simp)
    dsimp only
    split_ifs
    · have := rightDetour_length_le (width - 2) height a.2
      simp only [List.length_append, List.length_cons]; omega
    · have := rightDetour_length_le (width - 2) height b.2
      simp only [List.length_reverse, List.length_append, List.length_cons]; omega

theorem stripLeftPT_time (width height : ℕ) (p : List Coord) (hb : ∀ v ∈ p, v.2 < height) :
    (stripLeftPT width height p).time ≤ 8 * p.length + 15 * height + 40 := by
  unfold stripLeftPT
  simp only [time_bind]
  have hb' : ∀ v ∈ p.map (reflectX (width - 2)), v.2 < height := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    exact hb u hu
  have h1 := lmapT_time_le (fun v => (pure (reflectX (width - 2) v) : TimeM Coord)) p 0
    (fun _ _ => le_rfl)
  have e1 : (lmapT (fun v => (pure (reflectX (width - 2) v) : TimeM Coord)) p).ret =
      p.map (reflectX (width - 2)) := by simp [lmapT]
  rw [e1]
  have h2 := stripRightPT_time width height _ hb'
  have h3 := lmapT_time_le (fun v => (pure (reflectX width v) : TimeM Coord))
    (stripRightPT width height (p.map (reflectX (width - 2)))).ret 0 (fun _ _ => le_rfl)
  rw [stripRightPT_ret] at h3 ⊢
  have h4 := stripRightP_length width height _ hb'
  simp only [List.length_map] at h2 h4
  omega

/-- The step bound, at one level. -/
theorem normPT_time (n : ℕ)
    (IH : ∀ w h s t, w + h ≤ n → InBounds w h s → InBounds w h t → s ≠ t →
      IsAcceptable w h s t → (ipsPT n w h s t).time ≤ 100 * (w + h) * (w * h + 1))
    (w h : ℕ) (s t : Coord) (hsz : w + h ≤ n + 1) (hwh : h ≤ w) (hle : s.1 ≤ t.1)
    (hs : InBounds w h s) (ht : InBounds w h t) (hst : s ≠ t)
    (hacc : IsAcceptable w h s t) :
    (normPT (ipsPT n) w h s t).time + 10 * (w * h + 1) ≤ 100 * (w + h) * (w * h + 1) := by
  obtain ⟨sx, sy⟩ := s
  obtain ⟨tx, ty⟩ := t
  have hs' : sx < w ∧ sy < h := hs
  have ht' : tx < w ∧ ty < h := ht
  have hle' : sx ≤ tx := hle
  have hst' : ¬ (sx = tx ∧ sy = ty) := by
    rintro ⟨e1, e2⟩
    apply hst
    rw [e1, e2]
  have hA : AccA w h sx sy tx ty := (acc_iff w h (sx, sy) (tx, ty)).mp hacc
  have hV := fun w' h' s' t' (a : w' + h' ≤ n) b c d e =>
    ipsP_valid n w' h' s' t' a b c d e
  unfold normPT
  simp only [time_bind, time_tick]
  by_cases hnp : NotPrime w h
  · simp only [hnp, ↓reduceIte]
    have hw4 : 4 ≤ w := by unfold NotPrime at hnp; omega
    by_cases hA2 : 2 ≤ sx
    · simp only [hA2, ↓reduceIte, time_bind]
      obtain ⟨hsub, -⟩ := branchA w h sx sy tx ty hs' ht' hst' hwh hle' hnp hA hA2
      have a1 : (sx - 2, sy) ≠ (tx - 2, ty) := by
        intro e
        obtain ⟨e1, e2⟩ := Prod.mk.inj e
        exact hst' ⟨by omega, e2⟩
      have a2 := (acc_iff (w - 2) h (sx - 2, sy) (tx - 2, ty)).mpr hsub
      have b1 := IH (w - 2) h (sx - 2, sy) (tx - 2, ty) (by omega)
        (show sx - 2 < w - 2 ∧ sy < h by omega) (show tx - 2 < w - 2 ∧ ty < h by omega) a1 a2
      have v1 := hV (w - 2) h (sx - 2, sy) (tx - 2, ty) (by omega)
        (show sx - 2 < w - 2 ∧ sy < h by omega) (show tx - 2 < w - 2 ∧ ty < h by omega) a1 a2
      rw [← ipsPT_ret] at v1
      obtain ⟨hlen, -, -, -, hin, -, -⟩ := v1
      have b2 := stripLeftPT_time w h _ (fun v hv => (hin v hv).2)
      rw [hlen] at b2
      have : (w - 2) * h + 1 ≤ w * h + 1 := by
        have := Nat.mul_le_mul_right h (show w - 2 ≤ w by omega); omega
      have : 100 * (w - 2 + h) * ((w - 2) * h + 1) ≤ 100 * (w + h - 2) * (w * h + 1) := by
        have e : w - 2 + h = w + h - 2 := by omega
        rw [e]; exact Nat.mul_le_mul_left _ this
      have : 100 * (w + h - 2) * (w * h + 1) + 200 * (w * h + 1) = 100 * (w + h) * (w * h + 1) := by
        have e : w + h = (w + h - 2) + 2 := by omega
        conv_rhs => rw [e]
        ring
      nlinarith
    · simp only [hA2, ↓reduceIte]
      by_cases hC : tx + 2 < w
      · simp only [hC, ↓reduceIte, time_bind]
        obtain ⟨hsub, -⟩ :=
          branchC w h sx sy tx ty hs' ht' hst' hwh hle' hnp hA (by omega) hC
        have a2 := (acc_iff (w - 2) h (sx, sy) (tx, ty)).mpr hsub
        have b1 := IH (w - 2) h (sx, sy) (tx, ty) (by omega)
          (show sx < w - 2 ∧ sy < h by omega) (show tx < w - 2 ∧ ty < h by omega) hst a2
        have v1 := hV (w - 2) h (sx, sy) (tx, ty) (by omega)
          (show sx < w - 2 ∧ sy < h by omega) (show tx < w - 2 ∧ ty < h by omega) hst a2
        rw [← ipsPT_ret] at v1
        obtain ⟨hlen, -, -, -, hin, -, -⟩ := v1
        have b2 := stripRightPT_time w h _ (fun v hv => (hin v hv).2)
        rw [hlen] at b2
        have : (w - 2) * h + 1 ≤ w * h + 1 := by
          have := Nat.mul_le_mul_right h (show w - 2 ≤ w by omega); omega
        have : 100 * (w - 2 + h) * ((w - 2) * h + 1) ≤ 100 * (w + h - 2) * (w * h + 1) := by
          have e : w - 2 + h = w + h - 2 := by omega
          rw [e]; exact Nat.mul_le_mul_left _ this
        have : 100 * (w + h - 2) * (w * h + 1) + 200 * (w * h + 1) = 100 * (w + h) * (w * h + 1) := by
          have e : w + h = (w + h - 2) + 2 := by omega
          conv_rhs => rw [e]
          ring
        nlinarith
      · simp only [hC, ↓reduceIte, time_bind]
        have hB := branchB w h sx sy tx ty hs' ht' hst' hwh hle' hnp hA (by omega) (by omega)
        unfold BConcl at hB
        obtain ⟨hr, hs1, hq, haccL, haccR⟩ := hB
        have nL : (sx, sy) ≠ (1, rChoice sx sy h) := by
          intro e
          obtain ⟨e1, e2⟩ := Prod.mk.inj e
          exact hs1 ⟨e1, e2⟩
        have nR : (0, rChoice sx sy h) ≠ (tx - 2, ty) := by
          intro e
          obtain ⟨e1, e2⟩ := Prod.mk.inj e
          exact hq ⟨e1, e2⟩
        have aL := (acc_iff 2 h (sx, sy) (1, rChoice sx sy h)).mpr haccL
        have aR := (acc_iff (w - 2) h (0, rChoice sx sy h) (tx - 2, ty)).mpr haccR
        have bL := IH 2 h (sx, sy) (1, rChoice sx sy h) (by omega)
          (show sx < 2 ∧ sy < h by omega) (show 1 < 2 ∧ rChoice sx sy h < h by omega) nL aL
        have bR := IH (w - 2) h (0, rChoice sx sy h) (tx - 2, ty) (by omega)
          (show 0 < w - 2 ∧ rChoice sx sy h < h by omega)
          (show tx - 2 < w - 2 ∧ ty < h by omega) nR aR
        have vL := hV 2 h (sx, sy) (1, rChoice sx sy h) (by omega)
          (show sx < 2 ∧ sy < h by omega) (show 1 < 2 ∧ rChoice sx sy h < h by omega) nL aL
        have vR := hV (w - 2) h (0, rChoice sx sy h) (tx - 2, ty) (by omega)
          (show 0 < w - 2 ∧ rChoice sx sy h < h by omega)
          (show tx - 2 < w - 2 ∧ ty < h by omega) nR aR
        rw [← ipsPT_ret] at vL vR
        have lL := vL.1
        have lR := vR.1
        have m1 := lmapT_time_le (fun v => (pure (shiftX 2 v) : TimeM Coord))
          (ipsPT n (w - 2) h (0, rChoice sx sy h) (tx - 2, ty)).ret 0 (fun _ _ => le_rfl)
        simp only [lappendT, lL] at m1 ⊢
        rw [lR] at m1
        have hp : 9 * h + 1 ≤ 3 * w * h := by nlinarith
        have key : (2 + h) * (2 * h + 1) + (w - 2 + h) * ((w - 2) * h + 1) + (w * h + 1) ≤
            (w + h) * (w * h + 1) := by
          obtain ⟨k, rfl⟩ : ∃ k, w = k + 4 := ⟨w - 4, by omega⟩
          simp only [show k + 4 - 2 = k + 2 by omega]
          nlinarith
        nlinarith
  · simp only [hnp, ↓reduceIte]
    have := primeLookupT_time w h (sx, sy) (tx, ty)
    have h2 : 2 ≤ w * h + 1 := by have : 1 ≤ w * h := Nat.mul_pos (by omega) (by omega); omega
    have h3 : 2 * (w * h + 1) ≤ (w + h) * (w * h + 1) := Nat.mul_le_mul_right _ (by omega)
    nlinarith

/-- **The IPS path takes `O((w + h) w h)` steps.** -/
theorem ipsPT_time : ∀ n w h (s t : Coord), w + h ≤ n → InBounds w h s → InBounds w h t →
    s ≠ t → IsAcceptable w h s t → (ipsPT n w h s t).time ≤ 100 * (w + h) * (w * h + 1)
  | 0, w, h, s, _, hsz, hs, _, _, _ => by
    have hs0 : s.1 < w ∧ s.2 < h := hs
    omega
  | n + 1, w, h, s, t, hsz, hs, ht, hst, hacc => by
    have IH := ipsPT_time n
    unfold ipsPT stepPT
    have hs0 : s.1 < w ∧ s.2 < h := hs
    have ht0 : t.1 < w ∧ t.2 < h := ht
    by_cases hwh : h ≤ w
    · simp only [hwh, ↓reduceIte]
      by_cases hle : s.1 ≤ t.1
      · simp only [hle, ↓reduceIte]
        have := normPT_time n IH w h s t hsz hwh hle hs ht hst hacc
        omega
      · simp only [hle, ↓reduceIte, time_bind, lreverseT]
        have hacc' : IsAcceptable w h t s := (acc_iff w h t s).mpr
          ((accA_swap w h s.1 s.2 t.1 t.2 hs ht).mp ((acc_iff w h s t).mp hacc))
        have := normPT_time n IH w h t s hsz hwh (by omega) ht hs (Ne.symm hst) hacc'
        have hv := (normP_valid n (ipsP_valid n) w h t s hsz hwh (by omega) ht hs (Ne.symm hst)
          hacc').1
        rw [normPT_ret (ipsPT_ret n), hv]
        nlinarith
    · simp only [hwh, ↓reduceIte, time_bind]
      have hsT : InBounds h w (swapXY s) := show s.2 < h ∧ s.1 < w from ⟨hs0.2, hs0.1⟩
      have htT : InBounds h w (swapXY t) := show t.2 < h ∧ t.1 < w from ⟨ht0.2, ht0.1⟩
      have hstT : swapXY s ≠ swapXY t := fun e => hst (by
        have := congrArg swapXY e
        simpa [swapXY] using this)
      have haccT : IsAcceptable h w (swapXY s) (swapXY t) :=
        (acc_iff h w (swapXY s) (swapXY t)).mpr
          ((accA_transpose w h s.1 s.2 t.1 t.2 hs ht).mp ((acc_iff w h s t).mp hacc))
      have hm := fun (r : TimeM (List Coord)) =>
        lmapT_time_le (fun v => (pure (swapXY v) : TimeM Coord)) r.ret 0 (fun _ _ => le_rfl)
      by_cases hle : s.2 ≤ t.2
      · simp only [hle, ↓reduceIte]
        have := normPT_time n IH h w (swapXY s) (swapXY t) (by omega) (by omega) hle hsT htT hstT haccT
        have hv := (normP_valid n (ipsP_valid n) h w (swapXY s) (swapXY t) (by omega) (by omega) hle
          hsT htT hstT haccT).1
        have h2 := hm (normPT (ipsPT n) h w (swapXY s) (swapXY t))
        rw [normPT_ret (ipsPT_ret n), hv] at h2
        rw [normPT_ret (ipsPT_ret n)]
        have e1 : 100 * (h + w) * (h * w + 1) = 100 * (w + h) * (w * h + 1) := by ring
        omega
      · simp only [hle, ↓reduceIte, time_bind, lreverseT]
        have haccT' : IsAcceptable h w (swapXY t) (swapXY s) := (acc_iff h w _ _).mpr
          ((accA_swap h w s.2 s.1 t.2 t.1 hsT htT).mp ((acc_iff h w _ _).mp haccT))
        have := normPT_time n IH h w (swapXY t) (swapXY s) (by omega) (by omega)
          (by show t.2 ≤ s.2; omega) htT hsT (Ne.symm hstT) haccT'
        have hv := (normP_valid n (ipsP_valid n) h w (swapXY t) (swapXY s) (by omega) (by omega)
          (by show t.2 ≤ s.2; omega) htT hsT (Ne.symm hstT) haccT').1
        have h2 := hm (normPT (ipsPT n) h w (swapXY t) (swapXY s) >>= lreverseT)
        have er : (normPT (ipsPT n) h w (swapXY t) (swapXY s) >>= lreverseT).ret =
            (normP (ipsP n) h w (swapXY t) (swapXY s)).reverse := by
          simp [lreverseT, normPT_ret (ipsPT_ret n)]
        rw [er] at h2 ⊢
        simp only [List.length_reverse, hv] at h2
        rw [normPT_ret (ipsPT_ret n), hv]
        have e1 : 100 * (h + w) * (h * w + 1) = 100 * (w + h) * (w * h + 1) := by ring
        omega

end ZZN.T

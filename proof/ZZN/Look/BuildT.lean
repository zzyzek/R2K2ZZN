/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Look.Build
public import ZZN.Look.CheckT
public import ZZN.Look.IPST

@[expose] public section

/-!
# Building the paths of a checked tree, counted

`buildTT` is `buildT` (`buildTT_ret`). On a tree that checks on a piece with sides at most 16, it
takes at most `tcost T (520 N + 10) + N · 822 700` steps, `N` the number of leaves (`buildTT_time`):
each leaf runs `ipsPT` on at most `16 × 16` cells, each node splits, appends and joins paths, and
joining keeps the total number of cells (`joinL_cells`), at most `256` per leaf.
-/

namespace ZZN.T

open GridHam ZZN.Cut

/-- The total number of cells of a list of paths. -/
def cellsL (ps : List Seg) : ℕ := (ps.map fun x => x.p.length).sum

theorem cellsL_erase {ps : List Seg} {x : Seg} (hx : x ∈ ps) :
    cellsL (ps.erase x) + x.p.length = cellsL ps := by
  have hp := List.perm_cons_erase hx
  unfold cellsL
  rw [(hp.map _).sum_eq]
  simp only [List.map_cons, List.sum_cons]
  omega

theorem joinL_cells (a u v b : Coord) (ps : List Seg) :
    cellsL (joinL a u v b ps) = cellsL ps ∧ (joinL a u v b ps).length ≤ ps.length := by
  unfold joinL
  split
  · exact ⟨rfl, le_rfl⟩
  · rename_i x hx
    have hxm := List.mem_of_find?_eq_some hx
    split
    · exact ⟨rfl, le_rfl⟩
    · rename_i y hy
      have hym := List.mem_of_find?_eq_some hy
      have c1 := cellsL_erase hxm
      have c2 := cellsL_erase hym
      have l1 := List.length_erase_of_mem hxm
      have l2 := List.length_erase_of_mem hym
      have hpos : 0 < ps.length := List.length_pos_of_mem hxm
      refine ⟨?_, ?_⟩
      · simp only [cellsL, List.map_cons, List.sum_cons, List.length_append] at c1 c2 ⊢
        omega
      · simp only [List.length_cons]
        omega

theorem unsplit_cells (vert : Bool) (pos : ℕ) : ∀ ks ss acc (ps : List Seg),
    cellsL (unsplit vert pos ks ss acc ps) = cellsL ps ∧
      (unsplit vert pos ks ss acc ps).length ≤ ps.length
  | [], _, _, _ => ⟨rfl, le_rfl⟩
  | Kind.stay _ :: _, [], _, _ => ⟨rfl, le_rfl⟩
  | Kind.cross _ _ :: _, [], _, _ => ⟨rfl, le_rfl⟩
  | Kind.exc _ _ _ :: _, [], _, _ => ⟨rfl, le_rfl⟩
  | Kind.stay s :: ks, (a, b) :: ss, acc, ps => by
    simp only [unsplit]
    exact unsplit_cells vert pos ks ss _ ps
  | Kind.cross s y :: ks, (a, b) :: ss, acc, ps => by
    simp only [unsplit]
    obtain ⟨c1, l1⟩ := unsplit_cells vert pos ks ss
      (put (!s) (cutc vert pos (!s) y, b) (put s (a, cutc vert pos s y) acc)) ps
    obtain ⟨c2, l2⟩ := joinL_cells a (cutc vert pos s y) (cutc vert pos (!s) y) b
      (unsplit vert pos ks ss
        (put (!s) (cutc vert pos (!s) y, b) (put s (a, cutc vert pos s y) acc)) ps)
    exact ⟨c2.trans c1, l2.trans l1⟩
  | Kind.exc s y z :: ks, (a, b) :: ss, acc, ps => by
    simp only [unsplit]
    set U := unsplit vert pos ks ss
      (put (!s) (cutc vert pos (!s) y, cutc vert pos (!s) z)
        (put s (cutc vert pos s z, b) (put s (a, cutc vert pos s y) acc))) ps
    obtain ⟨c1, l1⟩ := unsplit_cells vert pos ks ss
      (put (!s) (cutc vert pos (!s) y, cutc vert pos (!s) z)
        (put s (cutc vert pos s z, b) (put s (a, cutc vert pos s y) acc))) ps
    obtain ⟨c2, l2⟩ := joinL_cells a (cutc vert pos s y) (cutc vert pos (!s) y)
      (cutc vert pos (!s) z) U
    obtain ⟨c3, l3⟩ := joinL_cells a (cutc vert pos (!s) z) (cutc vert pos s z) b
      (joinL a (cutc vert pos s y) (cutc vert pos (!s) y) (cutc vert pos (!s) z) U)
    exact ⟨c3.trans (c2.trans c1), l3.trans (l2.trans l1)⟩

def joinLT (a u v b : Coord) (ps : List Seg) : TimeM (List Seg) := do
  let x ← lfindT (fun x => pure (x.ends == (a, u))) ps
  match x with
  | none => pure ps
  | some x => do
    let ps1 ← leraseT ps x
    let y ← lfindT (fun y => pure (y.ends == (v, b))) ps1
    match y with
    | none => pure ps
    | some y => do
      let ps2 ← leraseT ps1 y
      let p ← lappendT x.p y.p
      pure (⟨a, b, p⟩ :: ps2)

theorem joinLT_ret (a u v b : Coord) (ps : List Seg) : (joinLT a u v b ps).ret = joinL a u v b ps := by
  unfold joinLT joinL
  simp only [ret_bind, lfindT, ret_pure, leraseT]
  cases ps.find? (fun x => x.ends == (a, u)) with
  | none => rfl
  | some x =>
    simp only [ret_bind]
    cases (ps.erase x).find? (fun y => y.ends == (v, b)) <;> rfl

theorem joinLT_time (a u v b : Coord) (ps : List Seg) :
    (joinLT a u v b ps).time ≤ 4 * ps.length + 4 + cellsL ps := by
  unfold joinLT
  simp only [time_bind]
  have f1 := lfindT_time_le (fun x : Seg => (pure (x.ends == (a, u)) : TimeM Bool)) ps 0
    (fun _ _ => le_rfl)
  cases hx : (lfindT (fun x : Seg => (pure (x.ends == (a, u)) : TimeM Bool)) ps).ret with
  | none => simp only [time_pure]; omega
  | some x =>
    have hxm : x ∈ ps := List.mem_of_find?_eq_some (by simpa [lfindT] using hx)
    simp only [time_bind, leraseT]
    have f2 := lfindT_time_le (fun y : Seg => (pure (y.ends == (v, b)) : TimeM Bool)) (ps.erase x) 0
      (fun _ _ => le_rfl)
    have le1 := List.length_erase_le (l := ps) (a := x)
    have cx := cellsL_erase hxm
    cases hy : (lfindT (fun y : Seg => (pure (y.ends == (v, b)) : TimeM Bool)) (ps.erase x)).ret with
    | none => simp only [time_pure]; omega
    | some y =>
      simp only [time_bind, lappendT, time_pure]
      have le2 := List.length_erase_le (l := ps.erase x) (a := y)
      omega

def unsplitT (vert : Bool) (pos : ℕ) :
    List (Kind ℕ) → List (Coord × Coord) → List (Coord × Coord) × List (Coord × Coord) →
      List Seg → TimeM (List Seg)
  | [], _, _, ps => do tick 1; pure ps
  | Kind.stay s :: ks, (a, b) :: ss, acc, ps => do
    tick 1
    let a1 ← putT s (a, b) acc
    unsplitT vert pos ks ss a1 ps
  | Kind.cross s y :: ks, (a, b) :: ss, acc, ps => do
    tick 1
    let a1 ← putT s (a, cutc vert pos s y) acc
    let a2 ← putT (!s) (cutc vert pos (!s) y, b) a1
    let r ← unsplitT vert pos ks ss a2 ps
    joinLT a (cutc vert pos s y) (cutc vert pos (!s) y) b r
  | Kind.exc s y z :: ks, (a, b) :: ss, acc, ps => do
    tick 1
    let a1 ← putT s (a, cutc vert pos s y) acc
    let a2 ← putT s (cutc vert pos s z, b) a1
    let a3 ← putT (!s) (cutc vert pos (!s) y, cutc vert pos (!s) z) a2
    let r ← unsplitT vert pos ks ss a3 ps
    let r2 ← joinLT a (cutc vert pos s y) (cutc vert pos (!s) y) (cutc vert pos (!s) z) r
    joinLT a (cutc vert pos (!s) z) (cutc vert pos s z) b r2
  | _ :: _, [], _, ps => do tick 1; pure ps

theorem unsplitT_ret (vert : Bool) (pos : ℕ) : ∀ ks ss acc ps,
    (unsplitT vert pos ks ss acc ps).ret = unsplit vert pos ks ss acc ps
  | [], _, _, _ => rfl
  | Kind.stay _ :: _, [], _, _ => rfl
  | Kind.cross _ _ :: _, [], _, _ => rfl
  | Kind.exc _ _ _ :: _, [], _, _ => rfl
  | Kind.stay s :: ks, (a, b) :: ss, acc, ps => by
    simp [unsplitT, unsplit, putT_ret, unsplitT_ret vert pos ks ss]
  | Kind.cross s y :: ks, (a, b) :: ss, acc, ps => by
    simp [unsplitT, unsplit, putT_ret, unsplitT_ret vert pos ks ss, joinLT_ret]
  | Kind.exc s y z :: ks, (a, b) :: ss, acc, ps => by
    simp [unsplitT, unsplit, putT_ret, unsplitT_ret vert pos ks ss, joinLT_ret]

theorem unsplitT_time (vert : Bool) (pos : ℕ) : ∀ ks ss acc ps,
    (unsplitT vert pos ks ss acc ps).time ≤
      (ks.length + 1) * (3 * (acc.1.length + acc.2.length + 3 * ks.length) + 12 +
        8 * ps.length + 2 * cellsL ps)
  | [], _, _, _ => by simp [unsplitT]; omega
  | Kind.stay _ :: _, [], _, _ => by simp [unsplitT]; nlinarith
  | Kind.cross _ _ :: _, [], _, _ => by simp [unsplitT]; nlinarith
  | Kind.exc _ _ _ :: _, [], _, _ => by simp [unsplitT]; nlinarith
  | Kind.stay s :: ks, (a, b) :: ss, acc, ps => by
    simp only [unsplitT, time_bind, time_tick, putT_ret]
    have h1 := putT_time s (a, b) acc
    have h2 := unsplitT_time vert pos ks ss (put s (a, b) acc) ps
    have e := put_len s (a, b) acc
    simp only [List.length_cons]
    rw [e] at h2
    nlinarith
  | Kind.cross s y :: ks, (a, b) :: ss, acc, ps => by
    simp only [unsplitT, time_bind, time_tick, putT_ret, unsplitT_ret]
    set A1 := put s (a, cutc vert pos s y) acc
    set A2 := put (!s) (cutc vert pos (!s) y, b) A1
    have h1 := putT_time s (a, cutc vert pos s y) acc
    have h1' := putT_time (!s) (cutc vert pos (!s) y, b) A1
    have h2 := unsplitT_time vert pos ks ss A2 ps
    have e1 : A1.1.length + A1.2.length = acc.1.length + acc.2.length + 1 := put_len _ _ _
    have e2 : A2.1.length + A2.2.length = A1.1.length + A1.2.length + 1 := put_len _ _ _
    obtain ⟨c, l⟩ := unsplit_cells vert pos ks ss A2 ps
    have hj := joinLT_time a (cutc vert pos s y) (cutc vert pos (!s) y) b
      (unsplit vert pos ks ss A2 ps)
    rw [c] at hj
    simp only [List.length_cons]
    nlinarith
  | Kind.exc s y z :: ks, (a, b) :: ss, acc, ps => by
    simp only [unsplitT, time_bind, time_tick, putT_ret, unsplitT_ret, joinLT_ret]
    set A1 := put s (a, cutc vert pos s y) acc
    set A2 := put s (cutc vert pos s z, b) A1
    set A3 := put (!s) (cutc vert pos (!s) y, cutc vert pos (!s) z) A2
    have h1 := putT_time s (a, cutc vert pos s y) acc
    have h1' := putT_time s (cutc vert pos s z, b) A1
    have h1'' := putT_time (!s) (cutc vert pos (!s) y, cutc vert pos (!s) z) A2
    have h2 := unsplitT_time vert pos ks ss A3 ps
    have e1 : A1.1.length + A1.2.length = acc.1.length + acc.2.length + 1 := put_len _ _ _
    have e2 : A2.1.length + A2.2.length = A1.1.length + A1.2.length + 1 := put_len _ _ _
    have e3 : A3.1.length + A3.2.length = A2.1.length + A2.2.length + 1 := put_len _ _ _
    set U := unsplit vert pos ks ss A3 ps
    obtain ⟨c, l⟩ := unsplit_cells vert pos ks ss A3 ps
    have hj := joinLT_time a (cutc vert pos s y) (cutc vert pos (!s) y) (cutc vert pos (!s) z) U
    obtain ⟨c', l'⟩ := joinL_cells a (cutc vert pos s y) (cutc vert pos (!s) y)
      (cutc vert pos (!s) z) U
    have hj' := joinLT_time a (cutc vert pos (!s) z) (cutc vert pos s z) b
      (joinL a (cutc vert pos s y) (cutc vert pos (!s) y) (cutc vert pos (!s) z) U)
    rw [c', c] at hj'
    rw [c] at hj
    simp only [List.length_cons]
    nlinarith

/-! ### Leaves and the tree -/

def leafPT (P : Piece) : TimeM (List Seg) :=
  match P.segs with
  | [(a, b)] =>
    if eqC a b then do tick 1; pure [⟨a, a, [a]⟩]
    else do
      let q ← ipsPT (P.pw + P.ph) P.pw P.ph (a.1 - P.ox, a.2 - P.oy) (b.1 - P.ox, b.2 - P.oy)
      let q' ← lmapT (fun v => pure (v.1 + P.ox, v.2 + P.oy)) q
      pure [⟨a, b, q'⟩]
  | _ => do tick 1; pure []

theorem leafPT_ret (P : Piece) : (leafPT P).ret = leafP P := by
  unfold leafPT leafP
  split
  · rename_i a b hs
    simp only [hs]
    split_ifs <;> simp [ipsPT_ret, lmapT]
  · rename_i hn
    split
    · rename_i a b hs
      exact absurd hs (hn a b)
    · rfl

/-- The IPS problem of an accepted leaf. -/
theorem leaf_ips {P : Piece} {a b : Coord} (hs : P.segs = [(a, b)]) (hab : eqC a b = false)
    (h : leafOK P = true) :
    InBounds P.pw P.ph (a.1 - P.ox, a.2 - P.oy) ∧ InBounds P.pw P.ph (b.1 - P.ox, b.2 - P.oy) ∧
      (a.1 - P.ox, a.2 - P.oy) ≠ (b.1 - P.ox, b.2 - P.oy) ∧
      IsAcceptable P.pw P.ph (a.1 - P.ox, a.2 - P.oy) (b.1 - P.ox, b.2 - P.oy) := by
  unfold leafOK at h
  rw [hs] at h
  simp only [hab, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Piece.regionB_iff,
    Lane.accB_eq, decide_eq_true_eq] at h
  obtain ⟨⟨ha, hb⟩, hacc⟩ := h
  have hab' : a ≠ b := fun e => by rw [e] at hab; simp [eqC] at hab
  unfold Piece.region at ha hb
  refine ⟨⟨by simp; omega, by simp; omega⟩, ⟨by simp; omega, by simp; omega⟩, ?_, hacc⟩
  intro e; apply hab'; simp only [Prod.mk.injEq] at e; ext <;> omega

theorem leafP_cells {P : Piece} (h : leafOK P = true) :
    cellsL (leafP P) ≤ P.pw * P.ph ∧ (leafP P).length ≤ 1 := by
  unfold leafP
  split
  · rename_i a b hs
    split_ifs with hab
    · unfold leafOK at h
      rw [hs] at h
      simp only [hab, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨h1, h2⟩, -⟩ := h
      simp [cellsL, h1, h2]
    · obtain ⟨i1, i2, i3, i4⟩ := leaf_ips hs (by simpa using hab) h
      have hv := ipsP_valid (P.pw + P.ph) P.pw P.ph _ _ le_rfl i1 i2 i3 i4
      simp [cellsL, hv.1]
  · simp [cellsL]

theorem leafPT_time {P : Piece} (h : leafOK P = true) (hw : P.pw ≤ 16) (hh : P.ph ≤ 16) :
    (leafPT P).time ≤ 822700 := by
  unfold leafPT
  split
  · rename_i a b hs
    split_ifs with hab
    · simp
    · obtain ⟨i1, i2, i3, i4⟩ := leaf_ips hs (by simpa using hab) h
      simp only [time_bind, time_pure]
      have t1 := ipsPT_time (P.pw + P.ph) P.pw P.ph _ _ le_rfl i1 i2 i3 i4
      have t2 := lmapT_time_le (fun v : Coord => (pure (v.1 + P.ox, v.2 + P.oy) : TimeM Coord))
        (ipsPT (P.pw + P.ph) P.pw P.ph (a.1 - P.ox, a.2 - P.oy) (b.1 - P.ox, b.2 - P.oy)).ret 0
        (fun _ _ => le_rfl)
      have hl : (ipsPT (P.pw + P.ph) P.pw P.ph (a.1 - P.ox, a.2 - P.oy)
          (b.1 - P.ox, b.2 - P.oy)).ret.length = P.pw * P.ph := by
        rw [ipsPT_ret]; exact (ipsP_valid (P.pw + P.ph) P.pw P.ph _ _ le_rfl i1 i2 i3 i4).1
      rw [hl] at t2
      have m1 : P.pw * P.ph ≤ 16 * 16 := Nat.mul_le_mul hw hh
      have m2 : (P.pw + P.ph) * (P.pw * P.ph + 1) ≤ 32 * 257 :=
        Nat.mul_le_mul (by omega) (by omega)
      have m3 := Nat.mul_le_mul_left 100 m2
      rw [← Nat.mul_assoc] at m3
      omega
  · simp

theorem dims_split {P : Piece} {vert : Bool} {pos : ℕ} (hin : inside vert pos P = true)
    (L R : List (Coord × Coord)) :
    (P.lo vert pos L).pw ≤ P.pw ∧ (P.lo vert pos L).ph ≤ P.ph ∧
      (P.hi vert pos R).pw ≤ P.pw ∧ (P.hi vert pos R).ph ≤ P.ph := by
  cases vert <;> simp only [inside, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
    decide_eq_true_eq] at hin <;> simp only [Piece.lo, Piece.hi, Bool.false_eq_true, ↓reduceIte] <;>
    omega

theorem buildT_cells : ∀ (T : CTree ℕ) (P : Piece), check T P = true → P.pw ≤ 16 → P.ph ≤ 16 →
    cellsL (buildT T P) ≤ 256 * tleaves T ∧ (buildT T P).length ≤ tleaves T
  | CTree.leaf, P, h, hw, hh => by
    obtain ⟨c, l⟩ := leafP_cells h
    have : P.pw * P.ph ≤ 16 * 16 := Nat.mul_le_mul hw hh
    simp only [buildT, tleaves]
    omega
  | CTree.cut vert pos ks l r, P, h, hw, hh => by
    simp only [check, Bool.and_eq_true] at h
    obtain ⟨hin, h⟩ := h
    simp only [buildT, tleaves]
    split at h
    · rename_i L R hsp
      rw [hsp]
      simp only [Bool.and_eq_true] at h
      obtain ⟨d1, d2, d3, d4⟩ := dims_split hin L R
      obtain ⟨c1, l1⟩ := buildT_cells l _ h.1 (by omega) (by omega)
      obtain ⟨c2, l2⟩ := buildT_cells r _ h.2 (by omega) (by omega)
      obtain ⟨c, ln⟩ := unsplit_cells vert pos ks P.segs ([], [])
        (buildT l (P.lo vert pos L) ++ buildT r (P.hi vert pos R))
      have hc : cellsL (buildT l (P.lo vert pos L) ++ buildT r (P.hi vert pos R)) =
          cellsL (buildT l (P.lo vert pos L)) + cellsL (buildT r (P.hi vert pos R)) := by
        simp [cellsL]
      simp only [List.length_append] at ln
      dsimp only
      omega
    · simp at h

def buildTT : CTree ℕ → Piece → TimeM (List Seg)
  | CTree.leaf, P => leafPT P
  | CTree.cut vert pos ks l r, P => do
    tick 1
    let o ← splitT vert pos ks P.segs ([], [])
    match o with
    | some (L, R) => do
      let a ← buildTT l (P.lo vert pos L)
      let b ← buildTT r (P.hi vert pos R)
      let ab ← lappendT a b
      unsplitT vert pos ks P.segs ([], []) ab
    | none => pure []

theorem buildTT_ret : ∀ (T : CTree ℕ) (P : Piece), (buildTT T P).ret = buildT T P
  | CTree.leaf, P => leafPT_ret P
  | CTree.cut vert pos ks l r, P => by
    simp only [buildTT, buildT, ret_bind, splitT_ret]
    rcases split vert pos ks P.segs ([], []) with _ | ⟨L, R⟩
    · rfl
    · simp [buildTT_ret l, buildTT_ret r, lappendT, unsplitT_ret]

theorem buildTT_time (N : ℕ) : ∀ (T : CTree ℕ) (P : Piece), check T P = true → P.pw ≤ 16 →
    P.ph ≤ 16 → tleaves T ≤ N →
    (buildTT T P).time ≤ tcost T * (520 * N + 10) + tleaves T * 822700
  | CTree.leaf, P, h, hw, hh, _ => by
    simp only [buildTT, tcost, tleaves]
    have := leafPT_time h hw hh
    omega
  | CTree.cut vert pos ks l r, P, h, hw, hh, hN => by
    have h0 := h
    simp only [check, Bool.and_eq_true] at h
    obtain ⟨hin, h⟩ := h
    simp only [buildTT, tcost, tleaves, time_bind, time_tick] at hN ⊢
    have hs := splitT_time vert pos ks P.segs ([], [])
    simp only [List.length_nil, Nat.zero_add] at hs
    rw [splitT_ret]
    split at h
    · rename_i L R hsp
      rw [hsp]
      simp only [Bool.and_eq_true] at h
      obtain ⟨d1, d2, d3, d4⟩ := dims_split hin L R
      have bl := buildTT_time N l _ h.1 (by omega) (by omega) (by omega)
      have br := buildTT_time N r _ h.2 (by omega) (by omega) (by omega)
      obtain ⟨cl, ll⟩ := buildT_cells l _ h.1 (by omega) (by omega)
      obtain ⟨cr, lr⟩ := buildT_cells r _ h.2 (by omega) (by omega)
      simp only [time_bind, lappendT, buildTT_ret]
      have hu := unsplitT_time vert pos ks P.segs ([], [])
        (buildT l (P.lo vert pos L) ++ buildT r (P.hi vert pos R))
      have hc : cellsL (buildT l (P.lo vert pos L) ++ buildT r (P.hi vert pos R)) =
          cellsL (buildT l (P.lo vert pos L)) + cellsL (buildT r (P.hi vert pos R)) := by
        simp [cellsL]
      simp only [List.length_nil, Nat.zero_add, List.length_append, hc] at hu
      have pl := tleaves_pos l
      have pr := tleaves_pos r
      have k1 : (buildT l (P.lo vert pos L)).length + (buildT r (P.hi vert pos R)).length ≤ N := by
        omega
      have k2 : cellsL (buildT l (P.lo vert pos L)) + cellsL (buildT r (P.hi vert pos R)) ≤
          256 * N := by omega
      have k3 : (ks.length + 1) * (3 * (3 * ks.length) + 12 +
          8 * ((buildT l (P.lo vert pos L)).length + (buildT r (P.hi vert pos R)).length) +
          2 * (cellsL (buildT l (P.lo vert pos L)) + cellsL (buildT r (P.hi vert pos R)))) ≤
          (ks.length + 1) * (9 * ks.length + 12 + 520 * N) :=
        Nat.mul_le_mul_left _ (by omega)
      nlinarith
    · simp at h

/-- The solution of a checked template, counted. -/
def solOfT (I : Inst) (ps : List Seg) : TimeM (List Coord × List Coord) := do
  let x ← lfindT (fun x => pure (x.ends == (I.s0, I.t0))) ps
  let y ← lfindT (fun x => pure (x.ends == (I.s1, I.t1))) ps
  pure (x.elim [] Seg.p, y.elim [] Seg.p)

theorem solOfT_ret (I : Inst) (ps : List Seg) : (solOfT I ps).ret = solOf I ps := by
  simp [solOfT, solOf, lfindT]

theorem solOfT_time (I : Inst) (ps : List Seg) : (solOfT I ps).time ≤ 2 * ps.length := by
  simp only [solOfT, time_bind, time_pure]
  have := lfindT_time_le (fun x : Seg => (pure (x.ends == (I.s0, I.t0)) : TimeM Bool)) ps 0
    (fun _ _ => le_rfl)
  have := lfindT_time_le (fun x : Seg => (pure (x.ends == (I.s1, I.t1)) : TimeM Bool)) ps 0
    (fun _ _ => le_rfl)
  omega

def tsolT (T : CTree TPos) (I : Inst) : TimeM (List Coord × List Coord) := do
  let T' ← instT (posN I.s0.1 I.t0.1 I.s1.1 I.t1.1 I.w) (posN I.s0.2 I.t0.2 I.s1.2 I.t1.2 I.h) T
  let ps ← buildTT T' (rootPiece I)
  solOfT I ps

theorem tsolT_ret (T : CTree TPos) (I : Inst) : (tsolT T I).ret = tsol T I := by
  simp [tsolT, tsol, instT_ret, buildTT_ret, solOfT_ret]

theorem tsolT_time (T : CTree TPos) (I : Inst) (h : tcheck T I = true) (hw : I.w ≤ 16)
    (hh : I.h ≤ 16) (N : ℕ) (hN : tleaves T ≤ N) :
    (tsolT T I).time ≤ tcost T * (520 * N + 11) + N * 822700 + 2 * N := by
  simp only [tsolT, time_bind, instT_ret, buildTT_ret]
  have t1 := instT_time (posN I.s0.1 I.t0.1 I.s1.1 I.t1.1 I.w) (posN I.s0.2 I.t0.2 I.s1.2 I.t1.2 I.h) T
  set T' := inst (posN I.s0.1 I.t0.1 I.s1.1 I.t1.1 I.w) (posN I.s0.2 I.t0.2 I.s1.2 I.t1.2 I.h) T
  have hc : tcost T' = tcost T := tcost_inst _ _ T
  have hl : tleaves T' = tleaves T := tleaves_inst _ _ T
  have t2 := buildTT_time N T' (rootPiece I) h hw hh (by omega)
  obtain ⟨-, ln⟩ := buildT_cells T' (rootPiece I) h hw hh
  have t3 := solOfT_time I (buildT T' (rootPiece I))
  rw [hc, hl] at t2
  rw [hl] at ln
  have : tleaves T * 822700 ≤ N * 822700 := Nat.mul_le_mul_right _ hN
  nlinarith

end ZZN.T

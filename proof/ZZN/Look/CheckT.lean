/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Cut.Template
public import ZZN.Timed.TimeM

@[expose] public section

/-!
# The template check, counted

`tcheckT` is `tcheck` (`tcheckT_ret`): instantiate the template, then check the cut tree. Each node
costs one step, each kind one step, and each append to a side list its length. `tcost T` bounds the
steps (`tcheckT_time`); it depends on the shape of `T` only.
-/

namespace ZZN.T

open GridHam ZZN.Cut

def putT (s : Bool) (e : Coord × Coord) (LR : List (Coord × Coord) × List (Coord × Coord)) :
    TimeM (List (Coord × Coord) × List (Coord × Coord)) :=
  if s then do let r ← lappendT LR.2 [e]; pure (LR.1, r)
  else do let l ← lappendT LR.1 [e]; pure (l, LR.2)

theorem putT_ret (s : Bool) (e : Coord × Coord) (LR : List (Coord × Coord) × List (Coord × Coord)) :
    (putT s e LR).ret = put s e LR := by
  cases s <;> rfl

theorem putT_time (s : Bool) (e : Coord × Coord) (LR : List (Coord × Coord) × List (Coord × Coord)) :
    (putT s e LR).time ≤ LR.1.length + LR.2.length + 1 := by
  cases s <;> simp [putT, lappendT]

theorem put_len (s : Bool) (e : Coord × Coord) (LR : List (Coord × Coord) × List (Coord × Coord)) :
    (put s e LR).1.length + (put s e LR).2.length = LR.1.length + LR.2.length + 1 := by
  cases s <;> simp [put] <;> omega

def splitT (vert : Bool) (pos : ℕ) :
    List (Kind ℕ) → List (Coord × Coord) → List (Coord × Coord) × List (Coord × Coord) →
      TimeM (Option (List (Coord × Coord) × List (Coord × Coord)))
  | [], [], acc => do tick 1; pure (some acc)
  | Kind.stay s :: ks, (a, b) :: ss, acc => do
    tick 1
    let a1 ← putT s (a, b) acc
    splitT vert pos ks ss a1
  | Kind.cross s y :: ks, (a, b) :: ss, acc => do
    tick 1
    let a1 ← putT s (a, cutc vert pos s y) acc
    let a2 ← putT (!s) (cutc vert pos (!s) y, b) a1
    splitT vert pos ks ss a2
  | Kind.exc s y z :: ks, (a, b) :: ss, acc => do
    tick 1
    let a1 ← putT s (a, cutc vert pos s y) acc
    let a2 ← putT s (cutc vert pos s z, b) a1
    let a3 ← putT (!s) (cutc vert pos (!s) y, cutc vert pos (!s) z) a2
    splitT vert pos ks ss a3
  | _, _, _ => do tick 1; pure none

theorem splitT_ret (vert : Bool) (pos : ℕ) : ∀ ks ss acc,
    (splitT vert pos ks ss acc).ret = split vert pos ks ss acc
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | Kind.stay _ :: _, [], _ => rfl
  | Kind.cross _ _ :: _, [], _ => rfl
  | Kind.exc _ _ _ :: _, [], _ => rfl
  | Kind.stay s :: ks, (a, b) :: ss, acc => by
    simp [splitT, split, putT_ret, splitT_ret vert pos ks ss]
  | Kind.cross s y :: ks, (a, b) :: ss, acc => by
    simp [splitT, split, putT_ret, splitT_ret vert pos ks ss]
  | Kind.exc s y z :: ks, (a, b) :: ss, acc => by
    simp [splitT, split, putT_ret, splitT_ret vert pos ks ss]

theorem splitT_time (vert : Bool) (pos : ℕ) : ∀ ks ss acc,
    (splitT vert pos ks ss acc).time ≤
      (ks.length + 1) * (3 * (acc.1.length + acc.2.length + 3 * ks.length) + 4)
  | [], [], _ => by simp [splitT]
  | [], _ :: _, _ => by simp [splitT]
  | Kind.stay _ :: _, [], _ => by simp [splitT]; nlinarith
  | Kind.cross _ _ :: _, [], _ => by simp [splitT]; nlinarith
  | Kind.exc _ _ _ :: _, [], _ => by simp [splitT]; nlinarith
  | Kind.stay s :: ks, (a, b) :: ss, acc => by
    simp only [splitT, time_bind, time_tick, putT_ret]
    have h1 := putT_time s (a, b) acc
    have h2 := splitT_time vert pos ks ss (put s (a, b) acc)
    have e := put_len s (a, b) acc
    simp only [List.length_cons]
    rw [e] at h2
    nlinarith
  | Kind.cross s y :: ks, (a, b) :: ss, acc => by
    simp only [splitT, time_bind, time_tick, putT_ret]
    have h1 := putT_time s (a, cutc vert pos s y) acc
    have h1' := putT_time (!s) (cutc vert pos (!s) y, b) (put s (a, cutc vert pos s y) acc)
    have h2 := splitT_time vert pos ks ss
      (put (!s) (cutc vert pos (!s) y, b) (put s (a, cutc vert pos s y) acc))
    have e1 := put_len s (a, cutc vert pos s y) acc
    have e2 := put_len (!s) (cutc vert pos (!s) y, b) (put s (a, cutc vert pos s y) acc)
    simp only [List.length_cons]
    rw [e2, e1] at h2
    rw [e1] at h1'
    nlinarith
  | Kind.exc s y z :: ks, (a, b) :: ss, acc => by
    simp only [splitT, time_bind, time_tick, putT_ret]
    have h1 := putT_time s (a, cutc vert pos s y) acc
    have h1' := putT_time s (cutc vert pos s z, b) (put s (a, cutc vert pos s y) acc)
    have h1'' := putT_time (!s) (cutc vert pos (!s) y, cutc vert pos (!s) z)
      (put s (cutc vert pos s z, b) (put s (a, cutc vert pos s y) acc))
    have h2 := splitT_time vert pos ks ss
      (put (!s) (cutc vert pos (!s) y, cutc vert pos (!s) z)
        (put s (cutc vert pos s z, b) (put s (a, cutc vert pos s y) acc)))
    have e1 := put_len s (a, cutc vert pos s y) acc
    have e2 := put_len s (cutc vert pos s z, b) (put s (a, cutc vert pos s y) acc)
    have e3 := put_len (!s) (cutc vert pos (!s) y, cutc vert pos (!s) z)
      (put s (cutc vert pos s z, b) (put s (a, cutc vert pos s y) acc))
    simp only [List.length_cons]
    rw [e3, e2, e1] at h2
    rw [e2, e1] at h1''
    rw [e1] at h1'
    nlinarith

/-- The step bound of a cut tree, from its shape. -/
def tcost {α : Type} : CTree α → ℕ
  | CTree.leaf => 2
  | CTree.cut _ _ ks l r => (ks.length + 1) * (9 * ks.length + 4) + ks.length + 3 + tcost l + tcost r

def checkT : CTree ℕ → Piece → TimeM Bool
  | CTree.leaf, P => do tick 1; pure (leafOK P)
  | CTree.cut vert pos ks l r, P => do
    tick 1
    if inside vert pos P then do
      let o ← splitT vert pos ks P.segs ([], [])
      match o with
      | some (L, R) => do
        let a ← checkT l (P.lo vert pos L)
        let b ← checkT r (P.hi vert pos R)
        pure (a && b)
      | none => pure false
    else pure false

theorem checkT_ret : ∀ (T : CTree ℕ) (P : Piece), (checkT T P).ret = check T P
  | CTree.leaf, P => rfl
  | CTree.cut vert pos ks l r, P => by
    simp only [checkT, check, ret_bind]
    by_cases hin : inside vert pos P
    · simp only [hin, ↓reduceIte, ret_bind, splitT_ret, Bool.true_and]
      rcases split vert pos ks P.segs ([], []) with _ | ⟨L, R⟩
      · rfl
      · simp [checkT_ret l, checkT_ret r]
    · simp [hin]

theorem checkT_time : ∀ (T : CTree ℕ) (P : Piece), (checkT T P).time ≤ tcost T
  | CTree.leaf, P => by simp [checkT, tcost]
  | CTree.cut vert pos ks l r, P => by
    simp only [checkT, tcost, time_bind, time_tick]
    by_cases hin : inside vert pos P
    · simp only [hin, ↓reduceIte, time_bind]
      have hs := splitT_time vert pos ks P.segs ([], [])
      simp only [List.length_nil, Nat.zero_add] at hs
      rw [splitT_ret]
      rcases split vert pos ks P.segs ([], []) with _ | ⟨L, R⟩
      · simp only [time_pure]; nlinarith
      · simp only [time_bind, time_pure]
        have := checkT_time l (P.lo vert pos L)
        have := checkT_time r (P.hi vert pos R)
        nlinarith
    · simp only [hin, Bool.false_eq_true, ↓reduceIte, time_pure]; omega

def instT {α : Type} (fR fC : TPos → α) : CTree TPos → TimeM (CTree α)
  | CTree.leaf => do tick 1; pure CTree.leaf
  | CTree.cut vert pos ks l r => do
    tick 1
    let ks' ← lmapT (fun k => pure (instK (if vert then fR else fC) k)) ks
    let l' ← instT fR fC l
    let r' ← instT fR fC r
    pure (CTree.cut vert (if vert then fC pos else fR pos) ks' l' r')

theorem instT_ret {α : Type} (fR fC : TPos → α) : ∀ T, (instT fR fC T).ret = inst fR fC T
  | CTree.leaf => rfl
  | CTree.cut vert pos ks l r => by
    simp [instT, inst, lmapT, instT_ret fR fC l, instT_ret fR fC r]

theorem instT_time {α : Type} (fR fC : TPos → α) : ∀ T, (instT fR fC T).time ≤ tcost T
  | CTree.leaf => by simp [instT, tcost]
  | CTree.cut vert pos ks l r => by
    simp only [instT, tcost, time_bind, time_tick, time_pure]
    have h1 := lmapT_time_le (fun k => (pure (instK (if vert then fR else fC) k) : TimeM (Kind α)))
      ks 0 (fun _ _ => le_rfl)
    have := instT_time fR fC l
    have := instT_time fR fC r
    nlinarith

theorem tcost_inst {α : Type} (fR fC : TPos → α) : ∀ T, tcost (inst fR fC T) = tcost T
  | CTree.leaf => rfl
  | CTree.cut vert pos ks l r => by
    simp [inst, tcost, tcost_inst fR fC l, tcost_inst fR fC r]

/-- The number of leaves. -/
def tleaves {α : Type} : CTree α → ℕ
  | CTree.leaf => 1
  | CTree.cut _ _ _ l r => tleaves l + tleaves r

theorem tleaves_inst {α : Type} (fR fC : TPos → α) : ∀ T, tleaves (inst fR fC T) = tleaves T
  | CTree.leaf => rfl
  | CTree.cut vert pos ks l r => by simp [inst, tleaves, tleaves_inst fR fC l, tleaves_inst fR fC r]

theorem tleaves_pos {α : Type} : ∀ T : CTree α, 1 ≤ tleaves T
  | CTree.leaf => le_rfl
  | CTree.cut _ _ _ l _ => by have := tleaves_pos l; simp only [tleaves]; omega

def tcheckT (T : CTree TPos) (I : Inst) : TimeM Bool := do
  let T' ← instT (posN I.s0.1 I.t0.1 I.s1.1 I.t1.1 I.w) (posN I.s0.2 I.t0.2 I.s1.2 I.t1.2 I.h) T
  checkT T' (rootPiece I)

theorem tcheckT_ret (T : CTree TPos) (I : Inst) : (tcheckT T I).ret = tcheck T I := by
  simp [tcheckT, tcheck, instT_ret, checkT_ret]

theorem tcheckT_time (T : CTree TPos) (I : Inst) : (tcheckT T I).time ≤ 2 * tcost T := by
  simp only [tcheckT, time_bind, instT_ret]
  have := instT_time (posN I.s0.1 I.t0.1 I.s1.1 I.t1.1 I.w) (posN I.s0.2 I.t0.2 I.s1.2 I.t1.2 I.h) T
  have := checkT_time (inst (posN I.s0.1 I.t0.1 I.s1.1 I.t1.1 I.w)
    (posN I.s0.2 I.t0.2 I.s1.2 I.t1.2 I.h) T) (rootPiece I)
  rw [tcost_inst] at this
  omega

end ZZN.T

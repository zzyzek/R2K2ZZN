-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Cut.Cover
import ZZN.Cut.LaneV

/-!
# Concrete cut trees and their checker

A piece is a rectangle (origin `(ox, oy)`, size `pw × ph`, absolute coordinates) with a list of
endpoint pairs. A cut node splits it by the line before row `pos` (`vert = false`, first
coordinate) or column `pos` (`vert = true`, second coordinate), and gives each endpoint pair a
kind and a side `s` (`false` = before the line) for its first end:

* `stay s`: both ends on side `s`;
* `cross s y`: the second end on the other side, the path crossing at cell `y` along the cut;
* `exc s y z`: both ends on side `s`, the path leaving at `y` and returning at `z`; the other side
  gets the pair of crossing cells.

Sides are data, not tests: a wrong side puts an endpoint into a piece whose leaf test
(`leafOK`, which checks region membership) fails, so soundness needs no side check.

New pairs are appended to each side in order (the order of `split/chain3.c`). A leaf holds one pair:
a Hamiltonian path of its rectangle (IPS), or a single cell.

`check_sound`: `check T P = true → RCover P.region P.segs`.
-/

namespace ZZN.Cut

open GridHam

/-- The kind of an endpoint pair at a cut, with the side (`false` = before the line) of its
first end. -/
inductive Kind (α : Type) where
  | stay (s : Bool)
  | cross (s : Bool) (y : α)
  | exc (s : Bool) (y z : α)

/-- A cut tree with positions in `α` (`ℕ` for one instance; lane vectors for many). -/
inductive CTree (α : Type) where
  | leaf
  | cut (vert : Bool) (pos : α) (ks : List (Kind α)) (l r : CTree α)

def Kind.map {α β : Type} (f : α → β) : Kind α → Kind β
  | stay s => stay s
  | cross s y => cross s (f y)
  | exc s y z => exc s (f y) (f z)

def CTree.map {α β : Type} (f : α → β) : CTree α → CTree β
  | leaf => leaf
  | cut vert pos ks l r => cut vert (f pos) (ks.map (Kind.map f)) (l.map f) (r.map f)

structure Piece where
  ox : ℕ
  oy : ℕ
  pw : ℕ
  ph : ℕ
  segs : List (Coord × Coord)

def Piece.region (P : Piece) (v : Coord) : Prop :=
  P.ox ≤ v.1 ∧ v.1 < P.ox + P.pw ∧ P.oy ≤ v.2 ∧ v.2 < P.oy + P.ph

instance (P : Piece) : DecidablePred P.region := fun v => by unfold Piece.region; infer_instance

/-- The crossing cell at position `y` along the cut, on side `s`. -/
def cutc (vert : Bool) (pos : ℕ) (s : Bool) (y : ℕ) : Coord :=
  let x := if s then pos else pos - 1
  if vert then (y, x) else (x, y)

/-- Append a pair to side `s`. -/
def put (s : Bool) (e : Coord × Coord) (LR : List (Coord × Coord) × List (Coord × Coord)) :
    List (Coord × Coord) × List (Coord × Coord) :=
  if s then (LR.1, LR.2 ++ [e]) else (LR.1 ++ [e], LR.2)

def split (vert : Bool) (pos : ℕ) :
    List (Kind ℕ) → List (Coord × Coord) → List (Coord × Coord) × List (Coord × Coord) →
      Option (List (Coord × Coord) × List (Coord × Coord))
  | [], [], acc => some acc
  | Kind.stay s :: ks, (a, b) :: ss, acc => split vert pos ks ss (put s (a, b) acc)
  | Kind.cross s y :: ks, (a, b) :: ss, acc =>
    split vert pos ks ss (put (!s) (cutc vert pos (!s) y, b) (put s (a, cutc vert pos s y) acc))
  | Kind.exc s y z :: ks, (a, b) :: ss, acc =>
    split vert pos ks ss
      (put (!s) (cutc vert pos (!s) y, cutc vert pos (!s) z)
        (put s (cutc vert pos s z, b) (put s (a, cutc vert pos s y) acc)))
  | _, _, _ => none

/-- The two sub-rectangles of a cut. -/
def Piece.lo (P : Piece) (vert : Bool) (pos : ℕ) (L : List (Coord × Coord)) : Piece :=
  if vert then ⟨P.ox, P.oy, P.pw, pos - P.oy, L⟩ else ⟨P.ox, P.oy, pos - P.ox, P.ph, L⟩

def Piece.hi (P : Piece) (vert : Bool) (pos : ℕ) (R : List (Coord × Coord)) : Piece :=
  if vert then ⟨P.ox, pos, P.pw, P.oy + P.ph - pos, R⟩ else ⟨pos, P.oy, P.ox + P.pw - pos, P.ph, R⟩

def inside (vert : Bool) (pos : ℕ) (P : Piece) : Bool :=
  if vert then decide (P.oy < pos) && decide (pos < P.oy + P.ph)
  else decide (P.ox < pos) && decide (pos < P.ox + P.pw)

def Piece.regionB (P : Piece) (v : Coord) : Bool :=
  (decide (P.ox ≤ v.1) && decide (v.1 < P.ox + P.pw)) && (decide (P.oy ≤ v.2) && decide (v.2 < P.oy + P.ph))

theorem Piece.regionB_iff (P : Piece) (v : Coord) : P.regionB v = true ↔ P.region v := by
  simp [Piece.regionB, Piece.region, and_assoc]

def eqC (a b : Coord) : Bool := decide (a.1 = b.1) && decide (a.2 = b.2)

theorem eqC_iff (a b : Coord) : eqC a b = true ↔ a = b := by
  simp [eqC, Prod.ext_iff]

/-- A leaf: one pair, either one cell or an IPS-acceptable rectangle (`Lane.accB`). -/
def leafOK (P : Piece) : Bool :=
  match P.segs with
  | [(a, b)] =>
    if eqC a b then (decide (P.pw = 1) && decide (P.ph = 1)) && eqC a (P.ox, P.oy)
    else (P.regionB a && P.regionB b) &&
      Lane.accB P.pw P.ph (a.1 - P.ox, a.2 - P.oy) (b.1 - P.ox, b.2 - P.oy)
  | _ => false

def check : CTree ℕ → Piece → Bool
  | CTree.leaf, P => leafOK P
  | CTree.cut vert pos ks l r, P =>
    inside vert pos P &&
      match split vert pos ks P.segs ([], []) with
      | some (L, R) => check l (P.lo vert pos L) && check r (P.hi vert pos R)
      | none => false

/-! ### Soundness -/

theorem cutc_adj (vert : Bool) (pos y : ℕ) (hp : 1 ≤ pos) (s : Bool) :
    Adjacent (cutc vert pos s y) (cutc vert pos (!s) y) := by
  cases vert <;> cases s <;> simp [cutc, Adjacent] <;> omega

theorem put_ms (s : Bool) (e : Coord × Coord) (LR : List (Coord × Coord) × List (Coord × Coord)) :
    ((put s e LR).1 : Multiset (Coord × Coord)) + (put s e LR).2 =
      e ::ₘ ((LR.1 : Multiset (Coord × Coord)) + LR.2) := by
  rw [← Multiset.singleton_add]
  cases s <;> simp only [put, Bool.false_eq_true, ite_false, ite_true, ← Multiset.coe_add,
    Multiset.coe_singleton] <;> abel

theorem cons_ms (e : Coord × Coord) (X : Multiset (Coord × Coord)) : e ::ₘ X = {e} + X :=
  (Multiset.singleton_add e X).symm

/-- The split invariant: covers of the two sides with the final lists give a cover with the
accumulated lists and the unprocessed pairs. -/
theorem split_sound {A : Coord → Prop} (vert : Bool) (pos : ℕ) (hp : 1 ≤ pos) :
    ∀ (ks : List (Kind ℕ)) (ss : List (Coord × Coord)) (acc : List (Coord × Coord) × List (Coord × Coord))
      (L R : List (Coord × Coord)), split vert pos ks ss acc = some (L, R) →
      RCover A ((L : Multiset (Coord × Coord)) + R) →
      RCover A ((acc.1 : Multiset (Coord × Coord)) + acc.2 + ss) := by
  intro ks
  induction ks with
  | nil =>
    intro ss acc L R h hc
    cases ss with
    | nil =>
      simp only [split, Option.some.injEq] at h
      subst h
      simpa using hc
    | cons e ss => simp [split] at h
  | cons k ks ih =>
    intro ss acc L R h hc
    cases ss with
    | nil => cases k <;> simp [split] at h
    | cons e ss =>
      obtain ⟨a, b⟩ := e
      cases k with
      | stay sa =>
        simp only [split] at h
        have := ih ss _ L R h hc
        rw [put_ms] at this
        have e : (a, b) ::ₘ ((acc.1 : Multiset (Coord × Coord)) + acc.2) + ss =
            (acc.1 : Multiset (Coord × Coord)) + acc.2 + ((a, b) :: ss : List _) := by
          rw [← Multiset.cons_coe, cons_ms, cons_ms]; abel
        rwa [e] at this
      | cross sa y =>
        simp only [split] at h
        have := ih ss _ L R h hc
        rw [put_ms, put_ms] at this
        have e : (cutc vert pos (!sa) y, b) ::ₘ (a, cutc vert pos sa y) ::ₘ
            ((acc.1 : Multiset (Coord × Coord)) + acc.2) + ss =
            (a, cutc vert pos sa y) ::ₘ (cutc vert pos (!sa) y, b) ::ₘ
            ((acc.1 : Multiset (Coord × Coord)) + acc.2 + ss) := by
          simp only [cons_ms]; abel
        rw [e] at this
        have j := this.join (cutc_adj vert pos y hp _)
        have e2 : (a, b) ::ₘ ((acc.1 : Multiset (Coord × Coord)) + acc.2 + ss) =
            (acc.1 : Multiset (Coord × Coord)) + acc.2 + ((a, b) :: ss : List _) := by
          rw [← Multiset.cons_coe, cons_ms, cons_ms]; abel
        rwa [e2] at j
      | exc sa y z =>
        simp only [split] at h
        have := ih ss _ L R h hc
        rw [put_ms, put_ms, put_ms] at this
        have e : (cutc vert pos (!sa) y, cutc vert pos (!sa) z) ::ₘ (cutc vert pos sa z, b) ::ₘ
            (a, cutc vert pos sa y) ::ₘ ((acc.1 : Multiset (Coord × Coord)) + acc.2) + ss =
            (a, cutc vert pos sa y) ::ₘ (cutc vert pos (!sa) y, cutc vert pos (!sa) z) ::ₘ
            (cutc vert pos sa z, b) ::ₘ ((acc.1 : Multiset (Coord × Coord)) + acc.2 + ss) := by
          simp only [cons_ms]; abel
        rw [e] at this
        have j1 := this.join (cutc_adj vert pos y hp sa)
        have j2 := j1.join (by simpa using cutc_adj vert pos z hp (!sa))
        have e2 : (a, b) ::ₘ ((acc.1 : Multiset (Coord × Coord)) + acc.2 + ss) =
            (acc.1 : Multiset (Coord × Coord)) + acc.2 + ((a, b) :: ss : List _) := by
          rw [← Multiset.cons_coe, cons_ms, cons_ms]; abel
        rwa [e2] at j2

theorem region_split (P : Piece) (vert : Bool) (pos : ℕ) (hin : inside vert pos P = true)
    (L R : List (Coord × Coord)) :
    (∀ v, P.region v ↔ ((P.lo vert pos L).region v ∨ (P.hi vert pos R).region v)) ∧
    (∀ v, (P.lo vert pos L).region v → ¬ (P.hi vert pos R).region v) := by
  cases vert <;> simp only [inside, Bool.false_eq_true, ite_false, ite_true, Bool.and_eq_true,
    decide_eq_true_eq] at hin <;> obtain ⟨h1, h2⟩ := hin <;>
    simp only [Piece.lo, Piece.hi, Piece.region, Bool.false_eq_true, ite_false, ite_true] <;>
    refine ⟨fun v => ?_, fun v => ?_⟩ <;> omega

theorem lo_segs (P : Piece) (vert : Bool) (pos : ℕ) (L : List (Coord × Coord)) :
    (P.lo vert pos L).segs = L := by cases vert <;> rfl

theorem hi_segs (P : Piece) (vert : Bool) (pos : ℕ) (R : List (Coord × Coord)) :
    (P.hi vert pos R).segs = R := by cases vert <;> rfl

theorem leaf_sound (P : Piece) (h : leafOK P = true) : RCover P.region P.segs := by
  obtain ⟨ox, oy, pw, ph, segs⟩ := P
  match segs, h with
  | [(a, b)], h =>
    show RCover _ ({(a, b)} : Multiset _)
    simp only [leafOK] at h
    split_ifs at h with hab
    · rw [eqC_iff] at hab
      simp only [Bool.and_eq_true, decide_eq_true_eq, eqC_iff] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      subst hab
      refine (RCover.single a).congr fun v => ?_
      simp only [Piece.region, h1, h2, h3]
      subst h3
      constructor
      · rintro rfl; omega
      · intro hv; ext <;> omega
    · rw [eqC_iff] at hab
      simp only [Bool.and_eq_true, Piece.regionB_iff, Lane.accB_eq, decide_eq_true_eq] at h
      obtain ⟨⟨ha, hb⟩, hacc⟩ := h
      unfold Piece.region at ha hb
      dsimp only at ha hb hacc ⊢
      have hc := RCover.ips (w := pw) (h := ph) (s := (a.1 - ox, a.2 - oy))
        (t := (b.1 - ox, b.2 - oy)) ⟨by simp; omega, by simp; omega⟩ ⟨by simp; omega, by simp; omega⟩
        (by intro e; apply hab; simp only [Prod.mk.injEq] at e; ext <;> omega) hacc
      have hm := hc.map (fun v => (v.1 + ox, v.2 + oy))
        (fun v w _ _ e => by simp only [Prod.mk.injEq] at e; ext <;> omega)
        (fun v w _ _ hvw => by unfold Adjacent at hvw ⊢; simp only; omega)
      simp only [Multiset.map_singleton] at hm
      have ea : (a.1 - ox + ox, a.2 - oy + oy) = a := by ext <;> simp <;> omega
      have eb : (b.1 - ox + ox, b.2 - oy + oy) = b := by ext <;> simp <;> omega
      rw [ea, eb] at hm
      refine hm.congr fun v => ?_
      simp only [Piece.region, InBounds]
      constructor
      · rintro ⟨w, ⟨h1, h2⟩, rfl⟩; simp only; omega
      · intro hv; exact ⟨(v.1 - ox, v.2 - oy), ⟨by simp; omega, by simp; omega⟩, by ext <;> simp <;> omega⟩

/-- **Soundness of the checker.** -/
theorem check_sound : ∀ (T : CTree ℕ) (P : Piece), check T P = true → RCover P.region P.segs
  | CTree.leaf, P, h => leaf_sound P h
  | CTree.cut vert pos ks l r, P, h => by
    simp only [check, Bool.and_eq_true] at h
    obtain ⟨hin, h⟩ := h
    match hsp : split vert pos ks P.segs ([], []), h with
    | some (L, R), h =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨hl, hr⟩ := h
      have cl := check_sound l _ hl
      have cr := check_sound r _ hr
      obtain ⟨hU, hD⟩ := region_split P vert pos hin L R
      have hu := cl.union cr hD
      have hp : 1 ≤ pos := by
        cases vert <;> simp only [inside, Bool.false_eq_true, ite_false, ite_true, Bool.and_eq_true,
          decide_eq_true_eq] at hin <;> omega
      rw [lo_segs, hi_segs] at hu
      have := split_sound (A := fun v => (P.lo vert pos L).region v ∨ (P.hi vert pos R).region v)
        vert pos hp ks P.segs ([], []) L R hsp hu
      simp only [Multiset.coe_nil, zero_add] at this
      exact this.congr fun v => (hU v).symm
    | none, h => simp at h

/-- The root piece of an instance. -/
def rootPiece (I : Inst) : Piece := ⟨0, 0, I.w, I.h, [(I.s0, I.t0), (I.s1, I.t1)]⟩

/-- A checked cut tree solves the instance. -/
theorem solvable_of_check {I : Inst} (T : CTree ℕ) (h : check T (rootPiece I) = true) : Solvable I := by
  have hc := check_sound T _ h
  refine RCover.solvable (hc.congr fun v => ?_)
  simp only [rootPiece, Piece.region, InBounds]
  omega

end ZZN.Cut

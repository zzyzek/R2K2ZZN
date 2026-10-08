-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Finite

/-!
# A faster move search for the boxes where every cut leaves thin pieces

`moveB2` searches one move type at a time, only the label choices each type needs, and each
candidate only at the width of its widest thin piece, solving the narrower piece first. Boxes may
use either check (`finite_of_checkC`).
-/

namespace ZZN

open GridHam

/-- The thin width of a two-path piece (0 if not thin). -/
def tw (w h : ℕ) : ℕ := if w ≤ 10 ∨ h ≤ 10 then min w h else 0

/-- Both pieces, the narrower first. -/
def bothB (p w : ℕ) (L R : Bool) : Bool := if p ≤ w - p then L && R else R && L

theorem bothB_true {p w : ℕ} {L R : Bool} (h : bothB p w L R = true) : L = true ∧ R = true := by
  unfold bothB at h
  split at h <;> simp only [Bool.and_eq_true] at h
  · exact h
  · exact ⟨h.2, h.1⟩

/-- One move type at a time (0 strip, 1 same, 2 one/three, 3 cross, 4 excursion), only for
candidates whose widest thin piece has width exactly `m`. -/
def canonT (t m : ℕ) (I : Inst) : Bool :=
  (List.range I.w).any fun p => decide (0 < p) &&
    match t with
    | 0 =>
      decide (I.s0.1 < p) && decide (I.t0.1 < p) && decide (I.s1.1 < p) && decide (I.t1.1 < p) &&
        decide (2 ≤ I.w - p) && decide (((I.w - p) * I.h) % 2 = 0) && decide (5 ≤ I.h) &&
        decide (tw p I.h = m) && pieceB m ⟨p, I.h, I.s0, I.t0, I.s1, I.t1⟩
    | 1 =>
      decide (m = 0) && decide (I.s0.1 < p) && decide (I.t0.1 < p) && decide (p ≤ I.s1.1) &&
        decide (p ≤ I.t1.1) && oneB p I.h I.s0 I.t0 &&
        oneB (I.w - p) I.h (I.s1.1 - p, I.s1.2) (I.t1.1 - p, I.t1.2)
    | 2 =>
      decide (I.s0.1 < p) && decide (p ≤ I.t0.1) && decide (p ≤ I.s1.1) && decide (p ≤ I.t1.1) &&
        decide (tw (I.w - p) I.h = m) &&
        (List.range I.h).any fun y => oneB p I.h I.s0 (p - 1, y) &&
          pieceB m ⟨I.w - p, I.h, (0, y), unX p I.t0, unX p I.s1, unX p I.t1⟩
    | 3 =>
      decide (I.s0.1 < p) && decide (I.s1.1 < p) && decide (p ≤ I.t0.1) && decide (p ≤ I.t1.1) &&
        decide (max (tw p I.h) (tw (I.w - p) I.h) = m) &&
        (List.range I.h).any fun y0 => (List.range I.h).any fun y1 =>
          bothB p I.w (pieceB m ⟨p, I.h, I.s0, (p - 1, y0), I.s1, (p - 1, y1)⟩)
            (pieceB m ⟨I.w - p, I.h, (0, y0), unX p I.t0, (0, y1), unX p I.t1⟩)
    | _ =>
      decide (I.s0.1 < p) && decide (I.t0.1 < p) && decide (p ≤ I.s1.1) && decide (p ≤ I.t1.1) &&
        decide (max (tw p I.h) (tw (I.w - p) I.h) = m) &&
        (List.range I.h).any fun ya => (List.range I.h).any fun yb =>
          bothB p I.w (pieceB m ⟨p, I.h, I.s0, (p - 1, ya), (p - 1, yb), I.t0⟩)
            (pieceB m ⟨I.w - p, I.h, unX p I.s1, unX p I.t1, (0, ya), (0, yb)⟩)

theorem canonT_sound {t m : ℕ} {I : Inst} (h : canonT t m I = true) : CanonMove I := by
  unfold canonT at h
  obtain ⟨p, hp, h⟩ := List.any_eq_true.mp h
  rw [List.mem_range] at hp
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hp0, h⟩ := h
  refine ⟨p, hp0, hp, ?_⟩
  match t, h with
  | 0, h =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, -⟩, a8⟩ := h
    exact Or.inl ⟨pieceB_sound a8, a5, a6, a7, a1, a2, a3, a4⟩
  | 1, h =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨-, a1⟩, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a1, a2, a3, a4, oneB_sound a5, oneB_sound a6⟩)))
  | 2, h =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range] at h
    obtain ⟨⟨⟨⟨⟨-, a2⟩, a3⟩, a4⟩, -⟩, y, hy, b1, b2⟩ := h
    exact Or.inr (Or.inl ⟨y, hy, oneB_sound b1, pieceB_sound b2, a2, a3, a4⟩)
  | 3, h =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range] at h
    obtain ⟨⟨⟨⟨⟨-, -⟩, a3⟩, a4⟩, -⟩, y0, hy0, y1, hy1, hb⟩ := h
    obtain ⟨b1, b2⟩ := bothB_true hb
    exact Or.inr (Or.inr (Or.inl ⟨y0, y1, hy0, hy1, pieceB_sound b1, pieceB_sound b2, a3, a4⟩))
  | t + 4, h =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range] at h
    obtain ⟨⟨⟨⟨⟨-, -⟩, a3⟩, a4⟩, -⟩, ya, hya, yb, hyb, hb⟩ := h
    obtain ⟨b1, b2⟩ := bothB_true hb
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ya, yb, hya, hyb, pieceB_sound b1, pieceB_sound b2, a3, a4⟩)))

/-- The label choices each move type needs (the others repeat the same pieces). -/
def labsFor : ℕ → List (Bool × Bool × Bool)
  | 0 => [(false, false, false)]
  | 1 => [(false, false, false), (false, false, true)]
  | 2 => [(false, false, false), (true, false, false), (false, false, true), (false, true, true)]
  | 3 => [(false, false, false), (true, false, false), (false, true, false), (true, true, false)]
  | _ => [(false, false, false), (false, false, true)]

/-- The (move type, symmetry) pairs searched. -/
def typeSyms : List (ℕ × Sym) :=
  (List.range 5).flatMap fun t =>
    ([false, true].flatMap fun tr => [false, true].flatMap fun rx => [false, true].map fun ry =>
      (tr, rx, ry)).flatMap fun g =>
      (labsFor t).map fun l => (t, ⟨g.1, g.2.1, g.2.2, l.1, l.2.1, l.2.2⟩)

/-- Search, by the width of the widest thin piece: `0` (none), then `1, …, 10`. -/
def moveB2 (I : Inst) : Bool :=
  (List.range 11).any fun m => typeSyms.any fun tσ => canonT tσ.1 m (tσ.2.apply I)

theorem moveB2_sound {I : Inst} (h : moveB2 I = true) : MoveOK I := by
  unfold moveB2 at h
  obtain ⟨m, -, h⟩ := List.any_eq_true.mp h
  obtain ⟨tσ, -, h⟩ := List.any_eq_true.mp h
  exact ⟨tσ.2, canonT_sound h⟩

def checkInst2 (J : Inst) : Bool :=
  !(quickB J) || !(isMinB J) || !(decide J.WellFormed) || !(passImgB J) || moveB2 J || solveCheck J

/-- A box part, with a chosen instance check. -/
def checkBoxC (ck : Inst → Bool) (w h a : ℕ) : Bool :=
  let Th := tuples h
  (tuplesA w a).all fun xs => Th.all fun ys => ck (mkInst w h xs ys)

theorem checkBoxC_checkInst (w h a : ℕ) : checkBoxC checkInst w h a = checkBoxA w h a := rfl

theorem hck_checkInst {J : Inst} (h : checkInst J = true) (q1 : quickB J = true) (q2 : isMinB J = true)
    (hw : J.WellFormed) (q3 : passImgB J = true) : moveB J = true ∨ moveB2 J = true ∨ solveCheck J = true := by
  unfold checkInst at h
  simp only [q1, q2, q3, decide_eq_true hw, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

theorem hck_checkInst2 {J : Inst} (h : checkInst2 J = true) (q1 : quickB J = true) (q2 : isMinB J = true)
    (hw : J.WellFormed) (q3 : passImgB J = true) : moveB J = true ∨ moveB2 J = true ∨ solveCheck J = true := by
  unfold checkInst2 at h
  simp only [q1, q2, q3, decide_eq_true hw, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem finite_of_checkC (ck : ℕ → ℕ → Inst → Bool)
    (hck : ∀ w h J, ck w h J = true → quickB J = true → isMinB J = true → J.WellFormed →
      passImgB J = true → moveB J = true ∨ moveB2 J = true ∨ solveCheck J = true)
    (hc : ∀ w h a, 11 ≤ w → w ≤ 22 → 11 ≤ h → h ≤ 22 → a < w → checkBoxC (ck w h) w h a = true) :
    FactsFinite := by
  refine ⟨fun I hI hw hh hP hR => ?_⟩
  have hwf := hI.2.2
  -- the instance is in the search region
  have hSI : SB I = true := by
    unfold SB
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨hI.1, hw, hI.2.1, hh⟩, axB_of_noRed (fun h => hR (Or.inl h))⟩, ?_⟩
    exact axB_of_noRed (I := I.transpose) (fun h => hR (Or.inr (Or.inl h)))
  -- the representative: the image with the least key
  obtain ⟨σ0, -, hmin⟩ := exists_min (fun σ => key (σ.apply I)) allSym (by simp [allSym])
  set J := σ0.apply I with hJ
  have hJS : SB J = true := by rw [hJ, SB_apply σ0 hwf]; exact hSI
  have hJD : InDom J := inDom_apply σ0 hwf hSI
  have hJwf := hJD.2.2
  have hmin' : ∀ σ : Sym, key J ≤ key (σ.apply J) := by
    intro σ
    rw [hJ, comp_apply σ σ0 hwf]
    exact hmin _ (mem_allSym _)
  -- the box check covers it
  have hJS' := hJS
  unfold SB at hJS'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hJS'
  obtain ⟨⟨⟨w1, w2, h1, h2⟩, ax⟩, ay⟩ := hJS'
  have hbox := hc J.w J.h J.s0.1 w1 w2 h1 h2 hJwf.1.1
  unfold checkBoxC at hbox
  dsimp only at hbox
  have bx := bounds_x hJwf
  have by_ : ∀ y ∈ ysOf J, y < J.h := bounds_x (I := J.transpose) (wf_transpose hJwf)
  simp only [xsOf, ysOf, Inst.ends, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] at bx by_
  have mx := mem_tuplesA (a := J.s0.1) bx.2.1 bx.2.2.1 bx.2.2.2 ax
  have my := mem_tuples by_.1 by_.2.1 by_.2.2.1 by_.2.2.2 ay
  have hci := List.all_eq_true.mp (List.all_eq_true.mp hbox _ mx) _ my
  have eJ : mkInst J.w J.h [J.s0.1, J.t0.1, J.s1.1, J.t1.1] [J.s0.2, J.t0.2, J.s1.2, J.t1.2] = J := by
    unfold mkInst; rfl
  rw [eJ] at hci
  -- the conditions hold
  have q1 : quickB J = true := by
    unfold quickB
    rw [List.all_eq_true]
    intro σ _
    exact decide_eq_true (hmin' σ)
  have q2 : isMinB J = true := by
    unfold isMinB
    rw [List.all_eq_true]
    intro σ _
    exact decide_eq_true (hmin' σ)
  have q3 : passImgB J = true := by
    obtain ⟨ρ, hρ⟩ := inv_exists σ0
    have hPJ : Passes (ρ.apply J) := by rw [hJ, hρ I hwf]; exact hP
    unfold passImgB
    rcases passes_refl_of_image hJD ρ hPJ with h | h | h | h <;> simp [h]
  rcases hck J.w J.h J hci q1 q2 hJwf q3 with hm | hm | hs
  · exact Or.inl (MoveOK.of_apply hwf (moveB_sound hm))
  · exact Or.inl (MoveOK.of_apply hwf (moveB2_sound hm))
  · exact Or.inr (Sym.solvable hwf (solvable_of_solveCheck hs))

/-- The check used for every box. -/
def ckBox (_w _h : ℕ) : Inst → Bool := checkInst2

theorem hck_ckBox (w h : ℕ) (J : Inst) (h1 : ckBox w h J = true) (q1 : quickB J = true)
    (q2 : isMinB J = true) (hw : J.WellFormed) (q3 : passImgB J = true) :
    moveB J = true ∨ moveB2 J = true ∨ solveCheck J = true := by
  exact hck_checkInst2 h1 q1 q2 hw q3

end ZZN

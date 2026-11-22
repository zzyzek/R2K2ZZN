/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Constr.EdgeBlock
public import ZZN.Constr.Lift
public import ZZN.Orbit

@[expose] public section

/-!
# Pulling a solution back through a symmetry

`unSym σ J s`: from a solution `s` of `σ.apply J`, a solution of `J` (`unSym_sol`). The label part
is undone by swapping and reversing the paths, the geometric part by mapping the cells.
-/

namespace ZZN

open GridHam

theorem IsSolution.of_swapColors {I : Inst} {p q : List Coord} (h : IsSolution I.swapColors p q) :
    IsSolution I q p := by
  obtain ⟨hp, hq, hd, hc⟩ := h
  exact ⟨hq, hp, fun v hv hv' => hd v hv' hv, fun v hv => (hc v hv).symm⟩

theorem IsSolution.of_rev0 {I : Inst} {p q : List Coord} (h : IsSolution I.rev0 p q) :
    IsSolution I p.reverse q := by
  obtain ⟨hp, hq, hd, hc⟩ := h
  refine ⟨hp.reverse, hq, fun v hv => hd v (List.mem_reverse.mp hv), fun v hv => ?_⟩
  rcases hc v hv with h | h
  · exact Or.inl (List.mem_reverse.mpr h)
  · exact Or.inr h

theorem IsSolution.of_rev1 {I : Inst} {p q : List Coord} (h : IsSolution I.rev1 p q) :
    IsSolution I p q.reverse := by
  obtain ⟨hp, hq, hd, hc⟩ := h
  refine ⟨hp, hq.reverse, fun v hv hv' => hd v hv (List.mem_reverse.mp hv'), fun v hv => ?_⟩
  rcases hc v hv with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_reverse.mpr h)

theorem IsSolution.of_reflectX {I : Inst} (hI : I.WellFormed) {p q : List Coord}
    (h : IsSolution I.reflectX p q) : IsSolution I (p.map (reflX I.w)) (q.map (reflX I.w)) := by
  obtain ⟨b0, b1, b2, b3, -⟩ := hI
  have rr : ∀ v : Coord, v.1 < I.w → reflX I.w (reflX I.w v) = v := fun v hv => by
    obtain ⟨a, b⟩ := v
    simp only [reflX] at hv ⊢
    exact Prod.ext (by simp only; omega) rfl
  exact IsSolution.reflect (I := I.reflectX) (J := I) rfl rfl (rr _ b0.1) (rr _ b1.1) (rr _ b2.1)
    (rr _ b3.1) h

theorem sol_ifSw (b : Bool) {I : Inst} {s : List Coord × List Coord}
    (h : IsSolution (if b then I.swapColors else I) s.1 s.2) :
    IsSolution I (if b then (s.2, s.1) else s).1 (if b then (s.2, s.1) else s).2 := by
  cases b
  · exact h
  · exact h.of_swapColors

theorem sol_ifR1 (b : Bool) {I : Inst} {s : List Coord × List Coord}
    (h : IsSolution (if b then I.rev1 else I) s.1 s.2) :
    IsSolution I (if b then (s.1, s.2.reverse) else s).1 (if b then (s.1, s.2.reverse) else s).2 := by
  cases b
  · exact h
  · exact h.of_rev1

theorem sol_ifR0 (b : Bool) {I : Inst} {s : List Coord × List Coord}
    (h : IsSolution (if b then I.rev0 else I) s.1 s.2) :
    IsSolution I (if b then (s.1.reverse, s.2) else s).1 (if b then (s.1.reverse, s.2) else s).2 := by
  cases b
  · exact h
  · exact h.of_rev0

/-- Undo the label part. -/
def unLab (σ : Sym) (s : List Coord × List Coord) : List Coord × List Coord :=
  let s1 := if σ.sw then (s.2, s.1) else s
  let s2 := if σ.r1 then (s1.1, s1.2.reverse) else s1
  if σ.r0 then (s2.1.reverse, s2.2) else s2

theorem unLab_sol (σ : Sym) (G : Inst) {s : List Coord × List Coord}
    (h : IsSolution (σ.lab G) s.1 s.2) : IsSolution G (unLab σ s).1 (unLab σ s).2 :=
  sol_ifR0 σ.r0 (sol_ifR1 σ.r1 (sol_ifSw σ.sw h))

theorem sol_ifTr (b : Bool) {I : Inst} {s : List Coord × List Coord}
    (h : IsSolution (if b then I.transpose else I) s.1 s.2) :
    IsSolution I (if b then (s.1.map Prod.swap, s.2.map Prod.swap) else s).1
      (if b then (s.1.map Prod.swap, s.2.map Prod.swap) else s).2 := by
  cases b
  · exact h
  · exact h.of_transpose

theorem sol_ifRx (b : Bool) {I : Inst} (hI : I.WellFormed) {s : List Coord × List Coord}
    (h : IsSolution (if b then I.reflectX else I) s.1 s.2) :
    IsSolution I (if b then (s.1.map (reflX I.w), s.2.map (reflX I.w)) else s).1
      (if b then (s.1.map (reflX I.w), s.2.map (reflX I.w)) else s).2 := by
  cases b
  · exact h
  · exact h.of_reflectX hI

/-- Undo `reflectY = transpose ∘ reflectX ∘ transpose` on the paths. -/
def unRy (hh : ℕ) (p : List Coord) : List Coord := ((p.map Prod.swap).map (reflX hh)).map Prod.swap

theorem sol_ifRy (b : Bool) {I : Inst} (hI : I.WellFormed) {s : List Coord × List Coord}
    (h : IsSolution (if b then I.reflectY else I) s.1 s.2) :
    IsSolution I (if b then (unRy I.h s.1, unRy I.h s.2) else s).1
      (if b then (unRy I.h s.1, unRy I.h s.2) else s).2 := by
  cases b
  · exact h
  · have h1 := IsSolution.of_transpose (I := I.transpose.reflectX) h
    have h2 := h1.of_reflectX (wf_transpose hI)
    exact h2.of_transpose

/-- Undo the geometric part. -/
def unGeo (σ : Sym) (J : Inst) (s : List Coord × List Coord) : List Coord × List Coord :=
  let I1 := if σ.tr then J.transpose else J
  let I2 := if σ.rx then I1.reflectX else I1
  let s4 := if σ.ry then (unRy I2.h s.1, unRy I2.h s.2) else s
  let s5 := if σ.rx then (s4.1.map (reflX I1.w), s4.2.map (reflX I1.w)) else s4
  if σ.tr then (s5.1.map Prod.swap, s5.2.map Prod.swap) else s5

theorem unGeo_sol (σ : Sym) {J : Inst} (hJ : J.WellFormed) {s : List Coord × List Coord}
    (h : IsSolution (σ.geo J) s.1 s.2) : IsSolution J (unGeo σ J s).1 (unGeo σ J s).2 := by
  have w1 : (if σ.tr then J.transpose else J).WellFormed := by
    split
    · exact wf_transpose hJ
    · exact hJ
  have w2 : (if σ.rx then (if σ.tr then J.transpose else J).reflectX
      else (if σ.tr then J.transpose else J)).WellFormed := by
    split
    · exact wf_reflectX w1
    · exact w1
  exact sol_ifTr σ.tr (sol_ifRx σ.rx w1 (sol_ifRy σ.ry w2 h))

/-- From a solution of `σ.apply J`, one of `J`. -/
def unSym (σ : Sym) (J : Inst) (s : List Coord × List Coord) : List Coord × List Coord :=
  unGeo σ J (unLab σ s)

theorem unSym_sol (σ : Sym) {J : Inst} (hJ : J.WellFormed) {s : List Coord × List Coord}
    (h : IsSolution (σ.apply J) s.1 s.2) : IsSolution J (unSym σ J s).1 (unSym σ J s).2 :=
  unGeo_sol σ hJ (unLab_sol σ (σ.geo J) h)

end ZZN

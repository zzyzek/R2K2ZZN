-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.StripExtend
import ZZN.Catalogue

/-!
# Valid moves

What the one-step move checker of the computations in `PROOF.md` §5 accepts,
stated in Lean, and the proof that an accepted move gives a solution when the non-thin pieces
are solvable (`CanonMove.solvable`, `MoveOK.solvable`).

A *two-path piece* is OK when it is thin (short side ≤ 10) and solvable, the plug DP's verdict,
or when both sides are ≥ 11, it is well formed, and it passes the catalogue. A *one-path piece*
is OK when it has a Hamiltonian path (IPS).

Canonical moves cut at `x = p`; every other move is the image of a canonical one under the
symmetries (transpose, reflection, reversing a path, swapping the colors).
-/

namespace ZZN

open GridHam

/-- A two-path piece is OK. -/
def PieceOK (J : Inst) : Prop :=
  ((J.w ≤ 10 ∨ J.h ≤ 10) ∧ Solvable J) ∨ (11 ≤ J.w ∧ 11 ≤ J.h ∧ J.WellFormed ∧ Passes J)

/-- The canonical moves, cutting at `x = p`. -/
def CanonMove (I : Inst) : Prop :=
  ∃ p, 0 < p ∧ p < I.w ∧
    -- strip: all endpoints left, the right block (even area, at least 2 wide) is empty
    ((PieceOK ⟨p, I.h, I.s0, I.t0, I.s1, I.t1⟩ ∧ 2 ≤ I.w - p ∧ ((I.w - p) * I.h) % 2 = 0 ∧
        5 ≤ I.h ∧ I.s0.1 < p ∧ I.t0.1 < p ∧ I.s1.1 < p ∧ I.t1.1 < p) ∨
    -- 1/3: s0 alone on the left
     (∃ y, y < I.h ∧ HasHamPath p I.h I.s0 (p - 1, y) ∧
        PieceOK ⟨I.w - p, I.h, (0, y), unX p I.t0, unX p I.s1, unX p I.t1⟩ ∧
        p ≤ I.t0.1 ∧ p ≤ I.s1.1 ∧ p ≤ I.t1.1) ∨
    -- 2/2 cross: s0, s1 left; t0, t1 right
     (∃ y0 y1, y0 < I.h ∧ y1 < I.h ∧
        PieceOK ⟨p, I.h, I.s0, (p - 1, y0), I.s1, (p - 1, y1)⟩ ∧
        PieceOK ⟨I.w - p, I.h, (0, y0), unX p I.t0, (0, y1), unX p I.t1⟩ ∧
        p ≤ I.t0.1 ∧ p ≤ I.t1.1) ∨
    -- 2/2 same: color 0 left, color 1 right, both pieces Hamiltonian
     (I.s0.1 < p ∧ I.t0.1 < p ∧ p ≤ I.s1.1 ∧ p ≤ I.t1.1 ∧ HasHamPath p I.h I.s0 I.t0 ∧
        HasHamPath (I.w - p) I.h (I.s1.1 - p, I.s1.2) (I.t1.1 - p, I.t1.2)) ∨
    -- excursion: color 0 left, crossing out at row ya and back at yb
     (∃ ya yb, ya < I.h ∧ yb < I.h ∧
        PieceOK ⟨p, I.h, I.s0, (p - 1, ya), (p - 1, yb), I.t0⟩ ∧
        PieceOK ⟨I.w - p, I.h, unX p I.s1, unX p I.t1, (0, ya), (0, yb)⟩ ∧
        p ≤ I.s1.1 ∧ p ≤ I.t1.1))

/-- Hypothesis available in the induction: smaller passing instances of the domain are
solvable. -/
def SmallerSolvable (I : Inst) : Prop :=
  ∀ J : Inst, 11 ≤ J.w → 11 ≤ J.h → J.WellFormed → J.w * J.h < I.w * I.h → Passes J → Solvable J

theorem PieceOK.solvable {I J : Inst} (hJ : PieceOK J) (ih : SmallerSolvable I)
    (harea : J.w * J.h < I.w * I.h) : Solvable J := by
  rcases hJ with ⟨-, h⟩ | ⟨hw, hh, hwf, hp⟩
  · exact h
  · exact ih J hw hh hwf harea hp

theorem CanonMove.solvable {I : Inst} (hm : CanonMove I) (ih : SmallerSolvable I) :
    Solvable I := by
  obtain ⟨p, hp0, hp, h⟩ := hm
  have hh : 0 < I.h ∨ I.h = 0 := by omega
  have aL : p * I.h ≤ I.w * I.h := Nat.mul_le_mul_right _ hp.le
  have aR : (I.w - p) * I.h ≤ I.w * I.h := Nat.mul_le_mul_right _ (by omega)
  -- pieces are strictly smaller when the grid is nonempty
  have smallL : 0 < I.h → p * I.h < I.w * I.h := fun h0 => Nat.mul_lt_mul_of_pos_right hp h0
  have smallR : 0 < I.h → (I.w - p) * I.h < I.w * I.h := fun h0 =>
    Nat.mul_lt_mul_of_pos_right (by omega) h0
  rcases h with ⟨hs, hk, harea, h5, -, -, -, -⟩ | ⟨y, hy, hA, hR, h1, h2, h3⟩ |
      ⟨y0, y1, hy0, hy1, hL, hR, h1, h2⟩ | ⟨a, b, c, d, hA, hB⟩ |
      ⟨ya, yb, hya, hyb, hN, hF, h1, h2⟩
  · have hJ := hs.solvable ih (smallL (by omega))
    have := strip_any ⟨p, I.h, I.s0, I.t0, I.s1, I.t1⟩ h5 (I.w - p) hk harea hJ
    have e : (⟨p, I.h, I.s0, I.t0, I.s1, I.t1⟩ : Inst).widen (I.w - p) = I := by
      cases I; simp only [Inst.widen, Inst.mk.injEq, and_true]; simp at hp ⊢; omega
    exact e ▸ this
  · exact glue_13 I p y hp0 hp hA (hR.solvable ih (smallR (by omega))) h1 h2 h3
  · exact glue_cross I p y0 y1 hp0 hp (hL.solvable ih (smallL (by omega)))
      (hR.solvable ih (smallR (by omega))) h1 h2
  · exact glue_same I p hp a b c d hA hB
  · exact glue_exc I p ya yb hp0 hp (hN.solvable ih (smallL (by omega)))
      (hF.solvable ih (smallR (by omega))) h1 h2

/-! ### Symmetries -/

/-- Reverse path 1. -/
def Inst.rev1 (I : Inst) : Inst := ⟨I.w, I.h, I.s0, I.t0, I.t1, I.s1⟩

/-- Reverse path 0. -/
def Inst.rev0 (I : Inst) : Inst := ⟨I.w, I.h, I.t0, I.s0, I.s1, I.t1⟩

theorem IsPath.reverse {w h : ℕ} {s t : Coord} {L : List Coord} (hp : IsPath w h s t L) :
    IsPath w h t s L.reverse := by
  obtain ⟨hh, hl, hn, hb, hc⟩ := hp
  exact ⟨by rw [List.head?_reverse, hl], by rw [List.getLast?_reverse, hh],
    List.nodup_reverse.mpr hn, fun v hv => hb v (List.mem_reverse.mp hv), chainAdjacent_reverse L hc⟩

theorem solvable_of_rev0 {I : Inst} (h : Solvable I.rev0) : Solvable I := by
  obtain ⟨p, q, hp, hq, hd, hc⟩ := h
  exact ⟨p.reverse, q, hp.reverse, hq, fun v hv => hd v (List.mem_reverse.mp hv),
    fun v hv => (hc v hv).imp_left List.mem_reverse.mpr⟩

theorem solvable_of_rev1 {I : Inst} (h : Solvable I.rev1) : Solvable I := by
  obtain ⟨p, q, hp, hq, hd, hc⟩ := h
  exact ⟨p, q.reverse, hp, hq.reverse, fun v hv hv' => hd v hv (List.mem_reverse.mp hv'),
    fun v hv => (hc v hv).imp_right List.mem_reverse.mpr⟩

/-- Reflect in y (`v ↦ (v.1, h - 1 - v.2)`), as transpose, reflect x, transpose. -/
def Inst.reflectY (I : Inst) : Inst := I.transpose.reflectX.transpose

theorem wf_transpose {I : Inst} (hI : I.WellFormed) : I.transpose.WellFormed := by
  obtain ⟨b0, b1, b2, b3, n01, n02, n03, n12, n13, n23⟩ := hI
  have sb : ∀ {v : Coord}, InBounds I.w I.h v → InBounds I.h I.w v.swap := fun {v} hv =>
    ⟨hv.2, hv.1⟩
  have sn : ∀ {u v : Coord}, u ≠ v → u.swap ≠ v.swap := fun {u v} h e =>
    h (Prod.swap_injective e)
  exact ⟨sb b0, sb b1, sb b2, sb b3, sn n01, sn n02, sn n03, sn n12, sn n13, sn n23⟩

theorem wf_reflectX {I : Inst} (hI : I.WellFormed) : I.reflectX.WellFormed := by
  obtain ⟨b0, b1, b2, b3, n01, n02, n03, n12, n13, n23⟩ := hI
  have sb : ∀ {v : Coord}, InBounds I.w I.h v → InBounds I.w I.h (reflX I.w v) := fun {v} hv =>
    ⟨by unfold reflX; have := hv.1; simp only; omega, hv.2⟩
  have sn : ∀ {u v : Coord}, InBounds I.w I.h u → InBounds I.w I.h v → u ≠ v →
      reflX I.w u ≠ reflX I.w v := by
    intro u v hu hv h e
    apply h
    obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v
    simp only [reflX, Prod.mk.injEq] at e
    have := hu.1; have := hv.1
    simp only at *
    exact Prod.ext (by omega) e.2
  exact ⟨sb b0, sb b1, sb b2, sb b3, sn b0 b1 n01, sn b0 b2 n02, sn b0 b3 n03, sn b1 b2 n12,
    sn b1 b3 n13, sn b2 b3 n23⟩

theorem wf_reflectY {I : Inst} (hI : I.WellFormed) : I.reflectY.WellFormed :=
  wf_transpose (wf_reflectX (wf_transpose hI))

theorem wf_rev0 {I : Inst} (hI : I.WellFormed) : I.rev0.WellFormed := by
  obtain ⟨b0, b1, b2, b3, n01, n02, n03, n12, n13, n23⟩ := hI
  exact ⟨b1, b0, b2, b3, Ne.symm n01, n12, n13, n02, n03, n23⟩

theorem wf_rev1 {I : Inst} (hI : I.WellFormed) : I.rev1.WellFormed := by
  obtain ⟨b0, b1, b2, b3, n01, n02, n03, n12, n13, n23⟩ := hI
  exact ⟨b0, b1, b3, b2, n01, n03, n02, n13, n12, Ne.symm n23⟩

theorem wf_swapColors {I : Inst} (hI : I.WellFormed) : I.swapColors.WellFormed := by
  obtain ⟨b0, b1, b2, b3, n01, n02, n03, n12, n13, n23⟩ := hI
  exact ⟨b2, b3, b0, b1, n23, Ne.symm n02, Ne.symm n12, Ne.symm n03, Ne.symm n13, n01⟩

theorem solvable_of_reflectX' {I : Inst} (hI : I.WellFormed) (h : Solvable I.reflectX) : Solvable I := by
  obtain ⟨b0, b1, b2, b3, -⟩ := hI
  refine solvable_of_reflectX ?_ h
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨b0.1, b1.1, b2.1, b3.1⟩

theorem solvable_of_reflectY {I : Inst} (hI : I.WellFormed) (h : Solvable I.reflectY) : Solvable I :=
  solvable_transpose_iff.mp (solvable_of_reflectX' (wf_transpose hI)
    (solvable_transpose_iff.mp h))

/-- A choice of symmetries: transpose, reflect x, reflect y, reverse path 0, reverse path 1, swap
colors, applied in that order. -/
structure Sym where
  tr : Bool
  rx : Bool
  ry : Bool
  r0 : Bool
  r1 : Bool
  sw : Bool

/-- The geometric part. -/
def Sym.geo (σ : Sym) (I : Inst) : Inst :=
  let I1 := if σ.tr then I.transpose else I
  let I2 := if σ.rx then I1.reflectX else I1
  if σ.ry then I2.reflectY else I2

/-- The labels part. -/
def Sym.lab (σ : Sym) (I : Inst) : Inst :=
  let I3 := if σ.r0 then I.rev0 else I
  let I4 := if σ.r1 then I3.rev1 else I3
  if σ.sw then I4.swapColors else I4

def Sym.apply (σ : Sym) (I : Inst) : Inst := σ.lab (σ.geo I)

theorem Sym.wf_geo (σ : Sym) {I : Inst} (hI : I.WellFormed) : (σ.geo I).WellFormed := by
  unfold Sym.geo
  have h1 : (if σ.tr then I.transpose else I).WellFormed := by
    split
    · exact wf_transpose hI
    · exact hI
  have h2 : (if σ.rx then (if σ.tr then I.transpose else I).reflectX
      else (if σ.tr then I.transpose else I)).WellFormed := by
    split
    · exact wf_reflectX h1
    · exact h1
  dsimp only
  split
  · exact wf_reflectY h2
  · exact h2

theorem Sym.solvable_lab (σ : Sym) {I : Inst} (h : Solvable (σ.lab I)) : Solvable I := by
  unfold Sym.lab at h
  dsimp only at h
  have h4 : Solvable (if σ.r1 then (if σ.r0 then I.rev0 else I).rev1 else (if σ.r0 then I.rev0 else I)) := by
    split at h
    · exact solvable_swapColors h
    · exact h
  have h3 : Solvable (if σ.r0 then I.rev0 else I) := by
    split at h4
    · exact solvable_of_rev1 h4
    · exact h4
  split at h3
  · exact solvable_of_rev0 h3
  · exact h3

theorem Sym.solvable_geo (σ : Sym) {I : Inst} (hI : I.WellFormed) (h : Solvable (σ.geo I)) :
    Solvable I := by
  unfold Sym.geo at h
  dsimp only at h
  have h1 : (if σ.tr then I.transpose else I).WellFormed := by
    split
    · exact wf_transpose hI
    · exact hI
  have h2 : (if σ.rx then (if σ.tr then I.transpose else I).reflectX
      else (if σ.tr then I.transpose else I)).WellFormed := by
    split
    · exact wf_reflectX h1
    · exact h1
  have g2 : Solvable (if σ.rx then (if σ.tr then I.transpose else I).reflectX
      else (if σ.tr then I.transpose else I)) := by
    split at h
    · exact solvable_of_reflectY h2 h
    · exact h
  have g1 : Solvable (if σ.tr then I.transpose else I) := by
    split at g2
    · exact solvable_of_reflectX' h1 g2
    · exact g2
  split at g1
  · exact solvable_transpose_iff.mp g1
  · exact g1

theorem Sym.solvable {σ : Sym} {I : Inst} (hI : I.WellFormed) (h : Solvable (σ.apply I)) :
    Solvable I :=
  σ.solvable_geo hI (σ.solvable_lab h)

/-- **A valid move**: a canonical move of some symmetric image. -/
def MoveOK (I : Inst) : Prop := ∃ σ : Sym, CanonMove (σ.apply I)

theorem Sym.area (σ : Sym) (I : Inst) : (σ.apply I).w * (σ.apply I).h = I.w * I.h := by
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  cases tr <;> cases rx <;> cases ry <;> cases r0 <;> cases r1 <;> cases sw <;>
    simp [Sym.apply, Sym.geo, Sym.lab, Inst.reflectY, Inst.transpose, Inst.reflectX, Inst.rev0,
      Inst.rev1, Inst.swapColors, Nat.mul_comm]

theorem MoveOK.solvable {I : Inst} (hI : I.WellFormed) (hm : MoveOK I) (ih : SmallerSolvable I) :
    Solvable I := by
  obtain ⟨σ, hc⟩ := hm
  refine Sym.solvable hI (hc.solvable ?_)
  intro J hw hh hwf ha hp
  exact ih J hw hh hwf (by rw [Sym.area] at ha; exact ha) hp

end ZZN

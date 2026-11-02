/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Cut.CheckF

@[expose] public section

/-!
# Templates on lanes, rows as scalars

`tcheckF N w h x Y T`: the template `T` on the row tuple `x` (scalars) and the column lanes `Y`
(8-bit lane words). Column positions are anchors plus offsets on lanes (`posF`). With columns,
`w` and `h` below 64 and every offset of `T` in `[-63, 63]` (`tsmall`), every lane stays below 128
and lane `j` is `tcheck` on the lane-`j` instance (`tcheckF_get`).
-/

namespace ZZN.Cut

open GridHam ZZN.Lane

/-- Every lane below 64, nothing above lane `N`. -/
def Sm64 (N a : ℕ) : Prop := a < Bs ^ N ∧ ∀ j, fld a j < 64

theorem Sm64.sm {N a : ℕ} (h : Sm64 N a) : Sm N a := ⟨h.1, fun j => by have := h.2 j; omega⟩

def offF (N a : ℕ) (o : ℤ) : ℕ := if 0 ≤ o then a + kS N o.toNat else subS N a (kS N (-o).toNat)

def posF (N y0 y1 y2 y3 h : ℕ) (p : TPos) : ℕ := offF N (anchors y0 y1 y2 y3 (kS N h) p.1) p.2

/-- Offsets in `[-63, 63]`. -/
def offOK (p : TPos) : Bool := decide (p.2.natAbs ≤ 63)

def kindsOK : List (Kind TPos) → Bool
  | [] => true
  | Kind.stay _ :: ks => kindsOK ks
  | Kind.cross _ y :: ks => offOK y && kindsOK ks
  | Kind.exc _ y z :: ks => offOK y && offOK z && kindsOK ks

def tsmall : CTree TPos → Bool
  | CTree.leaf => true
  | CTree.cut _ pos ks l r => offOK pos && kindsOK ks && tsmall l && tsmall r

def rootF (N w h : ℕ) (x Y : Fin 4 → ℕ) : PieceF :=
  ⟨0, w, 0, kS N h, [((x 0, Y 0), (x 1, Y 1)), ((x 2, Y 2), (x 3, Y 3))]⟩

def tcheckF (N w h : ℕ) (x Y : Fin 4 → ℕ) (T : CTree TPos) : ℕ :=
  checkF N (inst (posN (x 0) (x 1) (x 2) (x 3) w) (posF N (Y 0) (Y 1) (Y 2) (Y 3) h) T) (rootF N w h x Y)

/-- The instance in lane `j`. -/
def laneF (w h : ℕ) (x Y : Fin 4 → ℕ) (j : ℕ) : Inst :=
  ⟨w, h, (x 0, fld (Y 0) j), (x 1, fld (Y 1) j), (x 2, fld (Y 2) j), (x 3, fld (Y 3) j)⟩

/-! ### Positions -/

theorem kS_lt {N c : ℕ} (hc : c < 128) : kS N c < Bs ^ N := (Sm_kS hc).1

theorem fld_kS_all {N c : ℕ} (hc : c < 128) (i : ℕ) : fld (kS N c) i = if i < N then c else 0 := by
  by_cases hi : i < N
  · rw [fld_kS hc hi]; simp [hi]
  · rw [fld_of_lt (kS_lt hc) (by omega)]; simp [hi]

theorem offF_spec {N a : ℕ} (ha : Sm64 N a) {o : ℤ} (ho : o.natAbs ≤ 63) :
    Sm N (offF N a o) ∧ ∀ j, j < N → fld (offF N a o) j = offN (fld a j) o := by
  unfold offF offN
  by_cases h0 : 0 ≤ o
  · simp only [h0, ↓reduceIte]
    have hc : o.toNat < 128 := by omega
    have hadd : ∀ i, fld (a + kS N o.toNat) i = fld a i + fld (kS N o.toNat) i :=
      fun i => fld_add i _ _ fun k => by
        have := ha.2 k; rw [fld_kS_all hc]; split_ifs <;> simp [Bs] <;> omega
    refine ⟨⟨?_, fun i => ?_⟩, fun j hj => ?_⟩
    · have hle : a + kS N o.toNat ≤ kS N 127 := le_of_fld _ _ fun i => by
        rw [hadd, fld_kS_all hc, fld_kS_all (by norm_num : (127 : ℕ) < 128)]
        split_ifs with hi
        · have := ha.2 i; omega
        · rw [fld_of_lt ha.1 (by omega)]
      exact lt_of_le_of_lt hle (kS_lt (by norm_num))
    · rw [hadd, fld_kS_all hc]; have := ha.2 i; split_ifs <;> omega
    · rw [hadd, fld_kS hc hj]
  · simp only [h0, ↓reduceIte]
    have hc : (-o).toNat < 128 := by omega
    exact ⟨Sm_subS ha.sm (Sm_kS hc), fun j hj => by rw [fl_sub ha.sm (Sm_kS hc), fld_kS hc hj]⟩

theorem anchors_sm64 {N y0 y1 y2 y3 h : ℕ} (h0 : Sm64 N y0) (h1 : Sm64 N y1) (h2 : Sm64 N y2)
    (h3 : Sm64 N y3) (hh : h < 64) (a : ℕ) : Sm64 N (anchors y0 y1 y2 y3 (kS N h) a) := by
  rcases a with _ | _ | _ | _ | _ | a
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · show Sm64 N 0
    exact ⟨by simp [Bs], fun j => by simp [fld]⟩
  · show Sm64 N (kS N h)
    exact ⟨kS_lt (by omega), fun j => by rw [fld_kS_all (by omega)]; split_ifs <;> omega⟩

theorem fld_anchors {N y0 y1 y2 y3 h j : ℕ} (hj : j < N) (hh : h < 128) (a : ℕ) :
    fld (anchors y0 y1 y2 y3 (kS N h) a) j =
      anchors (fld y0 j) (fld y1 j) (fld y2 j) (fld y3 j) h a := by
  rcases a with _ | _ | _ | _ | _ | a
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [anchors, fld]
  · exact fld_kS hh hj

/-! ### Instantiation commutes with taking a lane -/

theorem inst_getF {fR fC : TPos → ℕ} (j : ℕ) : ∀ T : CTree TPos,
    (inst fR fC T).getF j = inst fR (fun p => fld (fC p) j) T
  | CTree.leaf => rfl
  | CTree.cut vert pos ks l r => by
    simp only [inst, CTree.getF, inst_getF j l, inst_getF j r, List.map_map]
    cases vert <;> simp only [lget, Bool.not_false, Bool.not_true, ite_true, ite_false,
      Bool.false_eq_true] <;> congr 1 <;> apply List.map_congr_left <;> intro k _ <;>
      cases k <;> rfl

theorem kindsOK_mem : ∀ {ks : List (Kind TPos)} {k : Kind TPos}, kindsOK ks = true → k ∈ ks →
    kindsOK [k] = true
  | [], _, _, hm => by simp at hm
  | k' :: ks, k, h, hm => by
    rcases List.mem_cons.mp hm with rfl | hm
    · cases k <;> simp_all [kindsOK]
    · apply kindsOK_mem _ hm
      cases k' <;> simp only [kindsOK, Bool.and_eq_true] at h ⊢ <;> tauto

/-- On the positions of a template with small offsets, `posF` is `posN` lane by lane. -/
theorem inst_posF {N j x0 x1 x2 x3 w h : ℕ} {Y : Fin 4 → ℕ} (hj : j < N) (hY : ∀ i, Sm64 N (Y i))
    (hh : h < 64) : ∀ T : CTree TPos, tsmall T = true →
    inst (posN x0 x1 x2 x3 w) (fun p => fld (posF N (Y 0) (Y 1) (Y 2) (Y 3) h p) j) T =
      inst (posN x0 x1 x2 x3 w) (posN (fld (Y 0) j) (fld (Y 1) j) (fld (Y 2) j) (fld (Y 3) j) h) T
  | CTree.leaf, _ => rfl
  | CTree.cut vert pos ks l r, hT => by
    simp only [tsmall, Bool.and_eq_true] at hT
    obtain ⟨⟨⟨hp, hk⟩, hl⟩, hr⟩ := hT
    have key : ∀ p : TPos, offOK p = true →
        fld (posF N (Y 0) (Y 1) (Y 2) (Y 3) h p) j =
          posN (fld (Y 0) j) (fld (Y 1) j) (fld (Y 2) j) (fld (Y 3) j) h p := by
      intro p hp
      simp only [offOK, decide_eq_true_eq] at hp
      unfold posF posN
      rw [(offF_spec (anchors_sm64 (hY 0) (hY 1) (hY 2) (hY 3) hh p.1) hp).2 j hj,
        fld_anchors hj (by omega)]
    have hks : ∀ k ∈ ks, (instK (fun p => fld (posF N (Y 0) (Y 1) (Y 2) (Y 3) h p) j) k) =
        instK (posN (fld (Y 0) j) (fld (Y 1) j) (fld (Y 2) j) (fld (Y 3) j) h) k := by
      intro k hkm
      have h1 := kindsOK_mem hk hkm
      cases k with
      | stay s => rfl
      | cross s y =>
        simp only [kindsOK, Bool.and_true] at h1
        simp only [instK, key y h1]
      | exc s y z =>
        simp only [kindsOK, Bool.and_eq_true, Bool.and_true] at h1
        simp only [instK, key y h1.1, key z h1.2]
    simp only [inst, inst_posF hj hY hh l hl, inst_posF hj hY hh r hr]
    cases vert <;> simp only [Bool.false_eq_true, ite_false, ite_true, key pos hp]
    congr 1
    exact List.map_congr_left hks

/-! ### Smallness of the instantiated tree -/

theorem tok_inst {N x0 x1 x2 x3 w h : ℕ} {Y : Fin 4 → ℕ} (hx : x0 < 64 ∧ x1 < 64 ∧ x2 < 64 ∧ x3 < 64)
    (hw : w < 64) (hY : ∀ i, Sm64 N (Y i)) (hh : h < 64) : ∀ T : CTree TPos, tsmall T = true →
    TOK N (inst (posN x0 x1 x2 x3 w) (posF N (Y 0) (Y 1) (Y 2) (Y 3) h) T)
  | CTree.leaf, _ => trivial
  | CTree.cut vert pos ks l r, hT => by
    simp only [tsmall, Bool.and_eq_true] at hT
    obtain ⟨⟨⟨hp, hk⟩, hl⟩, hr⟩ := hT
    have row : ∀ p : TPos, offOK p = true → posN x0 x1 x2 x3 w p < 128 := by
      intro p hp
      simp only [offOK, decide_eq_true_eq] at hp
      unfold posN offN
      have : anchors x0 x1 x2 x3 w p.1 < 64 := by
        rcases p with ⟨_ | _ | _ | _ | _ | a, o⟩ <;> simp [anchors] <;> omega
      split_ifs <;> omega
    have col : ∀ p : TPos, offOK p = true → Sm N (posF N (Y 0) (Y 1) (Y 2) (Y 3) h p) := by
      intro p hp
      simp only [offOK, decide_eq_true_eq] at hp
      exact (offF_spec (anchors_sm64 (hY 0) (hY 1) (hY 2) (hY 3) hh p.1) hp).1
    refine ⟨?_, ?_, tok_inst hx hw hY hh l hl, tok_inst hx hw hY hh r hr⟩
    · cases vert <;> simp only [PosOK, Bool.false_eq_true, ite_false, ite_true]
      · exact row pos hp
      · exact col pos hp
    · intro k hkm
      simp only [List.mem_map] at hkm
      obtain ⟨k0, hk0, rfl⟩ := hkm
      have h1 := kindsOK_mem hk hk0
      cases k0 <;> cases vert <;> simp only [kindsOK, Bool.and_eq_true,
        Bool.and_true] at h1 <;> simp only [instK, KindOK, PosOK, Bool.not_false, Bool.not_true,
          Bool.false_eq_true, ite_false, ite_true] <;>
        first | trivial | exact row _ h1 | exact col _ h1 | exact ⟨row _ h1.1, row _ h1.2⟩ |
          exact ⟨col _ h1.1, col _ h1.2⟩

/-- **Lane lemma.** Lane `j` of `tcheckF` is `tcheck` on lane `j`. -/
theorem tcheckF_get {N j w h : ℕ} (hj : j < N) {x Y : Fin 4 → ℕ} (hx : ∀ i, x i < 64) (hw : w < 64)
    (hY : ∀ i, Sm64 N (Y i)) (hh : h < 64) {T : CTree TPos} (hT : tsmall T = true) :
    (tcheckF N w h x Y T).testBit (8 * j) = tcheck T (laneF w h x Y j) := by
  have hroot : (rootF N w h x Y).OK N := by
    refine ⟨by simp [rootF]; omega, ⟨by simp [rootF, Bs], fun i => by simp [rootF, fld]⟩,
      Sm_kS (by omega), fun i => by simp [rootF, fld], ?_⟩
    intro e he
    simp only [rootF, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl
    · exact ⟨⟨hx 0 |>.trans (by norm_num), (hY 0).sm⟩, ⟨hx 1 |>.trans (by norm_num), (hY 1).sm⟩⟩
    · exact ⟨⟨hx 2 |>.trans (by norm_num), (hY 2).sm⟩, ⟨hx 3 |>.trans (by norm_num), (hY 3).sm⟩⟩
  unfold tcheckF tcheck
  rw [checkF_get hj _ _ (tok_inst ⟨hx 0, hx 1, hx 2, hx 3⟩ hw hY hh T hT) hroot, inst_getF,
    inst_posF hj hY hh T hT]
  have hk : fld (kS N h) j = h := fld_kS (by omega) hj
  have h0 : fld 0 j = 0 := by simp [fld]
  congr 1
  simp only [rootF, PieceF.get, rootPiece, laneF, segF, FC.get, hk, h0, Nat.sub_zero, List.map_cons,
    List.map_nil]

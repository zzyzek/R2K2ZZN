-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Defs
import GridHam.Main
import GridHam.StripSplit

/-!
# Region covers

`RCover A S`: the cell set `A` is covered by vertex-disjoint paths, one for each endpoint pair in
the multiset `S` (a pair `(a, a)` is the one-cell path `[a]`). Cut trees are assembled from five
operations on region covers:

* `RCover.union`: covers of disjoint regions combine;
* `RCover.join`: a path ending at `u` and a path starting at an adjacent `v` merge;
* `RCover.reverse`: a path is reversed;
* `RCover.map`: an injective, adjacency-preserving map moves a cover;
* `RCover.ips`, `RCover.single`: a rectangle with one Hamiltonian path (IPS), or one cell.

`RCover.solvable` turns a cover of the whole grid with the two endpoint pairs into a solution.
-/

namespace ZZN.Cut

open GridHam

/-- A path with its endpoints. -/
structure Seg where
  a : Coord
  b : Coord
  p : List Coord
  deriving DecidableEq

def Seg.Good (x : Seg) : Prop :=
  x.p.head? = some x.a ∧ x.p.getLast? = some x.b ∧ chainAdjacent x.p = true

def Seg.ends (x : Seg) : Coord × Coord := (x.a, x.b)

/-- All cells of a multiset of paths, with multiplicity. -/
def cells (ps : Multiset Seg) : Multiset Coord := ps.bind fun x => (x.p : Multiset Coord)

/-- The region `A` is covered by disjoint paths with endpoint pairs `S`. -/
def RCover (A : Coord → Prop) (S : Multiset (Coord × Coord)) : Prop :=
  ∃ ps : Multiset Seg, ps.map Seg.ends = S ∧ (∀ x ∈ ps, x.Good) ∧ (cells ps).Nodup ∧
    ∀ v, A v ↔ v ∈ cells ps

theorem cells_add (ps qs : Multiset Seg) : cells (ps + qs) = cells ps + cells qs := by
  simp [cells]

theorem cells_cons (x : Seg) (ps : Multiset Seg) : cells (x ::ₘ ps) = (x.p : Multiset Coord) + cells ps := by
  simp [cells, Multiset.cons_bind]

theorem RCover.congr {A B : Coord → Prop} {S : Multiset (Coord × Coord)} (h : RCover A S)
    (hAB : ∀ v, A v ↔ B v) : RCover B S := by
  obtain ⟨ps, h1, h2, h3, h4⟩ := h
  exact ⟨ps, h1, h2, h3, fun v => (hAB v).symm.trans (h4 v)⟩

theorem RCover.union {A B : Coord → Prop} {S T : Multiset (Coord × Coord)} (hA : RCover A S)
    (hB : RCover B T) (hd : ∀ v, A v → ¬ B v) : RCover (fun v => A v ∨ B v) (S + T) := by
  obtain ⟨ps, p1, p2, p3, p4⟩ := hA
  obtain ⟨qs, q1, q2, q3, q4⟩ := hB
  refine ⟨ps + qs, by simp [Multiset.map_add, p1, q1], ?_, ?_, ?_⟩
  · intro x hx
    rcases Multiset.mem_add.mp hx with h | h
    · exact p2 x h
    · exact q2 x h
  · rw [cells_add, Multiset.nodup_add]
    refine ⟨p3, q3, ?_⟩
    exact Multiset.disjoint_left.mpr fun {v} hv hv' => hd v ((p4 v).mpr hv) ((q4 v).mpr hv')
  · intro v
    show A v ∨ B v ↔ _
    rw [cells_add, Multiset.mem_add, p4, q4]

/-- Pick the path with given endpoints out of a cover. -/
theorem RCover.pick {A : Coord → Prop} {e : Coord × Coord} {S : Multiset (Coord × Coord)}
    (h : RCover A (e ::ₘ S)) :
    ∃ x : Seg, ∃ ps : Multiset Seg, x.ends = e ∧ ps.map Seg.ends = S ∧ x.Good ∧ (∀ y ∈ ps, y.Good) ∧
      (cells (x ::ₘ ps)).Nodup ∧ ∀ v, A v ↔ v ∈ cells (x ::ₘ ps) := by
  obtain ⟨qs, h1, h2, h3, h4⟩ := h
  obtain ⟨x, hx, hxe, hrest⟩ := (Multiset.map_eq_cons _ _ _ _).mpr h1
  have hq : qs = x ::ₘ qs.erase x := (Multiset.cons_erase hx).symm
  refine ⟨x, qs.erase x, hxe, hrest, h2 x hx, fun y hy => h2 y (Multiset.mem_of_mem_erase hy), ?_, ?_⟩
  · rw [← hq]; exact h3
  · intro v; rw [← hq]; exact h4 v

theorem RCover.of_pick {A : Coord → Prop} {S : Multiset (Coord × Coord)} (x : Seg)
    (ps : Multiset Seg) (h1 : ps.map Seg.ends = S) (hx : x.Good) (h2 : ∀ y ∈ ps, y.Good)
    (h3 : (cells (x ::ₘ ps)).Nodup) (h4 : ∀ v, A v ↔ v ∈ cells (x ::ₘ ps)) :
    RCover A (x.ends ::ₘ S) := by
  refine ⟨x ::ₘ ps, by simp [h1], ?_, h3, h4⟩
  intro y hy
  rcases Multiset.mem_cons.mp hy with h | h
  · exact h ▸ hx
  · exact h2 y h

theorem Seg.good_ne_nil {x : Seg} (h : x.Good) : x.p ≠ [] := by
  intro e; have := h.1; rw [e] at this; simp at this

/-- Join a path ending at `u` with a path starting at an adjacent `v`. -/
theorem RCover.join {A : Coord → Prop} {a u v b : Coord} {S : Multiset (Coord × Coord)}
    (h : RCover A ((a, u) ::ₘ (v, b) ::ₘ S)) (hadj : Adjacent u v) : RCover A ((a, b) ::ₘ S) := by
  obtain ⟨x, ps, hxe, hps, hxg, hpg, hnd, hcov⟩ := h.pick
  obtain ⟨y, hy, hye, hrest⟩ := (Multiset.map_eq_cons _ _ _ _).mpr hps
  have hpsy : ps = y ::ₘ ps.erase y := (Multiset.cons_erase hy).symm
  have hyg : y.Good := hpg y hy
  simp only [Seg.ends, Prod.mk.injEq] at hxe hye
  obtain ⟨hxa, hxu⟩ := hxe
  obtain ⟨hyv, hyb⟩ := hye
  let z : Seg := ⟨a, b, x.p ++ y.p⟩
  have hcz : cells (z ::ₘ ps.erase y) = cells (x ::ₘ ps) := by
    conv_rhs => rw [hpsy]
    simp only [cells_cons, z, ← Multiset.coe_add, add_assoc]
  have hzg : z.Good := by
    obtain ⟨hx1, hx2, hx3⟩ := hxg
    obtain ⟨hy1, hy2, hy3⟩ := hyg
    refine ⟨?_, ?_, ?_⟩
    · cases hxp : x.p with
      | nil => rw [hxp] at hx1; simp at hx1
      | cons c l =>
        rw [hxp] at hx1
        have : c = x.a := by simpa using hx1
        simp [z, hxp, this, hxa]
    · cases hyp : y.p with
      | nil => rw [hyp] at hy1; simp at hy1
      | cons c l =>
        have : (x.p ++ y.p).getLast? = y.p.getLast? := by
          rw [hyp, List.getLast?_append]; simp [List.getLast?_cons]
        show (x.p ++ y.p).getLast? = some b
        rw [this, hy2, hyb]
    · cases hyp : y.p with
      | nil => rw [hyp] at hy1; simp at hy1
      | cons c l =>
        rw [hyp] at hy1 hy3
        have hc : c = v := by simpa [hyv] using hy1
        show chainAdjacent (x.p ++ y.p) = true
        rw [hyp]
        exact chainAdjacent_append x.p c l u (hxu ▸ hx2) hx3 (hc ▸ hadj) hy3
  have := RCover.of_pick (A := A) (S := S) z (ps.erase y) hrest hzg
    (fun w hw => hpg w (Multiset.mem_of_mem_erase hw)) (hcz ▸ hnd) (fun w => hcz ▸ hcov w)
  simpa [Seg.ends, z] using this

/-- Reverse the path with endpoints `(a, b)`. -/
theorem RCover.reverse {A : Coord → Prop} {a b : Coord} {S : Multiset (Coord × Coord)}
    (h : RCover A ((a, b) ::ₘ S)) : RCover A ((b, a) ::ₘ S) := by
  obtain ⟨x, ps, hxe, hps, hxg, hpg, hnd, hcov⟩ := h.pick
  simp only [Seg.ends, Prod.mk.injEq] at hxe
  obtain ⟨hxa, hxb⟩ := hxe
  obtain ⟨hx1, hx2, hx3⟩ := hxg
  let z : Seg := ⟨b, a, x.p.reverse⟩
  have hcz : cells (z ::ₘ ps) = cells (x ::ₘ ps) := by
    simp only [cells_cons, z, Multiset.coe_reverse]
  have hzg : z.Good := by
    refine ⟨?_, ?_, chainAdjacent_reverse _ hx3⟩
    · simp only [z, List.head?_reverse, hx2, hxb]
    · simp only [z, List.getLast?_reverse, hx1, hxa]
  have := RCover.of_pick (A := A) (S := S) z ps hps hzg hpg (hcz ▸ hnd) (fun w => hcz ▸ hcov w)
  simpa [Seg.ends, z] using this

theorem chainAdjacent_map_on (B : Coord → Prop) (f : Coord → Coord)
    (hf : ∀ v w, B v → B w → Adjacent v w → Adjacent (f v) (f w)) :
    ∀ (l : List Coord), (∀ v ∈ l, B v) → chainAdjacent l = true → chainAdjacent (l.map f) = true := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons a l ih =>
    intro hB hch
    cases l with
    | nil => rfl
    | cons b rest =>
      have hc' : (adjacentB a b && chainAdjacent (b :: rest)) = true := by
        simpa [chainAdjacent] using hch
      simp only [Bool.and_eq_true] at hc'
      obtain ⟨hab, hcl⟩ := hc'
      have hadj : Adjacent a b := of_decide_eq_true hab
      have hA : adjacentB (f a) (f b) = true :=
        decide_eq_true (hf a b (hB a (by simp)) (hB b (by simp)) hadj)
      have hR : chainAdjacent ((b :: rest).map f) = true :=
        ih (fun v hv => hB v (List.mem_cons_of_mem a hv)) hcl
      have e : chainAdjacent ((a :: b :: rest).map f) =
          (adjacentB (f a) (f b) && chainAdjacent ((b :: rest).map f)) := rfl
      simp only [e, hA, hR, Bool.and_self]

/-- Move a cover by a map that is injective and preserves adjacency on the region. -/
theorem RCover.map {A : Coord → Prop} {S : Multiset (Coord × Coord)} (f : Coord → Coord)
    (hinj : ∀ v w, A v → A w → f v = f w → v = w)
    (hadj : ∀ v w, A v → A w → Adjacent v w → Adjacent (f v) (f w))
    (h : RCover A S) :
    RCover (fun v => ∃ w, A w ∧ f w = v) (S.map fun e => (f e.1, f e.2)) := by
  obtain ⟨ps, h1, h2, h3, h4⟩ := h
  let g : Seg → Seg := fun x => ⟨f x.a, f x.b, x.p.map f⟩
  have hc : cells (ps.map g) = (cells ps).map f := by
    simp [cells, g, Multiset.map_bind, Multiset.bind_map]
  refine ⟨ps.map g, ?_, ?_, ?_, ?_⟩
  · rw [← h1, Multiset.map_map, Multiset.map_map]; rfl
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
    obtain ⟨g1, g2, g3⟩ := h2 x hx
    have hxA : ∀ v ∈ x.p, A v := fun v hv =>
      (h4 v).mpr (Multiset.mem_bind.mpr ⟨x, hx, Multiset.mem_coe.mpr hv⟩)
    exact ⟨by simp [g, List.head?_map, g1], by simp [g, List.getLast?_map, g2],
      chainAdjacent_map_on A f hadj _ hxA g3⟩
  · rw [hc]
    exact h3.map_on fun v hv w hw e => hinj v w ((h4 v).mpr hv) ((h4 w).mpr hw) e
  · intro v
    rw [hc, Multiset.mem_map]
    exact ⟨fun ⟨w, hw, e⟩ => ⟨w, (h4 w).mp hw, e⟩, fun ⟨w, hw, e⟩ => ⟨w, (h4 w).mpr hw, e⟩⟩

/-- A one-cell region, covered by the one-cell path. -/
theorem RCover.single (c : Coord) : RCover (fun v => v = c) {(c, c)} := by
  refine ⟨{⟨c, c, [c]⟩}, rfl, ?_, ?_, ?_⟩
  · intro x hx
    rw [Multiset.mem_singleton] at hx
    subst hx
    exact ⟨rfl, rfl, rfl⟩
  · simp [cells]
  · intro v; simp [cells]

/-- A rectangle with one acceptable endpoint pair (IPS). -/
theorem RCover.ips {w h : ℕ} {s t : Coord} (hs : InBounds w h s) (ht : InBounds w h t) (hst : s ≠ t)
    (hacc : IsAcceptable w h s t) : RCover (InBounds w h) {(s, t)} := by
  obtain ⟨p, _, p1, p2, p3, p4, p5, p6⟩ := ips_sufficiency w h s t hs ht hst hacc
  refine ⟨{⟨s, t, p⟩}, rfl, ?_, ?_, ?_⟩
  · intro x hx
    rw [Multiset.mem_singleton] at hx
    subst hx
    exact ⟨p1, p2, p6⟩
  · simpa [cells] using p3
  · intro v
    simp only [cells, Multiset.singleton_bind, Multiset.mem_coe]
    exact ⟨fun hv => p5 v ((GridHam.mem_allCoords w h v).mpr hv), fun hv => p4 v hv⟩

/-- A cover of the whole grid with the two endpoint pairs is a solution. -/
theorem RCover.solvable {I : Inst} (h : RCover (InBounds I.w I.h) {(I.s0, I.t0), (I.s1, I.t1)}) :
    Solvable I := by
  obtain ⟨x, ps, hxe, hps, hxg, hpg, hnd, hcov⟩ := h.pick
  obtain ⟨y, hy, hye, hrest⟩ := (Multiset.map_eq_cons _ _ _ _).mpr hps
  have hpsy : ps = {y} := by
    have h0 : ps.erase y = 0 := Multiset.map_eq_zero.mp hrest
    rw [← Multiset.cons_erase hy, h0]; rfl
  subst hpsy
  simp only [Seg.ends, Prod.mk.injEq] at hxe hye
  have hyg := hpg y (Multiset.mem_singleton_self y)
  have hc : cells (x ::ₘ {y}) = (x.p : Multiset Coord) + (y.p : Multiset Coord) := by
    simp [cells]
  rw [hc, Multiset.nodup_add] at hnd
  obtain ⟨nx, ny, hdj⟩ := hnd
  have hin : ∀ v, v ∈ x.p ∨ v ∈ y.p → InBounds I.w I.h v := by
    intro v hv; apply (hcov v).mpr; rw [hc, Multiset.mem_add]; simpa using hv
  refine ⟨x.p, y.p, ⟨?_, ?_, nx, fun v hv => hin v (Or.inl hv), hxg.2.2⟩,
    ⟨?_, ?_, ny, fun v hv => hin v (Or.inr hv), hyg.2.2⟩, ?_, ?_⟩
  · rw [hxg.1, hxe.1]
  · rw [hxg.2.1, hxe.2]
  · rw [hyg.1, hye.1]
  · rw [hyg.2.1, hye.2]
  · intro v hv hv'
    exact Multiset.disjoint_left.mp hdj (Multiset.mem_coe.mpr hv) (Multiset.mem_coe.mpr hv')
  · intro v hv
    have := (hcov v).mp hv
    rw [hc, Multiset.mem_add] at this
    simpa using this

end ZZN.Cut

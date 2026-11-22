/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Cut.Template
public import ZZN.Look.IPS

@[expose] public section

/-!
# Paths from a checked cut tree

`RCW A S ps`: the explicit list `ps` of paths witnesses `RCover A S`. `buildT T P` builds the paths
of a cut tree: a leaf is one cell or an IPS rectangle (`ipsP`), a cut builds both sides and joins
the crossing paths back together (`unsplit`, the constructive form of `split_sound`).
`buildT_sound`: a checked tree gives a witness. `solOf`: the two paths of a witness for the root
piece, a solution (`solOf_sound`).
-/

namespace ZZN.Cut

open GridHam

/-- The paths `ps` cover `A` with endpoint pairs `S`. -/
def RCW (A : Coord → Prop) (S : Multiset (Coord × Coord)) (ps : List Seg) : Prop :=
  ((ps : Multiset Seg).map Seg.ends = S) ∧ (∀ x ∈ ps, x.Good) ∧ (cells (ps : Multiset Seg)).Nodup ∧
    ∀ v, A v ↔ v ∈ cells (ps : Multiset Seg)

theorem RCW.congr {A B : Coord → Prop} {S : Multiset (Coord × Coord)} {ps : List Seg}
    (h : RCW A S ps) (hAB : ∀ v, A v ↔ B v) : RCW B S ps := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, h3, fun v => (hAB v).symm.trans (h4 v)⟩

theorem RCW.union {A B : Coord → Prop} {S T : Multiset (Coord × Coord)} {ps qs : List Seg}
    (hA : RCW A S ps) (hB : RCW B T qs) (hd : ∀ v, A v → ¬ B v) :
    RCW (fun v => A v ∨ B v) (S + T) (ps ++ qs) := by
  obtain ⟨p1, p2, p3, p4⟩ := hA
  obtain ⟨q1, q2, q3, q4⟩ := hB
  refine ⟨by simp [← Multiset.coe_add, Multiset.map_add, p1, q1], ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact p2 x h
    · exact q2 x h
  · rw [← Multiset.coe_add, cells_add, Multiset.nodup_add]
    refine ⟨p3, q3, ?_⟩
    exact Multiset.disjoint_left.mpr fun {v} hv hv' => hd v ((p4 v).mpr hv) ((q4 v).mpr hv')
  · intro v
    show A v ∨ B v ↔ _
    rw [← Multiset.coe_add, cells_add, Multiset.mem_add, p4, q4]

/-- Join the path with ends `(a, u)` and the path with ends `(v, b)`. -/
def joinL (a u v b : Coord) (ps : List Seg) : List Seg :=
  match ps.find? (fun x => x.ends == (a, u)) with
  | none => ps
  | some x =>
    match (ps.erase x).find? (fun y => y.ends == (v, b)) with
    | none => ps
    | some y => ⟨a, b, x.p ++ y.p⟩ :: (ps.erase x).erase y

theorem find_of_mem_ends {ps : List Seg} {e : Coord × Coord}
    (h : e ∈ (ps : Multiset Seg).map Seg.ends) :
    ∃ x, ps.find? (fun x => x.ends == e) = some x ∧ x ∈ ps ∧ x.ends = e := by
  have hm : ∃ x ∈ ps, x.ends = e := by
    obtain ⟨y, hy, he⟩ := Multiset.mem_map.mp h
    exact ⟨y, Multiset.mem_coe.mp hy, he⟩
  obtain ⟨y, hy, he⟩ := hm
  obtain ⟨x, hf⟩ := Option.isSome_iff_exists.mp
    ((List.find?_isSome (p := fun x : Seg => x.ends == e)).mpr ⟨y, hy, by simp [he]⟩)
  exact ⟨x, hf, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩

theorem RCW.join {A : Coord → Prop} {a u v b : Coord} {S : Multiset (Coord × Coord)} {ps : List Seg}
    (h : RCW A ((a, u) ::ₘ (v, b) ::ₘ S) ps) (hadj : Adjacent u v) :
    RCW A ((a, b) ::ₘ S) (joinL a u v b ps) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨x, hfx, hx, hxe⟩ := find_of_mem_ends (e := (a, u)) (by rw [h1]; simp)
  have hpx : (ps : Multiset Seg) = x ::ₘ ((ps.erase x : List Seg) : Multiset Seg) := by
    have := Multiset.cons_erase (Multiset.mem_coe.mpr hx)
    simp only [Multiset.coe_erase] at this ⊢
    exact this.symm
  have h1' : ((ps.erase x : List Seg) : Multiset Seg).map Seg.ends = (v, b) ::ₘ S := by
    rw [hpx, Multiset.map_cons, hxe] at h1
    exact Multiset.cons_inj_right _ |>.mp h1
  obtain ⟨y, hfy, hy, hye⟩ := find_of_mem_ends (ps := ps.erase x) (e := (v, b)) (by rw [h1']; simp)
  have hpy : ((ps.erase x : List Seg) : Multiset Seg) =
      y ::ₘ (((ps.erase x).erase y : List Seg) : Multiset Seg) := by
    have := Multiset.cons_erase (Multiset.mem_coe.mpr hy)
    simp only [Multiset.coe_erase] at this ⊢
    exact this.symm
  have h1'' : (((ps.erase x).erase y : List Seg) : Multiset Seg).map Seg.ends = S := by
    rw [hpy, Multiset.map_cons, hye] at h1'
    exact Multiset.cons_inj_right _ |>.mp h1'
  unfold joinL
  rw [hfx]
  dsimp only
  rw [hfy]
  dsimp only
  have hxg := h2 x hx
  have hyg := h2 y (List.mem_of_mem_erase hy)
  simp only [Seg.ends, Prod.mk.injEq] at hxe hye
  obtain ⟨hxa, hxu⟩ := hxe
  obtain ⟨hyv, hyb⟩ := hye
  let z : Seg := ⟨a, b, x.p ++ y.p⟩
  have hcz : cells ((z :: (ps.erase x).erase y : List Seg) : Multiset Seg) =
      cells (ps : Multiset Seg) := by
    rw [hpx, hpy]
    simp only [← Multiset.cons_coe, cells_cons, z, ← Multiset.coe_add, add_assoc]
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
  refine ⟨?_, ?_, hcz ▸ h3, fun w => hcz ▸ h4 w⟩
  · rw [← Multiset.cons_coe, Multiset.map_cons, h1'']
    rfl
  · intro w hw
    rcases List.mem_cons.mp hw with e | e
    · exact e ▸ hzg
    · exact h2 w (List.mem_of_mem_erase (List.mem_of_mem_erase e))

/-! ### Undoing a split -/

/-- The constructive form of `split_sound`: join the crossing paths of a split. -/
def unsplit (vert : Bool) (pos : ℕ) :
    List (Kind ℕ) → List (Coord × Coord) → List (Coord × Coord) × List (Coord × Coord) →
      List Seg → List Seg
  | [], _, _, ps => ps
  | Kind.stay s :: ks, (a, b) :: ss, acc, ps => unsplit vert pos ks ss (put s (a, b) acc) ps
  | Kind.cross s y :: ks, (a, b) :: ss, acc, ps =>
    joinL a (cutc vert pos s y) (cutc vert pos (!s) y) b
      (unsplit vert pos ks ss (put (!s) (cutc vert pos (!s) y, b) (put s (a, cutc vert pos s y) acc)) ps)
  | Kind.exc s y z :: ks, (a, b) :: ss, acc, ps =>
    joinL a (cutc vert pos (!s) z) (cutc vert pos s z) b
      (joinL a (cutc vert pos s y) (cutc vert pos (!s) y) (cutc vert pos (!s) z)
        (unsplit vert pos ks ss
          (put (!s) (cutc vert pos (!s) y, cutc vert pos (!s) z)
            (put s (cutc vert pos s z, b) (put s (a, cutc vert pos s y) acc))) ps))
  | _, _, _, ps => ps

theorem unsplit_sound {A : Coord → Prop} (vert : Bool) (pos : ℕ) (hp : 1 ≤ pos) :
    ∀ (ks : List (Kind ℕ)) (ss : List (Coord × Coord)) (acc : List (Coord × Coord) × List (Coord × Coord))
      (L R : List (Coord × Coord)) (ps : List Seg), split vert pos ks ss acc = some (L, R) →
      RCW A ((L : Multiset (Coord × Coord)) + R) ps →
      RCW A ((acc.1 : Multiset (Coord × Coord)) + acc.2 + ss) (unsplit vert pos ks ss acc ps) := by
  intro ks
  induction ks with
  | nil =>
    intro ss acc L R ps h hc
    cases ss with
    | nil =>
      simp only [split, Option.some.injEq] at h
      subst h
      simpa [unsplit] using hc
    | cons e ss => simp [split] at h
  | cons k ks ih =>
    intro ss acc L R ps h hc
    cases ss with
    | nil => cases k <;> simp [split] at h
    | cons e ss =>
      obtain ⟨a, b⟩ := e
      cases k with
      | stay sa =>
        simp only [split] at h
        have := ih ss _ L R ps h hc
        rw [put_ms] at this
        have e : (a, b) ::ₘ ((acc.1 : Multiset (Coord × Coord)) + acc.2) + ss =
            (acc.1 : Multiset (Coord × Coord)) + acc.2 + ((a, b) :: ss : List _) := by
          rw [← Multiset.cons_coe, cons_ms, cons_ms]; abel
        rw [e] at this
        simpa [unsplit] using this
      | cross sa y =>
        simp only [split] at h
        have := ih ss _ L R ps h hc
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
        rw [e2] at j
        simpa [unsplit] using j
      | exc sa y z =>
        simp only [split] at h
        have := ih ss _ L R ps h hc
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
        rw [e2] at j2
        simpa [unsplit] using j2

/-! ### Building a tree -/

/-- The paths of a leaf: one cell, or an IPS path moved to the piece. -/
def leafP (P : Piece) : List Seg :=
  match P.segs with
  | [(a, b)] =>
    if eqC a b then [⟨a, a, [a]⟩]
    else [⟨a, b, (ipsP (P.pw + P.ph) P.pw P.ph (a.1 - P.ox, a.2 - P.oy) (b.1 - P.ox, b.2 - P.oy)).map
      fun v => (v.1 + P.ox, v.2 + P.oy)⟩]
  | _ => []

def buildT : CTree ℕ → Piece → List Seg
  | CTree.leaf, P => leafP P
  | CTree.cut vert pos ks l r, P =>
    match split vert pos ks P.segs ([], []) with
    | some (L, R) =>
      unsplit vert pos ks P.segs ([], []) (buildT l (P.lo vert pos L) ++ buildT r (P.hi vert pos R))
    | none => []

theorem leafP_sound (P : Piece) (h : leafOK P = true) : RCW P.region P.segs (leafP P) := by
  obtain ⟨ox, oy, pw, ph, segs⟩ := P
  match segs, h with
  | [(a, b)], h =>
    show RCW _ ({(a, b)} : Multiset _) (leafP ⟨ox, oy, pw, ph, [(a, b)]⟩)
    simp only [leafOK] at h
    unfold leafP
    dsimp only
    split_ifs at h ⊢ with hab
    · rw [eqC_iff] at hab
      simp only [Bool.and_eq_true, decide_eq_true_eq, eqC_iff] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      subst hab h3 h1 h2
      refine ⟨rfl, ?_, by simp [cells], ?_⟩
      · intro x hx
        simp only [List.mem_singleton] at hx
        subst hx
        exact ⟨rfl, rfl, rfl⟩
      · intro v
        simp only [Piece.region, cells, Multiset.coe_singleton, Multiset.singleton_bind,
          Multiset.mem_singleton]
        constructor
        · intro hv; ext <;> omega
        · rintro rfl; omega
    · rw [eqC_iff] at hab
      simp only [Bool.and_eq_true, Piece.regionB_iff, Lane.accB_eq, decide_eq_true_eq] at h
      obtain ⟨⟨ha, hb⟩, hacc⟩ := h
      unfold Piece.region at ha hb
      dsimp only at ha hb hacc ⊢
      have hv := ipsP_valid (pw + ph) pw ph (a.1 - ox, a.2 - oy) (b.1 - ox, b.2 - oy) le_rfl
        ⟨by simp; omega, by simp; omega⟩ ⟨by simp; omega, by simp; omega⟩
        (by intro e; apply hab; simp only [Prod.mk.injEq] at e; ext <;> omega) hacc
      obtain ⟨-, p1, p2, p3, p4, p5, p6⟩ := hv
      set p := ipsP (pw + ph) pw ph (a.1 - ox, a.2 - oy) (b.1 - ox, b.2 - oy)
      let f : Coord → Coord := fun v => (v.1 + ox, v.2 + oy)
      have ea : f (a.1 - ox, a.2 - oy) = a := by ext <;> simp [f] <;> omega
      have eb : f (b.1 - ox, b.2 - oy) = b := by ext <;> simp [f] <;> omega
      refine ⟨rfl, ?_, ?_, ?_⟩
      · intro x hx
        simp only [List.mem_singleton] at hx
        subst hx
        refine ⟨?_, ?_, ?_⟩
        · show (p.map f).head? = some a
          rw [List.head?_map, p1]
          exact congrArg some ea
        · show (p.map f).getLast? = some b
          rw [List.getLast?_map, p2]
          exact congrArg some eb
        · exact chainAdjacent_map_on (InBounds pw ph) f
            (fun v w _ _ hvw => by unfold Adjacent at hvw ⊢; simp only [f]; omega) p p4 p6
      · simp only [cells, Multiset.coe_singleton, Multiset.singleton_bind, Multiset.coe_nodup]
        exact p3.map_on fun v hv w hw e => by
          simp only [Prod.mk.injEq] at e
          ext <;> omega
      · intro v
        simp only [cells, Multiset.coe_singleton, Multiset.singleton_bind, Multiset.mem_coe,
          List.mem_map, Piece.region]
        constructor
        · intro hv
          refine ⟨(v.1 - ox, v.2 - oy), p5 _ ((mem_allCoords pw ph _).mpr ⟨by simp; omega,
            by simp; omega⟩), ?_⟩
          ext <;> simp <;> omega
        · rintro ⟨w, hw, rfl⟩
          have := p4 w hw
          unfold InBounds at this
          omega

/-- **A checked tree builds a witness.** -/
theorem buildT_sound : ∀ (T : CTree ℕ) (P : Piece), check T P = true →
    RCW P.region P.segs (buildT T P)
  | CTree.leaf, P, h => leafP_sound P h
  | CTree.cut vert pos ks l r, P, h => by
    simp only [check, Bool.and_eq_true] at h
    obtain ⟨hin, h⟩ := h
    unfold buildT
    match hsp : split vert pos ks P.segs ([], []), h with
    | some (L, R), h =>
      dsimp only
      simp only [Bool.and_eq_true] at h
      obtain ⟨hl, hr⟩ := h
      have cl := buildT_sound l _ hl
      have cr := buildT_sound r _ hr
      obtain ⟨hU, hD⟩ := region_split P vert pos hin L R
      have hu := cl.union cr hD
      have hp : 1 ≤ pos := by
        cases vert <;> simp only [inside, Bool.false_eq_true, ite_false, ite_true, Bool.and_eq_true,
          decide_eq_true_eq] at hin <;> omega
      rw [lo_segs, hi_segs] at hu
      have := unsplit_sound (A := fun v => (P.lo vert pos L).region v ∨ (P.hi vert pos R).region v)
        vert pos hp ks P.segs ([], []) L R _ hsp hu
      simp only [Multiset.coe_nil, zero_add] at this
      exact this.congr fun v => (hU v).symm
    | none, h => simp at h

/-! ### The solution of the root piece -/

/-- The two paths with the instance's endpoint pairs. -/
def solOf (I : Inst) (ps : List Seg) : List Coord × List Coord :=
  ((ps.find? (fun x => x.ends == (I.s0, I.t0))).elim [] Seg.p,
   (ps.find? (fun x => x.ends == (I.s1, I.t1))).elim [] Seg.p)

theorem solOf_sound {I : Inst} {ps : List Seg}
    (h : RCW (InBounds I.w I.h) {(I.s0, I.t0), (I.s1, I.t1)} ps) :
    IsSolution I (solOf I ps).1 (solOf I ps).2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨x, hfx, hx, hxe⟩ := find_of_mem_ends (ps := ps) (e := (I.s0, I.t0)) (by rw [h1]; simp)
  have hpx : (ps : Multiset Seg) = x ::ₘ ((ps.erase x : List Seg) : Multiset Seg) := by
    have := Multiset.cons_erase (Multiset.mem_coe.mpr hx)
    simp only [Multiset.coe_erase] at this ⊢
    exact this.symm
  have h1' : ((ps.erase x : List Seg) : Multiset Seg).map Seg.ends = {(I.s1, I.t1)} := by
    rw [hpx, Multiset.map_cons, hxe] at h1
    exact Multiset.cons_inj_right _ |>.mp h1
  obtain ⟨y, hy, hrest⟩ : ∃ y, ps.erase x = [y] ∧ y.ends = (I.s1, I.t1) := by
    rw [Multiset.map_coe] at h1'
    match he : ps.erase x, h1' with
    | [y], h1' =>
      exact ⟨y, rfl, by simpa using h1'⟩
    | [], h1' => simp at h1'
    | _ :: _ :: _, h1' =>
      have := congrArg Multiset.card h1'
      simp at this
  have hymem : y ∈ ps := List.mem_of_mem_erase (by rw [hy]; simp)
  have hfy : ps.find? (fun z => z.ends == (I.s1, I.t1)) = some y := by
    rcases hfind : ps.find? (fun z => z.ends == (I.s1, I.t1)) with _ | z
    · exfalso
      have := List.find?_eq_none.mp hfind y hymem
      simp [hrest] at this
    · have hz := List.mem_of_find?_eq_some hfind
      have hze : z.ends = (I.s1, I.t1) := by simpa using List.find?_some hfind
      suffices hzy : z = y by rw [hfind, hzy]
      by_contra hne
      have hzx : z = x := by
        by_contra hzx
        have : z ∈ ps.erase x := (List.mem_erase_of_ne hzx).mpr hz
        rw [hy] at this
        exact hne (List.mem_singleton.mp this)
      subst hzx
      have hc := h3
      rw [hpx, hy] at hc
      have hgx := h2 z hz
      have hgy := h2 y hymem
      simp only [cells, Multiset.coe_singleton, Multiset.cons_bind, Multiset.singleton_bind,
        Multiset.nodup_add, Multiset.coe_nodup] at hc
      obtain ⟨-, -, hdj⟩ := hc
      have hs1 : I.s1 ∈ z.p := by
        have := hgx.1
        simp only [Seg.ends, Prod.mk.injEq] at hze
        rw [← hze.1]
        exact List.mem_of_mem_head? this
      have hs1y : I.s1 ∈ y.p := by
        have := hgy.1
        simp only [Seg.ends, Prod.mk.injEq] at hrest
        rw [← hrest.1]
        exact List.mem_of_mem_head? this
      exact Multiset.disjoint_left.mp hdj (Multiset.mem_coe.mpr hs1) (Multiset.mem_coe.mpr hs1y)
  have hps : (ps : Multiset Seg) = x ::ₘ {y} := by rw [hpx, hy]; rfl
  simp only [Seg.ends, Prod.mk.injEq] at hxe hrest
  have hxg := h2 x hx
  have hyg := h2 y hymem
  have hc : cells (ps : Multiset Seg) = (x.p : Multiset Coord) + (y.p : Multiset Coord) := by
    rw [hps]; simp [cells]
  rw [hc, Multiset.nodup_add] at h3
  obtain ⟨nx, ny, hdj⟩ := h3
  have hin : ∀ v, v ∈ x.p ∨ v ∈ y.p → InBounds I.w I.h v := by
    intro v hv; apply (h4 v).mpr; rw [hc, Multiset.mem_add]; simpa using hv
  unfold solOf
  rw [hfx, hfy]
  simp only [Option.elim]
  refine ⟨⟨?_, ?_, nx, fun v hv => hin v (Or.inl hv), hxg.2.2⟩,
    ⟨?_, ?_, ny, fun v hv => hin v (Or.inr hv), hyg.2.2⟩, ?_, ?_⟩
  · rw [hxg.1, hxe.1]
  · rw [hxg.2.1, hxe.2]
  · rw [hyg.1, hrest.1]
  · rw [hyg.2.1, hrest.2]
  · intro v hv hv'
    exact Multiset.disjoint_left.mp hdj (Multiset.mem_coe.mpr hv) (Multiset.mem_coe.mpr hv')
  · intro v hv
    have := (h4 v).mp hv
    rw [hc, Multiset.mem_add] at this
    simpa using this

/-- The solution from a checked template. -/
def tsol (T : CTree TPos) (I : Inst) : List Coord × List Coord :=
  solOf I (buildT (inst (posN I.s0.1 I.t0.1 I.s1.1 I.t1.1 I.w) (posN I.s0.2 I.t0.2 I.s1.2 I.t1.2 I.h) T)
    (rootPiece I))

theorem tsol_sound {I : Inst} (T : CTree TPos) (h : tcheck T I = true) :
    IsSolution I (tsol T I).1 (tsol T I).2 := by
  have hc := buildT_sound _ _ h
  refine solOf_sound (hc.congr fun v => ?_)
  simp only [rootPiece, Piece.region, InBounds]
  omega

end ZZN.Cut

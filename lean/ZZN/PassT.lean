-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.PassStrip

/-!
# The catalogue is symmetric under transposition (`passT`)

Argument: `PROOF.md` §3 (symmetry).
-/

namespace ZZN

/-! ### Alternation of four keys is chord crossing -/

/-- The chord `k0 k1` (colour 0) crosses the chord `k2 k3` (colour 1): exactly one of `k2, k3`
lies strictly between `k0` and `k1`. -/
def Crosses (k0 k1 k2 k3 : ℕ) : Prop :=
  ((k0 < k2 ∧ k2 < k1) ∨ (k1 < k2 ∧ k2 < k0)) ↔ ¬ ((k0 < k3 ∧ k3 < k1) ∨ (k1 < k3 ∧ k3 < k0))

set_option maxHeartbeats 4000000 in
theorem alt_cross {k0 k1 k2 k3 : ℕ} (h01 : k0 ≠ k1) (h02 : k0 ≠ k2) (h03 : k0 ≠ k3)
    (h12 : k1 ≠ k2) (h13 : k1 ≠ k3) (h23 : k2 ≠ k3) :
    alternating ((sortByKey [(k0, 0), (k1, 0), (k2, 1), (k3, 1)]).map (·.2)) = true ↔
      Crosses k0 k1 k2 k3 := by
  unfold Crosses
  rcases Nat.lt_or_gt_of_ne h01 with a | a <;> rcases Nat.lt_or_gt_of_ne h02 with b | b <;>
  rcases Nat.lt_or_gt_of_ne h03 with c | c <;> rcases Nat.lt_or_gt_of_ne h12 with d | d <;>
  rcases Nat.lt_or_gt_of_ne h13 with e | e <;> rcases Nat.lt_or_gt_of_ne h23 with g | g <;>
  simp [sortByKey, alternating, a, b, c, d, e, g, Nat.lt_asymm a, Nat.lt_asymm b, Nat.lt_asymm c,
    Nat.lt_asymm d, Nat.lt_asymm e, Nat.lt_asymm g, a.le, b.le, c.le, d.le, e.le, g.le,
    Nat.not_le.mpr a, Nat.not_le.mpr b, Nat.not_le.mpr c, Nat.not_le.mpr d, Nat.not_le.mpr e,
    Nat.not_le.mpr g] <;> omega

/-- Reverse a cycle of length `n`, then rotate it so that the first `m` positions stay first. -/
def rr (m n p : ℕ) : ℕ := if p < m then m - 1 - p else m + n - 1 - p

set_option maxHeartbeats 4000000 in
theorem crosses_rr {m n k0 k1 k2 k3 : ℕ} (_hm : m ≤ n) (h0 : k0 < n) (h1 : k1 < n) (h2 : k2 < n)
    (h3 : k3 < n) (_h01 : k0 ≠ k1) (h02 : k0 ≠ k2) (h03 : k0 ≠ k3) (h12 : k1 ≠ k2) (h13 : k1 ≠ k3)
    (h23 : k2 ≠ k3) :
    Crosses (rr m n k0) (rr m n k1) (rr m n k2) (rr m n k3) ↔ Crosses k0 k1 k2 k3 := by
  unfold Crosses rr
  split_ifs <;> omega

theorem rr_inj {m n p q : ℕ} (_hm : m ≤ n) (hp : p < n) (hq : q < n) (h : p ≠ q) :
    rr m n p ≠ rr m n q := by
  unfold rr; split_ifs <;> omega

/-! ### T1 -/

theorem onPerim_swap {R C : ℕ} {p : ℕ × ℕ} (hx : p.1 < R) (hy : p.2 < C) :
    OnPerim C R p.swap ↔ OnPerim R C p := by
  unfold OnPerim; simp only [Prod.fst_swap, Prod.snd_swap]; omega

/-- The perimeter length. -/
def perimLen (R C : ℕ) : ℕ := 2 * (R - 1) + 2 * (C - 1)

theorem perimIndex_lt {R C : ℕ} (hR : 2 ≤ R) (hC : 2 ≤ C) {p : ℕ × ℕ} (hx : p.1 < R) (hy : p.2 < C) :
    (perimIndex R C p).getD 0 < perimLen R C := by
  obtain ⟨x, y⟩ := p
  unfold perimIndex perimLen
  simp only [beq_iff_eq] at hx hy ⊢
  split_ifs <;> simp only [Option.getD_some, Option.getD_none] <;> omega

theorem perimIndex_swap {R C : ℕ} (hR : 2 ≤ R) (hC : 2 ≤ C) {p : ℕ × ℕ} (hx : p.1 < R)
    (hy : p.2 < C) (hp : OnPerim R C p) :
    (perimIndex C R p.swap).getD 0 = rr 1 (perimLen R C) ((perimIndex R C p).getD 0) := by
  obtain ⟨x, y⟩ := p
  unfold OnPerim at hp
  unfold perimIndex rr perimLen
  simp only [Prod.swap_prod_mk, beq_iff_eq] at hx hy hp ⊢
  split_ifs <;> (try simp only [Option.getD_some, Option.getD_none] at *) <;> omega

theorem perimIndex_inj {R C : ℕ} (hR : 2 ≤ R) (hC : 2 ≤ C) {p q : ℕ × ℕ} (hpx : p.1 < R)
    (hpy : p.2 < C) (hqx : q.1 < R) (hqy : q.2 < C) (hp : OnPerim R C p) (hq : OnPerim R C q)
    (h : p ≠ q) : (perimIndex R C p).getD 0 ≠ (perimIndex R C q).getD 0 := by
  obtain ⟨x, y⟩ := p
  obtain ⟨u, v⟩ := q
  unfold OnPerim at hp hq
  unfold perimIndex
  simp only [ne_eq, Prod.mk.injEq, beq_iff_eq] at hpx hpy hqx hqy hp hq h ⊢
  split_ifs <;> simp only [Option.getD_some, Option.getD_none] <;> omega

/-- Four distinct cells of the grid, the endpoints of an instance. -/
structure Four (R C : ℕ) (a b c e : ℕ × ℕ) : Prop where
  inb : a.1 < R ∧ a.2 < C ∧ b.1 < R ∧ b.2 < C ∧ c.1 < R ∧ c.2 < C ∧ e.1 < R ∧ e.2 < C
  dis : a ≠ b ∧ a ≠ c ∧ a ≠ e ∧ b ≠ c ∧ b ≠ e ∧ c ≠ e

theorem t1_transpose {R C : ℕ} (hR : 2 ≤ R) (hC : 2 ≤ C) {a b c e : ℕ × ℕ} (h4 : Four R C a b c e) :
    t1Fires C R [(a.swap, 0), (b.swap, 0), (c.swap, 1), (e.swap, 1)] =
      t1Fires R C [(a, 0), (b, 0), (c, 1), (e, 1)] := by
  obtain ⟨⟨a1, a2, b1, b2, c1, c2, e1, e2⟩, ⟨dab, dac, dae, dbc, dbe, dce⟩⟩ := h4
  unfold t1Fires
  simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true,
    List.zip_cons_cons, List.zip_nil_right]
  have sw : ∀ p : ℕ × ℕ, p.1 < R → p.2 < C →
      (perimIndex C R p.swap).isSome = (perimIndex R C p).isSome := by
    intro p hx hy
    apply Bool.eq_iff_iff.mpr
    rw [perimIndex_isSome (by simpa using hy) (by simpa using hx), perimIndex_isSome hx hy,
      onPerim_swap hx hy]
  rw [sw a a1 a2, sw b b1 b2, sw c c1 c2, sw e e1 e2]
  by_cases hall : ((perimIndex R C a).isSome && (perimIndex R C b).isSome &&
      (perimIndex R C c).isSome && (perimIndex R C e).isSome) = true
  · simp only [Bool.and_eq_true] at hall
    obtain ⟨⟨⟨ha, hb⟩, hc⟩, he⟩ := hall
    rw [perimIndex_isSome a1 a2] at ha
    rw [perimIndex_isSome b1 b2] at hb
    rw [perimIndex_isSome c1 c2] at hc
    rw [perimIndex_isSome e1 e2] at he
    rw [perimIndex_swap hR hC a1 a2 ha, perimIndex_swap hR hC b1 b2 hb,
      perimIndex_swap hR hC c1 c2 hc, perimIndex_swap hR hC e1 e2 he]
    have L := fun p hx hy => perimIndex_lt (R := R) (C := C) hR hC (p := p) hx hy
    have I := fun p q hpx hpy hqx hqy hp hq h =>
      perimIndex_inj (R := R) (C := C) hR hC (p := p) (q := q) hpx hpy hqx hqy hp hq h
    have hm : 1 ≤ perimLen R C := by unfold perimLen; omega
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true]
    have := ((perimIndex R C a).isSome_iff_exists)
    rw [alt_cross (rr_inj hm (L a a1 a2) (L b b1 b2) (I a b a1 a2 b1 b2 ha hb dab))
        (rr_inj hm (L a a1 a2) (L c c1 c2) (I a c a1 a2 c1 c2 ha hc dac))
        (rr_inj hm (L a a1 a2) (L e e1 e2) (I a e a1 a2 e1 e2 ha he dae))
        (rr_inj hm (L b b1 b2) (L c c1 c2) (I b c b1 b2 c1 c2 hb hc dbc))
        (rr_inj hm (L b b1 b2) (L e e1 e2) (I b e b1 b2 e1 e2 hb he dbe))
        (rr_inj hm (L c c1 c2) (L e e1 e2) (I c e c1 c2 e1 e2 hc he dce)),
      alt_cross (I a b a1 a2 b1 b2 ha hb dab) (I a c a1 a2 c1 c2 ha hc dac)
        (I a e a1 a2 e1 e2 ha he dae) (I b c b1 b2 c1 c2 hb hc dbc) (I b e b1 b2 e1 e2 hb he dbe)
        (I c e c1 c2 e1 e2 hc he dce),
      crosses_rr hm (L a a1 a2) (L b b1 b2) (L c c1 c2) (L e e1 e2)
        (I a b a1 a2 b1 b2 ha hb dab) (I a c a1 a2 c1 c2 ha hc dac)
        (I a e a1 a2 e1 e2 ha he dae) (I b c b1 b2 c1 c2 hb hc dbc) (I b e b1 b2 e1 e2 hb he dbe)
        (I c e c1 c2 e1 e2 hc he dce)]
  · revert hall
    generalize (perimIndex R C a).isSome = A
    generalize (perimIndex R C b).isSome = B
    generalize (perimIndex R C c).isSome = Cc
    generalize (perimIndex R C e).isSome = E
    cases A <;> cases B <;> cases Cc <;> cases E <;> simp

/-! ### P, T2, L1, L6 -/

/-- Transpose the endpoints. -/
def swapPts (pts : List Pt) : List Pt := pts.map fun q => (q.1.swap, q.2)

theorem swapPts_swapPts (pts : List Pt) : swapPts (swapPts pts) = pts := by
  unfold swapPts; rw [List.map_map]; conv_rhs => rw [← List.map_id pts]
  exact List.map_congr_left (fun q _ => by simp)

theorem parityOk_transpose (R C : ℕ) (pts : List Pt) :
    parityOk C R (swapPts pts) = parityOk R C pts := by
  unfold parityOk swapPts
  rw [List.map_map, Nat.mul_comm C R]
  congr 3
  funext q
  simp only [Function.comp]
  unfold sgn
  rw [Prod.fst_swap, Prod.snd_swap, Nat.add_comm]

theorem t2_transpose (a b c e : ℕ × ℕ) :
    t2Fires [a.swap, b.swap, c.swap, e.swap] = t2Fires [a, b, c, e] := by
  unfold t2Fires
  simp only [List.map_cons, List.map_nil, Prod.fst_swap, Prod.snd_swap]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true]
  tauto

theorem l1_transpose_imp {R C : ℕ} {pts : List Pt} (h : L1Prop R C pts) :
    L1Prop C R (swapPts pts) := by
  obtain ⟨q, hq, hall⟩ := h
  refine ⟨(q.1.swap, q.2), List.mem_map.mpr ⟨q, hq, rfl⟩, fun n h1 h2 hadj => ?_⟩
  obtain ⟨e, he, hen, hc⟩ := hall n.swap h2 h1 (by
    have := adjacent_swap hadj; simpa using this)
  refine ⟨(e.1.swap, e.2), List.mem_map.mpr ⟨e, he, rfl⟩, ?_, hc⟩
  simp only [hen, Prod.swap_swap]

theorem l1_transpose (R C : ℕ) (pts : List Pt) : L1Prop C R (swapPts pts) ↔ L1Prop R C pts :=
  ⟨fun h => by have := l1_transpose_imp h; rwa [swapPts_swapPts] at this, l1_transpose_imp⟩

theorem closureAt_swap (pts : List Pt) (n1 n2 cor : ℕ × ℕ) :
    closureAt (swapPts pts) n1 n2 cor = closureAt pts n1.swap n2.swap cor.swap := by
  apply closureAt_rel
  unfold swapPts
  apply forall2_map_self
  intro q _
  refine ⟨rfl, ?_, ?_, ?_⟩ <;>
  · constructor
    · intro h; rw [← h]; simp
    · intro h; rw [h]; simp

theorem closureAt_comm (pts : List Pt) (n1 n2 cor : ℕ × ℕ) :
    closureAt pts n1 n2 cor = closureAt pts n2 n1 cor := by
  unfold closureAt
  cases pts.find? (·.1 == n1) with
  | none => cases pts.find? (·.1 == n2) <;> rfl
  | some a =>
    cases pts.find? (·.1 == n2) with
    | none => rfl
    | some b =>
      simp only
      by_cases hab : a.2 = b.2
      · rw [hab]
      · have h1 : (a.2 == b.2) = false := by rw [beq_eq_false_iff_ne]; exact hab
        have h2 : (b.2 == a.2) = false := by rw [beq_eq_false_iff_ne]; exact fun e => hab e.symm
        simp only [h1, h2, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

theorem l6_transpose {R C : ℕ} (hR : 2 ≤ R) (hC : 2 ≤ C) (pts : List Pt) :
    l6Fires C R (swapPts pts) = l6Fires R C pts := by
  unfold l6Fires
  rw [l6Closures_eq hC hR, l6Closures_eq hR hC, Nat.mul_comm C R]
  unfold l6List
  simp only [closureAt_swap, Prod.swap_prod_mk]
  rw [closureAt_comm pts (1, 0), closureAt_comm pts (R - 2, 0), closureAt_comm pts (1, C - 1),
    closureAt_comm pts (R - 2, C - 1)]
  generalize closureAt pts (0, 1) (1, 0) (0, 0) = o1
  generalize closureAt pts (0, C - 2) (1, C - 1) (0, C - 1) = o2
  generalize closureAt pts (R - 1, 1) (R - 2, 0) (R - 1, 0) = o3
  generalize closureAt pts (R - 1, C - 2) (R - 2, C - 1) (R - 1, C - 1) = o4
  have key : ∀ x : ℕ, ([o1, o3, o2, o4].filterMap id).contains x =
      ([o1, o2, o3, o4].filterMap id).contains x := by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [List.contains_iff_mem, List.mem_filterMap, List.mem_cons, List.not_mem_nil,
      or_false, id]
    constructor <;> rintro ⟨o, ho, hx⟩ <;> exact ⟨o, by tauto, hx⟩
  rw [key 0, key 1]

/-! ### The frame entries -/

/-- The frame of the transposed instance that gives the same view. -/
def Frame.tp (f : Frame) : Frame := ⟨f.fc, f.fr, !f.tr⟩

theorem to_tp (R C : ℕ) (f : Frame) (p : ℕ × ℕ) : f.tp.to C R p.swap = f.to R C p := by
  obtain ⟨fr, fc, tr⟩ := f
  cases tr <;> simp [Frame.tp, Frame.to]

theorem makeView_tp (R C : ℕ) (f : Frame) (pts : List Pt) :
    makeView C R f.tp (swapPts pts) = makeView R C f pts := by
  unfold makeView swapPts
  rw [List.map_map]
  have e : ((fun q : Pt => (f.tp.to C R q.1, q.2)) ∘ fun q : Pt => (q.1.swap, q.2)) =
      fun q => (f.to R C q.1, q.2) := funext fun q => by simp [to_tp]
  have hH : f.tp.H C R = f.H R C := by
    obtain ⟨fr, fc, tr⟩ := f; cases tr <;> rfl
  have hW : f.tp.W C R = f.W R C := by
    obtain ⟨fr, fc, tr⟩ := f; cases tr <;> rfl
  rw [e, hH, hW]

theorem frameFires_tp (R C : ℕ) (f : Frame) (pts : List Pt) :
    frameFires C R (swapPts pts) f.tp = frameFires R C pts f := by
  unfold frameFires
  rw [makeView_tp]
  have hb : boundaryOnly C R f.tp (swapPts pts) = boundaryOnly R C f pts := by
    unfold boundaryOnly swapPts
    rw [List.map_map]
    have e : ((fun q : Pt => (f.tp.to C R q.1, q.2)) ∘ fun q : Pt => (q.1.swap, q.2)) =
        fun q => (f.to R C q.1, q.2) := funext fun q => by simp [to_tp]
    have hH : f.tp.H C R = f.H R C := by
      obtain ⟨fr, fc, tr⟩ := f; cases tr <;> rfl
    have hW : f.tp.W C R = f.W R C := by
      obtain ⟨fr, fc, tr⟩ := f; cases tr <;> rfl
    rw [e, hH, hW, Bool.and_comm (C % 2 == 1)]
  have hc : corner4 C R f.tp (swapPts pts) = corner4 R C f pts := by
    unfold corner4 swapPts
    rw [Nat.mul_comm C R, List.filter_map, List.filter_map, List.map_map, List.map_map]
    have e : ((fun q : Pt => f.tp.to C R q.1) ∘ fun q : Pt => (q.1.swap, q.2)) =
        fun q => f.to R C q.1 := funext fun q => by simp [to_tp]
    have e2 : ∀ k : ℕ, ((fun q : Pt => q.2 == k) ∘ fun q : Pt => (q.1.swap, q.2)) =
        fun q => q.2 == k := fun k => rfl
    rw [e2, e2, e]
  rw [hb, hc]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  tauto

theorem tp_tp (f : Frame) : f.tp.tp = f := by
  obtain ⟨fr, fc, tr⟩ := f; simp [Frame.tp]

theorem frames_any_tp (R C : ℕ) (pts : List Pt) :
    frames.any (frameFires C R (swapPts pts)) = frames.any (frameFires R C pts) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨f, -, hf⟩
    refine ⟨f.tp, mem_frames _, ?_⟩
    have := frameFires_tp C R f (swapPts pts)
    rw [swapPts_swapPts] at this
    rw [this]; exact hf
  · rintro ⟨f, -, hf⟩
    exact ⟨f.tp, mem_frames _, by rw [frameFires_tp]; exact hf⟩

/-! ### Assembly, given the R test -/

theorem l1Fires_transpose (R C : ℕ) (pts : List Pt) :
    l1Fires C R (swapPts pts) = l1Fires R C pts :=
  Bool.eq_iff_iff.mpr (by rw [l1Fires_iff, l1Fires_iff, l1_transpose])

/-- Every entry but R is symmetric; so passing is, once R is. -/
theorem fires3_transpose {I : Inst} (hI : InDom I)
    (hR : effAlt3 I.h I.w (swapPts [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)]) =
      effAlt3 I.w I.h [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)]) :
    fires3 I.h I.w I.s0.swap I.t0.swap I.s1.swap I.t1.swap = fires3 I.w I.h I.s0 I.t0 I.s1 I.t1 := by
  obtain ⟨hw, hh, b0, b1, b2, b3, d1, d2, d3, d4, d5, d6⟩ := hI
  have h4 : Four I.w I.h I.s0 I.t0 I.s1 I.t1 :=
    ⟨⟨b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2⟩, ⟨d1, d2, d3, d4, d5, d6⟩⟩
  have e : ([(I.s0.swap, 0), (I.t0.swap, 0), (I.s1.swap, 1), (I.t1.swap, 1)] : List Pt) =
      swapPts [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)] := rfl
  unfold fires3
  simp only
  rw [t1_transpose (by omega) (by omega) h4, t2_transpose, e, parityOk_transpose,
    l1Fires_transpose, l6_transpose (by omega) (by omega), frames_any_tp, hR]

end ZZN

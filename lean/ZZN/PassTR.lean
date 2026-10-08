-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.PassT

/-!
# `passT`: the R test is symmetric under transposition

Argument: `PROOF.md` §3 (symmetry).
-/

namespace ZZN

/-! ### One rewrite step on the transposed instance -/

def swapSt (st : RWState) : RWState := ⟨swapPts st.eff, st.removed.map Prod.swap, st.any⟩

theorem back_tp (R C : ℕ) (f : Frame) (a : ℕ × ℕ) : f.tp.back C R a = (f.back R C a).swap := by
  obtain ⟨fr, fc, tr⟩ := f
  cases tr <;> simp [Frame.tp, Frame.back]

theorem findIdx_swap (a : ℕ × ℕ) : ∀ l : List Pt,
    (swapPts l).findIdx? (fun q => q.1 == a.swap) = l.findIdx? (fun q => q.1 == a)
  | [] => rfl
  | q :: l => by
    have ih := findIdx_swap a l
    simp only [swapPts, List.map_cons, List.findIdx?_cons] at ih ⊢
    have e : (q.1.swap == a.swap) = (q.1 == a) := by
      by_cases h : q.1 = a
      · simp [h]
      · have : q.1.swap ≠ a.swap := fun e => h (Prod.swap_injective e)
        simp [h, this]
    rw [e, ih]

theorem moveFirst_swap (e : List Pt) (m : (ℕ × ℕ) × (ℕ × ℕ)) :
    moveFirst (swapPts e) (m.1.swap, m.2.swap) = swapPts (moveFirst e m) := by
  unfold moveFirst
  simp only
  rw [findIdx_swap]
  cases e.findIdx? (fun q => q.1 == m.1) with
  | none => rfl
  | some i =>
    simp only [swapPts]
    exact (map_modify (fun q : Pt => (q.1.swap, q.2)) (fun q => (m.2, q.2))
      (fun q => (m.2.swap, q.2)) (fun x => rfl) e i).symm

theorem foldl_moveFirst_swap : ∀ (moves : List ((ℕ × ℕ) × (ℕ × ℕ))) (e : List Pt),
    (moves.map fun m => (m.1.swap, m.2.swap)).foldl moveFirst (swapPts e) =
      swapPts (moves.foldl moveFirst e)
  | [], _ => rfl
  | m :: ms, e => by
    simp only [List.map_cons, List.foldl_cons]
    rw [moveFirst_swap, foldl_moveFirst_swap ms]

theorem contains_swap (l : List (ℕ × ℕ)) (x : ℕ × ℕ) :
    (l.map Prod.swap).contains x.swap = l.contains x := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨y, hy, he⟩; rw [← Prod.swap_injective he]; exact hy
  · intro h; exact ⟨x, h, rfl⟩

theorem rwStep_tp (R C : ℕ) (st : RWState) (f : Frame) :
    rwStep C R (swapSt st) f.tp = swapSt (rwStep R C st f) := by
  unfold rwStep swapSt
  simp only
  rw [makeView_tp]
  cases hrw : rewritesAt (makeView R C f st.eff) with
  | none => rfl
  | some rw =>
    have ec : rw.removed.map (f.tp.back C R) = (rw.removed.map (f.back R C)).map Prod.swap := by
      rw [List.map_map]; exact List.map_congr_left (fun a _ => back_tp R C f a)
    have em : (rw.moves.map fun m => (f.tp.back C R m.1, f.tp.back C R m.2)) =
        (rw.moves.map fun m => (f.back R C m.1, f.back R C m.2)).map
          (fun m => (m.1.swap, m.2.swap)) := by
      rw [List.map_map]
      exact List.map_congr_left (fun m _ => by simp [Function.comp, back_tp])
    dsimp only
    rw [ec, em, List.any_map, List.any_map, foldl_moveFirst_swap]
    simp only [List.any_map, Function.comp_def, contains_swap]
    split_ifs <;> simp [List.map_append]

theorem foldl_rwStep_tp (R C : ℕ) : ∀ (fs : List Frame) (st : RWState),
    (fs.map Frame.tp).foldl (rwStep C R) (swapSt st) = swapSt (fs.foldl (rwStep R C) st)
  | [], _ => rfl
  | f :: fs, st => by
    simp only [List.map_cons, List.foldl_cons]
    rw [rwStep_tp, foldl_rwStep_tp R C fs]

/-- The frame order of the transposed instance, read as frames of the original. -/
theorem frames_tp : frames = (frames.map Frame.tp).map Frame.tp := by
  rw [List.map_map]
  conv_lhs => rw [← List.map_id frames]
  exact List.map_congr_left (fun f _ => (tp_tp f).symm)

theorem rewriteAll_tp (R C : ℕ) (pts : List Pt) :
    rewriteAll C R (swapPts pts) =
      swapSt ((frames.map Frame.tp).foldl (rwStep R C) ⟨pts, [], false⟩) := by
  unfold rewriteAll
  rw [frames_tp, ← foldl_rwStep_tp]
  rfl

/-! ### Moves, as membership -/

def cellsOf (l : List Pt) : List (ℕ × ℕ) := l.map (·.1)

theorem moveFirst_nil (m : (ℕ × ℕ) × (ℕ × ℕ)) : moveFirst [] m = [] := rfl

theorem moveFirst_cons (q : Pt) (l : List Pt) (m : (ℕ × ℕ) × (ℕ × ℕ)) :
    moveFirst (q :: l) m = if q.1 = m.1 then (m.2, q.2) :: l else q :: moveFirst l m := by
  unfold moveFirst
  simp only [List.findIdx?_cons]
  by_cases h : q.1 = m.1
  · simp [h]
  · have : (q.1 == m.1) = false := by simpa using h
    simp only [this, Bool.false_eq_true, ↓reduceIte, h]
    cases l.findIdx? (fun q => q.1 == m.1) with
    | none => rfl
    | some i => simp

/-- Membership after a move: the endpoint at `m.1` (if any) is now at `m.2`. -/
def mvP (P : Pt → Prop) (m : (ℕ × ℕ) × (ℕ × ℕ)) : Pt → Prop :=
  fun q => (P q ∧ q.1 ≠ m.1) ∨ (∃ col, P (m.1, col) ∧ q = (m.2, col))

theorem mem_moveFirst_iff : ∀ {l : List Pt} (m : (ℕ × ℕ) × (ℕ × ℕ)), (cellsOf l).Nodup →
    ∀ q, (q ∈ moveFirst l m ↔ mvP (· ∈ l) m q)
  | [], m, _, q => by simp [moveFirst_nil, mvP]
  | x :: l, m, hn, q => by
    rw [moveFirst_cons]
    simp only [cellsOf, List.map_cons, List.nodup_cons, List.mem_map] at hn
    obtain ⟨hx, hn⟩ := hn
    have ih := mem_moveFirst_iff (l := l) m hn q
    unfold mvP at ih ⊢
    split_ifs with h
    · -- `x` is the unique endpoint at `m.1`
      have nl : ∀ y ∈ l, y.1 ≠ m.1 := fun y hy e => hx ⟨y, hy, e.trans h.symm⟩
      simp only [List.mem_cons]
      constructor
      · rintro (rfl | hq)
        · exact Or.inr ⟨x.2, Or.inl (by rw [← h]), rfl⟩
        · exact Or.inl ⟨Or.inr hq, nl q hq⟩
      · rintro (⟨rfl | hq, hne⟩ | ⟨col, rfl | hc, rfl⟩)
        · exact absurd h hne
        · exact Or.inr hq
        · exact Or.inl rfl
        · exact absurd rfl (nl _ hc)
    · simp only [List.mem_cons]
      rw [ih]
      constructor
      · rintro (rfl | (⟨hq, hne⟩ | ⟨col, hc, rfl⟩))
        · exact Or.inl ⟨Or.inl rfl, h⟩
        · exact Or.inl ⟨Or.inr hq, hne⟩
        · exact Or.inr ⟨col, Or.inr hc, rfl⟩
      · rintro (⟨rfl | hq, hne⟩ | ⟨col, rfl | hc, rfl⟩)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨hq, hne⟩)
        · exact absurd rfl h
        · exact Or.inr (Or.inr ⟨col, hc, rfl⟩)

theorem cells_moveFirst_sub : ∀ {l : List Pt} (m : (ℕ × ℕ) × (ℕ × ℕ)) (x : ℕ × ℕ),
    x ∈ cellsOf (moveFirst l m) → x ∈ cellsOf l ∨ x = m.2
  | [], m, x, h => by simp [moveFirst_nil, cellsOf] at h
  | y :: l, m, x, h => by
    rw [moveFirst_cons] at h
    split_ifs at h
    · simp only [cellsOf, List.map_cons, List.mem_cons] at h ⊢
      rcases h with rfl | h
      · exact Or.inr rfl
      · exact Or.inl (Or.inr h)
    · simp only [cellsOf, List.map_cons, List.mem_cons] at h ⊢
      rcases h with rfl | h
      · exact Or.inl (Or.inl rfl)
      · rcases cells_moveFirst_sub m x h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'

theorem nodup_moveFirst : ∀ {l : List Pt} (m : (ℕ × ℕ) × (ℕ × ℕ)), (cellsOf l).Nodup →
    m.2 ∉ cellsOf l → (cellsOf (moveFirst l m)).Nodup
  | [], m, _, _ => by simp [moveFirst_nil, cellsOf]
  | y :: l, m, hn, hf => by
    rw [moveFirst_cons]
    simp only [cellsOf, List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hn hf
    split_ifs
    · simp only [cellsOf, List.map_cons, List.nodup_cons]
      exact ⟨hf.2, hn.2⟩
    · simp only [cellsOf, List.map_cons, List.nodup_cons]
      refine ⟨fun hy => ?_, nodup_moveFirst m hn.2 hf.2⟩
      rcases cells_moveFirst_sub m y.1 hy with h | h
      · exact hn.1 h
      · exact hf.1 h.symm

/-- Moves with fresh targets: each target is distinct from the other targets and sources, and
not occupied. -/
def Fresh (l : List Pt) (M : List ((ℕ × ℕ) × (ℕ × ℕ))) : Prop :=
  (∀ m ∈ M, m.2 ∉ cellsOf l) ∧ M.Pairwise (fun m m' => m.2 ≠ m'.2 ∧ m.2 ≠ m'.1 ∧ m'.2 ≠ m.1)

theorem foldl_moveFirst_mem : ∀ (M : List ((ℕ × ℕ) × (ℕ × ℕ))) {l : List Pt}, (cellsOf l).Nodup →
    Fresh l M → (cellsOf (M.foldl moveFirst l)).Nodup ∧
      ∀ q, (q ∈ M.foldl moveFirst l ↔ M.foldl mvP (· ∈ l) q)
  | [], l, hn, _ => ⟨hn, fun q => Iff.rfl⟩
  | m :: M, l, hn, ⟨hf, hp⟩ => by
    simp only [List.foldl_cons]
    rw [List.pairwise_cons] at hp
    have hn' := nodup_moveFirst m hn (hf m List.mem_cons_self)
    have hf' : Fresh (moveFirst l m) M := by
      refine ⟨fun m' hm' hc => ?_, hp.2⟩
      rcases cells_moveFirst_sub m _ hc with h | h
      · exact hf m' (List.mem_cons_of_mem _ hm') h
      · exact (hp.1 m' hm').1 h.symm
    obtain ⟨ih1, ih2⟩ := foldl_moveFirst_mem M hn' hf'
    refine ⟨ih1, fun q => (ih2 q).trans ?_⟩
    have e : (· ∈ moveFirst l m) = mvP (· ∈ l) m := funext fun q => propext (mem_moveFirst_iff m hn q)
    rw [e]

/-! ### The three rewrites -/

def rw3 : Rewrite := ⟨[(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0), (1, 2), (2, 1)],
  [((1, 2), (0, 3)), ((2, 1), (3, 0))]⟩
def rw2 : Rewrite := ⟨[(0, 0), (0, 1), (1, 0), (1, 1)], [((0, 0), (0, 2)), ((1, 1), (2, 0))]⟩
def rw1 : Rewrite := ⟨[(0, 0), (0, 1)], [((0, 1), (1, 0))]⟩

def c3 (v : View) : Bool :=
  (match v.at 1 2, v.at 2 1 with | some x, some y => x != y | _, _ => false) && decide (v.H ≥ 4) &&
    decide (v.W ≥ 4) && v.empty [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (2, 0), (3, 0)]
def c2 (v : View) : Bool :=
  (match v.at 0 0 with | some a => v.at 1 1 == some a | none => false) && decide (v.H ≥ 3) &&
    decide (v.W ≥ 3) && v.empty [(0, 1), (1, 0), (0, 2), (2, 0)]
def c1 (v : View) : Bool := (v.at 0 1).isSome && v.empty [(0, 0), (1, 0)] && decide (v.H ≥ 2)

theorem rewritesAt_eq (v : View) : rewritesAt v =
    if c3 v then some rw3 else if c2 v then some rw2 else if c1 v then some rw1 else none := rfl

theorem empty_iff (v : View) (l : List (ℕ × ℕ)) :
    v.empty l = true ↔ ∀ x ∈ l, v.at x.1 x.2 = none := by
  unfold View.empty; simp [Option.isNone_iff_eq_none]

theorem rewritesAt_cases {v : View} {rw : Rewrite} (h : rewritesAt v = some rw) :
    (rw = rw3 ∧ v.at 0 3 = none ∧ v.at 3 0 = none) ∨
    (rw = rw2 ∧ v.at 0 2 = none ∧ v.at 2 0 = none ∧ ∃ a, v.at 0 0 = some a ∧ v.at 1 1 = some a) ∨
    (rw = rw1 ∧ v.at 1 0 = none) := by
  rw [rewritesAt_eq] at h
  split_ifs at h with h3 h2 h1 <;> simp only [Option.some.injEq] at h <;> subst h
  · left
    unfold c3 at h3
    simp only [Bool.and_eq_true] at h3
    obtain ⟨-, he⟩ := h3
    rw [empty_iff] at he
    exact ⟨rfl, he (0, 3) (by simp), he (3, 0) (by simp)⟩
  · right; left
    unfold c2 at h2
    simp only [Bool.and_eq_true] at h2
    obtain ⟨⟨⟨hm, -⟩, -⟩, he⟩ := h2
    rw [empty_iff] at he
    refine ⟨rfl, he (0, 2) (by simp), he (2, 0) (by simp), ?_⟩
    cases ha : v.at 0 0 with
    | none => rw [ha] at hm; simp at hm
    | some a => rw [ha] at hm; exact ⟨a, rfl, by simpa using hm⟩
  · right; right
    unfold c1 at h1
    simp only [Bool.and_eq_true] at h1
    obtain ⟨⟨-, he⟩, -⟩ := h1
    rw [empty_iff] at he
    exact ⟨rfl, he (1, 0) (by simp)⟩

/-- Every rewrite settles the corner cell. -/
theorem corner_mem_removed {v : View} {rw : Rewrite} (h : rewritesAt v = some rw) :
    (0, 0) ∈ rw.removed := by
  rcases rewritesAt_cases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide

/-! ### The transposed view -/

def View.tp (v : View) : View := ⟨v.W, v.H, v.pts.map fun q => (q.1.swap, q.2)⟩

theorem at_tp (v : View) (r c : ℕ) : v.tp.at r c = v.at c r := by
  unfold View.at View.tp
  rw [List.find?_map, Option.map_map]
  have hp : ((fun q : Pt => q.1 == (r, c)) ∘ fun q : Pt => (q.1.swap, q.2)) =
      fun q => q.1 == (c, r) := by
    funext q
    simp only [Function.comp]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    constructor
    · intro h; rw [← Prod.swap_swap q.1, h]; rfl
    · intro h; rw [h]; rfl
  rw [hp]
  rfl

theorem makeView_flip (R C : ℕ) (fr fc tr : Bool) (pts : List Pt) :
    makeView R C ⟨fr, fc, !tr⟩ pts = (makeView R C ⟨fr, fc, tr⟩ pts).tp := by
  unfold makeView View.tp
  rw [List.map_map]
  cases tr <;> simp [Frame.H, Frame.W, Frame.to, Function.comp]

theorem c3_tp (v : View) : c3 v.tp = c3 v := by
  unfold c3
  rw [at_tp, at_tp]
  have he : v.tp.empty [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (2, 0), (3, 0)] =
      v.empty [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (2, 0), (3, 0)] := by
    apply Bool.eq_iff_iff.mpr
    simp only [empty_iff, at_tp, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq]
    tauto
  rw [he]
  simp only [View.tp]
  cases v.at 1 2 <;> cases v.at 2 1 <;>
    simp [bne_comm, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc]

theorem c2_tp (v : View) : c2 v.tp = c2 v := by
  unfold c2
  rw [at_tp, at_tp]
  have he : v.tp.empty [(0, 1), (1, 0), (0, 2), (2, 0)] = v.empty [(0, 1), (1, 0), (0, 2), (2, 0)] := by
    apply Bool.eq_iff_iff.mpr
    simp only [empty_iff, at_tp, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq]
    tauto
  rw [he]
  simp only [View.tp]
  simp [Bool.and_comm, Bool.and_left_comm]

theorem c1_tp_excl (v : View) (h : c1 v = true) (h' : c1 v.tp = true) : False := by
  unfold c1 at h h'
  rw [at_tp] at h'
  simp only [Bool.and_eq_true, empty_iff, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, at_tp] at h h'
  obtain ⟨⟨hs, -, -⟩, -⟩ := h
  obtain ⟨⟨-, -, hn⟩, -⟩ := h'
  rw [hn] at hs
  simp at hs

/-- If both orientations of a corner can rewrite, they use the same rule, R3 or R2. -/
theorem rewritesAt_both {v : View} {rw rw' : Rewrite} (h : rewritesAt v = some rw)
    (h' : rewritesAt v.tp = some rw') : (rw = rw3 ∧ rw' = rw3) ∨ (rw = rw2 ∧ rw' = rw2) := by
  rw [rewritesAt_eq] at h h'
  rw [c3_tp, c2_tp] at h'
  split_ifs at h h' with a b c d <;> simp only [Option.some.injEq] at h h' <;>
    subst h h' <;> simp
  exact absurd (c1_tp_excl v c d) id

/-! ### Corner windows -/

/-- The cell is in the grid and in the 4 × 4 window of corner `(fr, fc)`. -/
def Win (R C : ℕ) (fr fc : Bool) (x : ℕ × ℕ) : Prop :=
  x.1 < R ∧ x.2 < C ∧ (if fr then R - 1 - x.1 else x.1) ≤ 3 ∧ (if fc then C - 1 - x.2 else x.2) ≤ 3

theorem back_win {R C : ℕ} (hR : 4 ≤ R) (hC : 4 ≤ C) (f : Frame) {a : ℕ × ℕ} (h1 : a.1 ≤ 3)
    (h2 : a.2 ≤ 3) : Win R C f.fr f.fc (f.back R C a) := by
  obtain ⟨fr, fc, tr⟩ := f
  unfold Win Frame.back
  cases fr <;> cases fc <;> cases tr <;> simp <;> omega

theorem back_inj {R C : ℕ} (hR : 4 ≤ R) (hC : 4 ≤ C) (f : Frame) {a b : ℕ × ℕ} (ha1 : a.1 ≤ 3)
    (ha2 : a.2 ≤ 3) (hb1 : b.1 ≤ 3) (hb2 : b.2 ≤ 3) (h : f.back R C a = f.back R C b) : a = b := by
  obtain ⟨fr, fc, tr⟩ := f
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only at ha1 ha2 hb1 hb2
  unfold Frame.back at h
  cases fr <;> cases fc <;> cases tr <;> simp at h <;> simp only [Prod.mk.injEq] <;> omega

/-- In the window, `to` inverts `back`. -/
theorem to_eq_iff_back {R C : ℕ} (hR : 4 ≤ R) (hC : 4 ≤ C) (f : Frame) {a q : ℕ × ℕ}
    (h1 : a.1 ≤ 3) (h2 : a.2 ≤ 3) (hq1 : q.1 < R) (hq2 : q.2 < C) :
    f.to R C q = a ↔ q = f.back R C a := by
  obtain ⟨fr, fc, tr⟩ := f
  obtain ⟨a1, a2⟩ := a
  obtain ⟨q1, q2⟩ := q
  simp only at h1 h2 hq1 hq2
  unfold Frame.to Frame.back
  cases fr <;> cases fc <;> cases tr <;> simp only [Prod.mk.injEq] <;> simp <;> omega

/-- Different corners have disjoint windows. -/
theorem win_disj {R C : ℕ} (hR : 8 ≤ R) (hC : 8 ≤ C) {fr fc fr' fc' : Bool} {x : ℕ × ℕ}
    (h : Win R C fr fc x) (h' : Win R C fr' fc' x) : fr = fr' ∧ fc = fc' := by
  unfold Win at h h'
  cases fr <;> cases fc <;> cases fr' <;> cases fc' <;> simp at h h' ⊢ <;> omega

/-! ### Rewrite states -/

/-- Endpoints on distinct cells of the grid. -/
def Good (R C : ℕ) (st : RWState) : Prop :=
  (cellsOf st.eff).Nodup ∧ ∀ q ∈ st.eff, q.1.1 < R ∧ q.1.2 < C

theorem cell_unique {l : List Pt} (hn : (cellsOf l).Nodup) {q q' : Pt} (hq : q ∈ l) (hq' : q' ∈ l)
    (h : q.1 = q'.1) : q = q' :=
  List.inj_on_of_nodup_map hn hq hq' h

theorem find_cell_iff {l : List Pt} (hn : (cellsOf l).Nodup) (x : ℕ × ℕ) (q : Pt) :
    l.find? (fun q => q.1 == x) = some q ↔ q ∈ l ∧ q.1 = x := by
  constructor
  · intro h
    exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩
  · rintro ⟨hq, rfl⟩
    cases hf : l.find? (fun q' => q'.1 == q.1) with
    | none =>
      rw [List.find?_eq_none] at hf
      exact absurd (by simp) (hf q hq)
    | some y =>
      have hy := List.mem_of_find?_eq_some hf
      have hy1 : y.1 = q.1 := by simpa using List.find?_some hf
      rw [cell_unique hn hy hq hy1]

/-- The view of a frame, at a window cell, reads the endpoint on the corresponding grid cell. -/
theorem view_at_back {R C : ℕ} (hR : 4 ≤ R) (hC : 4 ≤ C) {st : RWState} (hg : Good R C st)
    (f : Frame) {a : ℕ × ℕ} (h1 : a.1 ≤ 3) (h2 : a.2 ≤ 3) :
    (makeView R C f st.eff).at a.1 a.2 =
      (st.eff.find? (fun q => q.1 == f.back R C a)).map (·.2) := by
  unfold View.at makeView
  simp only [List.find?_map, Option.map_map]
  congr 1
  apply find?_congr_mem
  intro q hq
  simp only [Function.comp]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact to_eq_iff_back hR hC f h1 h2 (hg.2 q hq).1 (hg.2 q hq).2

/-- The decision of one rewrite step: the cells it settles and the moves it makes. -/
def rwDec (R C : ℕ) (st : RWState) (f : Frame) :
    Option (List (ℕ × ℕ) × List ((ℕ × ℕ) × (ℕ × ℕ))) :=
  match rewritesAt (makeView R C f st.eff) with
  | none => none
  | some rw =>
    let cells := rw.removed.map (f.back R C)
    let moves := rw.moves.map fun (a, b) => (f.back R C a, f.back R C b)
    if cells.any (fun x => st.removed.contains x) then none
    else if moves.any (fun m => st.removed.contains m.2) then none
    else some (cells, moves)

def applyDec (st : RWState) : Option (List (ℕ × ℕ) × List ((ℕ × ℕ) × (ℕ × ℕ))) → RWState
  | none => st
  | some (K, M) => ⟨M.foldl moveFirst st.eff, st.removed ++ K, true⟩

theorem rwStep_dec (R C : ℕ) (st : RWState) (f : Frame) :
    rwStep R C st f = applyDec st (rwDec R C st f) := by
  unfold rwStep rwDec
  cases rewritesAt (makeView R C f st.eff) with
  | none => rfl
  | some rw =>
    dsimp only
    split_ifs <;> rfl

/-- Two states agree on a corner window. -/
def AgreeW (R C : ℕ) (fr fc : Bool) (st st' : RWState) : Prop :=
  (∀ q : Pt, Win R C fr fc q.1 → (q ∈ st.eff ↔ q ∈ st'.eff)) ∧
    (∀ x, Win R C fr fc x → (x ∈ st.removed ↔ x ∈ st'.removed))

theorem find_agree {R C : ℕ} {fr fc : Bool} {l l' : List Pt} (hn : (cellsOf l).Nodup)
    (hn' : (cellsOf l').Nodup) (h : ∀ q : Pt, Win R C fr fc q.1 → (q ∈ l ↔ q ∈ l'))
    {x : ℕ × ℕ} (hx : Win R C fr fc x) :
    l.find? (fun q => q.1 == x) = l'.find? (fun q => q.1 == x) := by
  apply Option.ext
  intro q
  rw [find_cell_iff hn, find_cell_iff hn']
  constructor
  · rintro ⟨hq, rfl⟩; exact ⟨(h q hx).mp hq, rfl⟩
  · rintro ⟨hq, rfl⟩; exact ⟨(h q hx).mpr hq, rfl⟩

theorem dec_congr {R C : ℕ} (hR : 4 ≤ R) (hC : 4 ≤ C) {st st' : RWState} (hg : Good R C st)
    (hg' : Good R C st') (f : Frame) (h : AgreeW R C f.fr f.fc st st') :
    rwDec R C st f = rwDec R C st' f := by
  have hv : rewritesAt (makeView R C f st'.eff) = rewritesAt (makeView R C f st.eff) := by
    apply rewritesAt_congr
    · intro r c hr hc
      rw [view_at_back hR hC hg' f (a := (r, c)) hr hc, view_at_back hR hC hg f (a := (r, c)) hr hc,
        find_agree hg.1 hg'.1 h.1 (back_win hR hC f hr hc)]
    all_goals (simp only [makeView, Frame.H, Frame.W]; split_ifs <;> omega)
  unfold rwDec
  rw [hv]
  cases hrw : rewritesAt (makeView R C f st.eff) with
  | none => rfl
  | some rw =>
    obtain ⟨hs1, hs2⟩ := rewritesAt_small hrw
    have c1 : (rw.removed.map (f.back R C)).any (fun x => st.removed.contains x) =
        (rw.removed.map (f.back R C)).any (fun x => st'.removed.contains x) := by
      rw [List.any_map, List.any_map]
      apply any_congr'
      intro a ha
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp, List.contains_iff_mem]
      exact h.2 _ (back_win hR hC f (hs1 a ha).1 (hs1 a ha).2)
    have c2 : (rw.moves.map fun m => (f.back R C m.1, f.back R C m.2)).any
          (fun m => st.removed.contains m.2) =
        (rw.moves.map fun m => (f.back R C m.1, f.back R C m.2)).any
          (fun m => st'.removed.contains m.2) := by
      rw [List.any_map, List.any_map]
      apply any_congr'
      intro m hm
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp, List.contains_iff_mem]
      exact h.2 _ (back_win hR hC f (hs2 m hm).2.2.1 (hs2 m hm).2.2.2)
    dsimp only
    rw [c1, c2]

/-! ### What a firing step does -/

theorem dec_some {R C : ℕ} {st : RWState} {f : Frame} {K : List (ℕ × ℕ)}
    {M : List ((ℕ × ℕ) × (ℕ × ℕ))} (h : rwDec R C st f = some (K, M)) :
    ∃ rw, rewritesAt (makeView R C f st.eff) = some rw ∧ K = rw.removed.map (f.back R C) ∧
      M = rw.moves.map (fun m => (f.back R C m.1, f.back R C m.2)) := by
  unfold rwDec at h
  cases hrw : rewritesAt (makeView R C f st.eff) with
  | none => rw [hrw] at h; simp at h
  | some rw =>
    rw [hrw] at h
    dsimp only at h
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨rw, rfl, h.1.symm, h.2.symm⟩

/-- When nothing is settled in the window, the step is not blocked. -/
theorem dec_free {R C : ℕ} (hR : 4 ≤ R) (hC : 4 ≤ C) {st : RWState} {f : Frame}
    (hfree : ∀ x ∈ st.removed, ¬ Win R C f.fr f.fc x) :
    rwDec R C st f = (rewritesAt (makeView R C f st.eff)).map
      (fun rw => (rw.removed.map (f.back R C), rw.moves.map (fun m => (f.back R C m.1, f.back R C m.2)))) := by
  unfold rwDec
  cases hrw : rewritesAt (makeView R C f st.eff) with
  | none => rfl
  | some rw =>
    obtain ⟨hs1, hs2⟩ := rewritesAt_small hrw
    have c1 : (rw.removed.map (f.back R C)).any (fun x => st.removed.contains x) = false := by
      rw [List.any_eq_false]
      intro x hx hc
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      exact hfree _ (List.contains_iff_mem.mp hc) (back_win hR hC f (hs1 a ha).1 (hs1 a ha).2)
    have c2 : (rw.moves.map fun m => (f.back R C m.1, f.back R C m.2)).any
        (fun m => st.removed.contains m.2) = false := by
      rw [List.any_eq_false]
      intro x hx hc
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
      exact hfree _ (List.contains_iff_mem.mp hc) (back_win hR hC f (hs2 m hm).2.2.1 (hs2 m hm).2.2.2)
    dsimp only
    rw [c1, c2]
    rfl

theorem rw_moves_fresh : ∀ rw ∈ [rw3, rw2, rw1], rw.moves.Pairwise
    (fun m m' => m.2 ≠ m'.2 ∧ m.2 ≠ m'.1 ∧ m'.2 ≠ m.1) := by decide

theorem fresh_of_rw {R C : ℕ} (hR : 4 ≤ R) (hC : 4 ≤ C) {st : RWState} (hg : Good R C st)
    (f : Frame) {rw : Rewrite} (hrw : rewritesAt (makeView R C f st.eff) = some rw) :
    Fresh st.eff (rw.moves.map (fun m => (f.back R C m.1, f.back R C m.2))) := by
  obtain ⟨hs1, hs2⟩ := rewritesAt_small hrw
  have empty : ∀ a : ℕ × ℕ, a.1 ≤ 3 → a.2 ≤ 3 → (makeView R C f st.eff).at a.1 a.2 = none →
      f.back R C a ∉ cellsOf st.eff := by
    intro a h1 h2 hn hc
    rw [view_at_back hR hC hg f h1 h2, Option.map_eq_none_iff, List.find?_eq_none] at hn
    obtain ⟨q, hq, he⟩ := List.mem_map.mp hc
    exact hn q hq (by simp [he])
  refine ⟨fun m hm => ?_, ?_⟩
  · obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
    rcases rewritesAt_cases hrw with ⟨rfl, h03, h30⟩ | ⟨rfl, h02, h20, -⟩ | ⟨rfl, h10⟩
    · simp only [rw3, List.mem_cons, List.not_mem_nil, or_false] at hm0
      rcases hm0 with rfl | rfl
      · exact empty (0, 3) (by decide) (by decide) h03
      · exact empty (3, 0) (by decide) (by decide) h30
    · simp only [rw2, List.mem_cons, List.not_mem_nil, or_false] at hm0
      rcases hm0 with rfl | rfl
      · exact empty (0, 2) (by decide) (by decide) h02
      · exact empty (2, 0) (by decide) (by decide) h20
    · simp only [rw1, List.mem_cons, List.not_mem_nil, or_false] at hm0
      subst hm0
      exact empty (1, 0) (by decide) (by decide) h10
  · have hp : rw.moves.Pairwise (fun m m' => m.2 ≠ m'.2 ∧ m.2 ≠ m'.1 ∧ m'.2 ≠ m.1) := by
      rcases rewritesAt_cases hrw with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact rw_moves_fresh rw3 (by simp)
      · exact rw_moves_fresh rw2 (by simp)
      · exact rw_moves_fresh rw1 (by simp)
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem (fun {m m'} hm hm' h => ?_) hp
    obtain ⟨a1, a2, a3, a4⟩ := hs2 m hm
    obtain ⟨b1, b2, b3, b4⟩ := hs2 m' hm'
    refine ⟨fun e => h.1 (back_inj hR hC f a3 a4 b3 b4 e), fun e => h.2.1 (back_inj hR hC f a3 a4 b1 b2 e),
      fun e => h.2.2 (back_inj hR hC f b3 b4 a1 a2 e)⟩

/-- Facts about a firing step. -/
theorem dec_facts {R C : ℕ} (hR : 4 ≤ R) (hC : 4 ≤ C) {st : RWState} (hg : Good R C st) {f : Frame}
    {K : List (ℕ × ℕ)} {M : List ((ℕ × ℕ) × (ℕ × ℕ))} (h : rwDec R C st f = some (K, M)) :
    (∀ x ∈ K, Win R C f.fr f.fc x) ∧ (∀ m ∈ M, Win R C f.fr f.fc m.1 ∧ Win R C f.fr f.fc m.2) ∧
      Fresh st.eff M ∧ f.back R C (0, 0) ∈ K := by
  obtain ⟨rw, hrw, rfl, rfl⟩ := dec_some h
  obtain ⟨hs1, hs2⟩ := rewritesAt_small hrw
  refine ⟨fun x hx => ?_, fun m hm => ?_, fresh_of_rw hR hC hg f hrw,
    List.mem_map.mpr ⟨(0, 0), corner_mem_removed hrw, rfl⟩⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact back_win hR hC f (hs1 a ha).1 (hs1 a ha).2
  · obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
    exact ⟨back_win hR hC f (hs2 m0 hm0).1 (hs2 m0 hm0).2.1,
      back_win hR hC f (hs2 m0 hm0).2.2.1 (hs2 m0 hm0).2.2.2⟩

theorem foldl_mvP_cases : ∀ (M : List ((ℕ × ℕ) × (ℕ × ℕ))) (P : Pt → Prop) (q : Pt),
    M.foldl mvP P q → P q ∨ ∃ m ∈ M, q.1 = m.2
  | [], _, _, h => Or.inl h
  | m :: M, P, q, h => by
    simp only [List.foldl_cons] at h
    rcases foldl_mvP_cases M _ q h with h' | ⟨m', hm', he⟩
    · rcases h' with ⟨hp, -⟩ | ⟨col, -, rfl⟩
      · exact Or.inl hp
      · exact Or.inr ⟨m, List.mem_cons_self, rfl⟩
    · exact Or.inr ⟨m', List.mem_cons_of_mem _ hm', he⟩

theorem good_step {R C : ℕ} (hR : 4 ≤ R) (hC : 4 ≤ C) {st : RWState} (hg : Good R C st)
    (f : Frame) : Good R C (rwStep R C st f) := by
  rw [rwStep_dec]
  cases hd : rwDec R C st f with
  | none => exact hg
  | some KM =>
    obtain ⟨K, M⟩ := KM
    obtain ⟨-, hM, hF, -⟩ := dec_facts hR hC hg hd
    obtain ⟨hn, hmem⟩ := foldl_moveFirst_mem M hg.1 hF
    refine ⟨hn, fun q hq => ?_⟩
    rcases foldl_mvP_cases M _ q ((hmem q).mp hq) with h | ⟨m, hm, he⟩
    · exact hg.2 q h
    · rw [he]; exact ⟨(hM m hm).2.1, (hM m hm).2.2.1⟩

/-! ### Equivalent states -/

/-- Same endpoints (as a set), same settled cells (as a set), same flag. -/
def Equiv (R C : ℕ) (st st' : RWState) : Prop :=
  Good R C st ∧ Good R C st' ∧ (∀ q, q ∈ st.eff ↔ q ∈ st'.eff) ∧
    (∀ x, x ∈ st.removed ↔ x ∈ st'.removed) ∧ st.any = st'.any

theorem Equiv.refl {R C : ℕ} {st : RWState} (h : Good R C st) : Equiv R C st st :=
  ⟨h, h, fun _ => Iff.rfl, fun _ => Iff.rfl, rfl⟩

theorem Equiv.symm {R C : ℕ} {st st' : RWState} (h : Equiv R C st st') : Equiv R C st' st :=
  ⟨h.2.1, h.1, fun q => (h.2.2.1 q).symm, fun x => (h.2.2.2.1 x).symm, h.2.2.2.2.symm⟩

theorem Equiv.trans {R C : ℕ} {a b c : RWState} (h : Equiv R C a b) (h' : Equiv R C b c) :
    Equiv R C a c :=
  ⟨h.1, h'.2.1, fun q => (h.2.2.1 q).trans (h'.2.2.1 q), fun x => (h.2.2.2.1 x).trans (h'.2.2.2.1 x),
    h.2.2.2.2.trans h'.2.2.2.2⟩

theorem cellsOf_mem {l : List Pt} {x : ℕ × ℕ} : x ∈ cellsOf l ↔ ∃ col, (x, col) ∈ l := by
  unfold cellsOf
  simp only [List.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩; exact ⟨q.2, hq⟩
  · rintro ⟨col, h⟩; exact ⟨_, h, rfl⟩

theorem fresh_congr {l l' : List Pt} (h : ∀ q, q ∈ l ↔ q ∈ l') {M : List ((ℕ × ℕ) × (ℕ × ℕ))}
    (hf : Fresh l M) : Fresh l' M := by
  refine ⟨fun m hm hc => hf.1 m hm ?_, hf.2⟩
  rw [cellsOf_mem] at hc ⊢
  obtain ⟨col, hc⟩ := hc
  exact ⟨col, (h _).mpr hc⟩

theorem Equiv.agree {R C : ℕ} {st st' : RWState} (h : Equiv R C st st') (fr fc : Bool) :
    AgreeW R C fr fc st st' :=
  ⟨fun q _ => h.2.2.1 q, fun x _ => h.2.2.2.1 x⟩

/-- The state after a firing step, as membership. -/
theorem fire_mem {R C : ℕ} (hR : 4 ≤ R) (hC : 4 ≤ C) {st : RWState} (hg : Good R C st) {f : Frame}
    {K : List (ℕ × ℕ)} {M : List ((ℕ × ℕ) × (ℕ × ℕ))} (hd : rwDec R C st f = some (K, M)) :
    ∀ q, (q ∈ (rwStep R C st f).eff ↔ M.foldl mvP (· ∈ st.eff) q) := by
  rw [rwStep_dec, hd]
  exact (foldl_moveFirst_mem M hg.1 (dec_facts hR hC hg hd).2.2.1).2

theorem equiv_step {R C : ℕ} (hR : 4 ≤ R) (hC : 4 ≤ C) {st st' : RWState} (h : Equiv R C st st')
    (f : Frame) : Equiv R C (rwStep R C st f) (rwStep R C st' f) := by
  have hd := dec_congr hR hC h.1 h.2.1 f (h.agree f.fr f.fc)
  refine ⟨good_step hR hC h.1 f, good_step hR hC h.2.1 f, ?_, ?_, ?_⟩
  · cases hdf : rwDec R C st f with
    | none =>
      rw [hdf] at hd
      rw [rwStep_dec, rwStep_dec, hdf, ← hd]
      exact h.2.2.1
    | some KM =>
      obtain ⟨K, M⟩ := KM
      rw [hdf] at hd
      intro q
      rw [fire_mem hR hC h.1 hdf, fire_mem hR hC h.2.1 hd.symm]
      have e : (· ∈ st.eff) = (· ∈ st'.eff) := funext fun q => propext (h.2.2.1 q)
      rw [e]
  · rw [rwStep_dec, rwStep_dec, ← hd]
    cases rwDec R C st f with
    | none => exact h.2.2.2.1
    | some KM =>
      intro x
      simp only [applyDec, List.mem_append, h.2.2.2.1 x]
  · rw [rwStep_dec, rwStep_dec, ← hd]
    cases rwDec R C st f with
    | none => exact h.2.2.2.2
    | some KM => rfl

theorem equiv_foldl {R C : ℕ} (hR : 4 ≤ R) (hC : 4 ≤ C) : ∀ (fs : List Frame) {st st' : RWState},
    Equiv R C st st' → Equiv R C (fs.foldl (rwStep R C) st) (fs.foldl (rwStep R C) st')
  | [], _, _, h => h
  | f :: fs, _, _, h => equiv_foldl hR hC fs (equiv_step hR hC h f)

/-! ### Steps at different corners commute -/

theorem mvP_away (P : Pt → Prop) (m : (ℕ × ℕ) × (ℕ × ℕ)) {q : Pt} (h1 : q.1 ≠ m.1) (h2 : q.1 ≠ m.2) :
    mvP P m q ↔ P q := by
  unfold mvP
  constructor
  · rintro (⟨h, -⟩ | ⟨col, -, rfl⟩)
    · exact h
    · exact absurd rfl h2
  · intro h; exact Or.inl ⟨h, h1⟩

theorem foldl_mvP_away : ∀ (M : List ((ℕ × ℕ) × (ℕ × ℕ))) (P : Pt → Prop) {q : Pt},
    (∀ m ∈ M, q.1 ≠ m.1 ∧ q.1 ≠ m.2) → (M.foldl mvP P q ↔ P q)
  | [], _, _, _ => Iff.rfl
  | m :: M, P, q, h => by
    simp only [List.foldl_cons]
    rw [foldl_mvP_away M (mvP P m) (fun m' hm' => h m' (List.mem_cons_of_mem _ hm'))]
    exact mvP_away P m (h m List.mem_cons_self).1 (h m List.mem_cons_self).2

theorem mvP_comm (P : Pt → Prop) {m m' : (ℕ × ℕ) × (ℕ × ℕ)} (h1 : m.1 ≠ m'.1) (h2 : m.2 ≠ m'.1)
    (h3 : m.1 ≠ m'.2) (_h4 : m.2 ≠ m'.2) : mvP (mvP P m) m' = mvP (mvP P m') m := by
  funext q
  apply propext
  unfold mvP
  constructor
  · rintro (⟨(⟨hp, ha⟩ | ⟨c, hc, rfl⟩), hb⟩ | ⟨c, (⟨hc, -⟩ | ⟨c', -, he⟩), rfl⟩)
    · exact Or.inl ⟨Or.inl ⟨hp, hb⟩, ha⟩
    · exact Or.inr ⟨c, Or.inl ⟨hc, h1⟩, rfl⟩
    · exact Or.inl ⟨Or.inr ⟨c, hc, rfl⟩, fun e => h3 e.symm⟩
    · exact absurd (Prod.mk.inj he).1.symm h2
  · rintro (⟨(⟨hp, ha⟩ | ⟨c, hc, rfl⟩), hb⟩ | ⟨c, (⟨hc, -⟩ | ⟨c', -, he⟩), rfl⟩)
    · exact Or.inl ⟨Or.inl ⟨hp, hb⟩, ha⟩
    · exact Or.inr ⟨c, Or.inl ⟨hc, fun e => h1 e.symm⟩, rfl⟩
    · exact Or.inl ⟨Or.inr ⟨c, hc, rfl⟩, h2⟩
    · exact absurd (Prod.mk.inj he).1 h3

/-- Moves with pairwise disjoint cells. -/
def Disj (M M' : List ((ℕ × ℕ) × (ℕ × ℕ))) : Prop :=
  ∀ m ∈ M, ∀ m' ∈ M', m.1 ≠ m'.1 ∧ m.2 ≠ m'.1 ∧ m.1 ≠ m'.2 ∧ m.2 ≠ m'.2

theorem mvP_foldl_comm (m : (ℕ × ℕ) × (ℕ × ℕ)) : ∀ (M : List ((ℕ × ℕ) × (ℕ × ℕ))) (P : Pt → Prop),
    Disj [m] M → mvP (M.foldl mvP P) m = M.foldl mvP (mvP P m)
  | [], _, _ => rfl
  | m' :: M, P, h => by
    simp only [List.foldl_cons]
    have h' := h m List.mem_cons_self m' List.mem_cons_self
    rw [mvP_foldl_comm m M (mvP P m') (fun a ha b hb => h a ha b (List.mem_cons_of_mem _ hb)),
      mvP_comm P h'.1 h'.2.1 h'.2.2.1 h'.2.2.2]

theorem foldl_mvP_comm : ∀ (M M' : List ((ℕ × ℕ) × (ℕ × ℕ))) (P : Pt → Prop), Disj M M' →
    M'.foldl mvP (M.foldl mvP P) = M.foldl mvP (M'.foldl mvP P)
  | [], _, _, _ => rfl
  | m :: M, M', P, h => by
    simp only [List.foldl_cons]
    rw [foldl_mvP_comm M M' (mvP P m) (fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b hb),
      mvP_foldl_comm m M' P (fun a ha b hb => by
        simp only [List.mem_singleton] at ha; subst ha; exact h a List.mem_cons_self b hb)]

theorem agree_step_other {R C : ℕ} (hR : 8 ≤ R) (hC : 8 ≤ C) {st : RWState} (hg : Good R C st)
    (f : Frame) {fr fc : Bool} (hne : ¬ (f.fr = fr ∧ f.fc = fc)) :
    AgreeW R C fr fc (rwStep R C st f) st := by
  cases hd : rwDec R C st f with
  | none =>
    rw [rwStep_dec, hd]
    exact ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
  | some KM =>
    obtain ⟨K, M⟩ := KM
    obtain ⟨hK, hM, -, -⟩ := dec_facts (by omega) (by omega) hg hd
    refine ⟨fun q hq => ?_, fun x hx => ?_⟩
    · rw [fire_mem (by omega) (by omega) hg hd]
      apply foldl_mvP_away
      intro m hm
      exact ⟨fun e => hne (win_disj hR hC (e ▸ (hM m hm).1) hq), fun e => hne (win_disj hR hC (e ▸ (hM m hm).2) hq)⟩
    · rw [rwStep_dec, hd]
      simp only [applyDec, List.mem_append]
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd (win_disj hR hC (hK x h) hx) hne
      · exact Or.inl

theorem dec_after_other {R C : ℕ} (hR : 8 ≤ R) (hC : 8 ≤ C) {st : RWState} (hg : Good R C st)
    (f g : Frame) (hne : ¬ (f.fr = g.fr ∧ f.fc = g.fc)) :
    rwDec R C (rwStep R C st f) g = rwDec R C st g :=
  dec_congr (by omega) (by omega) (good_step (by omega) (by omega) hg f) hg g
    (agree_step_other hR hC hg f hne)

theorem cells_foldl_sub {R C : ℕ} (hR : 4 ≤ R) (hC : 4 ≤ C) {st : RWState} (hg : Good R C st)
    {f : Frame} {K : List (ℕ × ℕ)} {M : List ((ℕ × ℕ) × (ℕ × ℕ))} (hd : rwDec R C st f = some (K, M))
    {x : ℕ × ℕ} (hx : x ∈ cellsOf (rwStep R C st f).eff) : x ∈ cellsOf st.eff ∨ ∃ m ∈ M, x = m.2 := by
  rw [cellsOf_mem] at hx
  obtain ⟨col, hx⟩ := hx
  rcases foldl_mvP_cases M _ _ ((fire_mem hR hC hg hd _).mp hx) with h | ⟨m, hm, he⟩
  · exact Or.inl (cellsOf_mem.mpr ⟨col, h⟩)
  · exact Or.inr ⟨m, hm, he⟩

theorem commute_steps {R C : ℕ} (hR : 8 ≤ R) (hC : 8 ≤ C) {st : RWState} (hg : Good R C st)
    (f g : Frame) (hne : ¬ (f.fr = g.fr ∧ f.fc = g.fc)) :
    Equiv R C (rwStep R C (rwStep R C st f) g) (rwStep R C (rwStep R C st g) f) := by
  have hne' : ¬ (g.fr = f.fr ∧ g.fc = f.fc) := fun ⟨a, b⟩ => hne ⟨a.symm, b.symm⟩
  have hgf := good_step (by omega) (by omega) hg f
  have hgg := good_step (by omega) (by omega) hg g
  have e1 := dec_after_other hR hC hg f g hne
  have e2 := dec_after_other hR hC hg g f hne'
  have G2 := good_step (by omega) (by omega) hgf g
  have G2' := good_step (by omega) (by omega) hgg f
  cases hdf : rwDec R C st f with
  | none =>
    have s1 : rwStep R C st f = st := by rw [rwStep_dec, hdf]; rfl
    rw [hdf] at e2
    have s2 : rwStep R C (rwStep R C st g) f = rwStep R C st g := by rw [rwStep_dec, e2]; rfl
    rw [s1, s2]
    exact Equiv.refl hgg
  | some KM =>
    obtain ⟨K, M⟩ := KM
    cases hdg : rwDec R C st g with
    | none =>
      rw [hdg] at e1
      have s1 : rwStep R C (rwStep R C st f) g = rwStep R C st f := by rw [rwStep_dec, e1]; rfl
      have s2 : rwStep R C st g = st := by rw [rwStep_dec, hdg]; rfl
      rw [s1, s2]
      exact Equiv.refl hgf
    | some KM' =>
      obtain ⟨K', M'⟩ := KM'
      rw [hdg] at e1
      rw [hdf] at e2
      obtain ⟨hK, hM, hF, -⟩ := dec_facts (by omega) (by omega) hg hdf
      obtain ⟨hK', hM', hF', -⟩ := dec_facts (by omega) (by omega) hg hdg
      have dj : Disj M M' := by
        intro m hm m' hm'
        have w := fun {x y : ℕ × ℕ} (hx : Win R C f.fr f.fc x) (hy : Win R C g.fr g.fc y) (e : x = y) =>
          hne (win_disj hR hC hx (e ▸ hy))
        exact ⟨w (hM m hm).1 (hM' m' hm').1, w (hM m hm).2 (hM' m' hm').1,
          w (hM m hm).1 (hM' m' hm').2, w (hM m hm).2 (hM' m' hm').2⟩
      refine ⟨G2, G2', fun q => ?_, fun x => ?_, ?_⟩
      · rw [fire_mem (by omega) (by omega) hgf e1, fire_mem (by omega) (by omega) hgg e2]
        have a1 : (· ∈ (rwStep R C st f).eff) = M.foldl mvP (· ∈ st.eff) :=
          funext fun q => propext (fire_mem (by omega) (by omega) hg hdf q)
        have a2 : (· ∈ (rwStep R C st g).eff) = M'.foldl mvP (· ∈ st.eff) :=
          funext fun q => propext (fire_mem (by omega) (by omega) hg hdg q)
        rw [a1, a2, foldl_mvP_comm M M' _ dj]
      · rw [rwStep_dec R C (rwStep R C st f) g, e1, rwStep_dec R C (rwStep R C st g) f, e2,
          rwStep_dec R C st f, hdf, rwStep_dec R C st g, hdg]
        simp only [applyDec, List.mem_append]
        tauto
      · rw [rwStep_dec R C (rwStep R C st f) g, e1, rwStep_dec R C (rwStep R C st g) f, e2]
        rfl

/-! ### The two orientations of one corner -/

theorem dec_blocked {R C : ℕ} {st : RWState} {g : Frame} (h : g.back R C (0, 0) ∈ st.removed) :
    rwDec R C st g = none := by
  unfold rwDec
  cases hrw : rewritesAt (makeView R C g st.eff) with
  | none => rfl
  | some rw =>
    have : (rw.removed.map (g.back R C)).any (fun x => st.removed.contains x) = true := by
      rw [List.any_eq_true]
      exact ⟨_, List.mem_map.mpr ⟨(0, 0), corner_mem_removed hrw, rfl⟩, List.contains_iff_mem.mpr h⟩
    dsimp only
    rw [ite_eq_left this]

theorem back_flipT (R C : ℕ) (fr fc : Bool) (a : ℕ × ℕ) :
    (⟨fr, fc, true⟩ : Frame).back R C a = (⟨fr, fc, false⟩ : Frame).back R C a.swap := by
  simp [Frame.back]

/-- Once one orientation fired, the other is blocked. -/
theorem step_after_fire {R C : ℕ} {st : RWState} {f g : Frame} (hfg : f.fr = g.fr ∧ f.fc = g.fc)
    {K : List (ℕ × ℕ)} {M : List ((ℕ × ℕ) × (ℕ × ℕ))} (hK : f.back R C (0, 0) ∈ K)
    (hd : rwDec R C st f = some (K, M)) : rwStep R C (rwStep R C st f) g = rwStep R C st f := by
  have hb : g.back R C (0, 0) ∈ (rwStep R C st f).removed := by
    rw [rwStep_dec, hd]
    have : g.back R C (0, 0) = f.back R C (0, 0) := by
      obtain ⟨fr, fc, tr⟩ := f
      obtain ⟨gr, gc, gt⟩ := g
      simp only at hfg
      obtain ⟨rfl, rfl⟩ := hfg
      simp [Frame.back]
    rw [this]
    exact List.mem_append_right _ hK
  rw [rwStep_dec R C (rwStep R C st f) g, dec_blocked hb]
  rfl

theorem two_moves_char (P : Pt → Prop) {s1 s2 t t' : ℕ × ℕ} {a : ℕ} (hs1 : P (s1, a))
    (hs2 : P (s2, a)) (u1 : ∀ c, P (s1, c) → c = a) (u2 : ∀ c, P (s2, c) → c = a) (d12 : s1 ≠ s2)
    (ht : t ≠ s2) (q : Pt) :
    [(s1, t), (s2, t')].foldl mvP P q ↔ (P q ∧ q.1 ≠ s1 ∧ q.1 ≠ s2) ∨ q = (t, a) ∨ q = (t', a) := by
  simp only [List.foldl_cons, List.foldl_nil]
  unfold mvP
  simp only
  constructor
  · rintro (⟨(⟨hp, h1⟩ | ⟨c, hc, rfl⟩), h2⟩ | ⟨c, (⟨hc, -⟩ | ⟨c', -, he⟩), rfl⟩)
    · exact Or.inl ⟨hp, h1, h2⟩
    · rw [u1 c hc]; exact Or.inr (Or.inl rfl)
    · rw [u2 c hc]; exact Or.inr (Or.inr rfl)
    · exact absurd (Prod.mk.inj he).1 (fun e => ht e.symm)
  · rintro (⟨hp, h1, h2⟩ | rfl | rfl)
    · exact Or.inl ⟨Or.inl ⟨hp, h1⟩, h2⟩
    · exact Or.inl ⟨Or.inr ⟨a, hs1, rfl⟩, ht⟩
    · exact Or.inr ⟨a, Or.inl ⟨hs2, fun e => d12 e.symm⟩, rfl⟩

theorem rw_removed_symm : ∀ rw ∈ [rw3, rw2],
    (rw.removed.map Prod.swap).all (· ∈ rw.removed) ∧ rw.removed.all (· ∈ rw.removed.map Prod.swap) := by
  decide

theorem removed_flip_mem {R C : ℕ} (fr fc : Bool) {rw : Rewrite} (hrw : rw = rw3 ∨ rw = rw2) (x : ℕ × ℕ) :
    x ∈ rw.removed.map ((⟨fr, fc, true⟩ : Frame).back R C) ↔
      x ∈ rw.removed.map ((⟨fr, fc, false⟩ : Frame).back R C) := by
  have hs := rw_removed_symm rw (by rcases hrw with rfl | rfl <;> simp)
  simp only [List.all_eq_true, decide_eq_true_eq] at hs
  simp only [List.mem_map, back_flipT]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.swap, hs.1 a.swap (List.mem_map.mpr ⟨a, ha, rfl⟩), rfl⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hba⟩ := List.mem_map.mp (hs.2 a ha)
    exact ⟨b, hb, by rw [hba]⟩

theorem mem_of_view {R C : ℕ} (hR : 4 ≤ R) (hC : 4 ≤ C) {st : RWState} (hg : Good R C st) (f : Frame)
    {a : ℕ × ℕ} (h1 : a.1 ≤ 3) (h2 : a.2 ≤ 3) {col : ℕ} (h : (makeView R C f st.eff).at a.1 a.2 = some col) :
    (f.back R C a, col) ∈ st.eff := by
  rw [view_at_back hR hC hg f h1 h2] at h
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hm, he⟩ := (find_cell_iff hg.1 _ q).mp hq
  rw [← he]
  exact hm

/-- **The two orientations of a corner, in either order.** -/
theorem pair_steps {R C : ℕ} (hR : 8 ≤ R) (hC : 8 ≤ C) {st : RWState} (hg : Good R C st) (fr fc : Bool)
    (hfree : ∀ x ∈ st.removed, ¬ Win R C fr fc x) :
    Equiv R C (rwStep R C (rwStep R C st ⟨fr, fc, false⟩) ⟨fr, fc, true⟩)
      (rwStep R C (rwStep R C st ⟨fr, fc, true⟩) ⟨fr, fc, false⟩) := by
  set f : Frame := ⟨fr, fc, false⟩ with hf
  set g : Frame := ⟨fr, fc, true⟩ with hg'
  have R4 : 4 ≤ R := by omega
  have C4 : 4 ≤ C := by omega
  have vg : makeView R C g st.eff = (makeView R C f st.eff).tp := makeView_flip R C fr fc false st.eff
  have df := dec_free R4 C4 (f := f) hfree
  have dg := dec_free R4 C4 (f := g) hfree
  rw [vg] at dg
  have gf := good_step R4 C4 hg f
  have gg := good_step R4 C4 hg g
  cases hv : rewritesAt (makeView R C f st.eff) with
  | none =>
    rw [hv] at df
    have s1 : rwStep R C st f = st := by rw [rwStep_dec, df]; rfl
    cases hvt : rewritesAt (makeView R C f st.eff).tp with
    | none =>
      rw [hvt] at dg
      have s2 : rwStep R C st g = st := by rw [rwStep_dec, dg]; rfl
      rw [s1, s2, s1]
      exact Equiv.refl hg
    | some rw' =>
      rw [hvt] at dg
      have hK := (dec_facts R4 C4 hg dg).2.2.2
      rw [step_after_fire (f := g) (g := f) ⟨rfl, rfl⟩ hK dg, s1]
      exact Equiv.refl gg
  | some rw =>
    rw [hv] at df
    have hKf := (dec_facts R4 C4 hg df).2.2.2
    rw [step_after_fire (f := f) (g := g) ⟨rfl, rfl⟩ hKf df]
    cases hvt : rewritesAt (makeView R C f st.eff).tp with
    | none =>
      rw [hvt] at dg
      have s2 : rwStep R C st g = st := by rw [rwStep_dec, dg]; rfl
      rw [s2]
      exact Equiv.refl gf
    | some rw' =>
      rw [hvt] at dg
      have hKg := (dec_facts R4 C4 hg dg).2.2.2
      rw [step_after_fire (f := g) (g := f) ⟨rfl, rfl⟩ hKg dg]
      -- both fire: the same rule
      have hsame := rewritesAt_both hv hvt
      have hrw' : rw' = rw := by rcases hsame with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
      subst hrw'
      have hrw : rw' = rw3 ∨ rw' = rw2 := by rcases hsame with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
      refine ⟨gf, gg, fun q => ?_, fun x => ?_, ?_⟩
      · rw [fire_mem R4 C4 hg df, fire_mem R4 C4 hg dg]
        have bF := fun {a : ℕ × ℕ} (h1 : a.1 ≤ 3) (h2 : a.2 ≤ 3) {b : ℕ × ℕ} (h3 : b.1 ≤ 3) (h4 : b.2 ≤ 3)
          (hab : a ≠ b) => fun e => hab (back_inj R4 C4 f h1 h2 h3 h4 e)
        rcases hrw with rfl | rfl
        · -- R3: the same two moves, in the other order
          simp only [rw3, List.map_cons, List.map_nil, back_flipT, Prod.swap_prod_mk, hg', hf]
          simp only [List.foldl_cons, List.foldl_nil]
          rw [mvP_comm _ (bF (by decide) (by decide) (by decide) (by decide) (by decide))
            (bF (by decide) (by decide) (by decide) (by decide) (by decide))
            (bF (by decide) (by decide) (by decide) (by decide) (by decide))
            (bF (by decide) (by decide) (by decide) (by decide) (by decide))]
        · -- R2: two endpoints of one colour trade targets
          rcases rewritesAt_cases hv with ⟨h, -⟩ | ⟨-, -, -, a, h00, h11⟩ | ⟨h, -⟩
          · simp [rw2, rw3] at h
          · simp only [rw2, List.map_cons, List.map_nil, back_flipT, Prod.swap_prod_mk, hg', hf]
            set F := Frame.back R C ⟨fr, fc, false⟩ with hF
            have hs1 : (F (0, 0), a) ∈ st.eff := mem_of_view R4 C4 hg f (a := (0, 0)) (by decide) (by decide) h00
            have hs2 : (F (1, 1), a) ∈ st.eff := mem_of_view R4 C4 hg f (a := (1, 1)) (by decide) (by decide) h11
            have u : ∀ x : ℕ × ℕ, (x, a) ∈ st.eff → ∀ c, (x, c) ∈ st.eff → c = a := fun x hx c hc =>
              (Prod.mk.inj (cell_unique hg.1 hc hx rfl)).2
            have d12 := bF (a := (0, 0)) (b := (1, 1)) (by decide) (by decide) (by decide) (by decide) (by decide)
            have ht := bF (a := (0, 2)) (b := (1, 1)) (by decide) (by decide) (by decide) (by decide) (by decide)
            have ht' := bF (a := (2, 0)) (b := (1, 1)) (by decide) (by decide) (by decide) (by decide) (by decide)
            rw [two_moves_char _ hs1 hs2 (u _ hs1) (u _ hs2) d12 ht q,
              two_moves_char _ hs1 hs2 (u _ hs1) (u _ hs2) d12 ht' q]
            tauto
          · simp [rw2, rw1] at h
      · simp only [rwStep_dec, df, dg, Option.map_some, applyDec, List.mem_append]
        rw [hg', hf, removed_flip_mem fr fc hrw x]
      · rw [rwStep_dec, df, rwStep_dec, dg]
        rfl

/-! ### Reordering the frames -/

theorem removed_step {R C : ℕ} (hR : 4 ≤ R) (hC : 4 ≤ C) {st : RWState} (hg : Good R C st)
    (f : Frame) {x : ℕ × ℕ} (hx : x ∈ (rwStep R C st f).removed) :
    x ∈ st.removed ∨ Win R C f.fr f.fc x := by
  rw [rwStep_dec] at hx
  cases hd : rwDec R C st f with
  | none => rw [hd] at hx; exact Or.inl hx
  | some KM =>
    obtain ⟨K, M⟩ := KM
    rw [hd] at hx
    simp only [applyDec, List.mem_append] at hx
    rcases hx with h | h
    · exact Or.inl h
    · exact Or.inr ((dec_facts hR hC hg hd).1 x h)

/-- After steps at other corners, a corner's window is still free. -/
theorem free_steps {R C : ℕ} (hR : 8 ≤ R) (hC : 8 ≤ C) (fr fc : Bool) :
    ∀ (fs : List Frame) {st : RWState}, Good R C st → (∀ x ∈ st.removed, ¬ Win R C fr fc x) →
      (∀ f ∈ fs, ¬ (f.fr = fr ∧ f.fc = fc)) →
      Good R C (fs.foldl (rwStep R C) st) ∧ ∀ x ∈ (fs.foldl (rwStep R C) st).removed, ¬ Win R C fr fc x
  | [], _, hg, h, _ => ⟨hg, h⟩
  | f :: fs, st, hg, h, hfs => by
    simp only [List.foldl_cons]
    apply free_steps hR hC fr fc fs (good_step (by omega) (by omega) hg f)
    · intro x hx hw
      rcases removed_step (by omega) (by omega) hg f hx with h' | h'
      · exact h x h' hw
      · exact hfs f List.mem_cons_self (win_disj hR hC h' hw)
    · exact fun g hg' => hfs g (List.mem_cons_of_mem _ hg')

theorem good_steps {R C : ℕ} (hR : 4 ≤ R) (hC : 4 ≤ C) : ∀ (fs : List Frame) {st : RWState},
    Good R C st → Good R C (fs.foldl (rwStep R C) st)
  | [], _, hg => hg
  | f :: fs, _, hg => good_steps hR hC fs (good_step hR hC hg f)

/-- Commute two steps at different corners, then continue with the same steps. -/
theorem commute_then {R C : ℕ} (hR : 8 ≤ R) (hC : 8 ≤ C) {st : RWState} (hg : Good R C st)
    (f g : Frame) (hne : ¬ (f.fr = g.fr ∧ f.fc = g.fc)) (fs : List Frame) :
    Equiv R C (fs.foldl (rwStep R C) (rwStep R C (rwStep R C st f) g))
      (fs.foldl (rwStep R C) (rwStep R C (rwStep R C st g) f)) :=
  equiv_foldl (by omega) (by omega) fs (commute_steps hR hC hg f g hne)

abbrev fTL0 : Frame := ⟨false, false, false⟩
abbrev fTL1 : Frame := ⟨false, false, true⟩
abbrev fTR0 : Frame := ⟨false, true, false⟩
abbrev fTR1 : Frame := ⟨false, true, true⟩
abbrev fBL0 : Frame := ⟨true, false, false⟩
abbrev fBL1 : Frame := ⟨true, false, true⟩
abbrev fBR0 : Frame := ⟨true, true, false⟩
abbrev fBR1 : Frame := ⟨true, true, true⟩

theorem frames_eq : frames = [fTL0, fTL1, fTR0, fTR1, fBL0, fBL1, fBR0, fBR1] := rfl
theorem frames_tp_eq : frames.map Frame.tp = [fTL1, fTL0, fBL1, fBL0, fTR1, fTR0, fBR1, fBR0] := rfl

/-- **The rewrite phase does not depend on the corner order or the orientation order.** -/
theorem rewrite_order {R C : ℕ} (hR : 8 ≤ R) (hC : 8 ≤ C) {s0 : RWState} (hg : Good R C s0)
    (h0 : s0.removed = []) :
    Equiv R C ((frames.map Frame.tp).foldl (rwStep R C) s0) (frames.foldl (rwStep R C) s0) := by
  have R4 : 4 ≤ R := by omega
  have C4 : 4 ≤ C := by omega
  rw [frames_tp_eq, frames_eq]
  simp only [List.foldl_cons, List.foldl_nil]
  have free0 : ∀ x ∈ s0.removed, ∀ fr fc, ¬ Win R C fr fc x := by simp [h0]
  have h1 := pair_steps hR hC hg false false (fun x hx => free0 x hx _ _)
  have gA : Good R C (rwStep R C (rwStep R C s0 fTL0) fTL1) := good_steps R4 C4 [fTL0, fTL1] hg
  have fBL := (free_steps hR hC true false [fTL0, fTL1] hg (fun x hx => free0 x hx _ _) (by simp)).2
  simp only [List.foldl_cons, List.foldl_nil] at fBL
  have h2 := pair_steps hR hC gA true false fBL
  have gB := good_steps R4 C4 [fBL0, fBL1] gA
  simp only [List.foldl_cons, List.foldl_nil] at gB
  have fTR := (free_steps hR hC false true [fTL0, fTL1, fBL0, fBL1] hg (fun x hx => free0 x hx _ _)
    (by simp)).2
  simp only [List.foldl_cons, List.foldl_nil] at fTR
  have h3 := pair_steps hR hC gB false true fTR
  have gD := good_steps R4 C4 [fTR0, fTR1] gB
  simp only [List.foldl_cons, List.foldl_nil] at gD
  have fBR := (free_steps hR hC true true [fTL0, fTL1, fBL0, fBL1, fTR0, fTR1] hg
    (fun x hx => free0 x hx _ _) (by simp)).2
  simp only [List.foldl_cons, List.foldl_nil] at fBR
  have h4 := pair_steps hR hC gD true true fBR
  have q1 := equiv_foldl R4 C4 [fBL1, fBL0, fTR1, fTR0, fBR1, fBR0] h1.symm
  have q2 := equiv_foldl R4 C4 [fTR1, fTR0, fBR1, fBR0] h2.symm
  have q3 := equiv_foldl R4 C4 [fBR1, fBR0] h3.symm
  have q4 := h4.symm
  simp only [List.foldl_cons, List.foldl_nil] at q1 q2 q3
  have ne : ¬ ((true : Bool) = false ∧ (false : Bool) = true) := by decide
  have gA0 := good_step R4 C4 gA fBL0
  have gA1 := good_step R4 C4 gA fTR0
  have p1 := commute_then hR hC gA0 fBL1 fTR0 ne [fTR1, fBR0, fBR1]
  have p2 := commute_then hR hC gA fBL0 fTR0 ne [fBL1, fTR1, fBR0, fBR1]
  have p3 := commute_then hR hC (good_step R4 C4 gA1 fBL0) fBL1 fTR1 ne [fBR0, fBR1]
  have p4 := commute_then hR hC gA1 fBL0 fTR1 ne [fBL1, fBR0, fBR1]
  simp only [List.foldl_cons, List.foldl_nil] at p1 p2 p3 p4
  exact q1.trans (q2.trans (q3.trans (q4.trans (p1.trans (p2.trans (p3.trans p4))))))

/-! ### The outer walk of the transposed instance -/

/-- The settled cells at one corner, in that corner's frame `(fr, fc, false)`: none, or the
cells of one rewrite (R1 in either orientation, R2, R3). -/
def shapes : List (List (ℕ × ℕ)) :=
  [[], rw1.removed, rw1.removed.map Prod.swap, rw2.removed, rw3.removed]

def lamS (S : List (ℕ × ℕ)) (i : ℕ) : ℕ := ((List.range 4).filter fun j => S.contains (i, j)).length
def kS (S : List (ℕ × ℕ)) : ℕ := ((List.range 4).filter fun i => lamS S i > 0).length

/-- Transposing a shape conjugates the partition: its staircase is traced backwards. -/
theorem shape_facts : ∀ S ∈ shapes,
    staircase (lamS (S.map Prod.swap)) = (staircase (lamS S)).reverse.map Prod.swap ∧
      lamS (S.map Prod.swap) 0 = kS S ∧ kS (S.map Prod.swap) = lamS S 0 ∧
      (∀ a ∈ S, a.1 ≤ 3 ∧ a.2 ≤ 3) := by
  decide

/-- The rest of the walk after the top-left staircase. -/
def walkRest (R C : ℕ) (tr br bl : List (ℕ × ℕ)) (lTL lTR lBR lBL kTL kTR kBR kBL : ℕ) :
    List (ℕ × ℕ) :=
  ((List.range C).filter fun y => decide (lTL < y ∧ y + 1 + lTR < C)).map (fun y => (0, y)) ++
    tr.reverse ++
    ((List.range R).filter fun x => decide (kTR < x ∧ x + 1 + kBR < R)).map (fun x => (x, C - 1)) ++
    br ++
    (((List.range C).filter fun y => decide (lBL < y ∧ y + 1 + lBR < C)).map
      (fun y => (R - 1, y))).reverse ++
    bl.reverse ++
    (((List.range R).filter fun x => decide (kTL < x ∧ x + 1 + kBL < R)).map (fun x => (x, 0))).reverse

theorem walk3Core_rest (R C : ℕ) (tl tr br bl : List (ℕ × ℕ)) (lTL lTR lBR lBL kTL kTR kBR kBL : ℕ) :
    walk3Core R C tl tr br bl lTL lTR lBR lBL kTL kTR kBR kBL =
      tl ++ walkRest R C tr br bl lTL lTR lBR lBL kTL kTR kBR kBL := by
  unfold walk3Core walkRest
  simp only [List.append_assoc]

/-- The walk identity, as list algebra. -/
theorem walk3Core_swap (R C : ℕ) (tl tr br bl : List (ℕ × ℕ))
    (lTL lTR lBR lBL kTL kTR kBR kBL : ℕ) :
    walk3Core C R (tl.reverse.map Prod.swap) (bl.reverse.map Prod.swap) (br.reverse.map Prod.swap)
        (tr.reverse.map Prod.swap) kTL kBL kBR kTR lTL lBL lBR lTR =
      (tl.reverse ++ (walkRest R C tr br bl lTL lTR lBR lBL kTL kTR kBR kBL).reverse).map Prod.swap := by
  unfold walk3Core walkRest
  simp only [List.reverse_append, List.map_append, List.map_reverse, List.reverse_reverse,
    List.map_map, List.append_assoc]
  rfl

/-- The settled cells at corner `(fr, fc)` form one of the shapes. -/
def CornerShape (R C : ℕ) (rem : List (ℕ × ℕ)) (fr fc : Bool) (S : List (ℕ × ℕ)) : Prop :=
  S ∈ shapes ∧ ∀ x, Win R C fr fc x → (x ∈ rem ↔ ∃ a ∈ S, x = (⟨fr, fc, false⟩ : Frame).back R C a)

def RemShape (R C : ℕ) (rem : List (ℕ × ℕ)) : Prop :=
  (∀ x ∈ rem, ∃ fr fc, Win R C fr fc x) ∧ ∀ fr fc, ∃ S, CornerShape R C rem fr fc S

theorem back4_notWin {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) (fr fc fr' fc' : Bool) {j : ℕ} (hj : j ≤ 3) :
    ¬ Win R C fr' fc' ((⟨fr, fc, false⟩ : Frame).back R C (4, j)) ∧
      ¬ Win R C fr' fc' ((⟨fr, fc, false⟩ : Frame).back R C (j, 4)) := by
  unfold Win Frame.back
  cases fr <;> cases fc <;> cases fr' <;> cases fc' <;> simp <;> omega

theorem notchLen_shape {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) {rem : List (ℕ × ℕ)}
    (hin : ∀ x ∈ rem, ∃ fr fc, Win R C fr fc x) {fr fc : Bool} {S : List (ℕ × ℕ)}
    (hS : CornerShape R C rem fr fc S) {i : ℕ} (hi : i ≤ 4) :
    notchLen R C ⟨fr, fc, false⟩ rem i = lamS S i ∧
      notchLen R C ⟨fr, fc, true⟩ rem i = lamS (S.map Prod.swap) i := by
  obtain ⟨hmem, hsh⟩ := hS
  have small := (shape_facts S hmem).2.2.2
  set F : Frame := ⟨fr, fc, false⟩ with hF
  have key : ∀ a : ℕ × ℕ, a.1 ≤ 4 → a.2 ≤ 4 → (a.1 = 4 ∨ a.2 = 4 ∨ (a.1 ≤ 3 ∧ a.2 ≤ 3)) →
      (rem.contains (F.back R C a) = S.contains a) := by
    intro a h1 h2 hc
    apply Bool.eq_iff_iff.mpr
    simp only [List.contains_iff_mem]
    rcases hc with h4 | h4 | ⟨h1', h2'⟩
    · obtain ⟨a1, a2⟩ := a
      simp only at h4 h2
      subst h4
      by_cases hj : a2 ≤ 3
      · constructor
        · intro hx
          obtain ⟨fr', fc', hw⟩ := hin _ hx
          exact absurd hw (back4_notWin hR hC fr fc fr' fc' hj).1
        · intro ha; exact absurd (small _ ha).1 (by simp)
      · constructor
        · intro hx
          obtain ⟨fr', fc', hw⟩ := hin _ hx
          unfold Win Frame.back at hw
          simp only [hF] at hw
          cases fr <;> cases fc <;> cases fr' <;> cases fc' <;> simp at hw <;> omega
        · intro ha; exact absurd (small _ ha).1 (by simp)
    · obtain ⟨a1, a2⟩ := a
      simp only at h4 h1
      subst h4
      by_cases hj : a1 ≤ 3
      · constructor
        · intro hx
          obtain ⟨fr', fc', hw⟩ := hin _ hx
          exact absurd hw (back4_notWin hR hC fr fc fr' fc' hj).2
        · intro ha; exact absurd (small _ ha).2 (by simp)
      · constructor
        · intro hx
          obtain ⟨fr', fc', hw⟩ := hin _ hx
          unfold Win Frame.back at hw
          simp only [hF] at hw
          cases fr <;> cases fc <;> cases fr' <;> cases fc' <;> simp at hw <;> omega
        · intro ha; exact absurd (small _ ha).2 (by simp)
    · rw [hsh _ (back_win (by omega) (by omega) F h1' h2')]
      constructor
      · rintro ⟨b, hb, he⟩
        rw [back_inj (by omega) (by omega) F h1' h2' (small b hb).1 (small b hb).2 he]
        exact hb
      · intro ha; exact ⟨a, ha, rfl⟩
  constructor
  · unfold notchLen lamS
    congr 1
    apply List.filter_congr
    intro j hj
    simp only [List.mem_range] at hj
    rw [key (i, j) hi (by simp only; omega) (by by_cases h : i = 4 <;> simp only <;> omega)]
  · unfold notchLen lamS
    congr 1
    apply List.filter_congr
    intro j hj
    simp only [List.mem_range] at hj
    rw [back_flipT, ← hF, Prod.swap_prod_mk, key (j, i) (by simp only; omega) hi
      (by by_cases h : i = 4 <;> simp only <;> omega)]
    apply Bool.eq_iff_iff.mpr
    simp only [List.contains_iff_mem, List.mem_map]
    constructor
    · intro h; exact ⟨(j, i), h, rfl⟩
    · rintro ⟨b, hb, he⟩
      have : b = (j, i) := by rw [← Prod.swap_swap b, he]; rfl
      rw [← this]
      exact hb

theorem notchLen_swap (R C : ℕ) (G : Frame) (rem : List (ℕ × ℕ)) (i : ℕ) :
    notchLen C R G (rem.map Prod.swap) i = notchLen R C G.tp rem i := by
  unfold notchLen
  congr 1
  apply List.filter_congr
  intro j _
  have := back_tp R C G.tp (i, j)
  rw [tp_tp] at this
  rw [this, contains_swap]

theorem corner_J {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) {rem : List (ℕ × ℕ)}
    (hin : ∀ x ∈ rem, ∃ fr fc, Win R C fr fc x) {gr gc : Bool} {S : List (ℕ × ℕ)}
    (hS : CornerShape R C rem gc gr S) :
    stairOf C R ⟨gr, gc, false⟩ (rem.map Prod.swap) =
        (stairOf R C ⟨gc, gr, false⟩ rem).reverse.map Prod.swap ∧
      notchLen C R ⟨gr, gc, false⟩ (rem.map Prod.swap) 0 = kOf R C ⟨gc, gr, false⟩ rem ∧
      kOf C R ⟨gr, gc, false⟩ (rem.map Prod.swap) = notchLen R C ⟨gc, gr, false⟩ rem 0 := by
  have sf := shape_facts S hS.1
  have nI : ∀ i, i ≤ 4 → notchLen R C ⟨gc, gr, false⟩ rem i = lamS S i :=
    fun i hi => (notchLen_shape hR hC hin hS hi).1
  have nJ : ∀ i, i ≤ 4 → notchLen C R ⟨gr, gc, false⟩ (rem.map Prod.swap) i = lamS (S.map Prod.swap) i :=
    fun i hi => by
      rw [notchLen_swap]
      exact (notchLen_shape hR hC hin hS hi).2
  have kI : kOf R C ⟨gc, gr, false⟩ rem = kS S := by
    unfold kOf kS; congr 1; apply List.filter_congr; intro i hi
    simp only [List.mem_range] at hi; rw [nI i (by omega)]
  have kJ : kOf C R ⟨gr, gc, false⟩ (rem.map Prod.swap) = kS (S.map Prod.swap) := by
    unfold kOf kS; congr 1; apply List.filter_congr; intro i hi
    simp only [List.mem_range] at hi; rw [nJ i (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · unfold stairOf
    rw [staircase_congr nJ, staircase_congr nI, sf.1]
    simp only [List.map_reverse, List.map_map]
    congr 1
  · rw [nJ 0 (by omega), kI, sf.2.1]
  · rw [kJ, nI 0 (by omega), sf.2.2.1]

theorem corner_I {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) {rem : List (ℕ × ℕ)}
    (hin : ∀ x ∈ rem, ∃ fr fc, Win R C fr fc x) {fr fc : Bool} {S : List (ℕ × ℕ)}
    (hS : CornerShape R C rem fr fc S) :
    stairOf R C ⟨fr, fc, false⟩ rem = (staircase (lamS S)).map (Frame.back R C ⟨fr, fc, false⟩) := by
  unfold stairOf
  rw [staircase_congr (fun i hi => (notchLen_shape hR hC hin hS hi).1)]

/-- **The walk of the transposed instance**: reverse and transpose the walk, keeping the
top-left staircase first. -/
theorem walk3_swap {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) {rem : List (ℕ × ℕ)} (h : RemShape R C rem) :
    ∃ T Y, walk3 R C rem = T ++ Y ∧ walk3 C R (rem.map Prod.swap) = (T.reverse ++ Y.reverse).map Prod.swap := by
  obtain ⟨hin, hsh⟩ := h
  obtain ⟨S1, h1⟩ := hsh false false
  obtain ⟨S2, h2⟩ := hsh true false
  obtain ⟨S3, h3⟩ := hsh true true
  obtain ⟨S4, h4⟩ := hsh false true
  obtain ⟨a1, a2, a3⟩ := corner_J hR hC hin (gr := false) (gc := false) h1
  obtain ⟨b1, b2, b3⟩ := corner_J hR hC hin (gr := false) (gc := true) h2
  obtain ⟨c1, c2, c3⟩ := corner_J hR hC hin (gr := true) (gc := true) h3
  obtain ⟨d1, d2, d3⟩ := corner_J hR hC hin (gr := true) (gc := false) h4
  rw [walk3_eq C R, walk3_eq R C]
  unfold frameTL frameTR frameBR frameBL
  rw [a1, b1, c1, d1, a2, b2, c2, d2, a3, b3, c3, d3, walk3Core_rest]
  exact ⟨_, _, rfl, walk3Core_swap _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩

/-! ### The R test depends on the endpoints only as a set -/

theorem sortBy_perm {α : Type} (key : α → ℕ) : ∀ l : List α, (sortBy key l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => by
    simp only [sortBy]
    have ih := sortBy_perm key xs
    have hp := List.filter_append_perm (fun y => decide (key y < key x)) (sortBy key xs)
    have e : (sortBy key xs).filter (fun y => !decide (key y < key x)) =
        (sortBy key xs).filter (fun y => decide ¬(key y < key x)) := by
      apply List.filter_congr; intro y _; rw [decide_not]
    rw [e] at hp
    have h1 : ((sortBy key xs).filter (fun y => decide (key y < key x)) ++ [x] ++
          (sortBy key xs).filter (fun y => decide ¬(key y < key x))).Perm
        (x :: ((sortBy key xs).filter (fun y => decide (key y < key x)) ++
          (sortBy key xs).filter (fun y => decide ¬(key y < key x)))) := by
      rw [List.append_assoc, List.singleton_append]; exact List.perm_middle
    exact h1.trans ((List.Perm.cons x hp).trans (List.Perm.cons x ih))

theorem sortBy_sorted {α : Type} (key : α → ℕ) : ∀ l : List α, (l.map key).Nodup →
    (sortBy key l).Pairwise (fun a b => key a < key b)
  | [] => fun _ => List.Pairwise.nil
  | x :: xs => by
    intro hn
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    have ih := sortBy_sorted key xs hn.2
    simp only [sortBy]
    rw [List.pairwise_append, List.pairwise_append]
    refine ⟨⟨ih.filter _, List.pairwise_singleton _ _, ?_⟩, ih.filter _, ?_⟩
    · intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      simpa using (List.mem_filter.mp ha).2
    · intro a ha b hb
      have hb' := List.mem_filter.mp hb
      have hbx : key b ≠ key x := fun e => hn.1 ⟨b, mem_sortBy key hb'.1, e⟩
      have : key x < key b := by simp at hb'; omega
      rcases List.mem_append.mp ha with ha | ha
      · have := (List.mem_filter.mp ha).2; simp at this; omega
      · simp only [List.mem_singleton] at ha; subst ha; exact this

theorem eq_of_perm_lt {α : Type} (key : α → ℕ) : ∀ {l l' : List α}, l.Perm l' →
    l.Pairwise (fun a b => key a < key b) → l'.Pairwise (fun a b => key a < key b) → l = l'
  | [], l', hp, _, _ => (List.perm_nil.mp hp.symm).symm
  | x :: xs, [], hp, _, _ => absurd hp.length_eq (by simp)
  | x :: xs, y :: ys, hp, h1, h2 => by
    rw [List.pairwise_cons] at h1 h2
    have hxy : x = y := by
      by_contra hne
      have hx : x ∈ ys := by
        rcases List.mem_cons.mp (hp.subset List.mem_cons_self) with e | e
        · exact absurd e hne
        · exact e
      have hy : y ∈ xs := by
        rcases List.mem_cons.mp (hp.symm.subset List.mem_cons_self) with e | e
        · exact absurd e.symm hne
        · exact e
      have := h1.1 y hy
      have := h2.1 x hx
      omega
    subst hxy
    rw [eq_of_perm_lt key (List.Perm.cons_inv hp) h1.2 h2.2]

theorem sortBy_eq_of_perm {α : Type} (key : α → ℕ) {l l' : List α} (hp : l.Perm l')
    (hn : (l.map key).Nodup) : sortBy key l = sortBy key l' := by
  have hn' : (l'.map key).Nodup := (hp.map key).nodup_iff.mp hn
  have s1 := sortBy_sorted key l hn
  have s2 := sortBy_sorted key l' hn'
  have p : (sortBy key l).Perm (sortBy key l') :=
    (sortBy_perm key l).trans (hp.trans (sortBy_perm key l').symm)
  exact eq_of_perm_lt key p s1 s2

theorem notchLen_congr {R C : ℕ} {r r' : List (ℕ × ℕ)} (h : ∀ x, x ∈ r ↔ x ∈ r') (f : Frame) :
    notchLen R C f r = notchLen R C f r' := by
  funext i
  unfold notchLen
  congr 1
  apply List.filter_congr
  intro j _
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, h]

theorem walk3_congr {R C : ℕ} {r r' : List (ℕ × ℕ)} (h : ∀ x, x ∈ r ↔ x ∈ r') :
    walk3 R C r = walk3 R C r' := by
  unfold walk3 stairOf
  simp only [notchLen_congr h]

theorem nodup_of_cells {l : List Pt} (h : (cellsOf l).Nodup) : l.Nodup := List.Nodup.of_map _ h

theorem idxOf_inj {W : List (ℕ × ℕ)} {x y : ℕ × ℕ} (hx : x ∈ W) (hy : y ∈ W)
    (h : W.idxOf x = W.idxOf y) : x = y := by
  have h1 := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hx)
  have h2 := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hy)
  simp only [h] at h1
  exact h1.symm.trans h2

/-- **The R test depends on the endpoints and settled cells only as sets.** -/
theorem effAltFrom_congr {R C : ℕ} {st st' : RWState} (hn : (cellsOf st.eff).Nodup)
    (hn' : (cellsOf st'.eff).Nodup) (he : ∀ q, q ∈ st.eff ↔ q ∈ st'.eff)
    (hr : ∀ x, x ∈ st.removed ↔ x ∈ st'.removed) (ha : st.any = st'.any) :
    effAltFrom R C st = effAltFrom R C st' := by
  have hp : st.eff.Perm st'.eff :=
    (List.perm_ext_iff_of_nodup (nodup_of_cells hn) (nodup_of_cells hn')).mpr he
  unfold effAltFrom
  rw [walk3_congr hr, ha]
  generalize walk3 R C st'.removed = W
  dsimp only
  have t1 : st.eff.any (fun q => st.removed.contains q.1) =
      st'.eff.any (fun q => st'.removed.contains q.1) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.contains_iff_mem, hr, he]
  have t2 : (st.eff.map (·.1)).dedup.length = (st'.eff.map (·.1)).dedup.length :=
    ((hp.map _).dedup).length_eq
  have t3 : (st.eff.map fun q => (positions W q.1, q.2)).any (fun pl => pl.1.length != 1) =
      (st'.eff.map fun q => (positions W q.1, q.2)).any (fun pl => pl.1.length != 1) :=
    (hp.map _).any_eq
  rw [t1, t2, t3]
  split_ifs with h1 h2 h3 h4
  · rfl
  · rfl
  · rfl
  · rfl
  · congr 2
    rw [sortByKey_eq, sortByKey_eq]
    apply sortBy_eq_of_perm _ ((hp.map _).map _)
    -- distinct keys: each endpoint is on the walk once, at distinct cells
    have hin : ∀ q ∈ st.eff, q.1 ∈ W := by
      intro q hq
      have : (positions W q.1).length = 1 := by
        by_contra hne
        apply h4
        rw [List.any_eq_true]
        exact ⟨(positions W q.1, q.2), List.mem_map.mpr ⟨q, (he q).mp hq, rfl⟩, by simpa using hne⟩
      rw [positions_length] at this
      exact List.count_pos_iff.mp (by omega)
    simp only [List.map_map]
    rw [List.nodup_map_iff_inj_on (nodup_of_cells hn)]
    intro q hq q' hq' heq
    simp only [Function.comp, positions_head (hin q hq), positions_head (hin q' hq')] at heq
    exact cell_unique hn hq hq' (idxOf_inj (hin q hq) (hin q' hq') heq)

/-! ### Colours are kept in place -/

theorem snd_moveFirst : ∀ (l : List Pt) (m : (ℕ × ℕ) × (ℕ × ℕ)),
    (moveFirst l m).map (·.2) = l.map (·.2)
  | [], _ => rfl
  | q :: l, m => by
    rw [moveFirst_cons]
    split_ifs
    · rfl
    · simp only [List.map_cons, snd_moveFirst l m]

theorem snd_foldl_moveFirst : ∀ (M : List ((ℕ × ℕ) × (ℕ × ℕ))) (l : List Pt),
    (M.foldl moveFirst l).map (·.2) = l.map (·.2)
  | [], _ => rfl
  | m :: M, l => by
    simp only [List.foldl_cons]
    rw [snd_foldl_moveFirst M, snd_moveFirst]

theorem snd_step (R C : ℕ) (st : RWState) (f : Frame) :
    (rwStep R C st f).eff.map (·.2) = st.eff.map (·.2) := by
  rw [rwStep_dec]
  cases rwDec R C st f with
  | none => rfl
  | some KM => exact snd_foldl_moveFirst KM.2 st.eff

theorem snd_steps (R C : ℕ) : ∀ (fs : List Frame) (st : RWState),
    (fs.foldl (rwStep R C) st).eff.map (·.2) = st.eff.map (·.2)
  | [], _ => rfl
  | f :: fs, st => by
    simp only [List.foldl_cons]
    rw [snd_steps R C fs, snd_step]

/-! ### The corner shapes after the rewrite phase -/

theorem removed_mono {R C : ℕ} (st : RWState) (f : Frame) {x : ℕ × ℕ} (hx : x ∈ st.removed) :
    x ∈ (rwStep R C st f).removed := by
  rw [rwStep_dec]
  cases rwDec R C st f with
  | none => exact hx
  | some KM => exact List.mem_append_left _ hx

theorem shapes_mem : rw1.removed ∈ shapes ∧ rw1.removed.map Prod.swap ∈ shapes ∧ rw2.removed ∈ shapes ∧
    rw3.removed ∈ shapes ∧ ([] : List (ℕ × ℕ)) ∈ shapes := by decide

theorem pair_shape {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) {st : RWState} (hg : Good R C st)
    (fr fc : Bool) (hfree : ∀ x ∈ st.removed, ¬ Win R C fr fc x) :
    ∃ S, CornerShape R C (rwStep R C (rwStep R C st ⟨fr, fc, false⟩) ⟨fr, fc, true⟩).removed fr fc S := by
  have R4 : 4 ≤ R := by omega
  have C4 : 4 ≤ C := by omega
  set f : Frame := ⟨fr, fc, false⟩ with hf
  set g : Frame := ⟨fr, fc, true⟩ with hg'
  have df := dec_free R4 C4 (f := f) hfree
  cases hv : rewritesAt (makeView R C f st.eff) with
  | some rw =>
    rw [hv] at df
    have hK := (dec_facts R4 C4 hg df).2.2.2
    rw [step_after_fire (f := f) (g := g) ⟨rfl, rfl⟩ hK df, rwStep_dec, df]
    have hS : rw.removed ∈ shapes := by
      rcases rewritesAt_cases hv with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact shapes_mem.2.2.2.1
      · exact shapes_mem.2.2.1
      · exact shapes_mem.1
    refine ⟨rw.removed, hS, fun x hx => ?_⟩
    simp only [Option.map_some, applyDec, List.mem_append, List.mem_map]
    constructor
    · rintro (h | ⟨a, ha, rfl⟩)
      · exact absurd hx (hfree x h)
      · exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact Or.inr ⟨a, ha, rfl⟩
  | none =>
    rw [hv] at df
    have s1 : rwStep R C st f = st := by rw [rwStep_dec, df]; rfl
    rw [s1]
    have dg := dec_free R4 C4 (f := g) hfree
    cases hvt : rewritesAt (makeView R C g st.eff) with
    | none =>
      rw [hvt] at dg
      rw [rwStep_dec, dg]
      refine ⟨[], shapes_mem.2.2.2.2, fun x hx => ?_⟩
      simp only [Option.map_none, applyDec, List.not_mem_nil, false_and, exists_false, iff_false]
      exact fun h => hfree x h hx
    | some rw =>
      rw [hvt] at dg
      rw [rwStep_dec, dg]
      have hc := rewritesAt_cases hvt
      -- R2 and R3 are symmetric; R1 transposes
      have key : ∃ S ∈ shapes, ∀ y, y ∈ rw.removed.map Prod.swap ↔ y ∈ S := by
        rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
        · refine ⟨rw3.removed, shapes_mem.2.2.2.1, fun y => ?_⟩
          have hs := rw_removed_symm rw3 (by simp)
          simp only [List.all_eq_true, decide_eq_true_eq] at hs
          exact ⟨fun h => hs.1 y h, fun h => hs.2 y h⟩
        · refine ⟨rw2.removed, shapes_mem.2.2.1, fun y => ?_⟩
          have hs := rw_removed_symm rw2 (by simp)
          simp only [List.all_eq_true, decide_eq_true_eq] at hs
          exact ⟨fun h => hs.1 y h, fun h => hs.2 y h⟩
        · exact ⟨_, shapes_mem.2.1, fun y => Iff.rfl⟩
      obtain ⟨S, hS, hSe⟩ := key
      refine ⟨S, hS, fun x hx => ?_⟩
      simp only [Option.map_some, applyDec, List.mem_append, List.mem_map]
      constructor
      · rintro (h | ⟨a, ha, rfl⟩)
        · exact absurd hx (hfree x h)
        · refine ⟨a.swap, (hSe a.swap).mp (List.mem_map.mpr ⟨a, ha, rfl⟩), ?_⟩
          rw [hg', back_flipT]
      · rintro ⟨b, hb, rfl⟩
        obtain ⟨a, ha, hab⟩ := List.mem_map.mp ((hSe b).mpr hb)
        refine Or.inr ⟨a, ha, ?_⟩
        rw [hg', back_flipT, hab]

theorem shape_steps {R C : ℕ} (hR : 8 ≤ R) (hC : 8 ≤ C) (fr fc : Bool) (S : List (ℕ × ℕ)) :
    ∀ (fs : List Frame) {st : RWState}, Good R C st → CornerShape R C st.removed fr fc S →
      (∀ f ∈ fs, ¬ (f.fr = fr ∧ f.fc = fc)) → CornerShape R C (fs.foldl (rwStep R C) st).removed fr fc S
  | [], _, _, h, _ => h
  | f :: fs, st, hg, h, hfs => by
    simp only [List.foldl_cons]
    apply shape_steps hR hC fr fc S fs (good_step (by omega) (by omega) hg f) _
      (fun g hg' => hfs g (List.mem_cons_of_mem _ hg'))
    refine ⟨h.1, fun x hx => ?_⟩
    rw [← h.2 x hx]
    constructor
    · intro hx'
      rcases removed_step (by omega) (by omega) hg f hx' with h' | h'
      · exact h'
      · exact absurd (win_disj hR hC h' hx) (hfs f List.mem_cons_self)
    · exact removed_mono st f

theorem inWins_steps {R C : ℕ} (hR : 4 ≤ R) (hC : 4 ≤ C) : ∀ (fs : List Frame) {st : RWState},
    Good R C st → (∀ x ∈ st.removed, ∃ fr fc, Win R C fr fc x) →
      ∀ x ∈ (fs.foldl (rwStep R C) st).removed, ∃ fr fc, Win R C fr fc x
  | [], _, _, h => h
  | f :: fs, st, hg, h => by
    simp only [List.foldl_cons]
    apply inWins_steps hR hC fs (good_step hR hC hg f)
    intro x hx
    rcases removed_step hR hC hg f hx with h' | h'
    · exact h x h'
    · exact ⟨_, _, h'⟩

/-- **After the rewrite phase, every corner holds one of the shapes.** -/
theorem remShape_rewriteAll {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) {s0 : RWState}
    (hg : Good R C s0) (h0 : s0.removed = []) :
    RemShape R C (frames.foldl (rwStep R C) s0).removed := by
  have R4 : 4 ≤ R := by omega
  have C4 : 4 ≤ C := by omega
  have R8 : 8 ≤ R := by omega
  have C8 : 8 ≤ C := by omega
  rw [frames_eq]
  have free0 : ∀ x ∈ s0.removed, ∀ fr fc, ¬ Win R C fr fc x := by simp [h0]
  refine ⟨?_, ?_⟩
  · exact inWins_steps R4 C4 _ hg (by simp [h0])
  · intro fr fc
    -- the pair of steps at corner (fr, fc), and the steps before and after it
    have split : ∀ (pre post : List Frame),
        [fTL0, fTL1, fTR0, fTR1, fBL0, fBL1, fBR0, fBR1] =
          pre ++ [(⟨fr, fc, false⟩ : Frame), ⟨fr, fc, true⟩] ++ post →
        (∀ f ∈ pre, ¬ (f.fr = fr ∧ f.fc = fc)) → (∀ f ∈ post, ¬ (f.fr = fr ∧ f.fc = fc)) →
        ∃ S, CornerShape R C ([fTL0, fTL1, fTR0, fTR1, fBL0, fBL1, fBR0, fBR1].foldl (rwStep R C) s0).removed
          fr fc S := by
      intro pre post hL hpre hpost
      rw [hL]
      obtain ⟨gp, fp⟩ := free_steps R8 C8 fr fc pre hg (fun x hx => free0 x hx _ _) hpre
      obtain ⟨S, hS⟩ := pair_shape hR hC gp fr fc fp
      refine ⟨S, ?_⟩
      rw [List.foldl_append, List.foldl_append]
      exact shape_steps R8 C8 fr fc S post (good_steps R4 C4 _ gp) hS hpost
    cases fr <;> cases fc
    · exact split [] [fTR0, fTR1, fBL0, fBL1, fBR0, fBR1] rfl (by simp) (by simp)
    · exact split [fTL0, fTL1] [fBL0, fBL1, fBR0, fBR1] rfl (by simp) (by simp)
    · exact split [fTL0, fTL1, fTR0, fTR1] [fBR0, fBR1] rfl (by simp) (by simp)
    · exact split [fTL0, fTL1, fTR0, fTR1, fBL0, fBL1] [] rfl (by simp) (by simp)

/-! ### Positions along the transposed walk -/

theorem idxOf_append_mem {x : ℕ × ℕ} : ∀ {l1 : List (ℕ × ℕ)} (l2 : List (ℕ × ℕ)), x ∈ l1 →
    (l1 ++ l2).idxOf x = l1.idxOf x
  | [], _, h => by simp at h
  | a :: l1, l2, h => by
    simp only [List.cons_append, List.idxOf_cons]
    by_cases ha : a = x
    · simp [ha]
    · have : x ∈ l1 := by rcases List.mem_cons.mp h with e | e; exact absurd e.symm ha; exact e
      have hb : (a == x) = false := by simpa using ha
      simp only [hb, idxOf_append_mem l2 this]

theorem idxOf_append_not_mem {x : ℕ × ℕ} : ∀ {l1 : List (ℕ × ℕ)} (l2 : List (ℕ × ℕ)), x ∉ l1 →
    (l1 ++ l2).idxOf x = l1.length + l2.idxOf x
  | [], _, _ => by simp
  | a :: l1, l2, h => by
    simp only [List.cons_append, List.idxOf_cons, List.length_cons]
    have ha : a ≠ x := fun e => h (e ▸ List.mem_cons_self)
    have hb : (a == x) = false := by simpa using ha
    simp only [hb, Bool.false_eq_true, ↓reduceIte, idxOf_append_not_mem l2 (fun hx => h (List.mem_cons_of_mem _ hx))]
    omega

theorem idxOf_reverse {l : List (ℕ × ℕ)} {x : ℕ × ℕ} (h : l.count x = 1) :
    l.reverse.idxOf x = l.length - 1 - l.idxOf x := by
  have hx : x ∈ l := List.count_pos_iff.mp (by omega)
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hx
  rw [List.count_append, List.count_cons_self] at h
  have hA : x ∉ A := fun hm => by have := List.count_pos_iff.mpr hm; omega
  have hB : x ∉ B := fun hm => by have := List.count_pos_iff.mpr hm; omega
  rw [idxOf_append_not_mem _ hA, List.idxOf_cons_self, List.reverse_append, List.reverse_cons,
    List.append_assoc, idxOf_append_not_mem _ (by simpa using hB)]
  simp

theorem idx_rr {T Y : List (ℕ × ℕ)} {x : ℕ × ℕ} (h : (T ++ Y).count x = 1) :
    ((T.reverse ++ Y.reverse).map Prod.swap).idxOf x.swap =
      rr T.length (T ++ Y).length ((T ++ Y).idxOf x) := by
  rw [idxOf_map_inj Prod.swap_injective]
  rw [List.count_append] at h
  unfold rr
  by_cases hT : x ∈ T
  · have hTc : T.count x = 1 := by have := List.count_pos_iff.mpr hT; omega
    rw [idxOf_append_mem _ (by simpa using hT), idxOf_append_mem _ hT, idxOf_reverse hTc]
    have : T.idxOf x < T.length := List.idxOf_lt_length_iff.mpr hT
    rw [ite_eq_left this]
  · have hTc : T.count x = 0 := List.count_eq_zero.mpr hT
    have hYc : Y.count x = 1 := by omega
    have hY : x ∈ Y := List.count_pos_iff.mp (by omega)
    rw [idxOf_append_not_mem _ (by simpa using hT), idxOf_append_not_mem _ hT, idxOf_reverse hYc,
      List.length_reverse, List.length_append]
    have : Y.idxOf x < Y.length := List.idxOf_lt_length_iff.mpr hY
    rw [ite_eq_right (by omega)]
    omega

theorem count_swapWalk {T Y : List (ℕ × ℕ)} (x : ℕ × ℕ) :
    ((T.reverse ++ Y.reverse).map Prod.swap).count x.swap = (T ++ Y).count x := by
  rw [List.count_map_of_injective _ _ Prod.swap_injective, List.count_append, List.count_append,
    List.count_reverse, List.count_reverse]

/-- **The R test on the transposed state.** -/
theorem effAltFrom_swap {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) {st : RWState} (hg : Good R C st)
    (hcol : st.eff.map (·.2) = [0, 0, 1, 1]) (hrem : RemShape R C st.removed) :
    effAltFrom C R (swapSt st) = effAltFrom R C st := by
  obtain ⟨T, Y, hW, hW'⟩ := walk3_swap hR hC hrem
  obtain ⟨E, rem, an⟩ := st
  simp only at hcol hW hW' hg
  unfold effAltFrom swapSt
  dsimp only
  rw [hW', hW]
  have g2 : (swapPts E).any (fun q => (rem.map Prod.swap).contains q.1) =
      E.any (fun q => rem.contains q.1) := by
    unfold swapPts; rw [List.any_map]; simp only [Function.comp_def, contains_swap]
  have g3 : ((swapPts E).map (·.1)).dedup.length = (E.map (·.1)).dedup.length := by
    unfold swapPts
    rw [List.map_map]
    have : ((·.1) ∘ fun q : Pt => (q.1.swap, q.2)) = Prod.swap ∘ (·.1) := rfl
    rw [this, ← List.map_map]
    exact dedup_length_map_inj (fun x _ y _ h => Prod.swap_injective h)
  have g4 : ((swapPts E).map fun q => (positions ((T.reverse ++ Y.reverse).map Prod.swap) q.1, q.2)).any
        (fun pl => pl.1.length != 1) =
      (E.map fun q => (positions (T ++ Y) q.1, q.2)).any (fun pl => pl.1.length != 1) := by
    unfold swapPts
    rw [List.map_map, List.any_map, List.any_map]
    apply any_congr'
    intro q _
    simp only [Function.comp, positions_length, count_swapWalk]
  rw [g2, g3, g4]
  split_ifs with h1 h2 h3 h4
  · rfl
  · rfl
  · rfl
  · rfl
  · have hc1 : ∀ q ∈ E, (T ++ Y).count q.1 = 1 := by
      intro q hq
      by_contra hne
      apply h4
      rw [List.any_eq_true]
      exact ⟨(positions (T ++ Y) q.1, q.2), List.mem_map.mpr ⟨q, hq, rfl⟩, by simpa [positions_length] using hne⟩
    have hin : ∀ q ∈ E, q.1 ∈ T ++ Y := fun q hq => List.count_pos_iff.mp (by rw [hc1 q hq]; omega)
    have hn := hg.1
    rcases E with _ | ⟨⟨e0, c0⟩, _ | ⟨⟨e1, c1⟩, _ | ⟨⟨e2, c2⟩, _ | ⟨⟨e3, c3⟩, _ | ⟨q, E⟩⟩⟩⟩⟩ <;>
      simp at hcol
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hcol
    simp only [cellsOf, List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨⟨d01, d02, d03⟩, ⟨d12, d13⟩, d23, -⟩ := hn
    have c0' : (T ++ Y).count e0 = 1 := hc1 (e0, 0) (by simp)
    have c1' : (T ++ Y).count e1 = 1 := hc1 (e1, 0) (by simp)
    have c2' : (T ++ Y).count e2 = 1 := hc1 (e2, 1) (by simp)
    have c3' : (T ++ Y).count e3 = 1 := hc1 (e3, 1) (by simp)
    have i0 : e0 ∈ T ++ Y := hin (e0, 0) (by simp)
    have i1 : e1 ∈ T ++ Y := hin (e1, 0) (by simp)
    have i2 : e2 ∈ T ++ Y := hin (e2, 1) (by simp)
    have i3 : e3 ∈ T ++ Y := hin (e3, 1) (by simp)
    have w : ∀ x, x ∈ T ++ Y → x.swap ∈ (T.reverse ++ Y.reverse).map Prod.swap := fun x hx =>
      List.mem_map.mpr ⟨x, by simp only [List.mem_append, List.mem_reverse] at hx ⊢; exact hx, rfl⟩
    simp only [swapPts, List.map_cons, List.map_nil, positions_head (w _ i0), positions_head (w _ i1),
      positions_head (w _ i2), positions_head (w _ i3), positions_head i0, positions_head i1,
      positions_head i2, positions_head i3, idx_rr c0', idx_rr c1', idx_rr c2', idx_rr c3']
    set n := (T ++ Y).length
    have L := fun {x : ℕ × ℕ} (hx : x ∈ T ++ Y) => (List.idxOf_lt_length_iff.mpr hx : (T ++ Y).idxOf x < n)
    have D := fun {x y : ℕ × ℕ} (hx : x ∈ T ++ Y) (hy : y ∈ T ++ Y) (hxy : x ≠ y) =>
      (fun e => hxy (idxOf_inj hx hy e) : (T ++ Y).idxOf x ≠ (T ++ Y).idxOf y)
    have hm : T.length ≤ n := by simp [n]
    have RD := fun {x y : ℕ × ℕ} (hx : x ∈ T ++ Y) (hy : y ∈ T ++ Y) (hxy : x ≠ y) =>
      rr_inj hm (L hx) (L hy) (D hx hy hxy)
    apply Bool.eq_iff_iff.mpr
    rw [alt_cross (RD i0 i1 d01) (RD i0 i2 d02) (RD i0 i3 d03) (RD i1 i2 d12) (RD i1 i3 d13) (RD i2 i3 d23),
      alt_cross (D i0 i1 d01) (D i0 i2 d02) (D i0 i3 d03) (D i1 i2 d12) (D i1 i3 d13) (D i2 i3 d23),
      crosses_rr hm (L i0) (L i1) (L i2) (L i3) (D i0 i1 d01) (D i0 i2 d02) (D i0 i3 d03) (D i1 i2 d12)
        (D i1 i3 d13) (D i2 i3 d23)]

/-! ### Assembly -/

theorem mem_swapPts {l : List Pt} {q : Pt} : q ∈ swapPts l ↔ (q.1.swap, q.2) ∈ l := by
  unfold swapPts
  simp only [List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩; simpa using hp
  · intro h; exact ⟨_, h, by simp⟩

theorem cells_swapPts (l : List Pt) : cellsOf (swapPts l) = (cellsOf l).map Prod.swap := by
  unfold cellsOf swapPts; rw [List.map_map, List.map_map]; rfl

/-- **The R test is symmetric under transposition.** -/
theorem effAlt3_transpose {I : Inst} (hI : InDom I) :
    effAlt3 I.h I.w (swapPts [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)]) =
      effAlt3 I.w I.h [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)] := by
  obtain ⟨hw, hh, b0, b1, b2, b3, d1, d2, d3, d4, d5, d6⟩ := hI
  set pts : List Pt := [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)] with hpts
  set s0 : RWState := ⟨pts, [], false⟩ with hs0
  have g0 : Good I.w I.h s0 := by
    refine ⟨?_, ?_⟩
    · simp only [hs0, hpts, cellsOf, List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, not_or]
      exact ⟨⟨d1, d2, d3⟩, ⟨d4, d5⟩, d6, by simp, List.nodup_nil⟩
    · intro q hq
      simp only [hs0, hpts, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact b0
      · exact b1
      · exact b2
      · exact b3
  have R8 : 8 ≤ I.w := by omega
  have C8 : 8 ≤ I.h := by omega
  have hQP := rewrite_order R8 C8 g0 rfl
  set Q := (frames.map Frame.tp).foldl (rwStep I.w I.h) s0
  set P := frames.foldl (rwStep I.w I.h) s0
  have hP : rewriteAll I.w I.h pts = P := rfl
  rw [effAlt3_eq, effAlt3_eq, rewriteAll_tp, hP]
  have gP := good_steps (by omega) (by omega) frames g0
  -- Q and P give the same answer
  have e1 : effAltFrom I.h I.w (swapSt Q) = effAltFrom I.h I.w (swapSt P) := by
    obtain ⟨gQ, gP', he, hr, ha⟩ := hQP
    apply effAltFrom_congr
    · simp only [swapSt, cells_swapPts]; exact gQ.1.map Prod.swap_injective
    · simp only [swapSt, cells_swapPts]; exact gP'.1.map Prod.swap_injective
    · intro q; simp only [swapSt, mem_swapPts, he]
    · intro x
      simp only [swapSt, List.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩; exact ⟨y, (hr y).mp hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩; exact ⟨y, (hr y).mpr hy, rfl⟩
    · simp only [swapSt]; exact ha
  rw [e1]
  apply effAltFrom_swap (by omega) (by omega) gP
  · show P.eff.map (·.2) = [0, 0, 1, 1]
    rw [snd_steps]
    rfl
  · exact remShape_rewriteAll (by omega) (by omega) g0 rfl

/-- **`passT`: passing the catalogue is symmetric under transposition.** -/
theorem passT {I : Inst} (hI : InDom I) (hP : Passes I) : Passes I.transpose := by
  unfold Passes at hP ⊢
  show fires3 I.h I.w I.s0.swap I.t0.swap I.s1.swap I.t1.swap = false
  rw [fires3_transpose hI (effAlt3_transpose hI)]
  exact hP

/-- What Theorem A still assumes: the computation. -/
structure FactsFinite : Prop where
  finite : ∀ I, InDom I → I.w ≤ 22 → I.h ≤ 22 → Passes I → ¬ Reducible I →
    MoveOK I ∨ Solvable I

/-- **Theorem A**, assuming only the finite computation. -/
theorem theoremA_fin (F : FactsFinite) (I : Inst) (hwf : I.WellFormed) (hw : 11 ≤ I.w) (hh : 11 ≤ I.h)
    (hP : Passes I) : Solvable I :=
  theoremA'' ⟨fun _ hI hP => passT hI hP, F.finite⟩ I hwf hw hh hP

end ZZN

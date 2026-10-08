-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.TheoremB

/-!
# Soundness of R (effective alternation)

Plan:
1. The rewrite phase, as functions of the original endpoints.
2. Forced routes: the solution paths, cut at the settled cells.
3. Exits from the effective endpoints to the perimeter, in doubled coordinates; then `t1_core`.
-/

namespace ZZN

open GridHam

/-! ### Moves as maps on the endpoint list -/

/-- Apply a list of moves to one cell. -/
def applyMoves (M : List ((ℕ × ℕ) × (ℕ × ℕ))) (x : ℕ × ℕ) : ℕ × ℕ :=
  M.foldl (fun y m => if y = m.1 then m.2 else y) x

theorem moveFirst_eq_map {l : List Pt} (hn : (cellsOf l).Nodup) (m : (ℕ × ℕ) × (ℕ × ℕ)) :
    moveFirst l m = l.map (fun q => if q.1 = m.1 then (m.2, q.2) else q) := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    simp only [cellsOf, List.map_cons, List.nodup_cons, List.mem_map] at hn
    rw [moveFirst_cons, List.map_cons]
    split_ifs with h
    · congr 1
      conv_lhs => rw [← List.map_id l]
      apply List.map_congr_left
      intro y hy
      have : y.1 ≠ m.1 := fun e => hn.1 ⟨y, hy, e.trans h.symm⟩
      simp [this]
    · rw [ih hn.2]

theorem foldl_moveFirst_eq : ∀ (M : List ((ℕ × ℕ) × (ℕ × ℕ))) {l : List Pt}, (cellsOf l).Nodup →
    Fresh l M → M.foldl moveFirst l = l.map (fun q => (applyMoves M q.1, q.2))
  | [], l, _, _ => by
    conv_lhs => rw [← List.map_id l]
    rfl
  | m :: M, l, hn, ⟨hf, hp⟩ => by
    simp only [List.foldl_cons]
    rw [List.pairwise_cons] at hp
    have hn' := nodup_moveFirst m hn (hf m List.mem_cons_self)
    have hf' : Fresh (moveFirst l m) M := by
      refine ⟨fun m' hm' hc => ?_, hp.2⟩
      rcases cells_moveFirst_sub m _ hc with h | h
      · exact hf m' (List.mem_cons_of_mem _ hm') h
      · exact (hp.1 m' hm').1 h.symm
    rw [foldl_moveFirst_eq M hn' hf', moveFirst_eq_map hn, List.map_map]
    apply List.map_congr_left
    intro q _
    simp only [Function.comp, applyMoves, List.foldl_cons]
    split_ifs <;> rfl

/-! ### The rewrite phase, corner by corner -/

/-- The rewrite at corner `(fr, fc)`, decided on the original endpoints: the unflipped
orientation first. -/
def decC (R C : ℕ) (pts : List Pt) (fr fc : Bool) : Option (List (ℕ × ℕ) × List ((ℕ × ℕ) × (ℕ × ℕ))) :=
  match rewritesAt (makeView R C ⟨fr, fc, false⟩ pts) with
  | some rw => some (rw.removed.map (Frame.back R C ⟨fr, fc, false⟩),
      rw.moves.map fun m => (Frame.back R C ⟨fr, fc, false⟩ m.1, Frame.back R C ⟨fr, fc, false⟩ m.2))
  | none => (rewritesAt (makeView R C ⟨fr, fc, true⟩ pts)).map fun rw =>
      (rw.removed.map (Frame.back R C ⟨fr, fc, true⟩),
        rw.moves.map fun m => (Frame.back R C ⟨fr, fc, true⟩ m.1, Frame.back R C ⟨fr, fc, true⟩ m.2))

theorem AgreeW.trans {R C : ℕ} {fr fc : Bool} {a b c : RWState} (h1 : AgreeW R C fr fc a b)
    (h2 : AgreeW R C fr fc b c) : AgreeW R C fr fc a c :=
  ⟨fun q hq => (h1.1 q hq).trans (h2.1 q hq), fun x hx => (h1.2 x hx).trans (h2.2 x hx)⟩

/-- The two steps at one corner, in a state that agrees with the start on that corner. -/
theorem pair_outcome {R C : ℕ} (hR : 8 ≤ R) (hC : 8 ≤ C) {st s0 : RWState} (hg : Good R C st)
    (hg0 : Good R C s0) (h0 : s0.removed = []) (fr fc : Bool) (hag : AgreeW R C fr fc st s0)
    (_hfree : ∀ x ∈ st.removed, ¬ Win R C fr fc x) :
    rwStep R C (rwStep R C st ⟨fr, fc, false⟩) ⟨fr, fc, true⟩ = applyDec st (decC R C s0.eff fr fc) := by
  have R4 : 4 ≤ R := by omega
  have C4 : 4 ≤ C := by omega
  have free0 : ∀ x ∈ s0.removed, ¬ Win R C fr fc x := by simp [h0]
  have d1 := dec_congr R4 C4 hg hg0 ⟨fr, fc, false⟩ hag
  have d2 := dec_congr R4 C4 hg hg0 ⟨fr, fc, true⟩ hag
  rw [dec_free R4 C4 (st := s0) free0] at d1
  rw [dec_free R4 C4 (st := s0) free0] at d2
  unfold decC
  cases hv : rewritesAt (makeView R C ⟨fr, fc, false⟩ s0.eff) with
  | some rw =>
    rw [hv] at d1
    simp only [Option.map_some] at d1
    have hK := (dec_facts R4 C4 hg d1).2.2.2
    rw [step_after_fire (f := ⟨fr, fc, false⟩) (g := ⟨fr, fc, true⟩) ⟨rfl, rfl⟩ hK d1, rwStep_dec, d1]
  | none =>
    rw [hv] at d1
    simp only [Option.map_none] at d1
    have s1 : rwStep R C st ⟨fr, fc, false⟩ = st := by rw [rwStep_dec, d1]; rfl
    rw [s1, rwStep_dec, d2]

theorem agree_steps {R C : ℕ} (hR : 8 ≤ R) (hC : 8 ≤ C) (fr fc : Bool) {s0 : RWState} :
    ∀ (fs : List Frame) {st : RWState}, Good R C st → AgreeW R C fr fc st s0 →
      (∀ f ∈ fs, ¬ (f.fr = fr ∧ f.fc = fc)) → AgreeW R C fr fc (fs.foldl (rwStep R C) st) s0
  | [], _, _, h, _ => h
  | f :: fs, st, hg, h, hfs => by
    simp only [List.foldl_cons]
    exact agree_steps hR hC fr fc fs (good_step (by omega) (by omega) hg f)
      ((agree_step_other hR hC hg f (hfs f List.mem_cons_self)).trans h)
      (fun g hg' => hfs g (List.mem_cons_of_mem _ hg'))

/-- **The rewrite phase**: each corner applies its own decision, made on the original endpoints. -/
theorem rewriteAll_corners {R C : ℕ} (hR : 8 ≤ R) (hC : 8 ≤ C) {pts : List Pt}
    (hg : Good R C ⟨pts, [], false⟩) :
    rewriteAll R C pts = applyDec (applyDec (applyDec (applyDec ⟨pts, [], false⟩
      (decC R C pts false false)) (decC R C pts false true)) (decC R C pts true false))
      (decC R C pts true true) := by
  have R4 : 4 ≤ R := by omega
  have C4 : 4 ≤ C := by omega
  set s0 : RWState := ⟨pts, [], false⟩ with hs0
  unfold rewriteAll
  rw [frames_eq]
  simp only [List.foldl_cons, List.foldl_nil]
  have refl0 : ∀ fr fc, AgreeW R C fr fc s0 s0 := fun _ _ => ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
  have free0 : ∀ x ∈ s0.removed, ∀ fr fc, ¬ Win R C fr fc x := by simp [hs0]
  -- corner TL
  have e1 := pair_outcome hR hC hg hg rfl false false (refl0 _ _) (fun x hx => free0 x hx _ _)
  rw [e1]
  have g1 : Good R C (applyDec s0 (decC R C pts false false)) := by
    rw [← e1]
    have := good_steps R4 C4 [fTL0, fTL1] hg
    simp only [List.foldl_cons, List.foldl_nil] at this
    exact this
  -- corner TR
  have a2 : AgreeW R C false true (applyDec s0 (decC R C pts false false)) s0 := by
    rw [← e1]
    have := agree_steps hR hC false true [fTL0, fTL1] hg (refl0 _ _) (by simp)
    simp only [List.foldl_cons, List.foldl_nil] at this
    exact this
  have f2 : ∀ x ∈ (applyDec s0 (decC R C pts false false)).removed, ¬ Win R C false true x := by
    rw [← e1]
    have := (free_steps hR hC false true [fTL0, fTL1] hg (fun x hx => free0 x hx _ _) (by simp)).2
    simp only [List.foldl_cons, List.foldl_nil] at this
    exact this
  have e2 := pair_outcome hR hC g1 hg rfl false true a2 f2
  rw [e2]
  have g2 : Good R C (applyDec (applyDec s0 (decC R C pts false false)) (decC R C pts false true)) := by
    rw [← e2]
    have := good_steps R4 C4 [fTR0, fTR1] g1
    simp only [List.foldl_cons, List.foldl_nil] at this
    exact this
  -- corner BL
  have a3 : AgreeW R C true false (applyDec (applyDec s0 (decC R C pts false false)) (decC R C pts false true)) s0 := by
    rw [← e2, ← e1]
    have := agree_steps hR hC true false [fTL0, fTL1, fTR0, fTR1] hg (refl0 _ _) (by simp)
    simp only [List.foldl_cons, List.foldl_nil] at this
    exact this
  have f3 : ∀ x ∈ (applyDec (applyDec s0 (decC R C pts false false)) (decC R C pts false true)).removed,
      ¬ Win R C true false x := by
    rw [← e2, ← e1]
    have := (free_steps hR hC true false [fTL0, fTL1, fTR0, fTR1] hg (fun x hx => free0 x hx _ _) (by simp)).2
    simp only [List.foldl_cons, List.foldl_nil] at this
    exact this
  have e3 := pair_outcome hR hC g2 hg rfl true false a3 f3
  rw [e3]
  have g3 := good_steps R4 C4 [fBL0, fBL1] g2
  simp only [List.foldl_cons, List.foldl_nil] at g3
  rw [e3] at g3
  -- corner BR
  have a4 : AgreeW R C true true (applyDec (applyDec (applyDec s0 (decC R C pts false false))
      (decC R C pts false true)) (decC R C pts true false)) s0 := by
    rw [← e3, ← e2, ← e1]
    have := agree_steps hR hC true true [fTL0, fTL1, fTR0, fTR1, fBL0, fBL1] hg (refl0 _ _) (by simp)
    simp only [List.foldl_cons, List.foldl_nil] at this
    exact this
  have f4 : ∀ x ∈ (applyDec (applyDec (applyDec s0 (decC R C pts false false))
      (decC R C pts false true)) (decC R C pts true false)).removed, ¬ Win R C true true x := by
    rw [← e3, ← e2, ← e1]
    have := (free_steps hR hC true true [fTL0, fTL1, fTR0, fTR1, fBL0, fBL1] hg
      (fun x hx => free0 x hx _ _) (by simp)).2
    simp only [List.foldl_cons, List.foldl_nil] at this
    exact this
  exact pair_outcome hR hC g3 hg rfl true true a4 f4

/-- A decision taken by the rewrite at a corner, with its facts. -/
theorem decC_facts {R C : ℕ} (hR : 8 ≤ R) (hC : 8 ≤ C) {st s0 : RWState} (hg : Good R C st)
    (hg0 : Good R C s0) (h0 : s0.removed = []) {fr fc : Bool} (hag : AgreeW R C fr fc st s0)
    (_hfree : ∀ x ∈ st.removed, ¬ Win R C fr fc x) {K : List (ℕ × ℕ)} {M : List ((ℕ × ℕ) × (ℕ × ℕ))}
    (hd : decC R C s0.eff fr fc = some (K, M)) :
    Fresh st.eff M ∧ (∀ x ∈ K, Win R C fr fc x) ∧ (∀ m ∈ M, Win R C fr fc m.1 ∧ Win R C fr fc m.2) := by
  have R4 : 4 ≤ R := by omega
  have C4 : 4 ≤ C := by omega
  have free0 : ∀ x ∈ s0.removed, ¬ Win R C fr fc x := by simp [h0]
  have d1 := dec_congr R4 C4 hg hg0 ⟨fr, fc, false⟩ hag
  have d2 := dec_congr R4 C4 hg hg0 ⟨fr, fc, true⟩ hag
  rw [dec_free R4 C4 (st := s0) free0] at d1
  rw [dec_free R4 C4 (st := s0) free0] at d2
  unfold decC at hd
  cases hv : rewritesAt (makeView R C ⟨fr, fc, false⟩ s0.eff) with
  | some rw =>
    rw [hv] at hd d1
    simp only [Option.map_some] at d1
    simp only [Option.some.injEq] at hd
    rw [hd] at d1
    obtain ⟨a, b, c, -⟩ := dec_facts R4 C4 hg d1
    exact ⟨c, a, b⟩
  | none =>
    rw [hv] at hd
    simp only at hd
    rw [hd] at d2
    obtain ⟨a, b, c, -⟩ := dec_facts R4 C4 hg d2
    exact ⟨c, a, b⟩

theorem applyDec_eff {R C : ℕ} {st : RWState} (hg : Good R C st) {d : Option (List (ℕ × ℕ) × List ((ℕ × ℕ) × (ℕ × ℕ)))}
    (hf : ∀ K M, d = some (K, M) → Fresh st.eff M) :
    (applyDec st d).eff = st.eff.map fun q => (applyMoves (d.elim [] Prod.snd) q.1, q.2) := by
  cases d with
  | none =>
    simp only [applyDec, Option.elim]
    conv_lhs => rw [← List.map_id st.eff]
    rfl
  | some KM =>
    obtain ⟨K, M⟩ := KM
    simp only [applyDec, Option.elim]
    exact foldl_moveFirst_eq M hg.1 (hf K M rfl)

def KofD (d : Option (List (ℕ × ℕ) × List ((ℕ × ℕ) × (ℕ × ℕ)))) : List (ℕ × ℕ) := d.elim [] Prod.fst
def MofD (d : Option (List (ℕ × ℕ) × List ((ℕ × ℕ) × (ℕ × ℕ)))) : List ((ℕ × ℕ) × (ℕ × ℕ)) := d.elim [] Prod.snd

/-- One corner's stage of the rewrite phase. -/
theorem stage {R C : ℕ} (hR : 8 ≤ R) (hC : 8 ≤ C) {st s0 : RWState} (hg : Good R C st)
    (hg0 : Good R C s0) (h0 : s0.removed = []) (fr fc : Bool) (hag : AgreeW R C fr fc st s0)
    (hfree : ∀ x ∈ st.removed, ¬ Win R C fr fc x) :
    let st' := applyDec st (decC R C s0.eff fr fc)
    Good R C st' ∧ st'.eff = st.eff.map (fun q => (applyMoves (MofD (decC R C s0.eff fr fc)) q.1, q.2)) ∧
      (∀ x, x ∈ st'.removed ↔ x ∈ st.removed ∨ x ∈ KofD (decC R C s0.eff fr fc)) ∧
      (∀ x ∈ KofD (decC R C s0.eff fr fc), Win R C fr fc x) ∧
      (∀ m ∈ MofD (decC R C s0.eff fr fc), Win R C fr fc m.1 ∧ Win R C fr fc m.2) ∧
      (∀ fr' fc', ¬ (fr = fr' ∧ fc = fc') → AgreeW R C fr' fc' st s0 → AgreeW R C fr' fc' st' s0) := by
  intro st'
  have R4 : 4 ≤ R := by omega
  have C4 : 4 ≤ C := by omega
  have eq := pair_outcome hR hC hg hg0 h0 fr fc hag hfree
  have win : (∀ x ∈ KofD (decC R C s0.eff fr fc), Win R C fr fc x) ∧
      (∀ m ∈ MofD (decC R C s0.eff fr fc), Win R C fr fc m.1 ∧ Win R C fr fc m.2) := by
    cases hd : decC R C s0.eff fr fc with
    | none => simp [KofD, MofD]
    | some KM =>
      obtain ⟨K, M⟩ := KM
      obtain ⟨-, a, b⟩ := decC_facts hR hC hg hg0 h0 hag hfree hd
      exact ⟨a, b⟩
  refine ⟨?_, ?_, ?_, win.1, win.2, ?_⟩
  · show Good R C (applyDec st _)
    rw [← eq]
    exact good_step R4 C4 (good_step R4 C4 hg _) _
  · show (applyDec st _).eff = _
    apply applyDec_eff hg
    intro K M hd
    exact (decC_facts hR hC hg hg0 h0 hag hfree hd).1
  · intro x
    show x ∈ (applyDec st _).removed ↔ _
    cases decC R C s0.eff fr fc with
    | none => simp [applyDec, KofD]
    | some KM => simp [applyDec, KofD]
  · intro fr' fc' hne h
    show AgreeW R C fr' fc' (applyDec st _) s0
    rw [← eq]
    have := agree_steps hR hC fr' fc' (s0 := st) [⟨fr, fc, false⟩, ⟨fr, fc, true⟩] hg
      ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩ (by simp; tauto)
    simp only [List.foldl_cons, List.foldl_nil] at this
    exact this.trans h

/-- **The rewrite phase in closed form.** -/
theorem rewriteAll_closed {R C : ℕ} (hR : 8 ≤ R) (hC : 8 ≤ C) {pts : List Pt}
    (hg : Good R C ⟨pts, [], false⟩) :
    let d := fun fr fc => decC R C pts fr fc
    (rewriteAll R C pts).eff = pts.map (fun q => (applyMoves (MofD (d false false) ++ MofD (d false true) ++
        MofD (d true false) ++ MofD (d true true)) q.1, q.2)) ∧
      (∀ x, x ∈ (rewriteAll R C pts).removed ↔ ∃ fr fc, x ∈ KofD (d fr fc)) ∧
      (∀ fr fc, ∀ x ∈ KofD (d fr fc), Win R C fr fc x) ∧
      (∀ fr fc, ∀ m ∈ MofD (d fr fc), Win R C fr fc m.1 ∧ Win R C fr fc m.2) ∧
      Good R C (rewriteAll R C pts) := by
  intro d
  set s0 : RWState := ⟨pts, [], false⟩ with hs0
  have refl0 : ∀ fr fc, AgreeW R C fr fc s0 s0 := fun _ _ => ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
  have wins : ∀ fr fc, (∀ x ∈ KofD (d fr fc), Win R C fr fc x) ∧
      (∀ m ∈ MofD (d fr fc), Win R C fr fc m.1 ∧ Win R C fr fc m.2) := by
    intro fr fc
    obtain ⟨-, -, -, a, b, -⟩ := stage hR hC hg hg rfl fr fc (refl0 _ _) (by simp [hs0])
    exact ⟨a, b⟩
  obtain ⟨g1, e1, r1, -, -, ag1⟩ := stage hR hC hg hg rfl false false (refl0 _ _) (by simp [hs0])
  set A1 := applyDec s0 (decC R C s0.eff false false)
  have free : ∀ (st : RWState) (fr fc : Bool), (∀ x, x ∈ st.removed → ∃ fr' fc', ¬ (fr' = fr ∧ fc' = fc) ∧
      x ∈ KofD (d fr' fc')) → ∀ x ∈ st.removed, ¬ Win R C fr fc x := by
    intro st fr fc h x hx hw
    obtain ⟨fr', fc', hne, hk⟩ := h x hx
    exact hne (win_disj hR hC ((wins fr' fc').1 x hk) hw)
  obtain ⟨g2, e2, r2, -, -, ag2⟩ := stage hR hC g1 hg rfl false true (ag1 false true (by decide) (refl0 _ _))
    (free A1 false true (fun x hx => by
      rcases (r1 x).mp hx with h | h
      · simp [hs0] at h
      · exact ⟨false, false, by decide, h⟩))
  set A2 := applyDec A1 (decC R C s0.eff false true)
  obtain ⟨g3, e3, r3, -, -, ag3⟩ := stage hR hC g2 hg rfl true false
    (ag2 true false (by decide) (ag1 true false (by decide) (refl0 _ _)))
    (free A2 true false (fun x hx => by
      rcases (r2 x).mp hx with h | h
      · rcases (r1 x).mp h with h' | h'
        · simp [hs0] at h'
        · exact ⟨false, false, by decide, h'⟩
      · exact ⟨false, true, by decide, h⟩))
  set A3 := applyDec A2 (decC R C s0.eff true false)
  obtain ⟨g4, e4, r4, -, -, -⟩ := stage hR hC g3 hg rfl true true
    (ag3 true true (by decide) (ag2 true true (by decide) (ag1 true true (by decide) (refl0 _ _))))
    (free A3 true true (fun x hx => by
      rcases (r3 x).mp hx with h | h
      · rcases (r2 x).mp h with h' | h'
        · rcases (r1 x).mp h' with h'' | h''
          · simp [hs0] at h''
          · exact ⟨false, false, by decide, h''⟩
        · exact ⟨false, true, by decide, h'⟩
      · exact ⟨true, false, by decide, h⟩))
  have hfin := rewriteAll_corners hR hC hg
  refine ⟨?_, ?_, fun fr fc => (wins fr fc).1, fun fr fc => (wins fr fc).2, ?_⟩
  · rw [hfin, e4, e3, e2, e1]
    simp only [List.map_map]
    apply List.map_congr_left
    intro q _
    simp only [Function.comp, applyMoves, List.foldl_append]
    rfl
  · intro x
    rw [hfin, r4, r3, r2, r1]
    simp only [hs0, List.not_mem_nil, false_or]
    constructor
    · rintro (((h | h) | h) | h)
      · exact ⟨false, false, h⟩
      · exact ⟨false, true, h⟩
      · exact ⟨true, false, h⟩
      · exact ⟨true, true, h⟩
    · rintro ⟨fr, fc, h⟩
      cases fr <;> cases fc
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  · rw [hfin]; exact g4

/-! ### Forced routes: list lemmas -/

/-- The next cell after `x` (arrived at from `x'`) along a path is `z`, if `z` is a path
neighbour of `x` other than `x'`. -/
theorem next_cell {L : List Coord} {x' x z : Coord} (hn : L.Nodup) (h1 : [x', x] <:+: L)
    (hz : Used L x z) (hne : z ≠ x') : [x, z] <:+: L := by
  rcases hz with h | h
  · exact h
  · exact absurd (pred_unique hn h h1) hne

/-- A forced continuation extends a prefix. -/
theorem prefix_extend {L F : List Coord} {x' x z : Coord} (hn : L.Nodup) (hF : F ++ [x', x] <+: L)
    (hz : Used L x z) (hne : z ≠ x') (hlast : L.getLast? ≠ some x) : F ++ [x', x, z] <+: L := by
  obtain ⟨T, hT⟩ := hF
  cases T with
  | nil =>
    exfalso; apply hlast; rw [← hT]; simp
  | cons t T =>
    have hi : [x', x] <:+: L := ⟨F, t :: T, by rw [← hT]⟩
    have hxt : [x, t] <:+: L := ⟨F ++ [x'], T, by rw [← hT]; simp⟩
    have hxz := next_cell hn hi hz hne
    have := succ_unique hn hxt hxz
    subst this
    exact ⟨T, by rw [← hT]; simp⟩

/-- The first step from the head of a path. -/
theorem prefix_start {L : List Coord} {e z : Coord} (hn : L.Nodup) (hh : L.head? = some e)
    (hz : Used L e z) : [e, z] <+: L := by
  have hez : [e, z] <:+: L := by
    rcases hz with h | h
    · exact h
    · exact absurd h (head_no_pred hn hh)
  obtain ⟨s, t, hL⟩ := infix_pair_iff.mp hez
  cases s with
  | nil => exact ⟨t, by rw [hL]; simp⟩
  | cons a s =>
    exfalso
    rw [hL] at hh hn
    simp at hh
    subst hh
    simp at hn

theorem used_reverse {L : List Coord} {u v : Coord} (h : Used L u v) : Used L.reverse u v := by
  rcases h with h | h
  · right; simpa using List.reverse_infix.mpr h
  · left; simpa using List.reverse_infix.mpr h

/-! ### Forced routes in the identity frame -/

section Forced

variable {J : Inst} {p q : List Coord}

/-- The path of endpoint `E`, read from `E`. -/
def orient (p q : List Coord) (E : Coord) : List Coord :=
  if (pathOf p q E).head? = some E then pathOf p q E else (pathOf p q E).reverse

theorem end_at_end (hS : IsSolution J p q) {E : Coord} (hE : IsEnd J E) :
    (pathOf p q E).head? = some E ∨ (pathOf p q E).getLast? = some E := by
  obtain ⟨m0, m1, m2, m3, n2, n3⟩ := ends_mem hS
  unfold IsEnd at hE
  unfold pathOf
  rcases hE with rfl | rfl | rfl | rfl
  · simp only [m0, ↓reduceIte]; exact Or.inl hS.1.1
  · simp only [m1, ↓reduceIte]; exact Or.inr hS.1.2.1
  · simp only [n2, ↓reduceIte]; exact Or.inl hS.2.1.1
  · simp only [n3, ↓reduceIte]; exact Or.inr hS.2.1.2.1

theorem path_ends (hS : IsSolution J p q) (v : Coord) {x : Coord}
    (h : (pathOf p q v).head? = some x ∨ (pathOf p q v).getLast? = some x) : IsEnd J x := by
  obtain ⟨s, t, hP, hst⟩ := pathOf_isPath hS v
  obtain ⟨hh, hl, -, -, -⟩ := hP
  rcases h with h | h
  · rw [hh] at h
    simp only [Option.some.injEq] at h
    subst h
    rcases hst with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> unfold IsEnd <;> simp
  · rw [hl] at h
    simp only [Option.some.injEq] at h
    subst h
    rcases hst with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> unfold IsEnd <;> simp

theorem orient_facts (hS : IsSolution J p q) {E : Coord} (hE : IsEnd J E) :
    (orient p q E).Nodup ∧ (orient p q E).head? = some E ∧
      (∀ x, x ∈ orient p q E ↔ x ∈ pathOf p q E) ∧
      (∀ x, (orient p q E).getLast? = some x → IsEnd J x) ∧
      (∀ u v, Used (pathOf p q E) u v → Used (orient p q E) u v) := by
  obtain ⟨s, t, hP, -⟩ := pathOf_isPath hS E
  have hn := hP.2.2.1
  unfold orient
  split_ifs with h
  · exact ⟨hn, h, fun _ => Iff.rfl, fun x hx => path_ends hS E (Or.inr hx), fun _ _ h => h⟩
  · have h2 := (end_at_end hS hE).resolve_left h
    refine ⟨List.nodup_reverse.mpr hn, by rw [List.head?_reverse]; exact h2,
      fun _ => List.mem_reverse, fun x hx => path_ends hS E (Or.inl (by rw [List.getLast?_reverse] at hx; exact hx)),
      fun _ _ h => used_reverse h⟩

theorem pathOf_eq (_hS : IsSolution J p q) {u v : Coord} (h : colOf p u = colOf p v) :
    pathOf p q u = pathOf p q v := by
  unfold colOf at h; unfold pathOf
  by_cases hu : u ∈ p <;> by_cases hv : v ∈ p <;> simp only [hu, hv, ↓reduceIte] at h ⊢ <;> omega

/-- A path neighbour of a cell of `E`'s colour is a step of `E`'s oriented path. -/
theorem used_of_nb (hS : IsSolution J p q) {E v u : Coord} (hE : IsEnd J E) (hn : Nb p q v u)
    (hc : colOf p v = colOf p E) : Used (orient p q E) v u := by
  have := (orient_facts hS hE).2.2.2.2 v u
  unfold Nb at hn
  rw [pathOf_eq hS hc] at hn
  exact this hn

/-- A cell that is not an endpoint is not the last cell of an oriented path. -/
theorem not_last (hS : IsSolution J p q) {E x : Coord} (hE : IsEnd J E) (hx : ¬ IsEnd J x) :
    (orient p q E).getLast? ≠ some x := fun h => hx ((orient_facts hS hE).2.2.2.1 x h)

/-- A free corner cell joins its two neighbours. -/
theorem corner_nbs (hS : IsSolution J p q) (h00 : (makeView J.w J.h idF (ptsOf J)).at 0 0 = none)
    (hin : InBounds J.w J.h (0, 0)) : Nb p q (0, 0) (1, 0) ∧ Nb p q (0, 0) (0, 1) := by
  obtain ⟨u, x, hux, hu, hx⟩ := interior hS hin (vat_none h00)
  have mu := adj_mem (nb_adj hS hu)
  have mx := adj_mem (nb_adj hS hx)
  simp [nbrList] at mu mx
  rcases mu with rfl | rfl <;> rcases mx with rfl | rfl
  · exact absurd rfl hux
  · exact ⟨hu, hx⟩
  · exact ⟨hx, hu⟩
  · exact absurd rfl hux

theorem forced_r1 (hS : IsSolution J p q) {a : ℕ}
    (hE : (makeView J.w J.h idF (ptsOf J)).at 0 1 = some a)
    (h00 : (makeView J.w J.h idF (ptsOf J)).at 0 0 = none)
    (_h10 : (makeView J.w J.h idF (ptsOf J)).at 1 0 = none) (hin : InBounds J.w J.h (0, 0)) :
    [(0, 1), (0, 0), (1, 0)] <+: orient p q (0, 1) := by
  have hEe := (vat_some hS hE).1
  obtain ⟨n1, n2⟩ := corner_nbs hS h00 hin
  have c0 := nb_col hS n2
  obtain ⟨hn, hh, -, -, -⟩ := orient_facts hS hEe
  have u1 := used_of_nb hS hEe (nb_symm hS n2) rfl
  have u2 := used_of_nb hS hEe n1 c0.symm
  have p1 := prefix_start hn hh u1
  exact prefix_extend (F := []) hn p1 u2 (by simp) (not_last hS hEe (vat_none h00))

theorem forced_r2 (_hwf : J.WellFormed) (hS : IsSolution J p q) {a : ℕ}
    (hA1 : (makeView J.w J.h idF (ptsOf J)).at 0 0 = some a)
    (hA2 : (makeView J.w J.h idF (ptsOf J)).at 1 1 = some a)
    (h01 : (makeView J.w J.h idF (ptsOf J)).at 0 1 = none)
    (h10 : (makeView J.w J.h idF (ptsOf J)).at 1 0 = none)
    (_h02 : (makeView J.w J.h idF (ptsOf J)).at 0 2 = none)
    (_h20 : (makeView J.w J.h idF (ptsOf J)).at 2 0 = none)
    (hin : InBounds J.w J.h (2, 2)) :
    ([(0, 0), (0, 1), (0, 2)] <+: orient p q (0, 0) ∧ [(1, 1), (1, 0), (2, 0)] <+: orient p q (1, 1)) ∨
      ([(0, 0), (1, 0), (2, 0)] <+: orient p q (0, 0) ∧ [(1, 1), (0, 1), (0, 2)] <+: orient p q (1, 1)) := by
  have e1 := (vat_some hS hA1).1
  have e2 := (vat_some hS hA2).1
  have c1 := (vat_some hS hA1).2
  have c2 := (vat_some hS hA2).2
  unfold InBounds at hin
  simp only at hin
  obtain ⟨y, z, hyz, hy, hz⟩ := interior hS (v := (0, 1)) ⟨by omega, by omega⟩ (vat_none h01)
  obtain ⟨y', z', hyz', hy', hz'⟩ := interior hS (v := (1, 0)) ⟨by omega, by omega⟩ (vat_none h10)
  have my := adj_mem (nb_adj hS hy); have mz := adj_mem (nb_adj hS hz)
  have my' := adj_mem (nb_adj hS hy'); have mz' := adj_mem (nb_adj hS hz')
  simp [nbrList] at my mz my' mz'
  -- an endpoint has one neighbour
  have one1 : ∀ u w, Nb p q (0, 0) u → Nb p q (0, 0) w → u = w := fun u w hu hw => end_unique hS e1 hu hw
  have one2 : ∀ u w, Nb p q (1, 1) u → Nb p q (1, 1) w → u = w := fun u w hu hw => end_unique hS e2 hu hw
  -- (0,1) takes (0,2), and (1,0) takes (2,0)
  have t01 : Nb p q (0, 1) (0, 2) ∧ (Nb p q (0, 1) (0, 0) ∨ Nb p q (0, 1) (1, 1)) := by
    rcases my with rfl | rfl | rfl <;> rcases mz with rfl | rfl | rfl <;>
      simp only [ne_eq, not_true_eq_false] at hyz <;>
      first
        | exact ⟨hz, Or.inr hy⟩ | exact ⟨hy, Or.inr hz⟩ | exact ⟨hz, Or.inl hy⟩ | exact ⟨hy, Or.inl hz⟩
        | skip
    all_goals
      exfalso
      rcases my' with rfl | rfl | rfl <;> rcases mz' with rfl | rfl | rfl <;>
        simp only [ne_eq, not_true_eq_false] at hyz' <;>
        first
          | (have := one2 _ _ (nb_symm hS hy) (nb_symm hS ‹Nb p q (1, 0) (1, 1)›); simp at this)
          | (have := one1 _ _ (nb_symm hS ‹Nb p q (0, 1) (0, 0)›) (nb_symm hS ‹Nb p q (1, 0) (0, 0)›); simp at this)
          | (have := one2 _ _ (nb_symm hS ‹Nb p q (0, 1) (1, 1)›) (nb_symm hS ‹Nb p q (1, 0) (1, 1)›); simp at this)
  have t10 : Nb p q (1, 0) (2, 0) ∧ (Nb p q (1, 0) (0, 0) ∨ Nb p q (1, 0) (1, 1)) := by
    rcases my' with rfl | rfl | rfl <;> rcases mz' with rfl | rfl | rfl <;>
      simp only [ne_eq, not_true_eq_false] at hyz' <;>
      first
        | exact ⟨hz', Or.inr hy'⟩ | exact ⟨hy', Or.inr hz'⟩ | exact ⟨hz', Or.inl hy'⟩ | exact ⟨hy', Or.inl hz'⟩
        | skip
    all_goals
      exfalso
      rcases my with rfl | rfl | rfl <;> rcases mz with rfl | rfl | rfl <;>
        simp only [ne_eq, not_true_eq_false] at hyz <;>
        first
          | (have := one2 _ _ (nb_symm hS hy') (nb_symm hS ‹Nb p q (0, 1) (1, 1)›); simp at this)
          | (have := one1 _ _ (nb_symm hS ‹Nb p q (1, 0) (0, 0)›) (nb_symm hS ‹Nb p q (0, 1) (0, 0)›); simp at this)
          | (have := one2 _ _ (nb_symm hS ‹Nb p q (1, 0) (1, 1)›) (nb_symm hS ‹Nb p q (0, 1) (1, 1)›); simp at this)
  obtain ⟨a02, b01⟩ := t01
  obtain ⟨a20, b10⟩ := t10
  obtain ⟨hn1, hh1, -, -, -⟩ := orient_facts hS e1
  obtain ⟨hn2, hh2, -, -, -⟩ := orient_facts hS e2
  rcases b01 with b01 | b01 <;> rcases b10 with b10 | b10
  · have := one1 _ _ (nb_symm hS b01) (nb_symm hS b10); simp at this
  · left
    have k1 := nb_col hS b01
    have k2 := nb_col hS b10
    refine ⟨prefix_extend (F := []) hn1 (prefix_start hn1 hh1 (used_of_nb hS e1 (nb_symm hS b01) rfl))
      (used_of_nb hS e1 a02 k1.symm) (by simp) (not_last hS e1 (vat_none h01)),
      prefix_extend (F := []) hn2 (prefix_start hn2 hh2 (used_of_nb hS e2 (nb_symm hS b10) rfl))
      (used_of_nb hS e2 a20 k2.symm) (by simp) (not_last hS e2 (vat_none h10))⟩
  · right
    have k1 := nb_col hS b10
    have k2 := nb_col hS b01
    refine ⟨prefix_extend (F := []) hn1 (prefix_start hn1 hh1 (used_of_nb hS e1 (nb_symm hS b10) rfl))
      (used_of_nb hS e1 a20 k1.symm) (by simp) (not_last hS e1 (vat_none h10)),
      prefix_extend (F := []) hn2 (prefix_start hn2 hh2 (used_of_nb hS e2 (nb_symm hS b01) rfl))
      (used_of_nb hS e2 a02 k2.symm) (by simp) (not_last hS e2 (vat_none h01))⟩
  · have := one2 _ _ (nb_symm hS b01) (nb_symm hS b10); simp at this

theorem used_idx {L : List Coord} (hn : L.Nodup) {u v : Coord} (h : Used L u v) :
    L.idxOf v = L.idxOf u + 1 ∨ L.idxOf u = L.idxOf v + 1 := by
  have key : ∀ {a b : Coord}, [a, b] <:+: L → L.idxOf b = L.idxOf a + 1 := by
    intro a b hab
    obtain ⟨s, t, rfl⟩ := infix_pair_iff.mp hab
    have hn' := hn
    rw [List.nodup_append] at hn'
    have ha : a ∉ s := fun hm => hn'.2.2 a hm a (by simp) rfl
    have hb : b ∉ s := fun hm => hn'.2.2 b hm b (by simp) rfl
    have hab' : a ≠ b := by
      have := hn'.2.1; simp at this; exact this.1.1
    rw [idxOf_append_not_mem _ ha, idxOf_append_not_mem _ hb, List.idxOf_cons_self,
      List.idxOf_cons_ne _ hab', List.idxOf_cons_self]
  rcases h with h | h
  · exact Or.inl (key h)
  · exact Or.inr (key h)

/-- No four path edges form a square. -/
theorem no_square (hS : IsSolution J p q) {a b c d : Coord} (hab : Nb p q a b) (hbc : Nb p q b c)
    (hcd : Nb p q c d) (hda : Nb p q d a) (h1 : a ≠ c) (h2 : b ≠ d) : False := by
  have cb := nb_col hS hab; have cc := nb_col hS hbc; have cd := nb_col hS hcd
  have e2 : pathOf p q b = pathOf p q a := pathOf_eq hS cb
  have e3 : pathOf p q c = pathOf p q a := pathOf_eq hS (cc.trans cb)
  have e4 : pathOf p q d = pathOf p q a := pathOf_eq hS (cd.trans (cc.trans cb))
  obtain ⟨s, t, hP, -⟩ := pathOf_isPath hS a
  have hn := hP.2.2.1
  unfold Nb at hab hbc hcd hda
  rw [e2] at hbc; rw [e3] at hcd; rw [e4] at hda
  generalize pathOf p q a = L at hab hbc hcd hda hn
  have ma := (Used.mem_left hab); have mb := Used.mem_left hbc
  have mc := Used.mem_left hcd; have md := Used.mem_left hda
  have i1 := used_idx hn hab; have i2 := used_idx hn hbc
  have i3 := used_idx hn hcd; have i4 := used_idx hn hda
  have n1 : L.idxOf a ≠ L.idxOf c := fun e => h1 (idxOf_inj ma mc e)
  have n2 : L.idxOf b ≠ L.idxOf d := fun e => h2 (idxOf_inj mb md e)
  omega

theorem forced_r3 (hS : IsSolution J p q) {xc yc : ℕ}
    (hX : (makeView J.w J.h idF (ptsOf J)).at 1 2 = some xc)
    (hY : (makeView J.w J.h idF (ptsOf J)).at 2 1 = some yc) (hxy : xc ≠ yc)
    (e00 : (makeView J.w J.h idF (ptsOf J)).at 0 0 = none)
    (e01 : (makeView J.w J.h idF (ptsOf J)).at 0 1 = none)
    (e02 : (makeView J.w J.h idF (ptsOf J)).at 0 2 = none)
    (e10 : (makeView J.w J.h idF (ptsOf J)).at 1 0 = none)
    (e11 : (makeView J.w J.h idF (ptsOf J)).at 1 1 = none)
    (e20 : (makeView J.w J.h idF (ptsOf J)).at 2 0 = none)
    (hin : InBounds J.w J.h (3, 3)) :
    ([(1, 2), (0, 2), (0, 3)] <+: orient p q (1, 2) ∧
        [(2, 1), (1, 1), (0, 1), (0, 0), (1, 0), (2, 0), (3, 0)] <+: orient p q (2, 1)) ∨
      ([(1, 2), (1, 1), (1, 0), (0, 0), (0, 1), (0, 2), (0, 3)] <+: orient p q (1, 2) ∧
        [(2, 1), (2, 0), (3, 0)] <+: orient p q (2, 1)) := by
  unfold InBounds at hin
  simp only at hin
  have eX := (vat_some hS hX).1; have cX := (vat_some hS hX).2
  have eY := (vat_some hS hY).1; have cY := (vat_some hS hY).2
  obtain ⟨c1, c2⟩ := corner_nbs hS e00 ⟨by omega, by omega⟩
  have nb := fun {v : Coord} (h : (makeView J.w J.h idF (ptsOf J)).at v.1 v.2 = none) (h1 : v.1 < J.w)
    (h2 : v.2 < J.h) => interior hS (v := v) ⟨h1, h2⟩ (vat_none h)
  obtain ⟨u, w, huw, hu, hw⟩ := nb (v := (1, 1)) e11 (by omega) (by omega)
  have mu := adj_mem (nb_adj hS hu); have mw := adj_mem (nb_adj hS hw)
  simp [nbrList] at mu mw
  -- (0,2) and (2,0) when (0,1), resp. (1,0), is full
  have full01 : ∀ z, Nb p q (0, 1) (1, 1) → Nb p q (0, 1) z → z = (0, 0) ∨ z = (1, 1) := by
    intro z h1 hz
    rcases le_two hS (nb_symm hS c2) h1 hz with h | h | h
    · simp at h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have full10 : ∀ z, Nb p q (1, 0) (1, 1) → Nb p q (1, 0) z → z = (0, 0) ∨ z = (1, 1) := by
    intro z h1 hz
    rcases le_two hS (nb_symm hS c1) h1 hz with h | h | h
    · simp at h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have bad1 : Nb p q (1, 1) (0, 1) → Nb p q (1, 1) (1, 2) → False := by
    intro h1 h2
    obtain ⟨y, z, hyz, hy, hz⟩ := nb (v := (0, 2)) e02 (by omega) (by omega)
    have my := adj_mem (nb_adj hS hy); have mz := adj_mem (nb_adj hS hz)
    simp [nbrList] at my mz
    rcases my with rfl | rfl | rfl <;> rcases mz with rfl | rfl | rfl <;>
      simp only [ne_eq, not_true_eq_false] at hyz <;>
      first
        | (have := full01 _ (nb_symm hS h1) (nb_symm hS hy); simp at this)
        | (have := full01 _ (nb_symm hS h1) (nb_symm hS hz); simp at this)
        | (have := end_unique hS eX (nb_symm hS h2) (nb_symm hS hy); simp at this)
        | (have := end_unique hS eX (nb_symm hS h2) (nb_symm hS hz); simp at this)
  have bad2 : Nb p q (1, 1) (1, 0) → Nb p q (1, 1) (2, 1) → False := by
    intro h1 h2
    obtain ⟨y, z, hyz, hy, hz⟩ := nb (v := (2, 0)) e20 (by omega) (by omega)
    have my := adj_mem (nb_adj hS hy); have mz := adj_mem (nb_adj hS hz)
    simp [nbrList] at my mz
    rcases my with rfl | rfl | rfl <;> rcases mz with rfl | rfl | rfl <;>
      simp only [ne_eq, not_true_eq_false] at hyz <;>
      first
        | (have := full10 _ (nb_symm hS h1) (nb_symm hS hy); simp at this)
        | (have := full10 _ (nb_symm hS h1) (nb_symm hS hz); simp at this)
        | (have := end_unique hS eY (nb_symm hS h2) (nb_symm hS hy); simp at this)
        | (have := end_unique hS eY (nb_symm hS h2) (nb_symm hS hz); simp at this)
  have key : (Nb p q (1, 1) (0, 1) ∧ Nb p q (1, 1) (2, 1)) ∨ (Nb p q (1, 1) (1, 0) ∧ Nb p q (1, 1) (1, 2)) := by
    rcases mu with rfl | rfl | rfl | rfl <;> rcases mw with rfl | rfl | rfl | rfl <;>
      simp only [ne_eq, not_true_eq_false] at huw <;>
      first
        | exact Or.inl ⟨hw, hu⟩ | exact Or.inl ⟨hu, hw⟩ | exact Or.inr ⟨hw, hu⟩ | exact Or.inr ⟨hu, hw⟩
        | (exfalso; have := nb_col hS hu; have := nb_col hS hw; omega)
        | (exfalso; exact no_square hS hu (nb_symm hS c2) c1 (nb_symm hS hw) (by simp) (by simp))
        | (exfalso; exact no_square hS hw (nb_symm hS c2) c1 (nb_symm hS hu) (by simp) (by simp))
        | exact (bad1 hu hw).elim | exact (bad1 hw hu).elim
        | exact (bad2 hu hw).elim | exact (bad2 hw hu).elim
  have only2 : ∀ {v a b : Coord}, (makeView J.w J.h idF (ptsOf J)).at v.1 v.2 = none → v.1 < J.w →
      v.2 < J.h → (∀ z, Nb p q v z → z = a ∨ z = b) → a ≠ b → Nb p q v a ∧ Nb p q v b := by
    intro v a b hv h1 h2 hz hab
    obtain ⟨y, z, hyz, hy, hz'⟩ := nb hv h1 h2
    rcases hz y hy with rfl | rfl <;> rcases hz z hz' with rfl | rfl
    · exact absurd rfl hyz
    · exact ⟨hy, hz'⟩
    · exact ⟨hz', hy⟩
    · exact absurd rfl hyz
  have nl := fun {E x : Coord} (hE : IsEnd J E) (hx : (makeView J.w J.h idF (ptsOf J)).at x.1 x.2 = none) =>
    not_last hS hE (vat_none hx)
  obtain ⟨hnX, hhX, -, -, -⟩ := orient_facts hS eX
  obtain ⟨hnY, hhY, -, -, -⟩ := orient_facts hS eY
  rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
  · -- Y claims the corner
    left
    have full11 : ∀ z, Nb p q (1, 1) z → z = (0, 1) ∨ z = (2, 1) := by
      intro z hz
      rcases le_two hS k1 k2 hz with h | h | h
      · simp at h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    have n10 := (only2 (v := (1, 0)) (a := (2, 0)) (b := (0, 0)) e10 (by omega) (by omega) (by
      intro z hz
      have mz := adj_mem (nb_adj hS hz); simp [nbrList] at mz
      rcases mz with rfl | rfl | rfl
      · exact Or.inl rfl
      · rcases full11 _ (nb_symm hS hz) with h | h <;> simp at h
      · exact Or.inr rfl) (by simp)).1
    have n20 := (only2 (v := (2, 0)) (a := (3, 0)) (b := (1, 0)) e20 (by omega) (by omega) (by
      intro z hz
      have mz := adj_mem (nb_adj hS hz); simp [nbrList] at mz
      rcases mz with rfl | rfl | rfl
      · exact Or.inl rfl
      · have := end_unique hS eY (nb_symm hS hz) (nb_symm hS k2); simp at this
      · exact Or.inr rfl) (by simp)).1
    obtain ⟨n02X, n03⟩ := only2 (v := (0, 2)) (a := (1, 2)) (b := (0, 3)) e02 (by omega) (by omega) (by
      intro z hz
      have mz := adj_mem (nb_adj hS hz); simp [nbrList] at mz
      rcases mz with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · rcases full01 _ (nb_symm hS k1) (nb_symm hS hz) with h | h <;> simp at h) (by simp)
    have q1 := nb_col hS k2; have q2 := nb_col hS k1; have q3 := nb_col hS c2
    have q4 := nb_col hS c1; have q5 := nb_col hS n10; have q6 := nb_col hS n02X
    refine ⟨?_, ?_⟩
    · have P1 := prefix_start hnX hhX (used_of_nb hS eX (nb_symm hS n02X) rfl)
      exact prefix_extend (F := []) hnX P1 (used_of_nb hS eX n03 q6.symm) (by simp) (nl (x := (0, 2)) eX e02)
    · have P1 := prefix_start hnY hhY (used_of_nb hS eY (nb_symm hS k2) rfl)
      have P2 := prefix_extend (F := []) hnY P1 (used_of_nb hS eY k1 q1.symm) (by simp) (nl (x := (1, 1)) eY e11)
      have P3 := prefix_extend (F := [(2, 1)]) hnY P2 (used_of_nb hS eY (nb_symm hS c2) (by omega))
        (by simp) (nl (x := (0, 1)) eY e01)
      have P4 := prefix_extend (F := [(2, 1), (1, 1)]) hnY P3 (used_of_nb hS eY c1 (by omega))
        (by simp) (nl (x := (0, 0)) eY e00)
      have P5 := prefix_extend (F := [(2, 1), (1, 1), (0, 1)]) hnY P4 (used_of_nb hS eY n10 (by omega))
        (by simp) (nl (x := (1, 0)) eY e10)
      exact prefix_extend (F := [(2, 1), (1, 1), (0, 1), (0, 0)]) hnY P5 (used_of_nb hS eY n20 (by omega))
        (by simp) (nl (x := (2, 0)) eY e20)
  · -- X claims the corner
    right
    have full11 : ∀ z, Nb p q (1, 1) z → z = (1, 0) ∨ z = (1, 2) := by
      intro z hz
      rcases le_two hS k1 k2 hz with h | h | h
      · simp at h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    have n01 := (only2 (v := (0, 1)) (a := (0, 2)) (b := (0, 0)) e01 (by omega) (by omega) (by
      intro z hz
      have mz := adj_mem (nb_adj hS hz); simp [nbrList] at mz
      rcases mz with rfl | rfl | rfl
      · rcases full11 _ (nb_symm hS hz) with h | h <;> simp at h
      · exact Or.inl rfl
      · exact Or.inr rfl) (by simp)).1
    have n02 := (only2 (v := (0, 2)) (a := (0, 3)) (b := (0, 1)) e02 (by omega) (by omega) (by
      intro z hz
      have mz := adj_mem (nb_adj hS hz); simp [nbrList] at mz
      rcases mz with rfl | rfl | rfl
      · have := end_unique hS eX (nb_symm hS hz) (nb_symm hS k2); simp at this
      · exact Or.inl rfl
      · exact Or.inr rfl) (by simp)).1
    obtain ⟨n20Y, n30⟩ := only2 (v := (2, 0)) (a := (2, 1)) (b := (3, 0)) e20 (by omega) (by omega) (by
      intro z hz
      have mz := adj_mem (nb_adj hS hz); simp [nbrList] at mz
      rcases mz with rfl | rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl rfl
      · rcases full10 _ (nb_symm hS k1) (nb_symm hS hz) with h | h <;> simp at h) (by simp)
    have q1 := nb_col hS k2; have q2 := nb_col hS k1; have q3 := nb_col hS c1
    have q4 := nb_col hS c2; have q5 := nb_col hS n01; have q6 := nb_col hS n20Y
    refine ⟨?_, ?_⟩
    · have P1 := prefix_start hnX hhX (used_of_nb hS eX (nb_symm hS k2) rfl)
      have P2 := prefix_extend (F := []) hnX P1 (used_of_nb hS eX k1 q1.symm) (by simp) (nl (x := (1, 1)) eX e11)
      have P3 := prefix_extend (F := [(1, 2)]) hnX P2 (used_of_nb hS eX (nb_symm hS c1) (by omega))
        (by simp) (nl (x := (1, 0)) eX e10)
      have P4 := prefix_extend (F := [(1, 2), (1, 1)]) hnX P3 (used_of_nb hS eX c2 (by omega))
        (by simp) (nl (x := (0, 0)) eX e00)
      have P5 := prefix_extend (F := [(1, 2), (1, 1), (1, 0)]) hnX P4 (used_of_nb hS eX n01 (by omega))
        (by simp) (nl (x := (0, 1)) eX e01)
      exact prefix_extend (F := [(1, 2), (1, 1), (1, 0), (0, 0)]) hnX P5 (used_of_nb hS eX n02 (by omega))
        (by simp) (nl (x := (0, 2)) eX e02)
    · have P1 := prefix_start hnY hhY (used_of_nb hS eY (nb_symm hS n20Y) rfl)
      exact prefix_extend (F := []) hnY P1 (used_of_nb hS eY n30 q6.symm) (by simp) (nl (x := (2, 0)) eY e20)

end Forced





/-! ### Moving a solution into a frame -/

theorem to_inj {R C : ℕ} (f : Frame) {u v : Coord} (hu : InBounds R C u) (hv : InBounds R C v)
    (h : f.to R C u = f.to R C v) : u = v := by
  obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v
  obtain ⟨fr, fc, tr⟩ := f
  unfold InBounds at hu hv; simp only at hu hv
  cases fr <;> cases fc <;> cases tr <;> simp [Frame.to] at h <;> simp only [Prod.mk.injEq] <;> omega

theorem back_to {R C : ℕ} (f : Frame) {u : Coord} (hu : InBounds R C u) : f.back R C (f.to R C u) = u := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨fr, fc, tr⟩ := f
  unfold InBounds at hu; simp only at hu
  cases fr <;> cases fc <;> cases tr <;> simp [Frame.to, Frame.back] <;> omega

theorem isPath_frameMap {I : Inst} (f : Frame) {s t : Coord} {L : List Coord}
    (hL : IsPath I.w I.h s t L) :
    IsPath (I.frameMap f).w (I.frameMap f).h (f.to I.w I.h s) (f.to I.w I.h t) (L.map (f.to I.w I.h)) := by
  obtain ⟨hh, hl, hn, hb, hc⟩ := hL
  obtain ⟨fr, fc, tr⟩ := f
  refine ⟨by rw [List.head?_map, hh]; rfl, by rw [List.getLast?_map, hl]; rfl,
    List.Nodup.map_on (fun x hx y hy h => to_inj _ (hb x hx) (hb y hy) h) hn, ?_, ?_⟩
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    have := hb u hu
    obtain ⟨u1, u2⟩ := u
    unfold InBounds at this ⊢
    simp only [Inst.frameMap] at this ⊢
    cases fr <;> cases fc <;> cases tr <;> simp [Frame.to, Frame.H, Frame.W] <;> omega
  · have adj : ∀ u v, Adjacent u v → InBounds I.w I.h u → InBounds I.w I.h v →
        Adjacent (Frame.to I.w I.h ⟨fr, fc, tr⟩ u) (Frame.to I.w I.h ⟨fr, fc, tr⟩ v) := by
      intro u v h hu hv
      obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v
      unfold InBounds at hu hv
      unfold Adjacent at h ⊢
      simp only at hu hv h
      cases fr <;> cases fc <;> cases tr <;> simp [Frame.to] <;> omega
    have : ∀ (l : List Coord), (∀ v ∈ l, InBounds I.w I.h v) → chainAdjacent l = true →
        chainAdjacent (l.map (Frame.to I.w I.h ⟨fr, fc, tr⟩)) = true := by
      intro l
      induction l with
      | nil => intro _ _; rfl
      | cons a l ih =>
        intro hbl hcl
        cases l with
        | nil => rfl
        | cons b l =>
          rw [chainAdjacent_cons_cons, Bool.and_eq_true] at hcl
          simp only [List.map_cons]
          rw [chainAdjacent_cons_cons, Bool.and_eq_true]
          refine ⟨(adjacentB_iff _ _).mpr (adj _ _ ((adjacentB_iff _ _).mp hcl.1)
            (hbl a (by simp)) (hbl b (by simp))), ?_⟩
          have := ih (fun v hv => hbl v (List.mem_cons_of_mem _ hv)) hcl.2
          simpa using this
    exact this L hb hc

theorem isSolution_frameMap {I : Inst} (f : Frame) {p q : List Coord} (hS : IsSolution I p q) :
    IsSolution (I.frameMap f) (p.map (f.to I.w I.h)) (q.map (f.to I.w I.h)) := by
  refine ⟨isPath_frameMap f hS.1, isPath_frameMap f hS.2.1, ?_, ?_⟩
  · intro v hv hv'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    obtain ⟨u', hu', he⟩ := List.mem_map.mp hv'
    have := to_inj f (hS.2.1.2.2.2.1 u' hu') (hS.1.2.2.2.1 u hu) he
    exact hS.2.2.1 u hu (this ▸ hu')
  · intro v hv
    have hb : InBounds I.w I.h (f.back I.w I.h v) := by
      obtain ⟨v1, v2⟩ := v
      obtain ⟨fr, fc, tr⟩ := f
      unfold InBounds at hv ⊢
      simp only [Inst.frameMap] at hv
      cases fr <;> cases fc <;> cases tr <;> simp [Frame.back, Frame.H, Frame.W] at hv ⊢ <;> omega
    have he : f.to I.w I.h (f.back I.w I.h v) = v := by
      obtain ⟨v1, v2⟩ := v
      obtain ⟨fr, fc, tr⟩ := f
      unfold InBounds at hv
      simp only [Inst.frameMap] at hv
      cases fr <;> cases fc <;> cases tr <;> simp [Frame.back, Frame.to, Frame.H, Frame.W] at hv ⊢ <;> omega
    rcases hS.2.2.2 _ hb with h | h
    · exact Or.inl (List.mem_map.mpr ⟨_, h, he⟩)
    · exact Or.inr (List.mem_map.mpr ⟨_, h, he⟩)

theorem mem_map_to {I : Inst} (f : Frame) {L : List Coord} (hb : ∀ v ∈ L, InBounds I.w I.h v)
    {v : Coord} (hv : InBounds I.w I.h v) : f.to I.w I.h v ∈ L.map (f.to I.w I.h) ↔ v ∈ L := by
  constructor
  · intro h
    obtain ⟨u, hu, he⟩ := List.mem_map.mp h
    rw [← to_inj f (hb u hu) hv he]; exact hu
  · intro h; exact List.mem_map_of_mem h

theorem orient_map {I : Inst} {p q : List Coord} (hS : IsSolution I p q) (f : Frame) {E : Coord}
    (hE : InBounds I.w I.h E) :
    orient (p.map (f.to I.w I.h)) (q.map (f.to I.w I.h)) (f.to I.w I.h E) =
      (orient p q E).map (f.to I.w I.h) := by
  have hbp := hS.1.2.2.2.1
  have hbq := hS.2.1.2.2.2.1
  have hpath : pathOf (p.map (f.to I.w I.h)) (q.map (f.to I.w I.h)) (f.to I.w I.h E) =
      (pathOf p q E).map (f.to I.w I.h) := by
    unfold pathOf
    by_cases h : E ∈ p
    · rw [ite_eq_left ((mem_map_to f hbp hE).mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h ((mem_map_to f hbp hE).mp h')), ite_eq_right h]
  have hbL : ∀ v ∈ pathOf p q E, InBounds I.w I.h v := by
    unfold pathOf; split_ifs
    · exact hbp
    · exact hbq
  unfold orient
  rw [hpath, List.head?_map]
  by_cases h : (pathOf p q E).head? = some E
  · rw [h]; simp
  · have h' : Option.map (f.to I.w I.h) (pathOf p q E).head? ≠ some (f.to I.w I.h E) := by
      intro e
      cases hh : (pathOf p q E).head? with
      | none => rw [hh] at e; simp at e
      | some x =>
        rw [hh] at e
        simp only [Option.map_some, Option.some.injEq] at e
        have hx : x ∈ pathOf p q E := List.mem_of_mem_head? hh
        exact h (by rw [hh, to_inj f (hbL x hx) hE e])
    rw [ite_eq_right h', ite_eq_right h, List.map_reverse]

/-- Transfer a prefix found in a frame back to the instance. -/
theorem prefix_back {I : Inst} {p q : List Coord} (hS : IsSolution I p q) (f : Frame) {E : Coord}
    (hE : InBounds I.w I.h E) {F : List Coord}
    (hF : F <+: orient (p.map (f.to I.w I.h)) (q.map (f.to I.w I.h)) (f.to I.w I.h E)) :
    F.map (f.back I.w I.h) <+: orient p q E := by
  rw [orient_map hS f hE] at hF
  have hm := hF.map (f.back I.w I.h)
  rw [List.map_map] at hm
  have hbL : ∀ v ∈ orient p q E, InBounds I.w I.h v := by
    intro v hv
    unfold orient at hv
    have : v ∈ pathOf p q E := by split_ifs at hv <;> simp_all
    unfold pathOf at this
    split_ifs at this
    · exact hS.1.2.2.2.1 v this
    · exact hS.2.1.2.2.2.1 v this
  have e : (orient p q E).map (f.back I.w I.h ∘ f.to I.w I.h) = orient p q E := by
    conv_rhs => rw [← List.map_id (orient p q E)]
    exact List.map_congr_left (fun v hv => back_to f (hbL v hv))
  rwa [e] at hm

/-! ### All conditions of a rewrite -/

theorem rewritesAt_full {v : View} {rw : Rewrite} (h : rewritesAt v = some rw) :
    (rw = rw3 ∧ (∃ x y, v.at 1 2 = some x ∧ v.at 2 1 = some y ∧ x ≠ y) ∧ 4 ≤ v.H ∧ 4 ≤ v.W ∧
      ∀ c ∈ [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (2, 0), (3, 0)], v.at c.1 c.2 = none) ∨
    (rw = rw2 ∧ (∃ a, v.at 0 0 = some a ∧ v.at 1 1 = some a) ∧ 3 ≤ v.H ∧ 3 ≤ v.W ∧
      ∀ c ∈ [(0, 1), (1, 0), (0, 2), (2, 0)], v.at c.1 c.2 = none) ∨
    (rw = rw1 ∧ (∃ a, v.at 0 1 = some a) ∧ ∀ c ∈ [(0, 0), (1, 0)], v.at c.1 c.2 = none) := by
  rw [rewritesAt_eq] at h
  split_ifs at h with h3 h2 h1 <;> simp only [Option.some.injEq] at h <;> subst h
  · left
    unfold c3 at h3
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
    obtain ⟨⟨⟨hm, hH⟩, hW⟩, he⟩ := h3
    rw [empty_iff] at he
    refine ⟨rfl, ?_, hH, hW, he⟩
    cases hx : v.at 1 2 with
    | none => rw [hx] at hm; simp at hm
    | some x =>
      cases hy : v.at 2 1 with
      | none => rw [hx, hy] at hm; simp at hm
      | some y => rw [hx, hy] at hm; exact ⟨x, y, rfl, rfl, by simpa using hm⟩
  · right; left
    unfold c2 at h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    obtain ⟨⟨⟨hm, hH⟩, hW⟩, he⟩ := h2
    rw [empty_iff] at he
    refine ⟨rfl, ?_, hH, hW, he⟩
    cases ha : v.at 0 0 with
    | none => rw [ha] at hm; simp at hm
    | some a => rw [ha] at hm; exact ⟨a, rfl, by simpa using hm⟩
  · right; right
    unfold c1 at h1
    simp only [Bool.and_eq_true] at h1
    obtain ⟨⟨hm, he⟩, -⟩ := h1
    rw [empty_iff] at he
    refine ⟨rfl, ?_, he⟩
    cases ha : v.at 0 1 with
    | none => rw [ha] at hm; simp at hm
    | some a => exact ⟨a, rfl⟩

/-! ### Forced routes at a corner, in the instance's coordinates -/

theorem to_back_eq {R C : ℕ} (f : Frame) {a : Coord} (h1 : a.1 < f.H R C) (h2 : a.2 < f.W R C) :
    f.to R C (f.back R C a) = a := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨fr, fc, tr⟩ := f
  simp only [Frame.H, Frame.W] at h1 h2
  cases fr <;> cases fc <;> cases tr <;> simp [Frame.to, Frame.back] at h1 h2 ⊢ <;> omega

theorem back_inb {R C : ℕ} (f : Frame) {a : Coord} (h1 : a.1 < f.H R C) (h2 : a.2 < f.W R C) :
    InBounds R C (f.back R C a) := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨fr, fc, tr⟩ := f
  simp only [Frame.H, Frame.W] at h1 h2
  unfold InBounds
  cases fr <;> cases fc <;> cases tr <;> simp [Frame.back] at h1 h2 ⊢ <;> omega

theorem isEnd_back {I : Inst} (f : Frame) (hwf : I.WellFormed) {a : Coord}
    (h : IsEnd (I.frameMap f) a) : IsEnd I (f.back I.w I.h a) := by
  obtain ⟨b0, b1, b2, b3, -⟩ := hwf
  unfold IsEnd at h ⊢
  simp only [Inst.frameMap] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl (back_to f b0)
  · exact Or.inr (Or.inl (back_to f b1))
  · exact Or.inr (Or.inr (Or.inl (back_to f b2)))
  · exact Or.inr (Or.inr (Or.inr (back_to f b3)))

theorem colOf_map {I : Inst} {p q : List Coord} (hS : IsSolution I p q) (f : Frame) {v : Coord}
    (hv : InBounds I.w I.h v) : colOf (p.map (f.to I.w I.h)) (f.to I.w I.h v) = colOf p v := by
  unfold colOf
  by_cases h : v ∈ p
  · rw [ite_eq_left ((mem_map_to f hS.1.2.2.2.1 hv).mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h ((mem_map_to f hS.1.2.2.2.1 hv).mp h')), ite_eq_right h]

theorem corner_forced {I : Inst} {p q : List Coord} (hwf : I.WellFormed) (hS : IsSolution I p q)
    (hw : 4 ≤ I.w) (hh : 4 ≤ I.h) (g : Frame) {rw : Rewrite}
    (hrw : rewritesAt (makeView I.w I.h g (ptsOf I)) = some rw) :
    let B := Frame.back I.w I.h g
    (rw = rw1 ∧ IsEnd I (B (0, 1)) ∧ [B (0, 1), B (0, 0), B (1, 0)] <+: orient p q (B (0, 1))) ∨
    (rw = rw2 ∧ IsEnd I (B (0, 0)) ∧ IsEnd I (B (1, 1)) ∧ colOf p (B (0, 0)) = colOf p (B (1, 1)) ∧
      (([B (0, 0), B (0, 1), B (0, 2)] <+: orient p q (B (0, 0)) ∧
          [B (1, 1), B (1, 0), B (2, 0)] <+: orient p q (B (1, 1))) ∨
        ([B (0, 0), B (1, 0), B (2, 0)] <+: orient p q (B (0, 0)) ∧
          [B (1, 1), B (0, 1), B (0, 2)] <+: orient p q (B (1, 1))))) ∨
    (rw = rw3 ∧ IsEnd I (B (1, 2)) ∧ IsEnd I (B (2, 1)) ∧
      (([B (1, 2), B (0, 2), B (0, 3)] <+: orient p q (B (1, 2)) ∧
          [B (2, 1), B (1, 1), B (0, 1), B (0, 0), B (1, 0), B (2, 0), B (3, 0)] <+: orient p q (B (2, 1))) ∨
        ([B (1, 2), B (1, 1), B (1, 0), B (0, 0), B (0, 1), B (0, 2), B (0, 3)] <+: orient p q (B (1, 2)) ∧
          [B (2, 1), B (2, 0), B (3, 0)] <+: orient p q (B (2, 1))))) := by
  intro B
  have hSJ := isSolution_frameMap g hS
  have hv : makeView (I.frameMap g).w (I.frameMap g).h idF (ptsOf (I.frameMap g)) = makeView I.w I.h g (ptsOf I) :=
    makeView_idF g I.w I.h (ptsOf I)
  rw [← hv] at hrw
  have hJw : 4 ≤ (I.frameMap g).w := by simp only [Inst.frameMap, Frame.H]; split_ifs <;> omega
  have hJh : 4 ≤ (I.frameMap g).h := by simp only [Inst.frameMap, Frame.W]; split_ifs <;> omega
  -- cells of the window, moved to the frame and back
  have tb : ∀ a : Coord, a.1 ≤ 3 → a.2 ≤ 3 → g.to I.w I.h (B a) = a := fun a h1 h2 =>
    to_back_eq g (by simp only [Inst.frameMap] at hJw; omega) (by simp only [Inst.frameMap] at hJh; omega)
  have ib : ∀ a : Coord, a.1 ≤ 3 → a.2 ≤ 3 → InBounds I.w I.h (B a) := fun a h1 h2 =>
    back_inb g (by simp only [Inst.frameMap] at hJw; omega) (by simp only [Inst.frameMap] at hJh; omega)
  have pb : ∀ (a : Coord) (F : List Coord), a.1 ≤ 3 → a.2 ≤ 3 →
      F <+: orient (p.map (g.to I.w I.h)) (q.map (g.to I.w I.h)) a → F.map B <+: orient p q (B a) := by
    intro a F h1 h2 hF
    rw [← tb a h1 h2] at hF
    exact prefix_back hS g (ib a h1 h2) hF
  have hwfJ := wellFormed_frameMap g hwf
  have ie := fun {a : Coord} {c : ℕ} (h : (makeView (I.frameMap g).w (I.frameMap g).h idF (ptsOf (I.frameMap g))).at a.1 a.2 = some c) =>
    isEnd_back g hwf (vat_some hSJ h).1
  rcases rewritesAt_full hrw with ⟨rfl, ⟨x, y, hx, hy, hxy⟩, -, -, he⟩ | ⟨rfl, ⟨a, h00, h11⟩, -, -, he⟩ |
      ⟨rfl, ⟨a, h01⟩, he⟩
  · right; right
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at he
    obtain ⟨e00, e01, e02, -, e10, e11, e20, -⟩ := he
    refine ⟨rfl, ie (a := (1, 2)) hx, ie (a := (2, 1)) hy, ?_⟩
    rcases forced_r3 hSJ hx hy hxy e00 e01 e02 e10 e11 e20 ⟨by omega, by omega⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨pb (1, 2) _ (by decide) (by decide) h1, pb (2, 1) _ (by decide) (by decide) h2⟩
    · exact Or.inr ⟨pb (1, 2) _ (by decide) (by decide) h1, pb (2, 1) _ (by decide) (by decide) h2⟩
  · right; left
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at he
    obtain ⟨e01, e10, e02, e20⟩ := he
    have c1 := (vat_some hSJ h00).2
    have c2 := (vat_some hSJ h11).2
    rw [← tb (0, 0) (by decide) (by decide), colOf_map hS g (ib _ (by decide) (by decide))] at c1
    rw [← tb (1, 1) (by decide) (by decide), colOf_map hS g (ib _ (by decide) (by decide))] at c2
    refine ⟨rfl, ie (a := (0, 0)) h00, ie (a := (1, 1)) h11, by rw [c1, c2], ?_⟩
    rcases forced_r2 hwfJ hSJ h00 h11 e01 e10 e02 e20 ⟨by omega, by omega⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨pb (0, 0) _ (by decide) (by decide) h1, pb (1, 1) _ (by decide) (by decide) h2⟩
    · exact Or.inr ⟨pb (0, 0) _ (by decide) (by decide) h1, pb (1, 1) _ (by decide) (by decide) h2⟩
  · left
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at he
    obtain ⟨e00, e10⟩ := he
    exact ⟨rfl, ie (a := (0, 1)) h01,
      pb (0, 1) _ (by decide) (by decide) (forced_r1 hSJ h01 e00 e10 ⟨by omega, by omega⟩)⟩

/-! ### Bookkeeping: moves, decisions, prefixes -/

theorem applyMoves_append (M1 M2 : List ((ℕ × ℕ) × (ℕ × ℕ))) (x : ℕ × ℕ) :
    applyMoves (M1 ++ M2) x = applyMoves M2 (applyMoves M1 x) := by
  unfold applyMoves; rw [List.foldl_append]

theorem applyMoves_id {M : List ((ℕ × ℕ) × (ℕ × ℕ))} {x : ℕ × ℕ} (h : ∀ m ∈ M, m.1 ≠ x) :
    applyMoves M x = x := by
  induction M with
  | nil => rfl
  | cons m M ih =>
    unfold applyMoves at ih ⊢
    simp only [List.foldl_cons]
    rw [ite_eq_right (fun e => h m List.mem_cons_self e.symm)]
    exact ih (fun m' hm' => h m' (List.mem_cons_of_mem _ hm'))

theorem decC_some {R C : ℕ} {pts : List Pt} {fr fc : Bool} {K : List (ℕ × ℕ)}
    {M : List ((ℕ × ℕ) × (ℕ × ℕ))} (h : decC R C pts fr fc = some (K, M)) :
    ∃ g : Frame, g.fr = fr ∧ g.fc = fc ∧ ∃ rw, rewritesAt (makeView R C g pts) = some rw ∧
      K = rw.removed.map (g.back R C) ∧ M = rw.moves.map (fun m => (g.back R C m.1, g.back R C m.2)) := by
  unfold decC at h
  cases hv : rewritesAt (makeView R C ⟨fr, fc, false⟩ pts) with
  | some rw =>
    rw [hv] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨_, rfl, rfl, rw, hv, h.1.symm, h.2.symm⟩
  | none =>
    rw [hv] at h
    simp only at h
    cases hv' : rewritesAt (makeView R C ⟨fr, fc, true⟩ pts) with
    | none => rw [hv'] at h; simp at h
    | some rw =>
      rw [hv'] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨_, rfl, rfl, rw, hv', h.1.symm, h.2.symm⟩

/-- A prefix of `L` that runs through settled cells to the first unsettled one. -/
def GoodPre (Rm : ℕ × ℕ → Prop) (L F : List Coord) : Prop :=
  F <+: L ∧ (∀ x ∈ F.dropLast, Rm x) ∧ ∃ f, F.getLast? = some f ∧ ¬ Rm f

theorem goodPre_unique {Rm : ℕ × ℕ → Prop} {L F F' : List Coord} (h : GoodPre Rm L F) (h' : GoodPre Rm L F') :
    F = F' := by
  obtain ⟨p1, d1, f, l1, n1⟩ := h
  obtain ⟨p2, d2, f', l2, n2⟩ := h'
  rcases List.prefix_or_prefix_of_prefix p1 p2 with h | h
  · -- F <+: F'
    by_contra hne
    obtain ⟨T, rfl⟩ := h
    have hT : T ≠ [] := fun e => hne (by simp [e])
    have hf : f ∈ (F ++ T).dropLast := by
      rw [List.dropLast_append_of_ne_nil hT]
      exact List.mem_append_left _ (List.mem_of_getLast? l1)
    exact n1 (d2 f hf)
  · by_contra hne
    obtain ⟨T, rfl⟩ := h
    have hT : T ≠ [] := fun e => hne (by simp [e])
    have hf : f' ∈ (F' ++ T).dropLast := by
      rw [List.dropLast_append_of_ne_nil hT]
      exact List.mem_append_left _ (List.mem_of_getLast? l2)
    exact n2 (d1 f' hf)

theorem prefix_of_append_disj {α : Type} [DecidableEq α] {b : α} : ∀ {A B F : List α},
    F <+: A ++ b :: B → b ∉ F → F <+: A
  | [], B, F, h, hb => by
    cases F with
    | nil => exact List.nil_prefix
    | cons f F =>
      exfalso; obtain ⟨T, hT⟩ := h
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at hT
      exact hb (hT.1 ▸ List.mem_cons_self)
  | a :: A, B, F, h, hb => by
    cases F with
    | nil => exact List.nil_prefix
    | cons f F =>
      obtain ⟨T, hT⟩ := h
      simp only [List.cons_append, List.cons.injEq] at hT
      obtain ⟨rfl, hT⟩ := hT
      have ih := prefix_of_append_disj (A := A) (B := B) (F := F) ⟨T, hT⟩
        (fun hm => hb (List.mem_cons_of_mem _ hm))
      exact List.cons_prefix_cons.mpr ⟨rfl, ih⟩

/-- Cut a path at a prefix and a suffix that share no cell. -/
theorem split_ends {L Fs Ft : List Coord} (hs : Fs <+: L) (ht : Ft <+: L.reverse) (hs0 : Fs ≠ [])
    (ht0 : Ft ≠ []) (hd : Fs.getLast hs0 ∉ Ft) :
    ∃ M, L = Fs.dropLast ++ M ++ Ft.dropLast.reverse ∧ M.head? = Fs.getLast? ∧ M.getLast? = Ft.getLast? := by
  obtain ⟨T, rfl⟩ := hs
  rw [List.reverse_append] at ht
  have hFs : Fs = Fs.dropLast ++ [Fs.getLast hs0] := (List.dropLast_append_getLast hs0).symm
  have hrev : Fs.reverse = Fs.getLast hs0 :: Fs.dropLast.reverse := by
    conv_lhs => rw [hFs]
    simp
  rw [hrev] at ht
  have hp := prefix_of_append_disj ht hd
  obtain ⟨U, hU⟩ := hp
  have hT : T = U.reverse ++ Ft.reverse := by
    have := congrArg List.reverse hU
    simpa using this.symm
  have hFt : Ft.reverse = Ft.getLast ht0 :: Ft.dropLast.reverse := by
    conv_lhs => rw [(List.dropLast_append_getLast ht0).symm]
    simp
  refine ⟨Fs.getLast hs0 :: (U.reverse ++ [Ft.getLast ht0]), ?_, ?_, ?_⟩
  · rw [hT, hFt]
    conv_lhs => rw [hFs]
    simp
  · simp [List.getLast?_eq_some_getLast hs0]
  · rw [List.getLast?_eq_some_getLast ht0, ← List.cons_append, List.getLast?_append]
    simp

/-! ### Everything a fired corner tells us -/

theorem view_end {I : Inst} (hwf : I.WellFormed) (g : Frame) {a : Coord} (h1 : a.1 < g.H I.w I.h)
    (h2 : a.2 < g.W I.w I.h) (he : IsEnd I (g.back I.w I.h a)) :
    (makeView I.w I.h g (ptsOf I)).at a.1 a.2 ≠ none := by
  intro hn
  rw [← makeView_idF g I.w I.h (ptsOf I)] at hn
  apply vat_none (J := I.frameMap g) hn
  obtain ⟨b0, b1, b2, b3, -⟩ := hwf
  have tb := to_back_eq g h1 h2
  unfold IsEnd at he ⊢
  simp only [Inst.frameMap]
  rcases he with e | e | e | e
  · left; rw [← e, tb]
  · right; left; rw [← e, tb]
  · right; right; left; rw [← e, tb]
  · right; right; right; rw [← e, tb]

theorem corner_package {I : Inst} {p q : List Coord} (hwf : I.WellFormed) (hS : IsSolution I p q)
    (hw : 4 ≤ I.w) (hh : 4 ≤ I.h) {fr fc : Bool} {K : List (ℕ × ℕ)} {M : List ((ℕ × ℕ) × (ℕ × ℕ))}
    (hd : decC I.w I.h (ptsOf I) fr fc = some (K, M)) :
    ∃ g : Frame, g.fr = fr ∧ g.fc = fc ∧
    let B := Frame.back I.w I.h g
    ((∀ x, x ∈ K ↔ x = B (0, 0) ∨ x = B (0, 1)) ∧ M = [(B (0, 1), B (1, 0))] ∧ IsEnd I (B (0, 1)) ∧
      ¬ IsEnd I (B (0, 0)) ∧ [B (0, 1), B (0, 0), B (1, 0)] <+: orient p q (B (0, 1))) ∨
    ((∀ x, x ∈ K ↔ x = B (0, 0) ∨ x = B (0, 1) ∨ x = B (1, 0) ∨ x = B (1, 1)) ∧
      M = [(B (0, 0), B (0, 2)), (B (1, 1), B (2, 0))] ∧ IsEnd I (B (0, 0)) ∧ IsEnd I (B (1, 1)) ∧
      ¬ IsEnd I (B (0, 1)) ∧ ¬ IsEnd I (B (1, 0)) ∧ colOf p (B (0, 0)) = colOf p (B (1, 1)) ∧
      (([B (0, 0), B (0, 1), B (0, 2)] <+: orient p q (B (0, 0)) ∧
          [B (1, 1), B (1, 0), B (2, 0)] <+: orient p q (B (1, 1))) ∨
        ([B (0, 0), B (1, 0), B (2, 0)] <+: orient p q (B (0, 0)) ∧
          [B (1, 1), B (0, 1), B (0, 2)] <+: orient p q (B (1, 1))))) ∨
    ((∀ x, x ∈ K ↔ x = B (0, 0) ∨ x = B (0, 1) ∨ x = B (0, 2) ∨ x = B (1, 0) ∨ x = B (1, 1) ∨
        x = B (2, 0) ∨ x = B (1, 2) ∨ x = B (2, 1)) ∧
      M = [(B (1, 2), B (0, 3)), (B (2, 1), B (3, 0))] ∧ IsEnd I (B (1, 2)) ∧ IsEnd I (B (2, 1)) ∧
      ¬ IsEnd I (B (0, 0)) ∧ ¬ IsEnd I (B (0, 1)) ∧ ¬ IsEnd I (B (0, 2)) ∧ ¬ IsEnd I (B (1, 0)) ∧
      ¬ IsEnd I (B (1, 1)) ∧ ¬ IsEnd I (B (2, 0)) ∧
      (([B (1, 2), B (0, 2), B (0, 3)] <+: orient p q (B (1, 2)) ∧
          [B (2, 1), B (1, 1), B (0, 1), B (0, 0), B (1, 0), B (2, 0), B (3, 0)] <+: orient p q (B (2, 1))) ∨
        ([B (1, 2), B (1, 1), B (1, 0), B (0, 0), B (0, 1), B (0, 2), B (0, 3)] <+: orient p q (B (1, 2)) ∧
          [B (2, 1), B (2, 0), B (3, 0)] <+: orient p q (B (2, 1))))) := by
  obtain ⟨g, hfr, hfc, rw, hrw, hK, hM⟩ := decC_some hd
  refine ⟨g, hfr, hfc, ?_⟩
  intro B
  have hH : 4 ≤ g.H I.w I.h := by unfold Frame.H; split_ifs <;> omega
  have hW : 4 ≤ g.W I.w I.h := by unfold Frame.W; split_ifs <;> omega
  have ne := fun (a : Coord) (h1 : a.1 ≤ 3) (h2 : a.2 ≤ 3)
    (hn : (makeView I.w I.h g (ptsOf I)).at a.1 a.2 = none) (he : IsEnd I (B a)) =>
    view_end hwf g (by omega) (by omega) he hn
  have hfull := rewritesAt_full hrw
  rcases corner_forced hwf hS hw hh g hrw with ⟨rfl, e1, f1⟩ | ⟨rfl, e1, e2, cc, f⟩ | ⟨rfl, e1, e2, f⟩
  · left
    rcases hfull with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, he⟩
    · simp [rw1, rw3] at h
    · simp [rw1, rw2] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at he
    refine ⟨fun x => by rw [hK]; simp [rw1, B, or_comm], by rw [hM]; rfl, e1,
      ne (0, 0) (by decide) (by decide) he.1, f1⟩
  · right; left
    rcases hfull with ⟨h, -⟩ | ⟨-, -, -, -, he⟩ | ⟨h, -⟩
    · simp [rw2, rw3] at h
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at he
      refine ⟨fun x => by rw [hK]; simp [rw2, B], by rw [hM]; rfl, e1, e2,
        ne (0, 1) (by decide) (by decide) he.1, ne (1, 0) (by decide) (by decide) he.2.1, cc, f⟩
    · simp [rw2, rw1] at h
  · right; right
    rcases hfull with ⟨-, -, -, -, he⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at he
      obtain ⟨n00, n01, n02, -, n10, n11, n20, -⟩ := he
      refine ⟨fun x => by rw [hK]; simp [rw3, B], by rw [hM]; rfl, e1, e2,
        ne (0, 0) (by decide) (by decide) n00, ne (0, 1) (by decide) (by decide) n01,
        ne (0, 2) (by decide) (by decide) n02, ne (1, 0) (by decide) (by decide) n10,
        ne (1, 1) (by decide) (by decide) n11, ne (2, 0) (by decide) (by decide) n20, f⟩
    · simp [rw3, rw2] at h
    · simp [rw3, rw1] at h

/-! ### Effective endpoints -/

def dI (I : Inst) (fr fc : Bool) := decC I.w I.h (ptsOf I) fr fc
def RmI (I : Inst) (x : Coord) : Prop := ∃ fr fc, x ∈ KofD (dI I fr fc)
def MallI (I : Inst) : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  MofD (dI I false false) ++ MofD (dI I false true) ++ MofD (dI I true false) ++ MofD (dI I true true)
def effI (I : Inst) (E : Coord) : Coord := applyMoves (MallI I) E

/-- Moves of one corner keep the cells of another corner's window. -/
theorem applyMoves_other {R C : ℕ} (hR : 8 ≤ R) (hC : 8 ≤ C) {M : List ((ℕ × ℕ) × (ℕ × ℕ))}
    {fr fc fr' fc' : Bool} (hM : ∀ m ∈ M, Win R C fr' fc' m.1) (hne : ¬ (fr = fr' ∧ fc = fc'))
    {x : Coord} (hx : Win R C fr fc x) : applyMoves M x = x :=
  applyMoves_id (fun m hm e => hne (win_disj hR hC hx (e ▸ hM m hm)))

theorem applyMoves_win {R C : ℕ} {M : List ((ℕ × ℕ) × (ℕ × ℕ))} {fr fc : Bool}
    (hM : ∀ m ∈ M, Win R C fr fc m.2) {x : Coord} (hx : Win R C fr fc x) :
    Win R C fr fc (applyMoves M x) := by
  induction M generalizing x with
  | nil => exact hx
  | cons m M ih =>
    unfold applyMoves at ih ⊢
    simp only [List.foldl_cons]
    apply ih (fun m' hm' => hM m' (List.mem_cons_of_mem _ hm'))
    split_ifs
    · exact hM m List.mem_cons_self
    · exact hx

/-- The effective cell of a window cell depends only on that corner's moves. -/
theorem effI_corner {I : Inst} (hw : 11 ≤ I.w) (hh : 11 ≤ I.h)
    (hMw : ∀ fr fc, ∀ m ∈ MofD (dI I fr fc), Win I.w I.h fr fc m.1 ∧ Win I.w I.h fr fc m.2)
    {fr fc : Bool} {x : Coord} (hx : Win I.w I.h fr fc x) :
    effI I x = applyMoves (MofD (dI I fr fc)) x := by
  have hR : 8 ≤ I.w := by omega
  have hC : 8 ≤ I.h := by omega
  have oth := fun (fr' fc' : Bool) (hne : ¬ (fr' = fr ∧ fc' = fc)) {y : Coord} (hy : Win I.w I.h fr fc y) =>
    applyMoves_other hR hC (M := MofD (dI I fr' fc')) (fun m hm => (hMw fr' fc' m hm).1)
      (fun ⟨a, b⟩ => hne ⟨a.symm, b.symm⟩) hy
  have stay := applyMoves_win (M := MofD (dI I fr fc)) (fun m hm => (hMw fr fc m hm).2) hx
  unfold effI MallI
  simp only [applyMoves_append]
  cases fr <;> cases fc
  · rw [oth false true (by decide) stay, oth true false (by decide) stay, oth true true (by decide) stay]
  · rw [oth false false (by decide) hx, oth true false (by decide) stay, oth true true (by decide) stay]
  · rw [oth false false (by decide) hx, oth false true (by decide) hx, oth true true (by decide) stay]
  · rw [oth false false (by decide) hx, oth false true (by decide) hx, oth true false (by decide) hx]

/-- The standing hypotheses of the R argument. -/
structure RHyp (I : Inst) (p q : List Coord) : Prop where
  wf : I.WellFormed
  sol : IsSolution I p q
  w11 : 11 ≤ I.w
  h11 : 11 ≤ I.h
  Kw : ∀ fr fc, ∀ x ∈ KofD (dI I fr fc), Win I.w I.h fr fc x
  Mw : ∀ fr fc, ∀ m ∈ MofD (dI I fr fc), Win I.w I.h fr fc m.1 ∧ Win I.w I.h fr fc m.2
  effOk : ∀ E, IsEnd I E → ¬ RmI I (effI I E)

theorem dl3 {K : List Coord} {a b c : Coord} (h1 : a ∈ K) (h2 : b ∈ K) : ∀ x ∈ [a, b, c].dropLast, x ∈ K := by
  intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption

theorem dl7 {K : List Coord} {a b c d e f g : Coord} (h1 : a ∈ K) (h2 : b ∈ K) (h3 : c ∈ K) (h4 : d ∈ K)
    (h5 : e ∈ K) (h6 : f ∈ K) : ∀ x ∈ [a, b, c, d, e, f, g].dropLast, x ∈ K := by
  intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

section Ends

variable {I : Inst} {p q : List Coord} (H : RHyp I p q)
include H

omit H in
theorem rm_of {fr fc : Bool} {x : Coord} (hx : x ∈ KofD (dI I fr fc)) : RmI I x := ⟨fr, fc, hx⟩

/-- Move sources are settled. -/
theorem src_settled {fr fc : Bool} {m : (ℕ × ℕ) × (ℕ × ℕ)} (hm : m ∈ MofD (dI I fr fc)) :
    RmI I m.1 := by
  cases hd : dI I fr fc with
  | none => rw [hd] at hm; simp [MofD] at hm
  | some KM =>
    obtain ⟨K, M⟩ := KM
    rw [hd] at hm
    simp only [MofD, Option.elim] at hm
    obtain ⟨g, -, -, hp⟩ := corner_package H.wf H.sol (by have := H.w11; omega) (by have := H.h11; omega) hd
    refine ⟨fr, fc, ?_⟩
    rw [hd]
    simp only [KofD, Option.elim]
    rcases hp with ⟨hK, rfl, -⟩ | ⟨hK, rfl, -⟩ | ⟨hK, rfl, -⟩ <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm <;> rw [hK] <;>
      rcases hm with rfl | rfl <;> simp

theorem eff_unsettled {E : Coord} (hr : ¬ RmI I E) : effI I E = E := by
  apply applyMoves_id
  intro m hm e
  unfold MallI at hm
  simp only [List.mem_append] at hm
  rcases hm with ((h | h) | h) | h <;> exact hr (e ▸ src_settled H h)

/-- **Each endpoint's forced prefix**: it ends at the endpoint's effective cell, or (R2 with the
other filling) at its partner's, which then ends at its own. -/
theorem endpoint_info {E : Coord} (hE : IsEnd I E) :
    ∃ F, GoodPre (RmI I) (orient p q E) F ∧ F.head? = some E ∧
      (F.getLast? = some (effI I E) ∨
        ∃ E', IsEnd I E' ∧ E' ≠ E ∧ colOf p E' = colOf p E ∧ F.getLast? = some (effI I E') ∧
          ∀ F', GoodPre (RmI I) (orient p q E') F' → F'.getLast? = some (effI I E)) := by
  have hw4 : 4 ≤ I.w := by have := H.w11; omega
  have hh4 : 4 ≤ I.h := by have := H.h11; omega
  have hS := H.sol
  obtain ⟨hn, hh, -, -, -⟩ := orient_facts hS hE
  by_cases hr : RmI I E
  · obtain ⟨fr, fc, hK⟩ := hr
    cases hd : dI I fr fc with
    | none => rw [hd] at hK; simp [KofD] at hK
    | some KM =>
      obtain ⟨K, M⟩ := KM
      rw [hd] at hK
      simp only [KofD, Option.elim] at hK
      have hEw : Win I.w I.h fr fc E := H.Kw fr fc E (by rw [hd]; exact hK)
      have effc := fun {x : Coord} (hx : Win I.w I.h fr fc x) => effI_corner H.w11 H.h11 H.Mw hx
      rw [hd] at effc
      simp only [MofD, Option.elim] at effc
      have rmK : ∀ x ∈ K, RmI I x := fun x hx => ⟨fr, fc, by rw [hd]; exact hx⟩
      obtain ⟨g, hfr, hfc, hp⟩ := corner_package H.wf hS hw4 hh4 hd
      set B := Frame.back I.w I.h g
      have bi := fun (a b : Coord) (h1 : a.1 ≤ 3) (h2 : a.2 ≤ 3) (h3 : b.1 ≤ 3) (h4 : b.2 ≤ 3) (hab : a ≠ b) =>
        (fun e => hab (back_inj hw4 hh4 g h1 h2 h3 h4 e) : B a ≠ B b)
      have bw := fun (a : Coord) (h1 : a.1 ≤ 3) (h2 : a.2 ≤ 3) =>
        (hfr ▸ hfc ▸ back_win hw4 hh4 g h1 h2 : Win I.w I.h fr fc (B a))
      have gp : ∀ (E0 : Coord) (F : List Coord) (f : Coord), F <+: orient p q E0 → (∀ x ∈ F.dropLast, x ∈ K) →
          F.getLast? = some f → (∃ E', IsEnd I E' ∧ f = effI I E') → GoodPre (RmI I) (orient p q E0) F := by
        intro E0 F f h1 h2 h3 ⟨E', hE', hf⟩
        exact ⟨h1, fun x hx => rmK x (h2 x hx), f, h3, hf ▸ H.effOk E' hE'⟩
      rcases hp with ⟨hKm, rfl, e1, n00, f1⟩ | ⟨hKm, rfl, e1, e2, n01, n10, cc, f⟩ |
          ⟨hKm, rfl, e1, e2, n00, n01, n02, n10, n11, n20, f⟩
      · -- R1
        have hE' : E = B (0, 1) := by
          rcases (hKm E).mp hK with h | h
          · exact absurd (h ▸ hE) n00
          · exact h
        subst hE'
        have ef : effI I (B (0, 1)) = B (1, 0) := by
          rw [effc (bw (0, 1) (by decide) (by decide))]
          simp [applyMoves]
        refine ⟨_, gp _ _ (B (1, 0)) f1 (by intro x hx; simp at hx; rw [hKm]; tauto) rfl
          ⟨_, e1, ef.symm⟩, rfl, Or.inl (by rw [ef]; rfl)⟩
      · -- R2
        have ef1 : effI I (B (0, 0)) = B (0, 2) := by
          rw [effc (bw (0, 0) (by decide) (by decide))]
          simp only [applyMoves, List.foldl_cons, List.foldl_nil, ↓reduceIte]
          rw [ite_eq_right (fun h => bi (0, 2) (1, 1) (by decide) (by decide) (by decide) (by decide) (by decide) h)]
        have ef2 : effI I (B (1, 1)) = B (2, 0) := by
          rw [effc (bw (1, 1) (by decide) (by decide))]
          simp only [applyMoves, List.foldl_cons, List.foldl_nil]
          rw [ite_eq_right (fun h => bi (1, 1) (0, 0) (by decide) (by decide) (by decide) (by decide) (by decide) h)]
          simp
        have d12 : B (1, 1) ≠ B (0, 0) := fun h => bi (1, 1) (0, 0) (by decide) (by decide) (by decide) (by decide) (by decide) h
        have inK : ∀ a ∈ ([(0, 0), (0, 1), (1, 0), (1, 1)] : List Coord), B a ∈ K := by
          intro a ha; rw [hKm]; simp at ha; rcases ha with rfl | rfl | rfl | rfl <;> simp
        have hEc : E = B (0, 0) ∨ E = B (1, 1) := by
          rcases (hKm E).mp hK with h | h | h | h
          · exact Or.inl h
          · exact absurd (h ▸ hE) n01
          · exact absurd (h ▸ hE) n10
          · exact Or.inr h
        rcases f with ⟨fa, fb⟩ | ⟨fa, fb⟩
        · have Ga := gp _ _ _ fa (dl3 (inK _ (by simp)) (inK _ (by simp))) rfl ⟨_, e1, ef1.symm⟩
          have Gb := gp _ _ _ fb (dl3 (inK _ (by simp)) (inK _ (by simp))) rfl ⟨_, e2, ef2.symm⟩
          rcases hEc with rfl | rfl
          · exact ⟨_, Ga, rfl, Or.inl (by rw [ef1]; rfl)⟩
          · exact ⟨_, Gb, rfl, Or.inl (by rw [ef2]; rfl)⟩
        · have Ga := gp _ _ _ fa (dl3 (inK _ (by simp)) (inK _ (by simp))) rfl ⟨_, e2, ef2.symm⟩
          have Gb := gp _ _ _ fb (dl3 (inK _ (by simp)) (inK _ (by simp))) rfl ⟨_, e1, ef1.symm⟩
          rcases hEc with rfl | rfl
          · refine ⟨_, Ga, rfl, Or.inr ⟨B (1, 1), e2, d12, cc.symm, by rw [ef2]; rfl, fun F' hF' => ?_⟩⟩
            rw [goodPre_unique hF' Gb, ef1]; rfl
          · refine ⟨_, Gb, rfl, Or.inr ⟨B (0, 0), e1, d12.symm, cc, by rw [ef1]; rfl, fun F' hF' => ?_⟩⟩
            rw [goodPre_unique hF' Ga, ef2]; rfl
      · -- R3
        have ef3 : effI I (B (1, 2)) = B (0, 3) := by
          rw [effc (bw (1, 2) (by decide) (by decide))]
          simp only [applyMoves, List.foldl_cons, List.foldl_nil, ↓reduceIte]
          rw [ite_eq_right (fun h => bi (0, 3) (2, 1) (by decide) (by decide) (by decide) (by decide) (by decide) h)]
        have ef4 : effI I (B (2, 1)) = B (3, 0) := by
          rw [effc (bw (2, 1) (by decide) (by decide))]
          simp only [applyMoves, List.foldl_cons, List.foldl_nil]
          rw [ite_eq_right (fun h => bi (2, 1) (1, 2) (by decide) (by decide) (by decide) (by decide) (by decide) h)]
          simp
        have inK : ∀ a ∈ ([(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0), (1, 2), (2, 1)] : List Coord),
            B a ∈ K := by
          intro a ha; rw [hKm]; simp at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
        have hEc : E = B (1, 2) ∨ E = B (2, 1) := by
          rcases (hKm E).mp hK with h | h | h | h | h | h | h | h
          · exact absurd (h ▸ hE) n00
          · exact absurd (h ▸ hE) n01
          · exact absurd (h ▸ hE) n02
          · exact absurd (h ▸ hE) n10
          · exact absurd (h ▸ hE) n11
          · exact absurd (h ▸ hE) n20
          · exact Or.inl h
          · exact Or.inr h
        rcases f with ⟨fa, fb⟩ | ⟨fa, fb⟩
        · rcases hEc with rfl | rfl
          · exact ⟨_, gp _ _ _ fa (dl3 (inK _ (by simp)) (inK _ (by simp))) rfl ⟨_, e1, ef3.symm⟩, rfl, Or.inl (by rw [ef3]; rfl)⟩
          · exact ⟨_, gp _ _ _ fb (dl7 (inK _ (by simp)) (inK _ (by simp)) (inK _ (by simp)) (inK _ (by simp)) (inK _ (by simp))
                (inK _ (by simp))) rfl
              ⟨_, e2, ef4.symm⟩, rfl, Or.inl (by rw [ef4]; rfl)⟩
        · rcases hEc with rfl | rfl
          · exact ⟨_, gp _ _ _ fa (dl7 (inK _ (by simp)) (inK _ (by simp)) (inK _ (by simp)) (inK _ (by simp)) (inK _ (by simp))
                (inK _ (by simp))) rfl
              ⟨_, e1, ef3.symm⟩, rfl, Or.inl (by rw [ef3]; rfl)⟩
          · exact ⟨_, gp _ _ _ fb (dl3 (inK _ (by simp)) (inK _ (by simp))) rfl ⟨_, e2, ef4.symm⟩, rfl, Or.inl (by rw [ef4]; rfl)⟩
  · obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp hh
    refine ⟨[E], ⟨⟨t, by rw [ht]; rfl⟩, by simp, E, rfl, hr⟩, rfl, Or.inl (by rw [eff_unsettled H hr]; rfl)⟩

omit H in
theorem prefix_dropLast_sub {Rm : Coord → Prop} {L F FL : List Coord} (hF : GoodPre Rm L F)
    (hFL : FL <+: L) (hd : ∀ y ∈ FL.dropLast, Rm y) : ∀ y ∈ FL.dropLast, y ∈ F.dropLast := by
  obtain ⟨p1, -, f, l1, n1⟩ := hF
  rcases List.prefix_or_prefix_of_prefix p1 hFL with h | h
  · -- F <+: FL: then F = FL, as `F`'s last cell is not settled
    obtain ⟨T, rfl⟩ := h
    cases T with
    | nil => intro y hy; simpa using hy
    | cons t T =>
      exfalso
      have : f ∈ (F ++ t :: T).dropLast := by
        rw [List.dropLast_append_of_ne_nil (by simp)]
        exact List.mem_append_left _ (List.mem_of_getLast? l1)
      exact n1 (hd f this)
  · obtain ⟨T, rfl⟩ := h
    intro y hy
    cases T with
    | nil => simpa using hy
    | cons t T =>
      rw [List.dropLast_append_of_ne_nil (by simp)]
      exact List.mem_append_left _ (List.dropLast_subset _ hy)

/-- **Coverage**: every settled cell is on the forced prefix of some endpoint. -/
theorem coverage {x : Coord} (hx : RmI I x) :
    ∃ E, IsEnd I E ∧ ∃ F, GoodPre (RmI I) (orient p q E) F ∧ F.head? = some E ∧ x ∈ F.dropLast := by
  have hw4 : 4 ≤ I.w := by have := H.w11; omega
  have hh4 : 4 ≤ I.h := by have := H.h11; omega
  obtain ⟨fr, fc, hK⟩ := hx
  cases hd : dI I fr fc with
  | none => rw [hd] at hK; simp [KofD] at hK
  | some KM =>
    obtain ⟨K, M⟩ := KM
    rw [hd] at hK
    simp only [KofD, Option.elim] at hK
    have rmK : ∀ y ∈ K, RmI I y := fun y hy => ⟨fr, fc, by rw [hd]; exact hy⟩
    obtain ⟨g, -, -, hp⟩ := corner_package H.wf H.sol hw4 hh4 hd
    set B := Frame.back I.w I.h g
    -- the forced list of an endpoint covers part of `K`
    have use : ∀ (E : Coord) (FL : List Coord), IsEnd I E → FL <+: orient p q E → (∀ y ∈ FL.dropLast, y ∈ K) →
        x ∈ FL.dropLast → ∃ E, IsEnd I E ∧ ∃ F, GoodPre (RmI I) (orient p q E) F ∧ F.head? = some E ∧
          x ∈ F.dropLast := by
      intro E FL hE hFL hsub hxF
      obtain ⟨F, hF, hh, -⟩ := endpoint_info H hE
      exact ⟨E, hE, F, hF, hh, prefix_dropLast_sub hF hFL (fun y hy => rmK y (hsub y hy)) x hxF⟩
    rcases hp with ⟨hKm, -, e1, -, f1⟩ | ⟨hKm, -, e1, e2, -, -, -, f⟩ | ⟨hKm, -, e1, e2, -, -, -, -, -, -, f⟩
    · have hs : ∀ y ∈ [B (0, 1), B (0, 0), B (1, 0)].dropLast, y ∈ K := by
        intro y hy; rw [hKm]; simp at hy; tauto
      exact use _ _ e1 f1 hs (by rcases (hKm x).mp hK with h | h <;> simp [h])
    · have inK : ∀ y, y = B (0, 0) ∨ y = B (0, 1) ∨ y = B (1, 0) ∨ y = B (1, 1) → y ∈ K := fun y hy => (hKm y).mpr hy
      rcases f with ⟨fa, fb⟩ | ⟨fa, fb⟩
      · rcases (hKm x).mp hK with h | h | h | h
        · exact use _ _ e1 fa (dl3 (inK _ (by simp)) (inK _ (by simp))) (by simp [h])
        · exact use _ _ e1 fa (dl3 (inK _ (by simp)) (inK _ (by simp))) (by simp [h])
        · exact use _ _ e2 fb (dl3 (inK _ (by simp)) (inK _ (by simp))) (by simp [h])
        · exact use _ _ e2 fb (dl3 (inK _ (by simp)) (inK _ (by simp))) (by simp [h])
      · rcases (hKm x).mp hK with h | h | h | h
        · exact use _ _ e1 fa (dl3 (inK _ (by simp)) (inK _ (by simp))) (by simp [h])
        · exact use _ _ e2 fb (dl3 (inK _ (by simp)) (inK _ (by simp))) (by simp [h])
        · exact use _ _ e1 fa (dl3 (inK _ (by simp)) (inK _ (by simp))) (by simp [h])
        · exact use _ _ e2 fb (dl3 (inK _ (by simp)) (inK _ (by simp))) (by simp [h])
    · have inK : ∀ y, y = B (0, 0) ∨ y = B (0, 1) ∨ y = B (0, 2) ∨ y = B (1, 0) ∨ y = B (1, 1) ∨
          y = B (2, 0) ∨ y = B (1, 2) ∨ y = B (2, 1) → y ∈ K := fun y hy => (hKm y).mpr hy
      have d7 := fun {a b c d e f' g' : Coord} (h1 : a ∈ K) (h2 : b ∈ K) (h3 : c ∈ K) (h4 : d ∈ K)
        (h5 : e ∈ K) (h6 : f' ∈ K) => dl7 (g := g') h1 h2 h3 h4 h5 h6
      rcases f with ⟨fa, fb⟩ | ⟨fa, fb⟩
      · have sa := dl3 (c := B (0, 3)) (inK (B (1, 2)) (by simp)) (inK (B (0, 2)) (by simp))
        have sb := d7 (g' := B (3, 0)) (inK (B (2, 1)) (by simp)) (inK (B (1, 1)) (by simp))
          (inK (B (0, 1)) (by simp)) (inK (B (0, 0)) (by simp)) (inK (B (1, 0)) (by simp)) (inK (B (2, 0)) (by simp))
        rcases (hKm x).mp hK with h | h | h | h | h | h | h | h <;> subst h
        · exact use _ _ e2 fb sb (by simp)
        · exact use _ _ e2 fb sb (by simp)
        · exact use _ _ e1 fa sa (by simp)
        · exact use _ _ e2 fb sb (by simp)
        · exact use _ _ e2 fb sb (by simp)
        · exact use _ _ e2 fb sb (by simp)
        · exact use _ _ e1 fa sa (by simp)
        · exact use _ _ e2 fb sb (by simp)
      · have sa := d7 (g' := B (0, 3)) (inK (B (1, 2)) (by simp)) (inK (B (1, 1)) (by simp))
          (inK (B (1, 0)) (by simp)) (inK (B (0, 0)) (by simp)) (inK (B (0, 1)) (by simp)) (inK (B (0, 2)) (by simp))
        have sb := dl3 (c := B (3, 0)) (inK (B (2, 1)) (by simp)) (inK (B (2, 0)) (by simp))
        rcases (hKm x).mp hK with h | h | h | h | h | h | h | h <;> subst h
        · exact use _ _ e1 fa sa (by simp)
        · exact use _ _ e1 fa sa (by simp)
        · exact use _ _ e1 fa sa (by simp)
        · exact use _ _ e1 fa sa (by simp)
        · exact use _ _ e1 fa sa (by simp)
        · exact use _ _ e2 fb sb (by simp)
        · exact use _ _ e1 fa sa (by simp)
        · exact use _ _ e2 fb sb (by simp)

/-- **The cut path**: between the effective cells, avoiding every settled cell. -/
theorem path_trim {L : List Coord} {s t : Coord} (hL : IsPath I.w I.h s t L)
    (hos : orient p q s = L) (hot : orient p q t = L.reverse) (hs : IsEnd I s) (ht : IsEnd I t)
    (hsame : ∀ E, IsEnd I E → colOf p E = colOf p s → E = s ∨ E = t) (hcol : colOf p t = colOf p s)
    (hst : s ≠ t)
    (hother : ∀ E, IsEnd I E → colOf p E ≠ colOf p s → ∀ v ∈ orient p q E, v ∉ L)
    (heff : effI I s ≠ effI I t) :
    ∃ P, P <:+: L ∧ (∀ x ∈ P, ¬ RmI I x) ∧
      ((P.head? = some (effI I s) ∧ P.getLast? = some (effI I t)) ∨
        (P.head? = some (effI I t) ∧ P.getLast? = some (effI I s))) := by
  obtain ⟨Fs, gs, hs1, is⟩ := endpoint_info H hs
  obtain ⟨Ft, gt, ht1, it⟩ := endpoint_info H ht
  have gs' := gs; have gt' := gt
  rw [hos] at gs'; rw [hot] at gt'
  obtain ⟨fs, lfs, nfs⟩ := gs'.2.2
  obtain ⟨ft, lft, nft⟩ := gt'.2.2
  -- the two effective cells
  have pair : (fs = effI I s ∧ ft = effI I t) ∨ (fs = effI I t ∧ ft = effI I s) := by
    have ps : fs = effI I s ∨ (fs = effI I t ∧ ft = effI I s) := by
      rcases is with h | ⟨E', hE', hne, hc, hl, hall⟩
      · left; rw [lfs] at h; exact Option.some.inj h
      · have : E' = t := by
          rcases hsame E' hE' hc with h | h
          · exact absurd h hne
          · exact h
        subst this
        right
        refine ⟨by rw [lfs] at hl; exact Option.some.inj hl, ?_⟩
        have := hall Ft gt
        rw [lft] at this; exact Option.some.inj this
    rcases ps with h | h
    · rcases it with h' | ⟨E', hE', hne, hc, hl, hall⟩
      · left; exact ⟨h, by rw [lft] at h'; exact Option.some.inj h'⟩
      · have : E' = s := by
          rcases hsame E' hE' (hc.trans hcol) with h'' | h''
          · exact h''
          · exact absurd h'' hne
        subst this
        right
        refine ⟨?_, by rw [lft] at hl; exact Option.some.inj hl⟩
        have := hall Fs gs
        rw [lfs] at this; exact Option.some.inj this
    · right; exact h
  have hne : fs ≠ ft := by
    rcases pair with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [a, b]
    · exact heff
    · exact fun e => heff e.symm
  have nes : Fs ≠ [] := fun e => by rw [e] at lfs; simp at lfs
  have net : Ft ≠ [] := fun e => by rw [e] at lft; simp at lft
  have efs : Fs.getLast nes = fs := by rw [List.getLast?_eq_some_getLast nes] at lfs; exact Option.some.inj lfs
  have eft : Ft.getLast net = ft := by rw [List.getLast?_eq_some_getLast net] at lft; exact Option.some.inj lft
  have fsFt : fs ∉ Ft := by
    intro hm
    have hFt : Ft = Ft.dropLast ++ [ft] := by rw [← eft]; exact (List.dropLast_append_getLast net).symm
    rw [hFt, List.mem_append, List.mem_singleton] at hm
    rcases hm with h | h
    · exact nfs (gt'.2.1 fs h)
    · exact hne h
  obtain ⟨M, hM, hMh, hMl⟩ := split_ends gs'.1 gt'.1 nes net (by rw [efs]; exact fsFt)
  have hn := hL.2.2.1
  refine ⟨M, ⟨Fs.dropLast, Ft.dropLast.reverse, hM.symm⟩, ?_, ?_⟩
  · intro y hy hr
    obtain ⟨E, hE, F, hF, hFh, hyF⟩ := coverage H hr
    have hyL : y ∈ L := by rw [hM]; simp [hy]
    by_cases hc : colOf p E = colOf p s
    · rcases hsame E hE hc with rfl | rfl
      · rw [hos] at hF
        rw [goodPre_unique hF gs'] at hyF
        rw [hM, List.append_assoc] at hn
        have := (List.nodup_append.mp hn).2.2 y hyF y (List.mem_append_left _ hy)
        exact this rfl
      · rw [hot] at hF
        rw [goodPre_unique hF gt'] at hyF
        rw [hM] at hn
        have := (List.nodup_append.mp hn).2.2 y (List.mem_append_right _ hy) y (by simpa using hyF)
        exact this rfl
    · exact hother E hE hc y (hF.1.subset (List.dropLast_subset _ hyF)) hyL
  · rw [hMh, hMl, lfs, lft]
    rcases pair with ⟨a, b⟩ | ⟨a, b⟩
    · left; rw [a, b]; exact ⟨rfl, rfl⟩
    · right; rw [a, b]; exact ⟨rfl, rfl⟩

end Ends




/-! ### Doubled paths in ℕ × ℕ -/

def dd (x : Coord) : Coord := (2 * x.1, 2 * x.2)
def dm (x y : Coord) : Coord := (x.1 + y.1, x.2 + y.2)

def dpN : List Coord → List Coord
  | [] => []
  | [x] => [dd x]
  | x :: y :: L => dd x :: dm x y :: dpN (y :: L)

theorem dpN_chain : ∀ (L : List Coord), chainAdjacent L = true → chainAdjacent (dpN L) = true
  | [], _ => rfl
  | [_], _ => rfl
  | x :: y :: L, h => by
    rw [chainAdjacent_cons_cons, Bool.and_eq_true] at h
    have hxy := (adjacentB_iff x y).mp h.1
    have ih := dpN_chain (y :: L) h.2
    obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y
    unfold Adjacent at hxy
    simp only at hxy
    cases L with
    | nil =>
      simp only [dpN]
      rw [chainAdjacent_cons_cons, chainAdjacent_cons_cons, Bool.and_eq_true, Bool.and_eq_true,
        adjacentB_iff, adjacentB_iff]
      refine ⟨by unfold Adjacent dd dm; simp only; omega, by unfold Adjacent dd dm; simp only; omega, rfl⟩
    | cons z L =>
      simp only [dpN] at ih ⊢
      rw [chainAdjacent_cons_cons, chainAdjacent_cons_cons, Bool.and_eq_true, Bool.and_eq_true,
        adjacentB_iff, adjacentB_iff]
      exact ⟨by unfold Adjacent dd dm; simp only; omega, by unfold Adjacent dd dm; simp only; omega, ih⟩

theorem mem_dpN : ∀ {L : List Coord}, chainAdjacent L = true → ∀ {z : Coord}, z ∈ dpN L →
    (∃ x ∈ L, z = dd x) ∨ (∃ x ∈ L, ∃ y ∈ L, Adjacent x y ∧ z = dm x y)
  | [], _, _, h => by simp [dpN] at h
  | [x], _, z, h => by simp [dpN] at h; exact Or.inl ⟨x, by simp, h⟩
  | x :: y :: L, hc, z, h => by
    rw [chainAdjacent_cons_cons, Bool.and_eq_true] at hc
    simp only [dpN, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · exact Or.inl ⟨x, by simp, rfl⟩
    · exact Or.inr ⟨x, by simp, y, by simp, (adjacentB_iff x y).mp hc.1, rfl⟩
    · rcases mem_dpN hc.2 h with ⟨u, hu, rfl⟩ | ⟨u, hu, v, hv, huv, rfl⟩
      · exact Or.inl ⟨u, List.mem_cons_of_mem _ hu, rfl⟩
      · exact Or.inr ⟨u, List.mem_cons_of_mem _ hu, v, List.mem_cons_of_mem _ hv, huv, rfl⟩

theorem dpN_head : ∀ (x : Coord) (L : List Coord), ∃ T, dpN (x :: L) = dd x :: T
  | _x, [] => ⟨[], rfl⟩
  | _x, _y :: _L => ⟨_, rfl⟩

theorem dpN_last : ∀ (x : Coord) (L : List Coord), (dpN (x :: L)).getLast? = some (dd (L.getLastD x))
  | x, [] => rfl
  | x, y :: L => by
    simp only [dpN]
    have := dpN_last y L
    obtain ⟨T, hT⟩ := dpN_head y L
    rw [hT] at this ⊢
    rw [List.getLast?_cons_cons, List.getLast?_cons_cons, this, List.getLastD_cons]

theorem dpN_inb {R C : ℕ} : ∀ {L : List Coord}, (∀ v ∈ L, v.1 < R ∧ v.2 < C) →
    chainAdjacent L = true → ∀ z ∈ dpN L, z.1 < 2 * R - 1 ∧ z.2 < 2 * C - 1 := by
  intro L hb hc z hz
  rcases mem_dpN hc hz with ⟨x, hx, rfl⟩ | ⟨x, hx, y, hy, -, rfl⟩
  · have := hb x hx; unfold dd; simp only; omega
  · have := hb x hx; have := hb y hy; unfold dm; simp only; omega

/-! ### Exits from the staircase cells, per corner shape (doubled corner coordinates) -/

/-- The exit from staircase cell `a` of a corner holding shape `S`: a doubled path from `dd a` to
the edge of the grid, through settled cells, square centres and edges at `a`. -/
def exitTab (S : List Coord) (a : Coord) : List Coord :=
  if S = rw1.removed then
    if a = (1, 1) then [(2, 2), (1, 2), (0, 2)]
    else if a = (1, 2) then [(2, 4), (1, 4), (1, 3), (0, 3)] else [dd a]
  else if S = rw1.removed.map Prod.swap then
    if a = (2, 1) then [(4, 2), (4, 1), (3, 1), (3, 0)]
    else if a = (1, 1) then [(2, 2), (2, 1), (2, 0)] else [dd a]
  else if S = rw2.removed then
    if a = (2, 1) then [(4, 2), (3, 2), (3, 1), (3, 0)]
    else if a = (2, 2) then [(4, 4), (3, 4), (3, 3), (2, 3), (2, 2), (2, 1), (2, 0)]
    else if a = (1, 2) then [(2, 4), (1, 4), (1, 3), (1, 2), (1, 1), (1, 0)] else [dd a]
  else if S = rw3.removed then
    if a = (3, 1) then [(6, 2), (5, 2), (5, 1), (5, 0)]
    else if a = (3, 2) then [(6, 4), (5, 4), (5, 3), (4, 3), (4, 2), (4, 1), (4, 0)]
    else if a = (2, 2) then [(4, 4), (3, 4), (3, 3), (3, 2), (3, 1), (3, 0)]
    else if a = (2, 3) then [(4, 6), (3, 6), (3, 5), (2, 5), (2, 4), (2, 3), (2, 2), (2, 1), (2, 0)]
    else if a = (1, 3) then [(2, 6), (1, 6), (1, 5), (1, 4), (1, 3), (1, 2), (1, 1), (1, 0)] else [dd a]
  else [dd a]

def stairOfS (S : List Coord) : List Coord := staircase (lamS S)

/-- A doubled point is safe for the end cell `a`: it cannot lie on the other path. -/
def safeB (S : List Coord) (a z : Coord) : Bool :=
  z == dd a || (nbrList a).any (fun y => z == dm a y) || (z.1 % 2 == 1 && z.2 % 2 == 1) ||
    S.any (fun u => z == dd u || (nbrList u).any (fun v => z == dm u v))

/-- The position of an exit end along the corner's two edges: the left edge upwards, then the
top edge rightwards. -/
def fkey (e : Coord) : ℕ := if e.2 = 0 then 8 - e.1 else 8 + e.2

theorem exit_facts : ∀ S ∈ shapes, ∀ a ∈ stairOfS S,
    (exitTab S a).head? = some (dd a) ∧ chainAdjacent (exitTab S a) = true ∧
      (∃ e, (exitTab S a).getLast? = some e ∧ (e.1 = 0 ∨ e.2 = 0)) ∧
      (exitTab S a).all (safeB S a) = true ∧ (exitTab S a).all (fun z => z.1 ≤ 7 && z.2 ≤ 7) = true := by
  decide

def exitEnd (S : List Coord) (a : Coord) : Coord := (exitTab S a).getLastD (dd a)

theorem exit_order : ∀ S ∈ shapes,
    (stairOfS S).Pairwise (fun a b => fkey (exitEnd S a) < fkey (exitEnd S b)) ∧
      (stairOfS S).Pairwise (fun a b => (exitTab S a).all (fun z => !(exitTab S b).contains z) = true) := by
  decide

/-! ### Exits at the four corners -/

theorem back2_dd {R C : ℕ} (F : Frame) (hF : F.tr = false) {a : Coord} (h1 : a.1 < R) (h2 : a.2 < C) :
    Frame.back (2 * R - 1) (2 * C - 1) F (dd a) = dd (Frame.back R C F a) := by
  obtain ⟨fr, fc, tr⟩ := F
  simp only at hF; subst hF
  obtain ⟨a1, a2⟩ := a
  simp only at h1 h2
  cases fr <;> cases fc <;> simp [Frame.back, dd] <;> omega

theorem back2_adj {R C : ℕ} (F : Frame) (hF : F.tr = false) {u v : Coord} (h : Adjacent u v)
    (hu : u.1 < 2 * R - 1 ∧ u.2 < 2 * C - 1) (hv : v.1 < 2 * R - 1 ∧ v.2 < 2 * C - 1) :
    Adjacent (Frame.back (2 * R - 1) (2 * C - 1) F u) (Frame.back (2 * R - 1) (2 * C - 1) F v) := by
  obtain ⟨fr, fc, tr⟩ := F
  simp only at hF; subst hF
  obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v
  unfold Adjacent at h ⊢
  simp only at hu hv h
  cases fr <;> cases fc <;> simp [Frame.back] <;> omega

/-- The perimeter anchor of an exit end, by corner, as a function of its corner key `fkey`. -/
theorem anc_corner {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) (fr fc : Bool) {e : Coord}
    (he : e.1 = 0 ∨ e.2 = 0) (h1 : e.1 ≤ 7) (h2 : e.2 ≤ 7) :
    let R2 := 2 * R - 1
    let C2 := 2 * C - 1
    let x := Frame.back R2 C2 ⟨fr, fc, false⟩ e
    OnPerim R2 C2 x ∧ x.1 < R2 ∧ x.2 < C2 ∧
    Planar.anc R2 C2 x =
      (match fr, fc with
        | false, false => if fkey e < 8 then 2 * C2 + 2 * R2 + 3 - 8 + fkey e else fkey e - 7
        | false, true => if fkey e < 8 then C2 + 10 - fkey e else C2 + 8 - fkey e
        | true, true => if fkey e ≤ 8 then C2 + R2 - 7 + fkey e else C2 + R2 - 5 + fkey e
        | true, false => if fkey e < 8 then 2 * C2 + R2 + 12 - fkey e else 2 * C2 + R2 + 10 - fkey e) := by
  intro R2 C2 x
  obtain ⟨e1, e2⟩ := e
  simp only at he h1 h2
  simp only [x, R2, C2]
  unfold OnPerim Planar.anc fkey
  cases fr <;> cases fc <;> simp only [Frame.back, Bool.false_eq_true, ↓reduceIte] <;>
    split_ifs <;> omega

theorem back2_dm {R C : ℕ} (F : Frame) (hF : F.tr = false) {u v : Coord} (hu : u.1 < R ∧ u.2 < C)
    (hv : v.1 < R ∧ v.2 < C) :
    Frame.back (2 * R - 1) (2 * C - 1) F (dm u v) = dm (Frame.back R C F u) (Frame.back R C F v) := by
  obtain ⟨fr, fc, tr⟩ := F
  simp only at hF; subst hF
  obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v
  simp only at hu hv
  cases fr <;> cases fc <;> simp [Frame.back, dm] <;> omega

theorem back2_odd {R C : ℕ} (F : Frame) (hF : F.tr = false) {z : Coord} (h1 : z.1 % 2 = 1) (h2 : z.2 % 2 = 1)
    (hz : z.1 < 2 * R - 1 ∧ z.2 < 2 * C - 1) :
    (Frame.back (2 * R - 1) (2 * C - 1) F z).1 % 2 = 1 ∧ (Frame.back (2 * R - 1) (2 * C - 1) F z).2 % 2 = 1 := by
  obtain ⟨fr, fc, tr⟩ := F
  simp only at hF; subst hF
  obtain ⟨z1, z2⟩ := z
  simp only at h1 h2 hz
  cases fr <;> cases fc <;> simp [Frame.back] <;> omega

/-- A doubled point safe for end cell `x` with settled cells `K`. -/
def SafeFor (K : Coord → Prop) (x z : Coord) : Prop :=
  z = dd x ∨ (∃ y, Adjacent x y ∧ z = dm x y) ∨ (z.1 % 2 = 1 ∧ z.2 % 2 = 1) ∨
    (∃ u, K u ∧ ∃ v, Adjacent u v ∧ z = dm u v) ∨ (∃ u, K u ∧ z = dd u)

theorem back_adj' {R C : ℕ} (F : Frame) (hF : F.tr = false) {u v : Coord} (h : Adjacent u v)
    (hu : u.1 < R ∧ u.2 < C) (hv : v.1 < R ∧ v.2 < C) :
    Adjacent (Frame.back R C F u) (Frame.back R C F v) := by
  obtain ⟨fr, fc, tr⟩ := F
  simp only at hF; subst hF
  obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v
  unfold Adjacent at h ⊢
  simp only at hu hv h
  cases fr <;> cases fc <;> simp [Frame.back] <;> omega

theorem adj_of_nbrList {a y : Coord} (h : y ∈ nbrList a) : Adjacent a y := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨y1, y2⟩ := y
  unfold nbrList at h
  unfold Adjacent
  split_ifs at h <;> simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at h <;> omega

theorem stair_small : ∀ S ∈ shapes, ∀ a ∈ stairOfS S, a.1 ≤ 4 ∧ a.2 ≤ 4 ∧
    (∀ b ∈ S, b.1 ≤ 3 ∧ b.2 ≤ 3) := by decide

theorem chain_map {f : Coord → Coord} (P : Coord → Prop) (hf : ∀ u v, Adjacent u v → P u → P v → Adjacent (f u) (f v)) :
    ∀ (l : List Coord), (∀ v ∈ l, P v) → chainAdjacent l = true → chainAdjacent (l.map f) = true
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | a :: b :: l, hl, hc => by
    rw [chainAdjacent_cons_cons, Bool.and_eq_true] at hc
    simp only [List.map_cons]
    rw [chainAdjacent_cons_cons, Bool.and_eq_true]
    refine ⟨(adjacentB_iff _ _).mpr (hf _ _ ((adjacentB_iff _ _).mp hc.1) (hl a (by simp)) (hl b (by simp))), ?_⟩
    have := chain_map P hf (b :: l) (fun v hv => hl v (List.mem_cons_of_mem _ hv)) hc.2
    simpa using this

/-- **The exit of a staircase cell, in grid coordinates.** -/
theorem stair_exit {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) (fr fc : Bool) {S : List Coord} (hS : S ∈ shapes)
    {a : Coord} (ha : a ∈ stairOfS S) :
    let F : Frame := ⟨fr, fc, false⟩
    let x := F.back R C a
    let ex := (exitTab S a).map (Frame.back (2 * R - 1) (2 * C - 1) F)
    ex.head? = some (dd x) ∧ chainAdjacent ex = true ∧ (∀ z ∈ ex, z.1 < 2 * R - 1 ∧ z.2 < 2 * C - 1) ∧
      (∀ z ∈ ex, SafeFor (fun u => ∃ b ∈ S, u = F.back R C b) x z) ∧
      ex.getLastD (dd x) = Frame.back (2 * R - 1) (2 * C - 1) F (exitEnd S a) := by
  intro F x ex
  obtain ⟨hh, hc, -, hsafe, hsm⟩ := exit_facts S hS a ha
  obtain ⟨a1, a2, hSs⟩ := stair_small S hS a ha
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hsafe hsm
  have hF : F.tr = false := rfl
  have aB : a.1 < R ∧ a.2 < C := ⟨by omega, by omega⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [ex, List.head?_map, hh, Option.map_some]
    rw [back2_dd F hF aB.1 aB.2]
  · exact chain_map (fun z => z.1 ≤ 7 ∧ z.2 ≤ 7) (fun u v h hu hv => back2_adj F hF h ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩) _ hsm hc
  · intro z hz
    obtain ⟨z0, hz0, rfl⟩ := List.mem_map.mp hz
    have := hsm z0 hz0
    obtain ⟨z1, z2⟩ := z0
    simp only at this
    cases fr <;> cases fc <;> simp [F, Frame.back] <;> omega
  · intro z hz
    obtain ⟨z0, hz0, rfl⟩ := List.mem_map.mp hz
    have hs := hsafe z0 hz0
    have hzs := hsm z0 hz0
    unfold safeB at hs
    simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true] at hs
    rcases hs with ((h | ⟨y, hy, h⟩) | h) | ⟨u, hu, h | ⟨v, hv, h⟩⟩
    · left; rw [h, back2_dd F hF aB.1 aB.2]
    · right; left
      have hay := adj_of_nbrList hy
      have yB : y.1 < R ∧ y.2 < C := by
        obtain ⟨y1, y2⟩ := y; obtain ⟨a1', a2'⟩ := a
        unfold Adjacent at hay; simp only at hay a1 a2 ⊢; omega
      exact ⟨F.back R C y, back_adj' F hF hay aB yB, by rw [h, back2_dm F hF aB yB]⟩
    · right; right; left
      exact back2_odd F hF (by simpa using h.1) (by simpa using h.2) ⟨by omega, by omega⟩
    · right; right; right; right
      obtain ⟨u1, u2⟩ := hSs u hu
      exact ⟨F.back R C u, ⟨u, hu, rfl⟩, by rw [h, back2_dd F hF (by omega) (by omega)]⟩
    · right; right; right; left
      have huv := adj_of_nbrList hv
      obtain ⟨u1, u2⟩ := hSs u hu
      have vB : v.1 < R ∧ v.2 < C := by
        obtain ⟨v1, v2⟩ := v; obtain ⟨uu1, uu2⟩ := u
        unfold Adjacent at huv; simp only at huv u1 u2 ⊢; omega
      have uB : u.1 < R ∧ u.2 < C := ⟨by omega, by omega⟩
      exact ⟨F.back R C u, ⟨u, hu, rfl⟩, F.back R C v, back_adj' F hF huv uB vB, by rw [h, back2_dm F hF uB vB]⟩
  · simp only [ex, exitEnd]
    have := Planar.getLastD_map (Frame.back (2 * R - 1) (2 * C - 1) F) (exitTab S a) (dd a)
    rw [back2_dd F hF aB.1 aB.2] at this
    exact this

/-! ### Order: rotation, positions and keys -/

def rotK (m n k : ℕ) : ℕ := if k < m then k + (n - m) else k - m

set_option maxHeartbeats 4000000 in
theorem crosses_rot {m n k0 k1 k2 k3 : ℕ} (hm : m ≤ n) (h0 : k0 < n) (h1 : k1 < n) (h2 : k2 < n)
    (h3 : k3 < n) (_h01 : k0 ≠ k1) (h02 : k0 ≠ k2) (h03 : k0 ≠ k3) (h12 : k1 ≠ k2) (h13 : k1 ≠ k3)
    (h23 : k2 ≠ k3) :
    Crosses (rotK m n k0) (rotK m n k1) (rotK m n k2) (rotK m n k3) ↔ Crosses k0 k1 k2 k3 := by
  unfold Crosses rotK
  split_ifs <;> omega

theorem idxOf_rotate {L X Y : List Coord} (hL : L = X ++ Y) (hn : L.Nodup) {x : Coord} (hx : x ∈ L) :
    (Y ++ X).idxOf x = rotK X.length L.length (L.idxOf x) := by
  subst hL
  unfold rotK
  rw [List.length_append]
  by_cases hX : x ∈ X
  · have hY : x ∉ Y := fun hy => (List.nodup_append.mp hn).2.2 x hX x hy rfl
    rw [idxOf_append_mem _ hX, idxOf_append_not_mem _ hY]
    have := List.idxOf_lt_length_iff.mpr hX
    rw [ite_eq_left this]; omega
  · rw [idxOf_append_not_mem _ hX]
    have hY : x ∈ Y := by
      rcases List.mem_append.mp hx with h | h
      · exact absurd h hX
      · exact h
    rw [idxOf_append_mem _ hY]
    rw [ite_eq_right (by omega)]; omega

theorem idx_lt_of_pairwise {L : List Coord} {κ : Coord → ℕ} (h : L.Pairwise (fun a b => κ a < κ b))
    {x y : Coord} (hx : x ∈ L) (hy : y ∈ L) : L.idxOf x < L.idxOf y ↔ κ x < κ y := by
  induction L with
  | nil => simp at hx
  | cons a L ih =>
    rw [List.pairwise_cons] at h
    by_cases hax : a = x <;> by_cases hay : a = y
    · subst hax; subst hay; simp
    · subst hax
      have hy' : y ∈ L := by rcases List.mem_cons.mp hy with e | e; exact absurd e.symm hay; exact e
      simp only [List.idxOf_cons_self, List.idxOf_cons_ne _ hay]
      constructor
      · intro _; exact h.1 y hy'
      · intro _; omega
    · subst hay
      have hx' : x ∈ L := by rcases List.mem_cons.mp hx with e | e; exact absurd e.symm hax; exact e
      simp only [List.idxOf_cons_self, List.idxOf_cons_ne _ hax]
      have := h.1 x hx'
      constructor
      · intro h'; omega
      · intro h'; omega
    · have hx' : x ∈ L := by rcases List.mem_cons.mp hx with e | e; exact absurd e.symm hax; exact e
      have hy' : y ∈ L := by rcases List.mem_cons.mp hy with e | e; exact absurd e.symm hay; exact e
      simp only [List.idxOf_cons_ne _ hax, List.idxOf_cons_ne _ hay]
      rw [← ih h.2 hx' hy']
      omega

/-! ### The walk with its exits -/

def stP (R C : ℕ) (fr fc : Bool) (S : List Coord) : List (Coord × List Coord) :=
  (stairOfS S).map fun a => (Frame.back R C ⟨fr, fc, false⟩ a,
    (exitTab S a).map (Frame.back (2 * R - 1) (2 * C - 1) ⟨fr, fc, false⟩))

def sdP (L : List Coord) : List (Coord × List Coord) := L.map fun x => (x, [dd x])

def walkP (R C : ℕ) (S1 S2 S3 S4 : List Coord) : List (Coord × List Coord) :=
  let lTL := lamS S1 0
  let lTR := lamS S2 0
  let lBR := lamS S3 0
  let lBL := lamS S4 0
  let kTL := kS S1
  let kTR := kS S2
  let kBR := kS S3
  let kBL := kS S4
  stP R C false false S1 ++
    sdP (((List.range C).filter fun y => decide (lTL < y ∧ y + 1 + lTR < C)).map (fun y => (0, y))) ++
    (stP R C false true S2).reverse ++
    sdP (((List.range R).filter fun x => decide (kTR < x ∧ x + 1 + kBR < R)).map (fun x => (x, C - 1))) ++
    stP R C true true S3 ++
    sdP ((((List.range C).filter fun y => decide (lBL < y ∧ y + 1 + lBR < C)).map
      (fun y => (R - 1, y))).reverse) ++
    (stP R C true false S4).reverse ++
    sdP ((((List.range R).filter fun x => decide (kTL < x ∧ x + 1 + kBL < R)).map (fun x => (x, 0))).reverse)

theorem kOf_shape {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) {rem : List (ℕ × ℕ)}
    (hin : ∀ x ∈ rem, ∃ fr fc, Win R C fr fc x) {fr fc : Bool} {S : List (ℕ × ℕ)}
    (hS : CornerShape R C rem fr fc S) : kOf R C ⟨fr, fc, false⟩ rem = kS S := by
  unfold kOf kS; congr 1; apply List.filter_congr; intro i hi
  simp only [List.mem_range] at hi; rw [(notchLen_shape hR hC hin hS (by omega)).1]

theorem walkP_fst {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) {rem : List (ℕ × ℕ)} (h : RemShape R C rem)
    {S1 S2 S3 S4 : List Coord} (h1 : CornerShape R C rem false false S1) (h2 : CornerShape R C rem false true S2)
    (h3 : CornerShape R C rem true true S3) (h4 : CornerShape R C rem true false S4) :
    (walkP R C S1 S2 S3 S4).map Prod.fst = walk3 R C rem := by
  obtain ⟨hin, -⟩ := h
  rw [walk3_eq]
  unfold frameTL frameTR frameBR frameBL
  rw [corner_I hR hC hin h1, corner_I hR hC hin h2, corner_I hR hC hin h3, corner_I hR hC hin h4,
    (notchLen_shape hR hC hin h1 (by omega)).1, (notchLen_shape hR hC hin h2 (by omega)).1,
    (notchLen_shape hR hC hin h3 (by omega)).1, (notchLen_shape hR hC hin h4 (by omega)).1,
    kOf_shape hR hC hin h1, kOf_shape hR hC hin h2, kOf_shape hR hC hin h3, kOf_shape hR hC hin h4]
  unfold walkP walk3Core stP sdP stairOfS
  simp only [List.map_append, List.map_reverse, List.map_map]
  rfl

/-- What every exit along the walk satisfies. -/
def ExitOK (R C : ℕ) (rem : List Coord) (x : Coord) (ex : List Coord) : Prop :=
  ex.head? = some (dd x) ∧ chainAdjacent ex = true ∧ (∀ z ∈ ex, z.1 < 2 * R - 1 ∧ z.2 < 2 * C - 1) ∧
    (∀ z ∈ ex, SafeFor (· ∈ rem) x z) ∧ OnPerim (2 * R - 1) (2 * C - 1) (ex.getLastD (dd x)) ∧
    (ex.getLastD (dd x)).1 < 2 * R - 1 ∧ (ex.getLastD (dd x)).2 < 2 * C - 1

theorem stP_ok {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) {rem : List Coord} {fr fc : Bool} {S : List Coord}
    (hS : CornerShape R C rem fr fc S) {x : Coord} {ex : List Coord} (hm : (x, ex) ∈ stP R C fr fc S) :
    ExitOK R C rem x ex := by
  obtain ⟨a, ha, he⟩ := List.mem_map.mp hm
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨hh, hc, hb, hsafe, hlast⟩ := stair_exit hR hC fr fc hS.1 ha
  obtain ⟨-, -, ⟨e, he, hee⟩, -, hsm⟩ := exit_facts S hS.1 a ha
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hsm
  have hle := hsm e (List.mem_of_getLast? he)
  have hend : exitEnd S a = e := by
    unfold exitEnd
    rw [List.getLastD_eq_getLast?, he]; rfl
  obtain ⟨hp, hb1, hb2, -⟩ := anc_corner hR hC fr fc hee hle.1 hle.2
  refine ⟨hh, hc, hb, fun z hz => ?_, ?_, ?_, ?_⟩
  · rcases hsafe z hz with h | h | h | ⟨u, ⟨b, hb', rfl⟩, h⟩ | ⟨u, ⟨b, hb', rfl⟩, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · have := (stair_small S hS.1 a ha).2.2 b hb'
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, (hS.2 _ (back_win (by omega) (by omega) _ this.1 this.2)).mpr
        ⟨b, hb', rfl⟩, h⟩)))
    · have := (stair_small S hS.1 a ha).2.2 b hb'
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, (hS.2 _ (back_win (by omega) (by omega) _ this.1 this.2)).mpr
        ⟨b, hb', rfl⟩, h⟩)))
  · rw [hlast, hend]; exact hp
  · rw [hlast, hend]; exact hb1
  · rw [hlast, hend]; exact hb2

theorem sdP_ok {R C : ℕ} {rem : List Coord} {x : Coord} (hx1 : x.1 < R) (hx2 : x.2 < C)
    (hp : x.1 = 0 ∨ x.1 = R - 1 ∨ x.2 = 0 ∨ x.2 = C - 1) : ExitOK R C rem x [dd x] := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz; simp at hz; subst hz; unfold dd; omega
  · intro z hz; simp at hz; exact Or.inl hz
  · simp only [List.getLastD_cons, List.getLastD_nil]; unfold OnPerim dd; omega
  · simp only [List.getLastD_cons, List.getLastD_nil]; unfold dd; omega
  · simp only [List.getLastD_cons, List.getLastD_nil]; unfold dd; omega

theorem walkP_ok {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) {rem : List (ℕ × ℕ)}
    {S1 S2 S3 S4 : List Coord} (h1 : CornerShape R C rem false false S1) (h2 : CornerShape R C rem false true S2)
    (h3 : CornerShape R C rem true true S3) (h4 : CornerShape R C rem true false S4)
    {x : Coord} {ex : List Coord} (hm : (x, ex) ∈ walkP R C S1 S2 S3 S4) : ExitOK R C rem x ex := by
  unfold walkP at hm
  simp only [List.mem_append, List.mem_reverse] at hm
  rcases hm with ((((((h | h) | h) | h) | h) | h) | h) | h
  · exact stP_ok hR hC h1 h
  · obtain ⟨y, hy, he⟩ := List.mem_map.mp h
    obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hy'
    exact sdP_ok (by simp; omega) (by simp; omega) (by simp)
  · exact stP_ok hR hC h2 h
  · obtain ⟨y, hy, he⟩ := List.mem_map.mp h
    obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hy'
    exact sdP_ok (by simp; omega) (by simp; omega) (by simp)
  · exact stP_ok hR hC h3 h
  · obtain ⟨y, hy, he⟩ := List.mem_map.mp h
    rw [List.mem_reverse] at hy
    obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hy'
    exact sdP_ok (by simp; omega) (by simp; omega) (by simp)
  · exact stP_ok hR hC h4 h
  · obtain ⟨y, hy, he⟩ := List.mem_map.mp h
    rw [List.mem_reverse] at hy
    obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hy'
    exact sdP_ok (by simp; omega) (by simp; omega) (by simp)

/-! ### Sorting the exit ends along the walk -/

theorem stair_ends : ∀ S ∈ shapes, (stairOfS S).head? = some (kS S, 0) ∧
    (stairOfS S).getLast? = some (0, lamS S 0) ∧ kS S ≤ 4 ∧ lamS S 0 ≤ 4 ∧
    (∀ a ∈ stairOfS S, 8 - 2 * kS S ≤ fkey (exitEnd S a) ∧ fkey (exitEnd S a) ≤ 8 + 2 * lamS S 0 ∧
      ((exitEnd S a).1 = 0 ∨ (exitEnd S a).2 = 0) ∧ (exitEnd S a).1 ≤ 7 ∧ (exitEnd S a).2 ≤ 7) ∧
    fkey (exitEnd S (kS S, 0)) = 8 - 2 * kS S ∧ fkey (exitEnd S (0, lamS S 0)) = 8 + 2 * lamS S 0 := by
  decide

/-- The anchor of an exit end at corner `(fr, fc)`, as a function of the corner key. -/
def cf (R C : ℕ) (fr fc : Bool) (f : ℕ) : ℕ :=
  let R2 := 2 * R - 1
  let C2 := 2 * C - 1
  match fr, fc with
  | false, false => if f < 8 then 2 * C2 + 2 * R2 + 3 - 8 + f else f - 7
  | false, true => if f < 8 then C2 + 10 - f else C2 + 8 - f
  | true, true => if f ≤ 8 then C2 + R2 - 7 + f else C2 + R2 - 5 + f
  | true, false => if f < 8 then 2 * C2 + R2 + 12 - f else 2 * C2 + R2 + 10 - f

def κ (R C : ℕ) (pr : Coord × List Coord) : ℕ :=
  Planar.anc (2 * R - 1) (2 * C - 1) (pr.2.getLastD (dd pr.1))

theorem stP_key {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) {fr fc : Bool} {S : List Coord} (hS : S ∈ shapes)
    {a : Coord} (ha : a ∈ stairOfS S) :
    κ R C (Frame.back R C ⟨fr, fc, false⟩ a,
      (exitTab S a).map (Frame.back (2 * R - 1) (2 * C - 1) ⟨fr, fc, false⟩)) = cf R C fr fc (fkey (exitEnd S a)) := by
  obtain ⟨-, -, -, -, hall, -, -⟩ := stair_ends S hS
  obtain ⟨-, -, he, h1, h2⟩ := hall a ha
  obtain ⟨-, -, -, -, hlast⟩ := stair_exit hR hC fr fc hS ha
  unfold κ
  simp only
  rw [hlast, (anc_corner hR hC fr fc he h1 h2).2.2.2]
  unfold cf
  cases fr <;> cases fc <;> rfl

/-- A sorted segment with its key range. -/
def Seg (R C : ℕ) (lo hi : ℕ) (L : List (Coord × List Coord)) : Prop :=
  L.Pairwise (fun a b => κ R C a < κ R C b) ∧ ∀ e ∈ L, lo ≤ κ R C e ∧ κ R C e ≤ hi

theorem stairs_sorted (S : List Coord) (hS : S ∈ shapes) :
    (stairOfS S).Pairwise (fun a b => fkey (exitEnd S a) < fkey (exitEnd S b)) := (exit_order S hS).1

/-- A staircase whose key grows with the corner key. -/
theorem seg_stair_up {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) {fr fc : Bool} {S : List Coord} (hS : S ∈ shapes)
    {L : List Coord} (hL : List.Sublist L (stairOfS S)) {lo hi flo fhi : ℕ}
    (hmono : ∀ f g, flo ≤ f → g ≤ fhi → f < g → cf R C fr fc f < cf R C fr fc g)
    (hb : ∀ f, flo ≤ f → f ≤ fhi → lo ≤ cf R C fr fc f ∧ cf R C fr fc f ≤ hi)
    (hf : ∀ a ∈ L, flo ≤ fkey (exitEnd S a) ∧ fkey (exitEnd S a) ≤ fhi) :
    Seg R C lo hi (L.map fun a => (Frame.back R C ⟨fr, fc, false⟩ a,
      (exitTab S a).map (Frame.back (2 * R - 1) (2 * C - 1) ⟨fr, fc, false⟩))) := by
  refine ⟨?_, ?_⟩
  · rw [List.pairwise_map]
    refine ((stairs_sorted S hS).sublist hL).imp_of_mem (fun {a b} ha hb' h => ?_)
    rw [stP_key hR hC hS (hL.subset ha), stP_key hR hC hS (hL.subset hb')]
    exact hmono _ _ (hf a ha).1 (hf b hb').2 h
  · intro e he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    rw [stP_key hR hC hS (hL.subset ha)]
    exact hb _ (hf a ha).1 (hf a ha).2

/-- A staircase whose key falls as the corner key grows, read backwards. -/
theorem seg_stair_down {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) {fr fc : Bool} {S : List Coord} (hS : S ∈ shapes)
    {lo hi flo fhi : ℕ}
    (hmono : ∀ f g, flo ≤ f → g ≤ fhi → f < g → cf R C fr fc g < cf R C fr fc f)
    (hb : ∀ f, flo ≤ f → f ≤ fhi → lo ≤ cf R C fr fc f ∧ cf R C fr fc f ≤ hi)
    (hf : ∀ a ∈ stairOfS S, flo ≤ fkey (exitEnd S a) ∧ fkey (exitEnd S a) ≤ fhi) :
    Seg R C lo hi (stP R C fr fc S).reverse := by
  refine ⟨?_, ?_⟩
  · rw [List.pairwise_reverse]
    unfold stP
    rw [List.pairwise_map]
    refine (stairs_sorted S hS).imp_of_mem (fun {a b} ha hb' h => ?_)
    rw [stP_key hR hC hS ha, stP_key hR hC hS hb']
    exact hmono _ _ (hf a ha).1 (hf b hb').2 h
  · intro e he
    rw [List.mem_reverse] at he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    rw [stP_key hR hC hS ha]
    exact hb _ (hf a ha).1 (hf a ha).2

/-- A side of the walk: exits of one point, keys an affine function of the position. -/
theorem seg_side {R C : ℕ} {L : List ℕ} (hL : L.Pairwise (· < ·)) (cell : ℕ → Coord) (key : ℕ → ℕ)
    (hk : ∀ y ∈ L, κ R C (cell y, [dd (cell y)]) = key y) (hmono : ∀ y ∈ L, ∀ z ∈ L, y < z → key y < key z)
    {lo hi : ℕ} (hb : ∀ y ∈ L, lo ≤ key y ∧ key y ≤ hi) :
    Seg R C lo hi (sdP (L.map cell)) := by
  refine ⟨?_, ?_⟩
  · unfold sdP
    rw [List.map_map, List.pairwise_map]
    refine hL.imp_of_mem (fun {a b} ha hb' h => ?_)
    simp only [Function.comp]
    rw [hk a ha, hk b hb']
    exact hmono a ha b hb' h
  · intro e he
    unfold sdP at he
    rw [List.map_map] at he
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp he
    simp only [Function.comp]
    rw [hk y hy]
    exact hb y hy

theorem seg_side_rev {R C : ℕ} {L : List ℕ} (hL : L.Pairwise (· < ·)) (cell : ℕ → Coord) (key : ℕ → ℕ)
    (hk : ∀ y ∈ L, κ R C (cell y, [dd (cell y)]) = key y) (hmono : ∀ y ∈ L, ∀ z ∈ L, y < z → key z < key y)
    {lo hi : ℕ} (hb : ∀ y ∈ L, lo ≤ key y ∧ key y ≤ hi) :
    Seg R C lo hi (sdP (L.map cell).reverse) := by
  refine ⟨?_, ?_⟩
  · unfold sdP
    rw [List.map_reverse, List.pairwise_reverse, List.map_map, List.pairwise_map]
    refine hL.imp_of_mem (fun {a b} ha hb' h => ?_)
    simp only [Function.comp]
    rw [hk a ha, hk b hb']
    exact hmono a ha b hb' h
  · intro e he
    unfold sdP at he
    rw [List.map_reverse, List.mem_reverse, List.map_map] at he
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp he
    simp only [Function.comp]
    rw [hk y hy]
    exact hb y hy

theorem seg_cons {R C lo hi lo' : ℕ} {A B : List (Coord × List Coord)} (hA : Seg R C lo hi A)
    (hB : B.Pairwise (fun a b => κ R C a < κ R C b) ∧ ∀ b ∈ B, lo' ≤ κ R C b) (h1 : hi < lo') (h2 : lo ≤ lo') :
    (A ++ B).Pairwise (fun a b => κ R C a < κ R C b) ∧ ∀ e ∈ A ++ B, lo ≤ κ R C e := by
  refine ⟨List.pairwise_append.mpr ⟨hA.1, hB.1, fun a ha b hb => ?_⟩, fun e he => ?_⟩
  · have := (hA.2 a ha).2; have := hB.2 b hb; omega
  · rcases List.mem_append.mp he with h | h
    · exact (hA.2 e h).1
    · have := hB.2 e h; omega

theorem dropWhile_ge {L : List Coord} {g : Coord → ℕ} (hs : L.Pairwise (fun a b => g a < g b)) :
    ∀ a ∈ L.dropWhile (fun a => decide (g a < 8)), 8 ≤ g a := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.pairwise_cons] at hs
    intro a ha
    simp only [List.dropWhile_cons] at ha
    split_ifs at ha with h
    · exact ih hs.2 a ha
    · simp only [decide_eq_true_eq] at h
      rcases List.mem_cons.mp ha with rfl | ha'
      · omega
      · have := hs.1 a ha'; omega

theorem anc_side {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) (a b : ℕ) (ha : a < R) (hb : b < C) :
    κ R C ((a, b), [dd (a, b)]) =
      if a = 0 then 2 * b + 1
      else if b = C - 1 then (2 * C - 1) + 2 + 2 * a
      else if a = R - 1 then 2 * (2 * C - 1) + (2 * R - 1) + 2 - 2 * b
      else 2 * (2 * C - 1) + 2 * (2 * R - 1) + 3 - 2 * a := by
  unfold κ Planar.anc dd
  simp only [List.getLastD_cons, List.getLastD_nil]
  split_ifs <;> omega

/-- **The exit ends, along the walk rotated past the left part of the top-left staircase, are in
perimeter order.** -/
theorem walkP_sorted {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) {S1 S2 S3 S4 : List Coord} (h1 : S1 ∈ shapes)
    (h2 : S2 ∈ shapes) (h3 : S3 ∈ shapes) (h4 : S4 ∈ shapes) :
    ∃ X Y, walkP R C S1 S2 S3 S4 = X ++ Y ∧ (Y ++ X).Pairwise (fun a b => κ R C a < κ R C b) := by
  obtain ⟨-, -, k1, l1, hf1, -, -⟩ := stair_ends S1 h1
  obtain ⟨-, -, k2, l2, hf2, -, -⟩ := stair_ends S2 h2
  obtain ⟨-, -, k3, l3, hf3, -, -⟩ := stair_ends S3 h3
  obtain ⟨-, -, k4, l4, hf4, -, -⟩ := stair_ends S4 h4
  have hall1 := hf1
  have hsplit : stP R C false false S1 =
      ((stairOfS S1).takeWhile (fun a => decide (fkey (exitEnd S1 a) < 8))).map (fun a =>
        (Frame.back R C ⟨false, false, false⟩ a,
          (exitTab S1 a).map (Frame.back (2 * R - 1) (2 * C - 1) ⟨false, false, false⟩))) ++
      ((stairOfS S1).dropWhile (fun a => decide (fkey (exitEnd S1 a) < 8))).map (fun a =>
        (Frame.back R C ⟨false, false, false⟩ a,
          (exitTab S1 a).map (Frame.back (2 * R - 1) (2 * C - 1) ⟨false, false, false⟩))) := by
    unfold stP; rw [← List.map_append, List.takeWhile_append_dropWhile]
  obtain ⟨-, -, hk1, hl1, -, -, -⟩ := stair_ends S1 h1
  obtain ⟨-, -, hk2, hl2, -, -, -⟩ := stair_ends S2 h2
  obtain ⟨-, -, hk3, hl3, -, -, -⟩ := stair_ends S3 h3
  obtain ⟨-, -, hk4, hl4, -, -, -⟩ := stair_ends S4 h4
  -- The nine segments, in order along the rotated walk.
  --
  have s1 : Seg R C 1 (1 + 2 * lamS S1 0)
      (((stairOfS S1).dropWhile (fun a => decide (fkey (exitEnd S1 a) < 8))).map (fun a =>
        (Frame.back R C ⟨false, false, false⟩ a,
          (exitTab S1 a).map (Frame.back (2 * R - 1) (2 * C - 1) ⟨false, false, false⟩)))) :=
    seg_stair_up hR hC h1 (List.dropWhile_suffix _).sublist (flo := 8) (fhi := 8 + 2 * lamS S1 0)
      (by intro f g _ _ _; simp only [cf]; split_ifs <;> omega)
      (by intro f _ _; simp only [cf]; split_ifs <;> omega)
      (fun a ha => ⟨dropWhile_ge (g := fun a => fkey (exitEnd S1 a)) (stairs_sorted S1 h1) a ha,
        (hall1 a ((List.dropWhile_suffix _).sublist.subset ha)).2.1⟩)
  have s9 : Seg R C (2 * (2 * C - 1) + 2 * (2 * R - 1) + 3 - 2 * kS S1) (2 * (2 * C - 1) + 2 * (2 * R - 1) + 2)
      (((stairOfS S1).takeWhile (fun a => decide (fkey (exitEnd S1 a) < 8))).map (fun a =>
        (Frame.back R C ⟨false, false, false⟩ a,
          (exitTab S1 a).map (Frame.back (2 * R - 1) (2 * C - 1) ⟨false, false, false⟩)))) :=
    seg_stair_up hR hC h1 (List.takeWhile_prefix _).sublist (flo := 8 - 2 * kS S1) (fhi := 7)
      (by intro f g _ _ _; simp only [cf]; split_ifs <;> omega)
      (by intro f _ _; simp only [cf]; split_ifs <;> omega)
      (fun a ha => ⟨(hall1 a ((List.takeWhile_prefix _).sublist.subset ha)).1,
        by have := List.mem_takeWhile_imp ha; simp only [decide_eq_true_eq] at this; omega⟩)
  have s3 : Seg R C (2 * C - 1 - 2 * lamS S2 0) (2 * C - 1 + 2 + 2 * kS S2) (stP R C false true S2).reverse :=
    seg_stair_down hR hC h2 (flo := 8 - 2 * kS S2) (fhi := 8 + 2 * lamS S2 0)
      (by intro f g _ _ _; simp only [cf]; split_ifs <;> omega)
      (by intro f _ _; simp only [cf]; split_ifs <;> omega)
      (fun a ha => ⟨(hf2 a ha).1, (hf2 a ha).2.1⟩)
  have s5 : Seg R C (2 * C - 1 + (2 * R - 1) + 1 - 2 * kS S3) (2 * C - 1 + (2 * R - 1) + 3 + 2 * lamS S3 0)
      (stP R C true true S3) :=
    seg_stair_up hR hC h3 (List.Sublist.refl _) (flo := 8 - 2 * kS S3) (fhi := 8 + 2 * lamS S3 0)
      (by intro f g _ _ _; simp only [cf]; split_ifs <;> omega)
      (by intro f _ _; simp only [cf]; split_ifs <;> omega)
      (fun a ha => ⟨(hf3 a ha).1, (hf3 a ha).2.1⟩)
  have s7 : Seg R C (2 * (2 * C - 1) + (2 * R - 1) + 2 - 2 * lamS S4 0) (2 * (2 * C - 1) + (2 * R - 1) + 4 + 2 * kS S4)
      (stP R C true false S4).reverse :=
    seg_stair_down hR hC h4 (flo := 8 - 2 * kS S4) (fhi := 8 + 2 * lamS S4 0)
      (by intro f g _ _ _; simp only [cf]; split_ifs <;> omega)
      (by intro f _ _; simp only [cf]; split_ifs <;> omega)
      (fun a ha => ⟨(hf4 a ha).1, (hf4 a ha).2.1⟩)
  have s2 : Seg R C (2 * lamS S1 0 + 3) (2 * C - 3 - 2 * lamS S2 0)
      (sdP (((List.range C).filter fun y => decide (lamS S1 0 < y ∧ y + 1 + lamS S2 0 < C)).map
        (fun y => (0, y)))) := by
    apply seg_side (List.pairwise_lt_range.filter _) (fun y => (0, y)) (fun y => 2 * y + 1)
    · intro y hy
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hy
      rw [anc_side hR hC 0 (y) (by omega) (by omega)]
      split_ifs <;> omega
    · intro y _ z _ h; omega
    · intro y hy
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hy
      omega
  have s4 : Seg R C (2 * C - 1 + 4 + 2 * kS S2) (2 * C - 1 + 2 + 2 * (R - 2 - kS S3))
      (sdP (((List.range R).filter fun x => decide (kS S2 < x ∧ x + 1 + kS S3 < R)).map
        (fun x => (x, C - 1)))) := by
    apply seg_side (List.pairwise_lt_range.filter _) (fun x => (x, C - 1)) (fun x => 2 * C - 1 + 2 + 2 * x)
    · intro x hx
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
      rw [anc_side hR hC x (C - 1) (by omega) (by omega)]
      split_ifs <;> omega
    · intro y _ z _ h; omega
    · intro x hx
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
      omega
  have s6 : Seg R C (2 * C - 1 + (2 * R - 1) + 5 + 2 * lamS S3 0) (2 * (2 * C - 1) + (2 * R - 1) - 2 * lamS S4 0)
      (sdP ((((List.range C).filter fun y => decide (lamS S4 0 < y ∧ y + 1 + lamS S3 0 < C)).map
        (fun y => (R - 1, y))).reverse)) := by
    apply seg_side_rev (List.pairwise_lt_range.filter _) (fun y => (R - 1, y))
      (fun y => 2 * (2 * C - 1) + (2 * R - 1) + 2 - 2 * y)
    · intro y hy
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hy
      rw [anc_side hR hC (R - 1) y (by omega) (by omega)]
      split_ifs <;> omega
    · intro y hy z hz h
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hy hz
      omega
    · intro y hy
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hy
      omega
  have s8 : Seg R C (2 * (2 * C - 1) + (2 * R - 1) + 6 + 2 * kS S4) (2 * (2 * C - 1) + 2 * (2 * R - 1) + 1 - 2 * kS S1)
      (sdP ((((List.range R).filter fun x => decide (kS S1 < x ∧ x + 1 + kS S4 < R)).map
        (fun x => (x, 0))).reverse)) := by
    apply seg_side_rev (List.pairwise_lt_range.filter _) (fun x => (x, 0))
      (fun x => 2 * (2 * C - 1) + 2 * (2 * R - 1) + 3 - 2 * x)
    · intro x hx
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
      rw [anc_side hR hC x (0) (by omega) (by omega)]
      split_ifs <;> omega
    · intro y hy z hz h
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hy hz
      omega
    · intro x hx
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
      omega
  have t9 := And.intro s9.1 (fun e he => (s9.2 e he).1)
  have t8 := seg_cons s8 t9 (by omega) (by omega)
  have t7 := seg_cons s7 t8 (by omega) (by omega)
  have t6 := seg_cons s6 t7 (by omega) (by omega)
  have t5 := seg_cons s5 t6 (by omega) (by omega)
  have t4 := seg_cons s4 t5 (by omega) (by omega)
  have t3 := seg_cons s3 t4 (by omega) (by omega)
  have t2 := seg_cons s2 t3 (by omega) (by omega)
  have t1 := seg_cons s1 t2 (by omega) (by omega)
  unfold walkP
  simp only [hsplit, List.append_assoc]
  refine ⟨_, _, rfl, ?_⟩
  simp only [List.append_assoc]
  exact t1.1

/-! ### Separation of doubled points -/

theorem dd_inj {x y : Coord} (h : dd x = dd y) : x = y := by
  obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y
  unfold dd at h; simp only [Prod.mk.injEq] at h ⊢; omega

/-- The midpoint of a unit edge has exactly one odd coordinate. -/
theorem dm_par {x y : Coord} (h : Adjacent x y) : (dm x y).1 % 2 + (dm x y).2 % 2 = 1 := by
  obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y
  unfold Adjacent at h; unfold dm; simp only at h ⊢; omega

/-- The midpoint of a unit edge determines the edge. -/
theorem dm_inj {x y v w : Coord} (hxy : Adjacent x y) (hvw : Adjacent v w) (h : dm x y = dm v w) :
    (x = v ∧ y = w) ∨ (x = w ∧ y = v) := by
  obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y; obtain ⟨v1, v2⟩ := v; obtain ⟨w1, w2⟩ := w
  unfold Adjacent at hxy hvw; unfold dm at h
  simp only [Prod.mk.injEq] at hxy hvw h ⊢
  omega

theorem dd_ne_dm {x u v : Coord} (h : Adjacent u v) : dd x ≠ dm u v := by
  intro e
  have := dm_par h
  rw [← e] at this
  unfold dd at this; simp only at this; omega

/-- **An exit point is not on the doubled path of a path avoiding the end cell and the settled
cells.** -/
theorem safe_not_dpN {K : Coord → Prop} {L : List Coord} (hc : chainAdjacent L = true) {x z : Coord}
    (hx : x ∉ L) (hK : ∀ v ∈ L, ¬ K v) (hs : SafeFor K x z) : z ∉ dpN L := by
  intro hz
  rcases mem_dpN hc hz with ⟨v, hv, rfl⟩ | ⟨v, hv, w, hw, hvw, rfl⟩
  · rcases hs with h | ⟨y, hy, h⟩ | h | ⟨u, hu, u', hu', h⟩ | ⟨u, hu, h⟩
    · exact hx (dd_inj h ▸ hv)
    · exact dd_ne_dm hy h
    · unfold dd at h; simp only at h; omega
    · exact dd_ne_dm hu' h
    · exact hK v hv (dd_inj h ▸ hu)
  · rcases hs with h | ⟨y, hy, h⟩ | h | ⟨u, hu, u', hu', h⟩ | ⟨u, hu, h⟩
    · exact dd_ne_dm hvw h.symm
    · rcases dm_inj hvw hy h with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact hx hv
      · exact hx hw
    · have := dm_par hvw; omega
    · rcases dm_inj hvw hu' h with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact hK _ hv hu
      · exact hK _ hw hu
    · exact dd_ne_dm hvw h.symm

/-- **Doubled paths of disjoint paths are disjoint.** -/
theorem dpN_disj {L M : List Coord} (hL : chainAdjacent L = true) (hM : chainAdjacent M = true)
    (hd : ∀ v ∈ L, v ∉ M) {z : Coord} (hz : z ∈ dpN L) : z ∉ dpN M := by
  intro hz'
  rcases mem_dpN hL hz with ⟨v, hv, rfl⟩ | ⟨v, hv, w, hw, hvw, rfl⟩ <;>
    rcases mem_dpN hM hz' with ⟨v', hv', h⟩ | ⟨v', hv', w', hw', hvw', h⟩
  · exact hd v hv (dd_inj h ▸ hv')
  · exact dd_ne_dm hvw' h
  · exact dd_ne_dm hvw h.symm
  · rcases dm_inj hvw hvw' h with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hd _ hv hv'
    · exact hd _ hv hw'

/-! ### Exits of distinct walk cells are disjoint -/

def Sf (S1 S2 S3 S4 : List Coord) : Bool → Bool → List Coord
  | false, false => S1
  | false, true => S2
  | true, true => S3
  | true, false => S4

/-- A walk entry is a side cell with the trivial exit, or a staircase cell of some corner. -/
theorem walkP_cases {R C : ℕ} {S1 S2 S3 S4 : List Coord} {e : Coord × List Coord}
    (he : e ∈ walkP R C S1 S2 S3 S4) :
    e.2 = [dd e.1] ∨ ∃ fr fc a, a ∈ stairOfS (Sf S1 S2 S3 S4 fr fc) ∧
      e = (Frame.back R C ⟨fr, fc, false⟩ a,
        (exitTab (Sf S1 S2 S3 S4 fr fc) a).map (Frame.back (2 * R - 1) (2 * C - 1) ⟨fr, fc, false⟩)) := by
  have side : ∀ L : List Coord, e ∈ sdP L → e.2 = [dd e.1] := by
    intro L h; unfold sdP at h; obtain ⟨x, -, rfl⟩ := List.mem_map.mp h; rfl
  unfold walkP at he
  simp only [List.mem_append, List.mem_reverse] at he
  rcases he with ((((((h | h) | h) | h) | h) | h) | h) | h
  · unfold stP at h; obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h; exact Or.inr ⟨false, false, a, ha, rfl⟩
  · exact Or.inl (side _ h)
  · unfold stP at h; obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h; exact Or.inr ⟨false, true, a, ha, rfl⟩
  · exact Or.inl (side _ h)
  · unfold stP at h; obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h; exact Or.inr ⟨true, true, a, ha, rfl⟩
  · exact Or.inl (side _ h)
  · unfold stP at h; obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h; exact Or.inr ⟨true, false, a, ha, rfl⟩
  · exact Or.inl (side _ h)

/-- A safe point of `x` is not the doubled cell of another unsettled cell. -/
theorem safe_dd {K : Coord → Prop} {x y : Coord} (hs : SafeFor K x (dd y)) (hxy : x ≠ y) (hy : ¬ K y) :
    False := by
  rcases hs with h | ⟨v, hv, h⟩ | h | ⟨u, hu, v, hv, h⟩ | ⟨u, hu, h⟩
  · exact hxy (dd_inj h).symm
  · exact dd_ne_dm hv h
  · unfold dd at h; simp only at h; omega
  · exact dd_ne_dm hv h
  · exact hy (by rw [dd_inj h]; exact hu)

theorem exit_disj : ∀ S ∈ shapes, ∀ a ∈ stairOfS S, ∀ b ∈ stairOfS S, a ≠ b →
    (exitTab S a).all (fun z => !(exitTab S b).contains z) = true := by
  decide

theorem back2_inj {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) (fr fc : Bool) {z z' : Coord} (h1 : z.1 ≤ 7)
    (h2 : z.2 ≤ 7) (h1' : z'.1 ≤ 7) (h2' : z'.2 ≤ 7)
    (h : Frame.back (2 * R - 1) (2 * C - 1) ⟨fr, fc, false⟩ z = Frame.back (2 * R - 1) (2 * C - 1) ⟨fr, fc, false⟩ z') :
    z = z' := by
  obtain ⟨a, b⟩ := z; obtain ⟨c, d⟩ := z'
  simp only at h1 h2 h1' h2'
  cases fr <;> cases fc <;> simp [Frame.back] at h ⊢ <;> omega

theorem corner_far {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) {fr fc fr' fc' : Bool} (hne : ¬ (fr = fr' ∧ fc = fc'))
    {z z' : Coord} (h1 : z.1 ≤ 7) (h2 : z.2 ≤ 7) (h1' : z'.1 ≤ 7) (h2' : z'.2 ≤ 7) :
    Frame.back (2 * R - 1) (2 * C - 1) ⟨fr, fc, false⟩ z ≠ Frame.back (2 * R - 1) (2 * C - 1) ⟨fr', fc', false⟩ z' := by
  obtain ⟨a, b⟩ := z; obtain ⟨c, d⟩ := z'
  simp only at h1 h2 h1' h2'
  cases fr <;> cases fc <;> cases fr' <;> cases fc' <;> simp [Frame.back] at hne ⊢ <;> omega

/-- **The exits of two distinct unsettled walk cells are disjoint.** -/
theorem exits_disj {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) {rem : List Coord} {S1 S2 S3 S4 : List Coord}
    (h1 : CornerShape R C rem false false S1) (h2 : CornerShape R C rem false true S2)
    (h3 : CornerShape R C rem true true S3) (h4 : CornerShape R C rem true false S4)
    {e e' : Coord × List Coord} (he : e ∈ walkP R C S1 S2 S3 S4) (he' : e' ∈ walkP R C S1 S2 S3 S4)
    (hne : e.1 ≠ e'.1) (hr : e.1 ∉ rem) (hr' : e'.1 ∉ rem) : ∀ z ∈ e.2, z ∉ e'.2 := by
  have ok := walkP_ok hR hC h1 h2 h3 h4 he
  have ok' := walkP_ok hR hC h1 h2 h3 h4 he'
  intro z hz hz'
  rcases walkP_cases he' with hs' | ⟨fr', fc', b, hb, he2⟩
  · rw [hs', List.mem_singleton] at hz'
    subst hz'
    exact safe_dd (ok.2.2.2.1 _ hz) hne hr'
  rcases walkP_cases he with hs | ⟨fr, fc, a, ha, he1⟩
  · rw [hs, List.mem_singleton] at hz
    subst hz
    exact safe_dd (ok'.2.2.2.1 _ hz') (Ne.symm hne) hr
  subst he1; subst he2
  simp only at hz hz' hne
  obtain ⟨z0, hz0, rfl⟩ := List.mem_map.mp hz
  obtain ⟨z1, hz1, e01⟩ := List.mem_map.mp hz'
  have hSf : ∀ fr fc, Sf S1 S2 S3 S4 fr fc ∈ shapes := by
    intro fr fc; cases fr <;> cases fc
    exacts [h1.1, h2.1, h4.1, h3.1]
  have b0 := (exit_facts _ (hSf fr fc) a ha).2.2.2.2
  have b1 := (exit_facts _ (hSf fr' fc') b hb).2.2.2.2
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at b0 b1
  have c0 := b0 z0 hz0
  have c1 := b1 z1 hz1
  by_cases hc : fr = fr' ∧ fc = fc'
  · obtain ⟨rfl, rfl⟩ := hc
    have hab : a ≠ b := fun e => hne (by rw [e])
    have hd := List.all_eq_true.mp (exit_disj _ (hSf fr fc) a ha b hb hab) z0 hz0
    have := back2_inj hR hC fr fc c1.1 c1.2 c0.1 c0.2 e01
    subst this
    simp [hz1] at hd
  · exact corner_far hR hC hc c0.1 c0.2 c1.1 c1.2 e01.symm

end ZZN

-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Statement
import ZZN.Thin.Fast
import ZZN.Symmetry

/-!
# A witness-carrying plug DP: a computable solver for thin rectangles

`insideF` (`Thin/Fast.lean`) decides solvability; its soundness proof (`step_W`) shows that every
state is backed by segments, but only existentially. Here every state carries those segments
explicitly:
- `Wit.1`: an association list from each piece code of the state to its segment (a list of cells
  whose head realizes the smaller end code and whose last cell realizes the larger one);
- `Wit.2`: the completed paths of colours 0 and 1 (`[]` while a colour is open).

`stepCellW` mirrors `stepCell` and builds the new segment as the proof of `step_W` does: orient the
attached pieces (`orientS`), snoc the current cell or join through it (`segNew`), then store the
result with the smaller code first (`orientN`) or, when a colour is completed, as a path from its
first endpoint (`orientP`). Stages keep the first witness of each state (`dedupKey`) and drop
states with exit ends, as `stageF` does.

Main results: `thinSolveW_sound` and `thinSolveW_complete`.
-/

namespace ZZN.Thin

open GridHam

/-! ### The computation -/



def dpOf (d : List Coord × List Coord) (col : ℕ) : List Coord := if col = 0 then d.1 else d.2























/-! ### Bookkeeping lemmas -/

theorem stepCell_eq (a b : ℕ) (e : Option ℕ) (r c : ℕ) (s : St) :
    stepCell a b e r c s =
      if degOf e < ninOf (puOf s r c) (plOf b s c) then [] else
      if (puOf s r c).isSome && puOf s r c == plOf b s c then [] else
      (optsOf a b r c e (puOf s r c) (plOf b s c)).filterMap fun outs =>
        match insOf a b c e (puOf s r c) (plOf b s c) ++ outs with
        | [x, y] => closeP a b x y (restK s.1 (puOf s r c) (plOf b s c)) s.2
        | _ => none := rfl

theorem stepCellG_snd (a b : ℕ) (e : Option ℕ) (r c : ℕ) (s : St) :
    (stepCellG a b e r c s).map Prod.snd = stepCell a b e r c s := by
  rw [stepCell_eq]
  unfold stepCellG closeOuts
  split_ifs
  · rfl
  · rfl
  · rw [List.map_filterMap]
    congr 1
    funext outs
    split <;> simp_all

theorem mem_closeOuts {a b : ℕ} {ins rest : List ℕ} {dn : ℕ} {opts : List (List ℕ)} {x y : ℕ} {s' : St}
    (h : ((x, y), s') ∈ closeOuts a b ins rest dn opts) : closeP a b x y rest dn = some s' := by
  unfold closeOuts at h
  rw [List.mem_filterMap] at h
  obtain ⟨outs, -, h⟩ := h
  split at h
  · rw [Option.map_eq_some_iff] at h
    obtain ⟨s'', h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
    exact h1
  · simp at h

theorem stepCellG_close {a b : ℕ} {e : Option ℕ} {r c : ℕ} {s s' : St} {x y : ℕ}
    (h : ((x, y), s') ∈ stepCellG a b e r c s) :
    closeP a b x y (restK s.1 (puOf s r c) (plOf b s c)) s.2 = some s' := by
  unfold stepCellG at h
  split_ifs at h
  · simp at h
  · simp at h
  · exact mem_closeOuts h

/-! ### The invariant with explicit segments -/

section Inv

variable {a b : ℕ} {J : Inst}

/-- The body of `W` with the segments `sg` and paths `dp` given. -/
def WF (a b : ℕ) (J : Inst) (i : ℕ) (s : St) (sg dp : ℕ → List Coord) : Prop :=
  s.1.Nodup ∧ s.2 < 4 ∧
    (∀ z ∈ s.1, lo z ≠ hi z ∧ SegE a b J i (lo z) (hi z) (sg z)) ∧
    (∀ col ∈ doneCols s.2, IsPath a b (ends2 J col).1 (ends2 J col).2 (dp col)) ∧
    (allOf sg dp s).Nodup ∧ (∀ x, prI a b i x ↔ x ∈ allOf sg dp s)

theorem W_of_WF {i : ℕ} {s : St} {sg dp : ℕ → List Coord} (h : WF a b J i s sg dp) : W a b J i s :=
  ⟨sg, dp, h⟩

theorem allOf_congr {s : St} {sg dp sg' dp' : ℕ → List Coord} (hs : ∀ z ∈ s.1, sg' z = sg z)
    (hd : ∀ c ∈ doneCols s.2, dp' c = dp c) : allOf sg' dp' s = allOf sg dp s := by
  unfold allOf
  rw [List.flatMap_congr hs, List.flatMap_congr hd]

theorem WF_congr {i : ℕ} {s : St} {sg dp sg' dp' : ℕ → List Coord} (h : WF a b J i s sg dp)
    (hs : ∀ z ∈ s.1, sg' z = sg z) (hd : ∀ c ∈ doneCols s.2, dp' c = dp c) : WF a b J i s sg' dp' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, fun z hz => ?_, fun c hc => ?_, ?_, ?_⟩
  · rw [hs z hz]; exact h3 z hz
  · rw [hd c hc]; exact h4 c hc
  · rw [allOf_congr hs hd]; exact h5
  · rw [allOf_congr hs hd]; exact h6

/-- `assemble`, with the new segments explicit. -/
theorem assembleF {i : ℕ} {x : Coord} (hpr : ∀ y, prI a b (i + 1) y ↔ prI a b i y ∨ y = x)
    {s s' : St} {sg dp sg' dp' : ℕ → List Coord}
    (hnod : (allOf sg dp s).Nodup) (hcov : ∀ y, prI a b i y ↔ y ∈ allOf sg dp s) (hx : ¬ prI a b i x)
    (h1 : s'.1.Nodup) (h2 : s'.2 < 4)
    (h3 : ∀ z ∈ s'.1, lo z ≠ hi z ∧ SegE a b J (i + 1) (lo z) (hi z) (sg' z))
    (h4 : ∀ col ∈ doneCols s'.2, IsPath a b (ends2 J col).1 (ends2 J col).2 (dp' col))
    (h5 : (allOf sg' dp' s').Perm (allOf sg dp s ++ [x])) : WF a b J (i + 1) s' sg' dp' := by
  refine ⟨h1, h2, h3, h4, ?_, ?_⟩
  · rw [h5.nodup_iff, List.nodup_append]
    refine ⟨hnod, List.nodup_singleton x, ?_⟩
    intro y hy z hz heq
    rw [List.mem_singleton] at hz
    rw [heq, hz] at hy
    exact hx ((hcov x).mpr hy)
  · intro y
    rw [hpr, h5.mem_iff, List.mem_append, List.mem_singleton, hcov]

/-- `orient`, made explicit. -/
theorem orientS_spec {i z e : ℕ} {L : List Coord} (hz : SegE a b J i (lo z) (hi z) L)
    (he : hasEnd e z = true) :
    SegE a b J i (other e z) e (orientS e z L) ∧ (orientS e z L).Perm L := by
  unfold hasEnd at he
  unfold other orientS
  by_cases h : lo z = e
  · rw [ite_eq_left (by simp [h]), ite_eq_left h]
    refine ⟨?_, List.reverse_perm _⟩
    rw [← h]; exact hz.rev
  · rw [ite_eq_right (by simp [h]), ite_eq_right h]
    have : hi z = e := by simpa [h] using he
    exact ⟨this ▸ hz, List.Perm.refl _⟩

end Inv

/-- The segment map after closing `Ln` with end codes `E1, E2`. -/
def closeSg (a b E1 E2 : ℕ) (Ln : List Coord) (sg : ℕ → List Coord) : ℕ → List Coord :=
  if isTerm a b E1 && isTerm a b E2 then sg
  else fun z => if z = mkP E1 E2 then orientN E1 E2 Ln else sg z

/-- The path map after closing `Ln` with end codes `E1, E2`. -/
def closeDp (J : Inst) (a b E1 E2 : ℕ) (Ln : List Coord) (dp : ℕ → List Coord) : ℕ → List Coord :=
  if isTerm a b E1 && isTerm a b E2 then
    fun c => if c = colE a b E1 then orientP J (colE a b E1) Ln else dp c
  else dp

section Close

variable {a b : ℕ} {J : Inst}

/-- `close_W` with the new segments explicit. -/
theorem close_WF {i : ℕ} (hia : i + 1 ≤ a * b) {x : Coord}
    (hpr : ∀ y, prI a b (i + 1) y ↔ prI a b i y ∨ y = x) (hx : ¬ prI a b i x)
    {s : St} {sg dp : ℕ → List Coord} (hdn : s.2 < 4)
    (hdone : ∀ col ∈ doneCols s.2, IsPath a b (ends2 J col).1 (ends2 J col).2 (dp col))
    (hnod : (allOf sg dp s).Nodup) (hcov : ∀ y, prI a b i y ↔ y ∈ allOf sg dp s)
    {K rest : List ℕ} (hperm : s.1.Perm (K ++ rest)) (hrn : rest.Nodup)
    (hrest : ∀ z ∈ rest, lo z ≠ hi z ∧ SegE a b J (i + 1) (lo z) (hi z) (sg z))
    {E1 E2 : ℕ} {Ln : List Coord} (hseg : SegE a b J (i + 1) E1 E2 Ln)
    (hmem : Ln.Perm (K.flatMap sg ++ [x]))
    (hlen : (isTerm a b E1 && isTerm a b E2) = true → 2 ≤ Ln.length)
    (hneq : (isTerm a b E1 && isTerm a b E2) = false → E1 ≠ E2)
    {s' : St} (hcl : closeP a b E1 E2 rest s.2 = some s') :
    WF a b J (i + 1) s' (closeSg a b E1 E2 Ln sg) (closeDp J a b E1 E2 Ln dp) := by
  have hold : (allOf sg dp s).Perm (K.flatMap sg ++ rest.flatMap sg ++ (doneCols s.2).flatMap dp) := by
    unfold allOf
    rw [← List.flatMap_append]
    exact (hperm.flatMap_right sg).append_right _
  have hnod' := hold.nodup_iff.mp hnod
  have hxo : x ∉ allOf sg dp s := fun h => hx ((hcov x).mpr h)
  have dKR : ∀ y, y ∈ K.flatMap sg → y ∉ rest.flatMap sg := by
    intro y h1 h2
    rw [List.nodup_append, List.nodup_append] at hnod'
    exact hnod'.1.2.2 y h1 y h2 rfl
  have hseg0 := hseg
  obtain ⟨hLn, hLc, hLp, u, v, hu, hv, eu, ev⟩ := hseg
  unfold closeSg closeDp
  unfold closeP at hcl
  split_ifs at hcl with hT hc hbit
  -- a colour is completed
  · simp only [Option.some.injEq] at hcl
    subst hcl
    rw [ite_eq_left hT, ite_eq_left hT]
    simp only [Bool.and_eq_true] at hT
    have e1 := isTerm_eq hT.1
    have e2 := isTerm_eq hT.2
    simp only [bne_iff_ne, ne_eq, not_not] at hc
    set col := colE a b E1 with hcol
    have pu := hLp u (List.mem_of_head? hu)
    have pv := hLp v (List.mem_of_getLast? hv)
    have cu := endOK_term pu (e1 ▸ eu)
    have cv := endOK_term pv (by rw [e2, ← hc] at ev; exact ev)
    have huv := head_ne_last hLn (hlen (by simp [hT])) hu hv
    have hcol2 : col < 2 := by rcases endCol_cases cu with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
    obtain ⟨d4, dperm⟩ := doneCols_add hdn hcol2 (by simpa using hbit)
    have hpath : IsPath a b (ends2 J col).1 (ends2 J col).2 (orientP J col Ln) ∧
        (orientP J col Ln).Perm Ln := by
      have inb : ∀ y ∈ Ln, InBounds a b y := fun y hy => ⟨(hLp y hy).1, (hLp y hy).2.1⟩
      have pathF : IsPath a b u v Ln := ⟨hu, hv, hLn, inb, hLc⟩
      have key : (u = (ends2 J col).1 ∧ v = (ends2 J col).2) ∨
          (u = (ends2 J col).2 ∧ v = (ends2 J col).1) := by
        unfold ends2
        rcases endCol_cases cu with ⟨h0, hu'⟩ | ⟨h0, hu'⟩ <;>
          rcases endCol_cases cv with ⟨h1, hv'⟩ | ⟨h1, hv'⟩
        · rw [ite_eq_left h0]
          rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
          · exact absurd rfl huv
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr ⟨rfl, rfl⟩
          · exact absurd rfl huv
        · omega
        · omega
        · rw [ite_eq_right (by omega)]
          rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
          · exact absurd rfl huv
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr ⟨rfl, rfl⟩
          · exact absurd rfl huv
      unfold orientP
      rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [ite_eq_left hu]; exact ⟨pathF, List.Perm.refl _⟩
      · rw [ite_eq_right (by rw [hu]; intro h; exact huv (Option.some.inj h))]
        exact ⟨pathF.reverse, List.reverse_perm _⟩
    obtain ⟨hP, hPp⟩ := hpath
    have hnot : col ∉ doneCols s.2 := by
      intro h
      unfold doneCols at h
      rw [List.mem_filter] at h
      unfold bitOf at h
      exact hbit h.2
    refine assembleF (sg := sg) (dp := dp) hpr hnod hcov hx hrn d4 hrest ?_ ?_
    · intro c hc'
      show IsPath a b _ _ (if c = col then orientP J col Ln else dp c)
      by_cases hcc : c = col
      · rw [ite_eq_left hcc, hcc]; exact hP
      · rw [ite_eq_right hcc]
        rcases List.mem_cons.mp (dperm.mem_iff.mp hc') with h | h
        · exact absurd h hcc
        · exact hdone c h
    · unfold allOf
      dsimp only
      have hd : ((doneCols (s.2 + 2 ^ col)).flatMap
          (fun c => if c = col then orientP J col Ln else dp c)).Perm
          (orientP J col Ln ++ (doneCols s.2).flatMap dp) := by
        refine (dperm.flatMap_right _).trans ?_
        rw [List.flatMap_cons, ite_eq_left rfl]
        refine List.Perm.append_left _ (List.Perm.of_eq (List.flatMap_congr ?_))
        intro c hc'
        exact ite_eq_right (fun (e : c = col) => hnot (e ▸ hc'))
      rw [List.perm_iff_count]
      intro z
      have h1 := (hPp.trans hmem).count_eq z
      have h2 := hold.count_eq z
      have h3 := hd.count_eq z
      unfold allOf at h2
      simp only [List.count_append] at h1 h2 h3 ⊢
      omega
  -- a new piece is stored
  · simp only [Option.some.injEq] at hcl
    subst hcl
    have hT' : (isTerm a b E1 && isTerm a b E2) = false := by simpa using hT
    rw [ite_eq_right hT, ite_eq_right hT]
    have hne := hneq hT'
    set z' := mkP E1 E2 with hz'
    obtain ⟨p, w, hpE, hw, hwOK, hpl⟩ : ∃ p w, (p = E1 ∨ p = E2) ∧ w ∈ Ln ∧ EndOK a b J (i + 1) p w ∧
        p < a + 2 * b + 1 := by
      by_cases h1 : isTerm a b E1 = true
      · have h2 : isTerm a b E2 = false := by simpa [h1] using hT'
        refine ⟨E2, v, Or.inr rfl, List.mem_of_getLast? hv, ev, ?_⟩
        unfold isTerm at h2; simpa using h2
      · refine ⟨E1, u, Or.inl rfl, List.mem_of_head? hu, eu, ?_⟩
        unfold isTerm at h1; simpa using h1
    have hpz : hasEnd p z' = true := by rw [hz', hasEnd_mkP]; rcases hpE with rfl | rfl <;> simp
    have hfresh : z' ∉ rest := by
      intro hzr
      obtain ⟨L1, s1, m1, -⟩ := orient (hrest z' hzr).2 hpz
      obtain ⟨v1, -, vm1, ev1, pv1⟩ := s1.mem_last
      obtain ⟨y1, ny1, ad1, d1⟩ := plug_of pv1 ev1 hpl
      obtain ⟨y2, ny2, ad2, d2⟩ := plug_of (hLp w hw) hwOK hpl
      obtain ⟨rfl, -⟩ := desc_inj hia pv1 ny1 ad1 (hLp w hw) ny2 ad2 (d1.trans d2.symm)
      have hr : v1 ∈ rest.flatMap sg := List.mem_flatMap.mpr ⟨z', hzr, (m1 v1).mp vm1⟩
      rcases List.mem_append.mp (hmem.mem_iff.mp hw) with hk | hk
      · exact dKR v1 hk hr
      · rw [List.mem_singleton] at hk
        subst hk
        exact hxo (hold.mem_iff.mpr (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hr)))))
    have hsegN : SegE a b J (i + 1) (lo z') (hi z') (orientN E1 E2 Ln) := by
      rw [hz', mkP_lo, mkP_hi]
      unfold orientN
      split_ifs with h
      · rw [min_eq_left h, max_eq_right h]; exact hseg0
      · rw [min_eq_right (by omega), max_eq_left (by omega)]; exact hseg0.rev
    have hsg' : ∀ z ∈ rest, (if z = z' then orientN E1 E2 Ln else sg z) = sg z :=
      fun z hz => ite_eq_right (fun (e : z = z') => hfresh (e ▸ hz))
    have hins := insSorted_perm z' rest
    refine assembleF (sg := sg) (dp := dp) hpr hnod hcov hx ?_ hdn ?_ hdone ?_
    · exact hins.nodup_iff.mpr (List.nodup_cons.mpr ⟨hfresh, hrn⟩)
    · intro z hz
      rcases List.mem_cons.mp (hins.mem_iff.mp hz) with rfl | hz
      · refine ⟨?_, ?_⟩
        · rw [hz', mkP_lo, mkP_hi]; omega
        · show SegE a b J (i + 1) _ _ (if z' = z' then _ else _)
          rw [ite_eq_left rfl]; exact hsegN
      · rw [hsg' z hz]; exact hrest z hz
    · unfold allOf
      dsimp only
      have hl : ((insSorted z' rest).flatMap (fun z => if z = z' then orientN E1 E2 Ln else sg z)).Perm
          (orientN E1 E2 Ln ++ rest.flatMap sg) := by
        refine (hins.flatMap_right _).trans ?_
        rw [List.flatMap_cons, ite_eq_left rfl]
        exact List.Perm.append_left _ (List.Perm.of_eq (List.flatMap_congr hsg'))
      have hLp' : (orientN E1 E2 Ln).Perm Ln := by
        unfold orientN
        split_ifs
        · exact List.Perm.refl _
        · exact List.reverse_perm _
      rw [List.perm_iff_count]
      intro z
      have h1 := (hLp'.trans hmem).count_eq z
      have h2 := hold.count_eq z
      have h3 := hl.count_eq z
      unfold allOf at h2
      simp only [List.count_append] at h1 h2 h3 ⊢
      omega

end Close

section Step

variable {a b : ℕ} {J : Inst}

/-- **One DP step keeps the explicit invariant** (`step_W` with the new segments explicit). -/
theorem step_WF {tm : List ((ℕ × ℕ) × ℕ)}
    (htm : ∀ y : Coord, y.1 < a → y.2 < b → termAt tm y = endCol J y)
    {i : ℕ} (hlt : i < a * b) {s s' : St} {sg dp : ℕ → List Coord} (hW : WF a b J i s sg dp) {E1 E2 : ℕ}
    (hs : ((E1, E2), s') ∈ stepCellG a b (termAt tm (cell b i)) (cell b i).1 (cell b i).2 s) :
    WF a b J (i + 1) s'
      (closeSg a b E1 E2 (segNew b (cell b i).1 (cell b i).2 sg (puOf s (cell b i).1 (cell b i).2)
        (plOf b s (cell b i).2)) sg)
      (closeDp J a b E1 E2 (segNew b (cell b i).1 (cell b i).2 sg (puOf s (cell b i).1 (cell b i).2)
        (plOf b s (cell b i).2)) dp) := by
  obtain ⟨c1, c2, c3⟩ := cell_spec hlt
  have hpr0 := fun y => prI_succ hlt (y := y)
  have hlex0 := fun y => prI_lex hlt (y := y)
  rcases hxc : cell b i with ⟨x1, x2⟩
  rw [hxc] at c1 c2 c3 hs hpr0 hlex0
  simp only at c1 c2 c3 hs hlex0 ⊢
  have hpr : ∀ y, prI a b (i + 1) y ↔ prI a b i y ∨ y = (x1, x2) := hpr0
  have hlex : ∀ y : Coord, prI a b i y ↔ y.1 < a ∧ y.2 < b ∧ (y.1 < x1 ∨ (y.1 = x1 ∧ y.2 < x2)) := hlex0
  have hx : ¬ prI a b i (x1, x2) := by unfold prI; simp only; omega
  have hia : i + 1 ≤ a * b := hlt
  have hpx : prI a b (i + 1) (x1, x2) := (hpr _).mpr (Or.inr rfl)
  obtain ⟨hn, h4, hseg, hdone, hnod, hcov⟩ := hW
  have hflat : (s.1.flatMap sg).Nodup := (List.nodup_append.mp hnod).1
  have huniq := fun {e z z'} hz hz' he h1 h2 =>
    plug_unique (a := a) (b := b) (J := J) (le_of_lt hlt) hn hseg hflat (e := e) (z := z) (z' := z')
      hz hz' he h1 h2
  have keep : ∀ {e : ℕ} {w : Coord}, prI a b i w → EndOK a b J i e w → (x1 ≠ 0 → e ≠ x2) →
      (x2 ≠ 0 → e ≠ b) → EndOK a b J (i + 1) e w := by
    intro e w pw h h1 h2
    refine endOK_succ hpr h (fun y ad d ny hy => ?_)
    subst hy
    rcases (nb_proc hlex c1 c2 (adj_symm ad)).mp pw with ⟨h0, rfl⟩ | ⟨h0, rfl⟩
    · exact h1 (by omega) (by rw [← d, desc_up c1 h0])
    · exact h2 (by omega) (by rw [← d, desc_lft c2 h0])
  have keepSeg : ∀ z ∈ s.1, (x1 ≠ 0 → hasEnd x2 z = false) → (x2 ≠ 0 → hasEnd b z = false) →
      SegE a b J (i + 1) (lo z) (hi z) (sg z) := by
    intro z hz k1 k2
    have hs0 := (hseg z hz).2
    have hs1 := hs0
    obtain ⟨-, -, hp, u, v, hu, hv, eu, ev⟩ := hs1
    refine hs0.succ hpr (fun u' hu' => ?_) (fun v' hv' => ?_)
    · rw [hu] at hu'; cases hu'
      exact keep (hp u (List.mem_of_head? hu)) eu
        (fun h e => by have := k1 h; rw [← e, hasEnd_lo] at this; simp at this)
        (fun h e => by have := k2 h; rw [← e, hasEnd_lo] at this; simp at this)
    · rw [hv] at hv'; cases hv'
      exact keep (hp v (List.mem_of_getLast? hv)) ev
        (fun h e => by have := k1 h; rw [← e, hasEnd_hi] at this; simp at this)
        (fun h e => by have := k2 h; rw [← e, hasEnd_hi] at this; simp at this)
  have fromUp : ∀ zu, x1 ≠ 0 → s.1.find? (hasEnd x2) = some zu → zu ∈ s.1 ∧ hasEnd x2 zu = true ∧
      SegE a b J i (other x2 zu) x2 (orientS x2 zu (sg zu)) ∧ (orientS x2 zu (sg zu)).Perm (sg zu) ∧
      (orientS x2 zu (sg zu)).getLast? = some (x1 - 1, x2) := by
    intro zu h0 hf
    have hz := List.mem_of_find?_eq_some hf
    have he := List.find?_some hf
    obtain ⟨sL, pL⟩ := orientS_spec (hseg zu hz).2 he
    obtain ⟨v, hv, -, ev, pv⟩ := sL.mem_last
    obtain ⟨y, ny, ad, d⟩ := plug_of pv ev (by omega)
    obtain ⟨-, rfl, -⟩ := bd_plug hlex c2 pv ny ad d
    exact ⟨hz, he, sL, pL, hv⟩
  have fromLeft : ∀ zl, x2 ≠ 0 → s.1.find? (hasEnd b) = some zl → zl ∈ s.1 ∧ hasEnd b zl = true ∧
      SegE a b J i (other b zl) b (orientS b zl (sg zl)) ∧ (orientS b zl (sg zl)).Perm (sg zl) ∧
      (orientS b zl (sg zl)).getLast? = some (x1, x2 - 1) := by
    intro zl h0 hf
    have hz := List.mem_of_find?_eq_some hf
    have he := List.find?_some hf
    obtain ⟨sL, pL⟩ := orientS_spec (hseg zl hz).2 he
    obtain ⟨v, hv, -, ev, pv⟩ := sL.mem_last
    obtain ⟨y, ny, ad, d⟩ := plug_of pv ev (by omega)
    obtain ⟨-, rfl, -⟩ := bd_left hlex pv ny ad d
    exact ⟨hz, he, sL, pL, hv⟩
  have endD : EndOK a b J (i + 1) (if x1 + 1 < a then x2 else exitE b (a + (b - 1 - x2))) (x1, x2) := by
    refine Or.inr ⟨(x1 + 1, x2), ?_, by unfold Adjacent; omega, desc_down⟩
    unfold prI; simp only; intro h
    have : (x1 + 1) * b = x1 * b + b := Nat.succ_mul x1 b
    omega
  have endR : EndOK a b J (i + 1) (if x2 + 1 < b then b else exitE b x1) (x1, x2) := by
    refine Or.inr ⟨(x1, x2 + 1), ?_, by unfold Adjacent; omega, desc_right⟩
    unfold prI; simp only; omega
  have endT : ∀ col, termAt tm (x1, x2) = some col → EndOK a b J (i + 1) (termE a b col) (x1, x2) := by
    intro col h
    exact Or.inl ⟨col, rfl, by rw [← htm _ c1 c2]; exact h⟩
  have plugD : (if x1 + 1 < a then x2 else exitE b (a + (b - 1 - x2))) < a + 2 * b + 1 := by
    unfold exitE; split_ifs <;> omega
  have plugR : (if x2 + 1 < b then b else exitE b x1) < a + 2 * b + 1 := by
    unfold exitE; split_ifs <;> omega
  have isT_plug : ∀ e, e < a + 2 * b + 1 → isTerm a b e = false := by
    intro e he; unfold isTerm; simp; omega
  have neqLong : ∀ {E1 E2 : ℕ} {Ln : List Coord}, SegE a b J (i + 1) E1 E2 Ln → 2 ≤ Ln.length →
      (isTerm a b E1 && isTerm a b E2) = false → E1 ≠ E2 := by
    intro E1 E2 Ln hL hl hT heq
    subst heq
    have : isTerm a b E1 = false := by simpa using hT
    unfold isTerm at this
    exact plug_ends_ne hia hL hl (by simpa using this)
  have findNone : ∀ {e : ℕ}, s.1.find? (hasEnd e) = none → ∀ z ∈ s.1, hasEnd e z = false := by
    intro e h z hz
    rw [List.find?_eq_none] at h
    simpa using h z hz
  have restNodup := fun (z : ℕ) => hn.erase z
  have lenPos : ∀ {L : List Coord} {w : Coord}, L.getLast? = some w → 1 ≤ L.length := by
    intro L w h; cases L with
    | nil => simp at h
    | cons _ _ => simp
  have case0 : ∀ E1 E2, (x1 ≠ 0 → s.1.find? (hasEnd x2) = none) → (x2 ≠ 0 → s.1.find? (hasEnd b) = none) →
      EndOK a b J (i + 1) E1 (x1, x2) → EndOK a b J (i + 1) E2 (x1, x2) → E1 ≠ E2 →
      (isTerm a b E1 && isTerm a b E2) = false → closeP a b E1 E2 s.1 s.2 = some s' →
      WF a b J (i + 1) s' (closeSg a b E1 E2 [(x1, x2)] sg) (closeDp J a b E1 E2 [(x1, x2)] dp) := by
    intro E1 E2 nu nl e1 e2 hne hT hcl
    exact close_WF hia hpr hx h4 hdone hnod hcov (K := []) (rest := s.1) (by simp) hn
      (fun z hz => ⟨(hseg z hz).1, keepSeg z hz (fun h => findNone (nu h) z hz)
        (fun h => findNone (nl h) z hz)⟩)
      (segE_single hpx e1 e2) (by simp) (fun h => by rw [hT] at h; simp at h) (fun _ => hne) hcl
  have caseL : ∀ zl E2, x2 ≠ 0 → s.1.find? (hasEnd b) = some zl → (x1 ≠ 0 → s.1.find? (hasEnd x2) = none) →
      EndOK a b J (i + 1) E2 (x1, x2) → closeP a b (other b zl) E2 (s.1.erase zl) s.2 = some s' →
      WF a b J (i + 1) s' (closeSg a b (other b zl) E2 (orientS b zl (sg zl) ++ [(x1, x2)]) sg)
        (closeDp J a b (other b zl) E2 (orientS b zl (sg zl) ++ [(x1, x2)]) dp) := by
    intro zl E2 h0 hf nu e2 hcl
    obtain ⟨hz, he, sL, pL, hv⟩ := fromLeft zl h0 hf
    have sL' := sL
    obtain ⟨-, -, hp, u, -, hu, -, eu, -⟩ := sL'
    have hseg' : SegE a b J (i + 1) (other b zl) E2 (orientS b zl (sg zl) ++ [(x1, x2)]) := by
      refine segE_snoc hpr hx sL hv (by unfold Adjacent; omega) (fun u' hu' => ?_) e2
      rw [hu] at hu'; cases hu'
      refine keep (hp u (List.mem_of_head? hu)) eu (fun h e => ?_) (fun _ => other_ne he (hseg zl hz).1)
      have := findNone (nu h) zl hz
      rw [← e, hasEnd_other he] at this; simp at this
    refine close_WF hia hpr hx h4 hdone hnod hcov (K := [zl]) (rest := s.1.erase zl)
      (List.perm_cons_erase hz) (restNodup zl) (fun z hz' => ?_) hseg' ?_ ?_ ?_ hcl
    · obtain ⟨hzne, hz2⟩ := (hn.mem_erase_iff).mp hz'
      refine ⟨(hseg z hz2).1, keepSeg z hz2 (fun h => findNone (nu h) z hz2) (fun _ => ?_)⟩
      by_contra hb
      exact hzne (huniq hz2 hz (by omega) (by simpa using hb) he)
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact pL.append_right _
    · intro _; have := lenPos hv; simp; omega
    · exact neqLong hseg' (by have := lenPos hv; simp; omega)
  have caseU : ∀ zu E2, x1 ≠ 0 → s.1.find? (hasEnd x2) = some zu → (x2 ≠ 0 → s.1.find? (hasEnd b) = none) →
      EndOK a b J (i + 1) E2 (x1, x2) → closeP a b (other x2 zu) E2 (s.1.erase zu) s.2 = some s' →
      WF a b J (i + 1) s' (closeSg a b (other x2 zu) E2 (orientS x2 zu (sg zu) ++ [(x1, x2)]) sg)
        (closeDp J a b (other x2 zu) E2 (orientS x2 zu (sg zu) ++ [(x1, x2)]) dp) := by
    intro zu E2 h0 hf nl e2 hcl
    obtain ⟨hz, he, sL, pL, hv⟩ := fromUp zu h0 hf
    have sL' := sL
    obtain ⟨-, -, hp, u, -, hu, -, eu, -⟩ := sL'
    have hseg' : SegE a b J (i + 1) (other x2 zu) E2 (orientS x2 zu (sg zu) ++ [(x1, x2)]) := by
      refine segE_snoc hpr hx sL hv (by unfold Adjacent; omega) (fun u' hu' => ?_) e2
      rw [hu] at hu'; cases hu'
      refine keep (hp u (List.mem_of_head? hu)) eu (fun _ => other_ne he (hseg zu hz).1) (fun h e => ?_)
      have := findNone (nl h) zu hz
      rw [← e, hasEnd_other he] at this; simp at this
    refine close_WF hia hpr hx h4 hdone hnod hcov (K := [zu]) (rest := s.1.erase zu)
      (List.perm_cons_erase hz) (restNodup zu) (fun z hz' => ?_) hseg' ?_ ?_ ?_ hcl
    · obtain ⟨hzne, hz2⟩ := (hn.mem_erase_iff).mp hz'
      refine ⟨(hseg z hz2).1, keepSeg z hz2 (fun _ => ?_) (fun h => findNone (nl h) z hz2)⟩
      by_contra hb
      exact hzne (huniq hz2 hz (by omega) (by simpa using hb) he)
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact pL.append_right _
    · intro _; have := lenPos hv; simp; omega
    · exact neqLong hseg' (by have := lenPos hv; simp; omega)
  have case2 : ∀ zu zl, x1 ≠ 0 → x2 ≠ 0 → s.1.find? (hasEnd x2) = some zu → s.1.find? (hasEnd b) = some zl →
      zu ≠ zl → closeP a b (other x2 zu) (other b zl) ((s.1.erase zu).erase zl) s.2 = some s' →
      WF a b J (i + 1) s'
        (closeSg a b (other x2 zu) (other b zl)
          (orientS x2 zu (sg zu) ++ [(x1, x2)] ++ (orientS b zl (sg zl)).reverse) sg)
        (closeDp J a b (other x2 zu) (other b zl)
          (orientS x2 zu (sg zu) ++ [(x1, x2)] ++ (orientS b zl (sg zl)).reverse) dp) := by
    intro zu zl h0 h0' hfu hfl hne hcl
    obtain ⟨hzu, heu, sU, pU, hvu⟩ := fromUp zu h0 hfu
    obtain ⟨hzl, hel, sLl, pLl, hvl⟩ := fromLeft zl h0' hfl
    have sU' := sU
    obtain ⟨-, -, hpu', uu, -, huu, -, euu, -⟩ := sU'
    have sLl' := sLl
    obtain ⟨-, -, hpl', ul, -, hul, -, eul, -⟩ := sLl'
    have hdis : ∀ y ∈ orientS x2 zu (sg zu), y ∉ orientS b zl (sg zl) := by
      intro y h1 h2
      exact hne (flatMap_unique hn hflat hzu hzl (pU.mem_iff.mp h1) (pLl.mem_iff.mp h2))
    have hseg' : SegE a b J (i + 1) (other x2 zu) (other b zl)
        (orientS x2 zu (sg zu) ++ [(x1, x2)] ++ (orientS b zl (sg zl)).reverse) := by
      refine segE_join hpr hx sU sLl hdis hvu (by unfold Adjacent; omega) hvl (by unfold Adjacent; omega)
        (fun u' hu' => ?_) (fun u' hu' => ?_)
      · rw [huu] at hu'; cases hu'
        refine keep (hpu' uu (List.mem_of_head? huu)) euu (fun _ => other_ne heu (hseg zu hzu).1)
          (fun _ e => ?_)
        exact hne (huniq hzu hzl (by omega) (by rw [← e]; exact hasEnd_other heu) hel)
      · rw [hul] at hu'; cases hu'
        refine keep (hpl' ul (List.mem_of_head? hul)) eul (fun _ e => ?_)
          (fun _ => other_ne hel (hseg zl hzl).1)
        exact hne (huniq hzu hzl (by omega) heu (by rw [← e]; exact hasEnd_other hel))
    have hzl' : zl ∈ s.1.erase zu := (hn.mem_erase_iff).mpr ⟨Ne.symm hne, hzl⟩
    have hperm : s.1.Perm ([zu, zl] ++ (s.1.erase zu).erase zl) :=
      (List.perm_cons_erase hzu).trans (List.Perm.cons _ (List.perm_cons_erase hzl'))
    refine close_WF hia hpr hx h4 hdone hnod hcov (K := [zu, zl]) (rest := (s.1.erase zu).erase zl)
      hperm ((restNodup zu).erase zl) (fun z hz' => ?_) hseg' ?_ ?_ ?_ hcl
    · obtain ⟨hz1, hz2⟩ := ((restNodup zu).mem_erase_iff).mp hz'
      obtain ⟨hz3, hz4⟩ := (hn.mem_erase_iff).mp hz2
      refine ⟨(hseg z hz4).1, keepSeg z hz4 (fun _ => ?_) (fun _ => ?_)⟩
      · by_contra hb; exact hz3 (huniq hz4 hzu (by omega) (by simpa using hb) heu)
      · by_contra hb; exact hz1 (huniq hz4 hzl (by omega) (by simpa using hb) hel)
    · rw [List.perm_iff_count]; intro y
      have h1 := pU.count_eq y
      have h2 := pLl.count_eq y
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_append,
        List.count_reverse] at h1 h2 ⊢
      omega
    · intro _; have := lenPos hvu; simp; omega
    · exact neqLong hseg' (by have := lenPos hvu; simp; omega)
  -- the DP's cases
  unfold stepCellG closeOuts optsOf insOf degOf ninOf restK at hs
  unfold segNew
  unfold puOf plOf at hs ⊢
  generalize hpu : (if x1 = 0 then none else s.1.find? (hasEnd x2)) = pu at hs ⊢
  generalize hpl : (if x2 = 0 then none else s.1.find? (hasEnd b)) = pl at hs ⊢
  generalize hte : termAt tm (x1, x2) = te at hs endT
  have nuOf : pu = none → x1 ≠ 0 → s.1.find? (hasEnd x2) = none := by
    intro h h0; rw [← hpu, ite_eq_right h0] at h; exact h
  have nlOf : pl = none → x2 ≠ 0 → s.1.find? (hasEnd b) = none := by
    intro h h0; rw [← hpl, ite_eq_right h0] at h; exact h
  have suOf : ∀ zu, pu = some zu → x1 ≠ 0 ∧ s.1.find? (hasEnd x2) = some zu := by
    intro zu h; rw [← hpu] at h; split_ifs at h with h0; exact ⟨h0, h⟩
  have slOf : ∀ zl, pl = some zl → x2 ≠ 0 ∧ s.1.find? (hasEnd b) = some zl := by
    intro zl h; rw [← hpl] at h; split_ifs at h with h0; exact ⟨h0, h⟩
  have tT : ∀ col o, o < a + 2 * b + 1 → termE a b col ≠ o := by intro col o h; unfold termE; omega
  cases te <;> cases pu <;> cases pl <;>
    simp only [Option.isSome_none, Option.isSome_some, Option.map_none, Option.map_some, Option.toList,
      Bool.false_eq_true, ↓reduceIte, Option.getD_some, List.nil_append, List.cons_append,
      Bool.false_and, Bool.true_and, beq_iff_eq, Option.getD_none, List.reverse_nil,
      List.append_nil] at hs ⊢
  · simp at hs
    obtain ⟨hs, rfl, rfl⟩ := hs
    exact case0 _ _ (nuOf rfl) (nlOf rfl) endD endR (by unfold exitE; split_ifs <;> omega)
      (by rw [isT_plug _ plugD]; simp) hs
  · rename_i zl
    obtain ⟨h0, hf⟩ := slOf zl rfl
    simp at hs
    rcases hs with ⟨hs, rfl, rfl⟩ | ⟨hs, rfl, rfl⟩
    · exact caseL zl _ h0 hf (nuOf rfl) endD hs
    · exact caseL zl _ h0 hf (nuOf rfl) endR hs
  · rename_i zu
    obtain ⟨h0, hf⟩ := suOf zu rfl
    simp at hs
    rcases hs with ⟨hs, rfl, rfl⟩ | ⟨hs, rfl, rfl⟩
    · exact caseU zu _ h0 hf (nlOf rfl) endD hs
    · exact caseU zu _ h0 hf (nlOf rfl) endR hs
  · rename_i zu zl
    obtain ⟨h0, hf⟩ := suOf zu rfl
    obtain ⟨h0', hf'⟩ := slOf zl rfl
    simp at hs
    obtain ⟨hne, hs, rfl, rfl⟩ := hs
    exact case2 zu zl h0 h0' hf hf' hne hs
  · rename_i col
    simp at hs
    rcases hs with ⟨hs, rfl, rfl⟩ | ⟨hs, rfl, rfl⟩
    · exact case0 _ _ (nuOf rfl) (nlOf rfl) (endT col rfl) endD (tT col _ plugD)
        (by rw [isT_plug _ plugD]; simp) hs
    · exact case0 _ _ (nuOf rfl) (nlOf rfl) (endT col rfl) endR (tT col _ plugR)
        (by rw [isT_plug _ plugR]; simp) hs
  · rename_i col zl
    obtain ⟨h0, hf⟩ := slOf zl rfl
    simp at hs
    obtain ⟨hs, rfl, rfl⟩ := hs
    exact caseL zl _ h0 hf (nuOf rfl) (endT col rfl) hs
  · rename_i col zu
    obtain ⟨h0, hf⟩ := suOf zu rfl
    simp at hs
    obtain ⟨hs, rfl, rfl⟩ := hs
    exact caseU zu _ h0 hf (nlOf rfl) (endT col rfl) hs
  · simp at hs

end Step

/-! ### The invariant of the witness-carrying DP -/

/-- **The witness invariant** after `i` cells: the stored segments and paths realize the state
(`WF`, the concrete form of `W`), the stored keys are exactly the state's pieces, and an open
colour stores no path. -/
def WC (a b : ℕ) (J : Inst) (i : ℕ) (sw : St × Wit) : Prop :=
  WF a b J i sw.1 (lookD sw.2.1) (dpOf sw.2.2) ∧ (sw.2.1.map Prod.fst).Perm sw.1.1 ∧
    ∀ col < 2, col ∉ doneCols sw.1.2 → dpOf sw.2.2 col = []

theorem restK_eq_filter {ps : List ℕ} (hn : ps.Nodup) (pu pl : Option ℕ) :
    restK ps pu pl = ps.filter (fun k => pu != some k && pl != some k) := by
  unfold restK
  cases pu <;> cases pl
  · exact (List.filter_eq_self.mpr (fun k _ => rfl)).symm
  · simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte, Option.getD_some]
    rw [hn.erase_eq_filter]
    refine List.filter_congr (fun k _ => ?_)
    rw [Bool.eq_iff_iff]
    simp only [bne_iff_ne, ne_eq, Bool.and_eq_true, Option.some.injEq, reduceCtorEq, not_false_eq_true,
      true_and]
    omega
  · simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte, Option.getD_some]
    rw [hn.erase_eq_filter]
    refine List.filter_congr (fun k _ => ?_)
    rw [Bool.eq_iff_iff]
    simp only [bne_iff_ne, ne_eq, Bool.and_eq_true, Option.some.injEq, reduceCtorEq, not_false_eq_true,
      and_true]
    omega
  · simp only [Option.isSome_some, ↓reduceIte, Option.getD_some]
    rw [(hn.erase _).erase_eq_filter, hn.erase_eq_filter, List.filter_filter]
    refine List.filter_congr (fun k _ => ?_)
    rw [Bool.eq_iff_iff]
    simp only [bne_iff_ne, ne_eq, Bool.and_eq_true, Option.some.injEq]
    omega

theorem find_filter_key {p : ℕ × List Coord → Bool} {z : ℕ} (hp : ∀ q : ℕ × List Coord, q.1 = z → p q = true) :
    ∀ l : List (ℕ × List Coord), (l.filter p).find? (fun q => q.1 == z) = l.find? (fun q => q.1 == z)
  | [] => rfl
  | q :: l => by
    have ih := find_filter_key hp l
    by_cases hq : q.1 = z
    · rw [List.filter_cons_of_pos (hp q hq)]; simp [hq]
    · by_cases hpq : p q = true
      · rw [List.filter_cons_of_pos hpq]; simp [hq, ih]
      · rw [List.filter_cons_of_neg hpq]; simp [hq, ih]

theorem lookD_dropKeys {pu pl : Option ℕ} {z : ℕ} (h : (pu != some z && pl != some z) = true)
    (l : List (ℕ × List Coord)) : lookD (dropKeys pu pl l) z = lookD l z := by
  unfold lookD dropKeys
  rw [find_filter_key (fun q hq => by rw [hq]; exact h)]

theorem keys_dropKeys {ps : List ℕ} (hn : ps.Nodup) {l : List (ℕ × List Coord)} (hl : (l.map Prod.fst).Perm ps)
    (pu pl : Option ℕ) : ((dropKeys pu pl l).map Prod.fst).Perm (restK ps pu pl) := by
  have e : ((l.filter fun q => pu != some q.1 && pl != some q.1).map Prod.fst) =
      (l.map Prod.fst).filter (fun k => pu != some k && pl != some k) := by
    rw [List.filter_map]; rfl
  rw [restK_eq_filter hn, dropKeys, e]
  exact hl.filter _

theorem lookD_cons (k z : ℕ) (L : List Coord) (l : List (ℕ × List Coord)) :
    lookD ((k, L) :: l) z = if z = k then L else lookD l z := by
  unfold lookD
  by_cases h : z = k
  · subst h; simp
  · simp [Ne.symm h, h]

theorem dpOf_setDp {d : List Coord × List Coord} {col c : ℕ} {P : List Coord} (hcol : col < 2) (hc : c < 2) :
    dpOf (setDp d col P) c = if c = col then P else dpOf d c := by
  unfold dpOf setDp
  interval_cases col <;> interval_cases c <;> simp

theorem closeP_some {a b x y : ℕ} {rest : List ℕ} {dn : ℕ} {s' : St} (h : closeP a b x y rest dn = some s') :
    ((isTerm a b x && isTerm a b y) = true ∧ s' = (rest, dn + 2 ^ colE a b x) ∧
        ¬ (dn / 2 ^ colE a b x) % 2 = 1) ∨
      ((isTerm a b x && isTerm a b y) = false ∧ s' = (insSorted (mkP x y) rest, dn)) := by
  unfold closeP at h
  split_ifs at h with hT hc hbit
  · simp only [Option.some.injEq] at h
    exact Or.inl ⟨hT, h.symm, by simpa using hbit⟩
  · simp only [Option.some.injEq] at h
    exact Or.inr ⟨by simpa using hT, h.symm⟩

theorem mem_doneCols_lt {dn c : ℕ} (h : c ∈ doneCols dn) : c < 2 := by
  unfold doneCols at h
  rw [List.mem_filter, List.mem_range] at h
  exact h.1

section StepW

variable {a b : ℕ} {J : Inst}

/-- **One step of the witness-carrying DP keeps the witness invariant.** -/
theorem stepW_WC {tm : List ((ℕ × ℕ) × ℕ)}
    (htm : ∀ y : Coord, y.1 < a → y.2 < b → termAt tm y = endCol J y)
    {i : ℕ} (hlt : i < a * b) {sw sw' : St × Wit} (hW : WC a b J i sw)
    (h : sw' ∈ stepCellW J a b (termAt tm (cell b i)) (cell b i).1 (cell b i).2 sw) :
    WC a b J (i + 1) sw' := by
  obtain ⟨s, w⟩ := sw
  unfold stepCellW at h
  rw [List.mem_map] at h
  obtain ⟨⟨⟨E1, E2⟩, s'⟩, hg, rfl⟩ := h
  have hF := step_WF htm hlt hW.1 hg
  have hcl := stepCellG_close hg
  obtain ⟨⟨hn, -⟩, hkeys, hemp⟩ := hW
  dsimp only at hF hcl hn hkeys hemp ⊢
  generalize puOf s (cell b i).1 (cell b i).2 = pu at hF hcl ⊢
  generalize plOf b s (cell b i).2 = pl at hF hcl ⊢
  generalize segNew b (cell b i).1 (cell b i).2 (lookD w.1) pu pl = Ln at hF ⊢
  have hrest : ∀ z ∈ restK s.1 pu pl, lookD (dropKeys pu pl w.1) z = lookD w.1 z := by
    intro z hz
    rw [restK_eq_filter hn, List.mem_filter] at hz
    exact lookD_dropKeys hz.2 _
  unfold closeWit
  rcases closeP_some hcl with ⟨hT, rfl, hbit⟩ | ⟨hT, rfl⟩
  · rw [ite_eq_left hT]
    have hcol : colE a b E1 < 2 := by
      have h4 := hF.2.1
      dsimp only at h4
      by_contra hc
      have h5 : 2 ^ 2 ≤ 2 ^ colE a b E1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h6 : (4 : ℕ) ≤ 2 ^ colE a b E1 := by simpa using h5
      omega
    obtain ⟨-, dperm⟩ := doneCols_add (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hF.2.1) hcol hbit
    refine ⟨?_, keys_dropKeys hn hkeys pu pl, ?_⟩
    · refine WF_congr hF (fun z hz => ?_) (fun c hc => ?_)
      · unfold closeSg; rw [ite_eq_left hT]; exact hrest z hz
      · unfold closeDp; rw [ite_eq_left hT]
        exact dpOf_setDp hcol (mem_doneCols_lt hc)
    · intro c hc hnd
      dsimp only at hnd
      rw [dpOf_setDp hcol hc]
      have h1 : c ≠ colE a b E1 := fun e => hnd (dperm.mem_iff.mpr (by rw [e]; exact List.mem_cons_self))
      rw [ite_eq_right h1]
      exact hemp c hc (fun hm => hnd (dperm.mem_iff.mpr (List.mem_cons_of_mem _ hm)))
  · rw [ite_eq_right (by rw [hT]; simp)]
    have hT' : ¬ (isTerm a b E1 && isTerm a b E2) = true := by rw [hT]; simp
    refine ⟨?_, ?_, hemp⟩
    · refine WF_congr hF (fun z hz => ?_) (fun c _ => ?_)
      · unfold closeSg; rw [ite_eq_right hT', lookD_cons]
        by_cases hz' : z = mkP E1 E2
        · rw [ite_eq_left hz', ite_eq_left hz']
        · rw [ite_eq_right hz', ite_eq_right hz']
          have := (insSorted_perm _ _).mem_iff.mp hz
          rcases List.mem_cons.mp this with e | hm
          · exact absurd e hz'
          · exact hrest z hm
      · unfold closeDp; rw [ite_eq_right hT']
    · dsimp only
      rw [List.map_cons]
      exact ((keys_dropKeys hn hkeys pu pl).cons _).trans (insSorted_perm _ _).symm

end StepW

/-! ### Stages -/

theorem dedupKeyAux_sub : ∀ (seen : List St) (l : List (St × Wit)) (x : St × Wit),
    x ∈ dedupKeyAux seen l → x ∈ l
  | _, [], _, h => by simp [dedupKeyAux] at h
  | seen, y :: l, x, h => by
    unfold dedupKeyAux at h
    split_ifs at h
    · exact List.mem_cons_of_mem _ (dedupKeyAux_sub _ _ _ h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (dedupKeyAux_sub _ _ _ h)

theorem dedupKeyAux_fst : ∀ (seen : List St) (l : List (St × Wit)) (s : St),
    s ∈ (dedupKeyAux seen l).map Prod.fst ↔ s ∈ l.map Prod.fst ∧ s ∉ seen
  | _, [], _ => by simp [dedupKeyAux]
  | seen, y :: l, s => by
    unfold dedupKeyAux
    split_ifs with hy
    · rw [dedupKeyAux_fst seen l s, List.map_cons, List.mem_cons]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · exact absurd (h1 ▸ hy) h2
        · exact ⟨h1, h2⟩
    · rw [List.map_cons, List.mem_cons, dedupKeyAux_fst _ l s, List.map_cons, List.mem_cons, List.mem_cons]
      by_cases e : s = y.1
      · subst e; simp [hy]
      · simp [e]

theorem mem_dedupKey_fst {l : List (St × Wit)} {s : St} :
    s ∈ (dedupKey l).map Prod.fst ↔ s ∈ l.map Prod.fst := by
  unfold dedupKey; rw [dedupKeyAux_fst]; simp

theorem stepCellW_fst (J : Inst) (a b : ℕ) (e : Option ℕ) (r c : ℕ) (sw : St × Wit) :
    (stepCellW J a b e r c sw).map Prod.fst = stepCell a b e r c sw.1 := by
  unfold stepCellW
  rw [List.map_map]
  exact stepCellG_snd a b e r c sw.1

section Stages

variable {a b : ℕ} {J : Inst} {tm : List ((ℕ × ℕ) × ℕ)}

/-- **The states of the witness-carrying DP are those of `insideF`**, stage by stage. -/
theorem foldW_fst (n : ℕ) (s : St) :
    s ∈ ((List.range n).foldl (stageW J a b tm) [(([], 0), ([], ([], [])))]).map Prod.fst ↔
      s ∈ (List.range n).foldl (stageF a b tm) [([], 0)] := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    unfold stageW stageF stage
    rw [mem_dedupKey_fst, List.mem_filter, mem_normS, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨sw, hsw, rfl⟩
      rw [List.mem_filter, List.mem_flatMap] at hsw
      obtain ⟨⟨t, ht, hst⟩, hne⟩ := hsw
      refine ⟨⟨t.1, (ih t.1).mp (List.mem_map_of_mem ht), ?_⟩, hne⟩
      rw [← stepCellW_fst J]
      exact List.mem_map_of_mem hst
    · rintro ⟨⟨t, ht, hst⟩, hne⟩
      obtain ⟨tw, htw, rfl⟩ := List.mem_map.mp ((ih t).mpr ht)
      rw [← stepCellW_fst J] at hst
      obtain ⟨sw, hsw, rfl⟩ := List.mem_map.mp hst
      exact ⟨sw, List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨tw, htw, hsw⟩, hne⟩, rfl⟩

theorem mem_insideW_fst {s : St} : s ∈ (insideW J a b tm).map Prod.fst ↔ s ∈ insideF a b tm :=
  foldW_fst _ s

theorem WC_zero : WC a b J 0 (([], 0), ([], ([], []))) := by
  refine ⟨?_, List.Perm.refl _, fun col _ _ => by unfold dpOf; split_ifs <;> rfl⟩
  obtain ⟨sg, dp, h⟩ := (W_zero : W a b J 0 ([], 0))
  refine WF_congr h (by simp) (fun c hc => ?_)
  simp [doneCols, bitOf] at hc

/-- **Every entry of the witness-carrying DP satisfies the witness invariant.** -/
theorem insideW_WC (htm : ∀ y : Coord, y.1 < a → y.2 < b → termAt tm y = endCol J y) :
    ∀ sw ∈ insideW J a b tm, WC a b J (a * b) sw := by
  unfold insideW
  suffices h : ∀ n, n ≤ a * b →
      ∀ sw ∈ (List.range n).foldl (stageW J a b tm) [(([], 0), ([], ([], [])))], WC a b J n sw from
    h _ (le_refl _)
  intro n
  induction n with
  | zero => intro _ sw hs; rw [List.mem_singleton.mp hs]; exact WC_zero
  | succ n ih =>
    intro hn sw hs
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hs
    unfold stageW dedupKey at hs
    have hs := dedupKeyAux_sub _ _ _ hs
    rw [List.mem_filter, List.mem_flatMap] at hs
    obtain ⟨⟨t, ht, hst⟩, -⟩ := hs
    exact stepW_WC htm (by omega) (ih (by omega) t ht) hst

end Stages

/-! ### The solver is sound and complete -/

theorem solveDP_sound {J : Inst} {p q : List Coord} (h : solveDP J = some (p, q)) : IsSolution J p q := by
  unfold solveDP at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨sw, hf, hpq⟩ := h
  have hmem := List.mem_of_find?_eq_some hf
  have hs : sw.1 = (([], 3) : St) := by simpa using List.find?_some hf
  obtain ⟨⟨-, -, -, hdone, hnod, hcov⟩, -, -⟩ := insideW_WC (fun y _ _ => termAt_tmOf J y) sw hmem
  rw [hs] at hdone hnod hcov
  have hd : doneCols 3 = [0, 1] := by decide
  simp only [hd, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hdone
  obtain ⟨p0, p1⟩ := hdone
  simp only [ends2, ite_true, show (1 : ℕ) ≠ 0 by omega, ite_false] at p0 p1
  have e0 : dpOf sw.2.2 0 = p := by unfold dpOf; rw [hpq]; rfl
  have e1 : dpOf sw.2.2 1 = q := by unfold dpOf; rw [hpq]; rfl
  rw [e0] at p0
  rw [e1] at p1
  have ha : allOf (lookD sw.2.1) (dpOf sw.2.2) (([], 3) : St) = p ++ q := by
    simp [allOf, hd, e0, e1]
  rw [ha] at hnod hcov
  refine ⟨p0, p1, fun v hv hv' => List.disjoint_of_nodup_append hnod hv hv', fun v hv => ?_⟩
  exact List.mem_append.mp ((hcov v).mp (prI_all.mpr ⟨hv.1, hv.2⟩))

theorem solveDP_complete {J : Inst} (hwf : J.WellFormed) (hS : Solvable J) : (solveDP J).isSome := by
  have h := (dpAcceptF_iff hwf).mpr hS
  unfold dpAcceptF at h
  rw [List.contains_iff_mem, ← mem_insideW_fst (J := J)] at h
  obtain ⟨sw, hsw, hs⟩ := List.mem_map.mp h
  unfold solveDP
  rw [Option.isSome_map, List.find?_isSome]
  exact ⟨sw, hsw, by simp [hs]⟩

theorem isSolution_transpose {I : Inst} {p q : List Coord} (hS : IsSolution I p q) :
    IsSolution I.transpose (p.map Prod.swap) (q.map Prod.swap) := by
  obtain ⟨hp, hq, hd, hc⟩ := hS
  refine ⟨hp.swap, hq.swap, ?_, ?_⟩
  · intro v hv hv'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    obtain ⟨u', hu', he⟩ := List.mem_map.mp hv'
    exact hd u hu (Prod.swap_injective he ▸ hu')
  · intro v hv
    have hb : InBounds I.w I.h v.swap := by
      unfold InBounds at hv ⊢
      exact ⟨hv.2, hv.1⟩
    rcases hc v.swap hb with h | h
    · exact Or.inl (List.mem_map.mpr ⟨v.swap, h, Prod.swap_swap v⟩)
    · exact Or.inr (List.mem_map.mpr ⟨v.swap, h, Prod.swap_swap v⟩)

/-- **The solver is sound**: whatever it returns is a solution (no well-formedness needed). -/
theorem thinSolveW_sound {J : Inst} {p q : List Coord} (h : thinSolveW J = some (p, q)) :
    IsSolution J p q := by
  unfold thinSolveW at h
  split_ifs at h
  · exact solveDP_sound h
  · rw [Option.map_eq_some_iff] at h
    obtain ⟨⟨p', q'⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    have := isSolution_transpose (solveDP_sound h1)
    rwa [Inst.transpose_transpose] at this

/-- **The solver is complete**: a solvable well-formed instance gets a solution. -/
theorem thinSolveW_complete {J : Inst} (hwf : J.WellFormed) (hS : Solvable J) : (thinSolveW J).isSome := by
  unfold thinSolveW
  split_ifs
  · exact solveDP_complete hwf hS
  · rw [Option.isSome_map]
    exact solveDP_complete (wf_transpose hwf) (solvable_transpose hS)

/-- **The solver decides solvability.** -/
theorem thinSolveW_isSome_iff {J : Inst} (hwf : J.WellFormed) : (thinSolveW J).isSome ↔ Solvable J := by
  refine ⟨fun h => ?_, thinSolveW_complete hwf⟩
  obtain ⟨⟨p, q⟩, hpq⟩ := Option.isSome_iff_exists.mp h
  exact ⟨p, q, thinSolveW_sound hpq⟩

end ZZN.Thin

-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.WinInside

/-!
# Window certificates: one DP step, as a computation

The two path sides of the current cell, by kind; `stepCell` then yields the state closing the
merged run.
-/

namespace ZZN.Win

open GridHam

/-- How a path side of the current cell looks: the path ends here; a processed run attached from
above or from the left (its code and its far end); or an unprocessed neighbour below or right. -/
inductive Kind where
  | term
  | up (c o : ℕ)
  | lft (c o : ℕ)
  | dn
  | rt
  deriving DecidableEq

def Kind.val (a b x1 x2 col : ℕ) : Kind → ℕ
  | term => termE a b col
  | up _ o => o
  | lft _ o => o
  | dn => if x1 + 1 < a then x2 else exitE b (a + (b - 1 - x2))
  | rt => if x2 + 1 < b then b else exitE b x1

def Kind.upC : Kind → Option ℕ
  | up c _ => some c
  | _ => none

def Kind.lftC : Kind → Option ℕ
  | lft c _ => some c
  | _ => none

/-- The pieces left after removing the attached runs, as `stepCell` computes them. -/
def restK (ps : List ℕ) (pu pl : Option ℕ) : List ℕ :=
  if pu.isSome then (if pl.isSome then (ps.erase (pu.getD 0)).erase (pl.getD 0) else ps.erase (pu.getD 0))
  else (if pl.isSome then ps.erase (pl.getD 0) else ps)

theorem closeP_comm (a b x y : ℕ) (rest : List ℕ) (dn : ℕ) :
    closeP a b x y rest dn = closeP a b y x rest dn := by
  unfold closeP
  rw [mkP_comm x y, Bool.and_comm]
  by_cases h : (isTerm a b x && isTerm a b y) = true
  · rw [Bool.and_comm] at h
    simp only [h, ↓reduceIte, bne_iff_ne, ne_eq]
    by_cases e : colE a b x = colE a b y
    · rw [e]
    · simp [e, Ne.symm e]
  · rw [Bool.and_comm] at h
    simp only [h, Bool.false_eq_true, ↓reduceIte]

/-- **The DP step as a computation.** -/
theorem stepCell_kinds {a b x1 x2 col : ℕ} {e : Option ℕ} {s : St} {kP kN : Kind}
    (hU : x1 ≠ 0 → s.1.find? (hasEnd x2) = (kP.upC <|> kN.upC))
    (hU0 : x1 = 0 → kP.upC = none ∧ kN.upC = none)
    (hL : x2 ≠ 0 → s.1.find? (hasEnd b) = (kP.lftC <|> kN.lftC))
    (hL0 : x2 = 0 → kP.lftC = none ∧ kN.lftC = none)
    (hoU : ∀ c o, (kP = .up c o ∨ kN = .up c o) → other x2 c = o)
    (hoL : ∀ c o, (kP = .lft c o ∨ kN = .lft c o) → other b c = o)
    (he : e = if kP = .term ∨ kN = .term then some col else none)
    (d1 : ¬ (kP = .term ∧ kN = .term)) (d2 : ¬ (kP.upC.isSome ∧ kN.upC.isSome))
    (d3 : ¬ (kP.lftC.isSome ∧ kN.lftC.isSome)) (d4 : ¬ (kP = .dn ∧ kN = .dn))
    (d5 : ¬ (kP = .rt ∧ kN = .rt))
    (d6 : ∀ c c', (kP.upC = some c ∨ kN.upC = some c) → (kP.lftC = some c' ∨ kN.lftC = some c') → c ≠ c')
    {s' : St}
    (hc : closeP a b (kP.val a b x1 x2 col) (kN.val a b x1 x2 col)
      (restK s.1 (kP.upC <|> kN.upC) (kP.lftC <|> kN.lftC)) s.2 = some s') :
    s' ∈ stepCell a b e x1 x2 s := by
  have hc' := hc
  rw [closeP_comm] at hc'
  have eU : (if x1 = 0 then none else s.1.find? (hasEnd x2)) = (kP.upC <|> kN.upC) := by
    by_cases h : x1 = 0
    · rw [ite_eq_left h, (hU0 h).1, (hU0 h).2]; rfl
    · rw [ite_eq_right h, hU h]
  have eL : (if x2 = 0 then none else s.1.find? (hasEnd b)) = (kP.lftC <|> kN.lftC) := by
    by_cases h : x2 = 0
    · rw [ite_eq_left h, (hL0 h).1, (hL0 h).2]; rfl
    · rw [ite_eq_right h, hL h]
  unfold stepCell
  dsimp only
  rw [eU, eL]
  unfold restK at hc hc'
  subst he
  cases kP <;> cases kN <;>
    simp_all [Kind.upC, Kind.lftC, Kind.val, List.mem_filterMap]


/-! ### Helpers -/

theorem insSorted_perm (x : ℕ) : ∀ l : List ℕ, (insSorted x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: l => by
    unfold insSorted
    split_ifs
    · exact List.Perm.refl _
    · exact ((insSorted_perm x l).cons y).trans (List.Perm.swap x y l)

theorem restK_mem {ps : List ℕ} (hn : ps.Nodup) {pu pl : Option ℕ}
    (hne : ∀ c c', pu = some c → pl = some c' → c ≠ c') (z : ℕ) :
    z ∈ restK ps pu pl ↔ z ∈ ps ∧ pu ≠ some z ∧ pl ≠ some z := by
  unfold restK
  cases pu with
  | none =>
    cases pl with
    | none => simp
    | some c' => simp only [Option.isSome_some, Option.isSome_none, ↓reduceIte, Option.getD_some,
        List.Nodup.mem_erase_iff hn, ne_eq, reduceCtorEq, not_false_eq_true, Option.some.injEq, true_and]
                 constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨?_, ?_⟩ <;> (first | assumption | omega)
  | some c =>
    cases pl with
    | none => simp only [Option.isSome_some, Option.isSome_none, ↓reduceIte, Option.getD_some,
        List.Nodup.mem_erase_iff hn, ne_eq, Option.some.injEq, reduceCtorEq, not_false_eq_true, and_true]
              constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨?_, ?_⟩ <;> (first | assumption | omega)
    | some c' =>
      simp only [Option.isSome_some, ↓reduceIte, Option.getD_some, List.Nodup.mem_erase_iff (hn.erase _),
        List.Nodup.mem_erase_iff hn, ne_eq, Option.some.injEq]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h3, fun e => h2 e.symm, fun e => h1 e.symm⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨fun e => h3 e.symm, fun e => h2 e.symm, h1⟩

theorem restK_nodup {ps : List ℕ} (hn : ps.Nodup) (pu pl : Option ℕ) : (restK ps pu pl).Nodup := by
  unfold restK; split_ifs
  · exact (hn.erase _).erase _
  · exact hn.erase _
  · exact hn.erase _
  · exact hn

theorem find_unique {l : List ℕ} {f : ℕ → Bool} {z0 : ℕ} (hz : z0 ∈ l) (hf : f z0 = true)
    (hu : ∀ z ∈ l, f z = true → z = z0) : l.find? f = some z0 := by
  cases hw : l.find? f with
  | none => rw [List.find?_eq_none] at hw; exact absurd hf (hw z0 hz)
  | some w => rw [hu w (List.mem_of_find?_eq_some hw) (List.find?_some hw)]

theorem find_none {l : List ℕ} {f : ℕ → Bool} (hu : ∀ z ∈ l, f z ≠ true) : l.find? f = none :=
  List.find?_eq_none.mpr fun z hz => by simpa using hu z hz

/-! ### The DP step is sound -/

theorem isRun_congr {P Q : Coord → Prop} (h : ∀ y, P y ↔ Q y) {L : List Coord} {st en : ℕ} :
    IsRun P L st en ↔ IsRun Q L st en := by
  have : P = Q := funext fun y => propext (h y)
  subst this; rfl

theorem orElse_some {x y : Option ℕ} {z : ℕ} : (x <|> y) = some z ↔ x = some z ∨ (x = none ∧ y = some z) := by
  cases x <;> simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse]

theorem doneMask_succ {a b i : ℕ} {p q L M : List Coord} {col col' : ℕ} (hL : PathC p q L col)
    (hM : PathC p q M col') (hLM : L ≠ M) (hnot : ¬ ∀ y ∈ L, prI a b i y)
    (hMeq : (∀ y ∈ M, prI a b (i + 1) y) ↔ (∀ y ∈ M, prI a b i y)) :
    doneMask a b (i + 1) p q = doneMask a b i p q + (if ∀ y ∈ L, prI a b (i + 1) y then 2 ^ col else 0) := by
  unfold doneMask
  rcases hL with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hM with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd rfl hLM
  · rw [ite_eq_right hnot, if_congr hMeq rfl rfl]; split_ifs <;> simp
  · rw [ite_eq_right hnot, if_congr hMeq rfl rfl]; split_ifs <;> simp
  · exact absurd rfl hLM

section Core

variable {a b : ℕ} {J : Inst} {p q : List Coord}

set_option maxHeartbeats 1000000 in
theorem step_core (ha : a ≤ 8) (hb : b ≤ 8) (hS : IsSolution J p q) {i : ℕ} (hi : i < a * b)
    {x1 x2 : ℕ} (hx : cell b i = (x1, x2))
    {L M : List Coord} {col col' : ℕ} (hL : PathC p q L col) (hM : PathC p q M col')
    (hxL : (x1, x2) ∈ L) (hxM : (x1, x2) ∉ M)
    (hcov : ∀ L'' c'', PathC p q L'' c'' → (L'' = L ∧ c'' = col) ∨ (L'' = M ∧ c'' = col'))
    (hlen : 2 ≤ L.length)
    {e : Option ℕ}
    (he : e = if (L.idxOf (x1, x2) = 0 ∨ L.idxOf (x1, x2) + 1 = L.length) then some col else none)
    {s : St} (hs : Inv a b i p q s) :
    ∃ s' ∈ stepCell a b e x1 x2 s, Inv a b (i + 1) p q s' := by
  obtain ⟨c1, c2, c3⟩ := cell_spec hi
  rw [hx] at c1 c2 c3
  dsimp only at c1 c2 c3
  have hlex : ∀ y : Coord, prI a b i y ↔ y.1 < a ∧ y.2 < b ∧ (y.1 < x1 ∨ (y.1 = x1 ∧ y.2 < x2)) := by
    intro y; rw [prI_lex hi, hx]
  obtain ⟨nL, cL, colL⟩ := pathC_facts hS hL
  obtain ⟨nM, cM, colM⟩ := pathC_facts hS hM
  obtain ⟨j0, hj0d⟩ : ∃ j0, j0 = L.idxOf (x1, x2) := ⟨_, rfl⟩
  rw [← hj0d] at he
  have hj0 : j0 < L.length := by rw [hj0d]; exact List.idxOf_lt_length_iff.mpr hxL
  have hnx : nth L j0 = (x1, x2) := by subst hj0d; rw [nth_eq hj0]; exact List.getElem_idxOf _
  have hxP : ¬ prI a b i (nth L j0) := by rw [hnx, hlex]; dsimp only; omega
  have eP : ∀ y, prI a b (i + 1) y ↔ prI a b i y ∨ y = nth L j0 := by
    intro y; rw [prI_succ hi, hx, hnx]
  have hxP' : prI a b (i + 1) (x1, x2) := (eP _).mpr (Or.inr hnx.symm)
  -- the merged run
  obtain ⟨sM, hsM⟩ := leftOK_exists (P := prI a b i) hj0 hxP
  obtain ⟨eM, heM⟩ := rightOK_exists (P := prI a b i) hj0 hxP
  have hmerge : IsRun (prI a b (i + 1)) L sM eM := (isRun_congr eP).mpr (run_merge nL hj0 hsM heM)
  -- neighbours along the path
  have adjP : 0 < j0 → Adjacent (x1, x2) (nth L (j0 - 1)) := fun h => by
    have := chain_nth cL (j := j0 - 1) (by omega)
    rw [show j0 - 1 + 1 = j0 by omega, hnx] at this; exact adj_symm this
  have adjN : j0 + 1 < L.length → Adjacent (x1, x2) (nth L (j0 + 1)) := fun h => by
    have := chain_nth cL (j := j0) h; rw [hnx] at this; exact this
  have pn : 0 < j0 → j0 + 1 < L.length → nth L (j0 - 1) ≠ nth L (j0 + 1) := fun h h' e =>
    absurd (nth_inj nL (by omega) h' e) (by omega)
  have proc := fun {y : Coord} (h : Adjacent (x1, x2) y) => nb_proc hlex c1 c2 (y := y) h
  have unproc : ∀ {y : Coord}, Adjacent (x1, x2) y → ¬ prI a b i y → y ≠ (x1, x2) →
      y = (x1 + 1, x2) ∨ y = (x1, x2 + 1) := fun {y} h hy hne =>
    bd_dir hxP' (fun c => ((eP y).mp c).elim hy (fun e => hne (e.trans hnx))) h
  have neX : ∀ k, k < L.length → k ≠ j0 → nth L k ≠ (x1, x2) := fun k hk hne e =>
    hne (nth_inj nL hk hj0 (e.trans hnx.symm))
  -- the sides
  have sideL : (0 < j0 ∧ prI a b i (nth L (j0 - 1)) ∧ sM < j0 ∧ IsRun (prI a b i) L sM (j0 - 1)) ∨
      (sM = j0 ∧ (j0 = 0 ∨ ¬ prI a b i (nth L (j0 - 1)))) := by
    rcases hsM with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl ⟨by omega, h2.all (j0 - 1) (by omega) (le_refl _), h1, h2⟩
  have sideR : (j0 + 1 < L.length ∧ prI a b i (nth L (j0 + 1)) ∧ j0 < eM ∧ IsRun (prI a b i) L (j0 + 1) eM) ∨
      (eM = j0 ∧ (j0 + 1 = L.length ∨ ¬ prI a b i (nth L (j0 + 1)))) := by
    rcases heM with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl ⟨by have := h2.lt; omega, h2.all (j0 + 1) (le_refl _) (by omega), h1, h2⟩
  -- codes of the attached runs
  obtain ⟨cA, hcA⟩ : ∃ c, c = runCode a b col L sM (j0 - 1) := ⟨_, rfl⟩
  obtain ⟨cB, hcB⟩ : ∃ c, c = runCode a b col L (j0 + 1) eM := ⟨_, rfl⟩
  have endA : 0 < j0 → endR a b col L (j0 - 1) = desc a b (nth L (j0 - 1)) (x1, x2) := fun h => by
    unfold endR; rw [ite_eq_right (by omega), show j0 - 1 + 1 = j0 by omega, hnx]
  have endB : j0 + 1 < L.length → endL a b col L (j0 + 1) = desc a b (nth L (j0 + 1)) (x1, x2) := fun h => by
    unfold endL; rw [ite_eq_right (by omega), show j0 + 1 - 1 = j0 by omega, hnx]
  /- Any piece with the plug code of `x`'s upper or left neighbour `u` is the run just before or
  just after `x` on its path. -/
  have attach : ∀ z ∈ s.1, ∀ (ee : ℕ) (u : Coord),
      ((ee = x2 ∧ 0 < x1 ∧ u = (x1 - 1, x2)) ∨ (ee = b ∧ 0 < x2 ∧ u = (x1, x2 - 1))) →
      hasEnd ee z = true →
      (0 < j0 ∧ nth L (j0 - 1) = u ∧ prI a b i u ∧ z = cA) ∨
        (j0 + 1 < L.length ∧ nth L (j0 + 1) = u ∧ prI a b i u ∧ z = cB) := by
    intro z hz ee u hee hh
    obtain ⟨L'', col'', st, en, hp, hr, hinc, rfl⟩ := (hs.2.1 z).mp hz
    obtain ⟨-, cL'', colL''⟩ := pathC_facts hS hp
    obtain ⟨l1, l2⟩ := end_lt32 ha hb colL'' cL'' hr
    unfold runCode at hh
    rw [hasEnd_mkP l1 l2] at hh
    have eeb : ee < a + 2 * b + 1 := by rcases hee with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> omega
    have into : ∀ w v, prI a b i w → ¬ prI a b i v → Adjacent w v → desc a b w v = ee →
        w = u ∧ v = (x1, x2) := by
      intro w v hw hv hwv hd
      rcases hee with ⟨rfl, h0, rfl⟩ | ⟨rfl, h0, rfl⟩
      · obtain ⟨-, e1, e2⟩ := bd_plug hlex c2 hw hv hwv hd; exact ⟨e1, e2⟩
      · obtain ⟨-, e1, e2⟩ := bd_left hlex hw hv hwv hd; exact ⟨e1, e2⟩
    have hlt := hr.lt
    have hle := hr.le
    rcases hh with hh | hh
    · rcases endL_cases cL'' hr col'' with ⟨-, d⟩ | ⟨h0, d, -⟩
      · rw [d] at hh; unfold termE at hh; omega
      obtain ⟨b1, b2, b3⟩ := endL_bd cL'' hr h0
      obtain ⟨e1, e2⟩ := into _ _ b1 b2 b3 (by rw [← d, hh])
      have xm : (x1, x2) ∈ L'' := by rw [← e2]; exact nth_mem (by omega)
      obtain ⟨rfl, rfl⟩ := pathC_same hS hp hL xm hxL
      have := nth_inj nL (by omega) hj0 (e2.trans hnx.symm)
      have hst : st = j0 + 1 := by omega
      subst hst
      right
      rcases sideR with ⟨r1, r2, r3, r4⟩ | ⟨r1, r2⟩
      · obtain ⟨-, u2⟩ := run_unique hr r4 (le_refl _) hle (le_refl _) (by omega)
        subst u2
        exact ⟨r1, e1, by rw [← e1]; exact r2, hcB.symm⟩
      · exfalso
        rcases r2 with r2 | r2
        · omega
        · exact r2 (hr.all (j0 + 1) (le_refl _) hle)
    · rcases endR_cases cL'' hr col'' with ⟨-, d⟩ | ⟨h0, d, -⟩
      · rw [d] at hh; unfold termE at hh; omega
      obtain ⟨b1, b2, b3⟩ := endR_bd cL'' hr h0
      obtain ⟨e1, e2⟩ := into _ _ b1 b2 b3 (by rw [← d, hh])
      have xm : (x1, x2) ∈ L'' := by rw [← e2]; exact nth_mem (by omega)
      obtain ⟨rfl, rfl⟩ := pathC_same hS hp hL xm hxL
      have := nth_inj nL (by omega) hj0 (e2.trans hnx.symm)
      have hen : en = j0 - 1 := by omega
      subst hen
      left
      rcases sideL with ⟨r1, r2, r3, r4⟩ | ⟨r1, r2⟩
      · obtain ⟨u1, -⟩ := run_unique hr r4 hle (le_refl _) (by omega) (le_refl _)
        subst u1
        exact ⟨r1, e1, by rw [← e1]; exact r2, hcA.symm⟩
      · exfalso
        rcases r2 with r2 | r2
        · omega
        · exact r2 (hr.all (j0 - 1) hle (le_refl _))
  -- the attached runs are pieces, ending at `x`
  have pieceA : 0 < j0 → prI a b i (nth L (j0 - 1)) →
      cA ∈ s.1 ∧ hasEnd (desc a b (nth L (j0 - 1)) (x1, x2)) cA = true ∧
      other (desc a b (nth L (j0 - 1)) (x1, x2)) cA = endL a b col L sM := fun h0 hp => by
    rcases sideL with ⟨-, -, r3, r4⟩ | ⟨r1, r2⟩
    · obtain ⟨l1, l2⟩ := end_lt32 ha hb colL cL r4
      refine ⟨(hs.2.1 cA).mpr ⟨L, col, sM, j0 - 1, hL, r4, fun c => by omega, hcA⟩, ?_, ?_⟩
      · rw [hcA]; unfold runCode; rw [hasEnd_mkP l1 l2]; exact Or.inr (endA h0)
      · rw [hcA]; unfold runCode; rw [← endA h0]; exact other_mkP_r l1 l2
    · exfalso; rcases r2 with r2 | r2
      · omega
      · exact r2 hp
  have pieceB : j0 + 1 < L.length → prI a b i (nth L (j0 + 1)) →
      cB ∈ s.1 ∧ hasEnd (desc a b (nth L (j0 + 1)) (x1, x2)) cB = true ∧
      other (desc a b (nth L (j0 + 1)) (x1, x2)) cB = endR a b col L eM := fun h0 hp => by
    rcases sideR with ⟨-, -, r3, r4⟩ | ⟨r1, r2⟩
    · obtain ⟨l1, l2⟩ := end_lt32 ha hb colL cL r4
      refine ⟨(hs.2.1 cB).mpr ⟨L, col, j0 + 1, eM, hL, r4, fun c => by omega, hcB⟩, ?_, ?_⟩
      · rw [hcB]; unfold runCode; rw [hasEnd_mkP l1 l2]; exact Or.inl (endB h0)
      · rw [hcB]; unfold runCode; rw [← endB h0]; exact other_mkP_l l1 l2
    · exfalso; rcases r2 with r2 | r2
      · omega
      · exact r2 hp
  -- the two kinds
  obtain ⟨kP, hkP⟩ : ∃ k : Kind, k = (if j0 = 0 then Kind.term
      else if prI a b i (nth L (j0 - 1)) then
        (if nth L (j0 - 1) = (x1 - 1, x2) then Kind.up cA (endL a b col L sM)
          else Kind.lft cA (endL a b col L sM))
      else (if nth L (j0 - 1) = (x1 + 1, x2) then Kind.dn else Kind.rt)) := ⟨_, rfl⟩
  obtain ⟨kN, hkN⟩ : ∃ k : Kind, k = (if j0 + 1 = L.length then Kind.term
      else if prI a b i (nth L (j0 + 1)) then
        (if nth L (j0 + 1) = (x1 - 1, x2) then Kind.up cB (endR a b col L eM)
          else Kind.lft cB (endR a b col L eM))
      else (if nth L (j0 + 1) = (x1 + 1, x2) then Kind.dn else Kind.rt)) := ⟨_, rfl⟩
  have vP : kP.val a b x1 x2 col = endL a b col L sM := by
    rw [hkP]
    by_cases h0 : j0 = 0
    · rw [ite_eq_left h0]
      have : sM = 0 := by rcases sideL with ⟨r1, -⟩ | ⟨r1, -⟩ <;> omega
      rw [this]; unfold endL; simp [Kind.val]
    rw [ite_eq_right h0]
    have ad := adjP (by omega)
    by_cases hp : prI a b i (nth L (j0 - 1))
    · rw [ite_eq_left hp]; split_ifs <;> rfl
    · rw [ite_eq_right hp]
      have : sM = j0 := by
        rcases sideL with ⟨-, r2, -⟩ | ⟨r1, -⟩
        · exact absurd r2 hp
        · exact r1
      rw [this]
      have endj : endL a b col L j0 = desc a b (x1, x2) (nth L (j0 - 1)) := by
        unfold endL; rw [ite_eq_right h0, hnx]
      rw [endj]
      rcases unproc ad hp (neX _ (by omega) (by omega)) with e | e
      · rw [ite_eq_left e, e, desc_down]; simp only [Kind.val]
      · have : ¬ nth L (j0 - 1) = (x1 + 1, x2) := by rw [e]; simp
        rw [ite_eq_right this, e, desc_right]; simp only [Kind.val]
  have vN : kN.val a b x1 x2 col = endR a b col L eM := by
    rw [hkN]
    by_cases h0 : j0 + 1 = L.length
    · rw [ite_eq_left h0]
      have : eM = j0 := by rcases sideR with ⟨r1, -⟩ | ⟨r1, -⟩ <;> omega
      rw [this]; unfold endR; simp [Kind.val, h0]
    rw [ite_eq_right h0]
    have ad := adjN (by omega)
    by_cases hp : prI a b i (nth L (j0 + 1))
    · rw [ite_eq_left hp]; split_ifs <;> rfl
    · rw [ite_eq_right hp]
      have : eM = j0 := by
        rcases sideR with ⟨-, r2, -⟩ | ⟨r1, -⟩
        · exact absurd r2 hp
        · exact r1
      rw [this]
      have endj : endR a b col L j0 = desc a b (x1, x2) (nth L (j0 + 1)) := by
        unfold endR; rw [ite_eq_right h0, hnx]
      rw [endj]
      rcases unproc ad hp (neX _ (by omega) (by omega)) with e | e
      · rw [ite_eq_left e, e, desc_down]; simp only [Kind.val]
      · have : ¬ nth L (j0 + 1) = (x1 + 1, x2) := by rw [e]; simp
        rw [ite_eq_right this, e, desc_right]; simp only [Kind.val]
  -- the plug lookups
  have uP : kP.upC = if (0 < j0 ∧ prI a b i (nth L (j0 - 1)) ∧ nth L (j0 - 1) = (x1 - 1, x2))
      then some cA else none := by
    rw [hkP]
    by_cases h0 : j0 = 0
    · rw [ite_eq_left h0, ite_eq_right (by omega)]; rfl
    · rw [ite_eq_right h0]
      by_cases hp : prI a b i (nth L (j0 - 1))
      · rw [ite_eq_left hp]
        by_cases hu : nth L (j0 - 1) = (x1 - 1, x2)
        · rw [ite_eq_left hu, ite_eq_left ⟨by omega, hp, hu⟩]; rfl
        · rw [ite_eq_right hu, ite_eq_right (fun h => hu h.2.2)]; rfl
      · rw [ite_eq_right hp, ite_eq_right (show ¬ (0 < j0 ∧ prI a b i (nth L (j0 - 1)) ∧ nth L (j0 - 1) = (x1 - 1, x2)) from fun h => hp h.2.1)]; split_ifs <;> rfl
  have uN : kN.upC = if (j0 + 1 < L.length ∧ prI a b i (nth L (j0 + 1)) ∧ nth L (j0 + 1) = (x1 - 1, x2))
      then some cB else none := by
    rw [hkN]
    by_cases h0 : j0 + 1 = L.length
    · rw [ite_eq_left h0, ite_eq_right (by omega)]; rfl
    · rw [ite_eq_right h0]
      by_cases hp : prI a b i (nth L (j0 + 1))
      · rw [ite_eq_left hp]
        by_cases hu : nth L (j0 + 1) = (x1 - 1, x2)
        · rw [ite_eq_left hu, ite_eq_left ⟨by omega, hp, hu⟩]; rfl
        · rw [ite_eq_right hu, ite_eq_right (fun h => hu h.2.2)]; rfl
      · rw [ite_eq_right hp, ite_eq_right (show ¬ (j0 + 1 < L.length ∧ prI a b i (nth L (j0 + 1)) ∧ nth L (j0 + 1) = (x1 - 1, x2)) from fun h => hp h.2.1)]; split_ifs <;> rfl
  have lP : kP.lftC = if (0 < j0 ∧ prI a b i (nth L (j0 - 1)) ∧ ¬ nth L (j0 - 1) = (x1 - 1, x2))
      then some cA else none := by
    rw [hkP]
    by_cases h0 : j0 = 0
    · rw [ite_eq_left h0, ite_eq_right (by omega)]; rfl
    · rw [ite_eq_right h0]
      by_cases hp : prI a b i (nth L (j0 - 1))
      · rw [ite_eq_left hp]
        by_cases hu : nth L (j0 - 1) = (x1 - 1, x2)
        · rw [ite_eq_left hu, ite_eq_right (fun h => h.2.2 hu)]; rfl
        · rw [ite_eq_right hu, ite_eq_left ⟨by omega, hp, hu⟩]; rfl
      · rw [ite_eq_right hp, ite_eq_right (show ¬ (0 < j0 ∧ prI a b i (nth L (j0 - 1)) ∧ ¬ nth L (j0 - 1) = (x1 - 1, x2)) from fun h => hp h.2.1)]; split_ifs <;> rfl
  have lN : kN.lftC = if (j0 + 1 < L.length ∧ prI a b i (nth L (j0 + 1)) ∧ ¬ nth L (j0 + 1) = (x1 - 1, x2))
      then some cB else none := by
    rw [hkN]
    by_cases h0 : j0 + 1 = L.length
    · rw [ite_eq_left h0, ite_eq_right (by omega)]; rfl
    · rw [ite_eq_right h0]
      by_cases hp : prI a b i (nth L (j0 + 1))
      · rw [ite_eq_left hp]
        by_cases hu : nth L (j0 + 1) = (x1 - 1, x2)
        · rw [ite_eq_left hu, ite_eq_right (fun h => h.2.2 hu)]; rfl
        · rw [ite_eq_right hu, ite_eq_left ⟨by omega, hp, hu⟩]; rfl
      · rw [ite_eq_right hp, ite_eq_right (show ¬ (j0 + 1 < L.length ∧ prI a b i (nth L (j0 + 1)) ∧ ¬ nth L (j0 + 1) = (x1 - 1, x2)) from fun h => hp h.2.1)]; split_ifs <;> rfl
  -- a processed neighbour that is not above is to the left
  have leftOf : ∀ {y : Coord}, Adjacent (x1, x2) y → prI a b i y → ¬ y = (x1 - 1, x2) →
      0 < x2 ∧ y = (x1, x2 - 1) := fun {y} h hp hu => by
    rcases (proc h).mp hp with ⟨-, e⟩ | e
    · exact absurd e hu
    · exact e
  have UL : ∀ {y : Coord}, y = (x1, x2 - 1) → 0 < x2 → ¬ y = (x1 - 1, x2) := by
    rintro y rfl h0 e; simp only [Prod.mk.injEq] at e; omega
  have hU : x1 ≠ 0 → s.1.find? (hasEnd x2) = (kP.upC <|> kN.upC) := by
    intro hx0
    rw [uP, uN]
    by_cases A : 0 < j0 ∧ prI a b i (nth L (j0 - 1)) ∧ nth L (j0 - 1) = (x1 - 1, x2)
    · rw [ite_eq_left A]
      obtain ⟨m, h, -⟩ := pieceA A.1 A.2.1
      rw [A.2.2, desc_up c1 (by omega)] at h
      apply find_unique m h
      intro z hz hz'
      rcases attach z hz x2 _ (Or.inl ⟨rfl, by omega, rfl⟩) hz' with ⟨-, -, -, rfl⟩ | ⟨g1, g2, -, -⟩
      · rfl
      · exact absurd (A.2.2.trans g2.symm) (pn A.1 g1)
    · rw [ite_eq_right A]
      by_cases B : j0 + 1 < L.length ∧ prI a b i (nth L (j0 + 1)) ∧ nth L (j0 + 1) = (x1 - 1, x2)
      · rw [ite_eq_left B]
        obtain ⟨m, h, -⟩ := pieceB B.1 B.2.1
        rw [B.2.2, desc_up c1 (by omega)] at h
        apply find_unique m h
        intro z hz hz'
        rcases attach z hz x2 _ (Or.inl ⟨rfl, by omega, rfl⟩) hz' with ⟨g1, g2, g3, -⟩ | ⟨-, -, -, rfl⟩
        · exact absurd ⟨g1, g2 ▸ g3, g2⟩ A
        · rfl
      · rw [ite_eq_right B]
        apply find_none
        intro z hz hz'
        rcases attach z hz x2 _ (Or.inl ⟨rfl, by omega, rfl⟩) hz' with ⟨g1, g2, g3, -⟩ | ⟨g1, g2, g3, -⟩
        · exact A ⟨g1, g2 ▸ g3, g2⟩
        · exact B ⟨g1, g2 ▸ g3, g2⟩
  have hU0 : x1 = 0 → kP.upC = none ∧ kN.upC = none := by
    intro hx0
    have e : ((x1 - 1, x2) : Coord) = (x1, x2) := by rw [hx0]
    rw [uP, uN, e]
    exact ⟨ite_eq_right (fun h => neX _ (by omega) (by omega) h.2.2),
      ite_eq_right (fun h => neX _ h.1 (by omega) h.2.2)⟩
  have hLk : x2 ≠ 0 → s.1.find? (hasEnd b) = (kP.lftC <|> kN.lftC) := by
    intro hx0
    rw [lP, lN]
    by_cases A : 0 < j0 ∧ prI a b i (nth L (j0 - 1)) ∧ ¬ nth L (j0 - 1) = (x1 - 1, x2)
    · rw [ite_eq_left A]
      obtain ⟨-, e⟩ := leftOf (adjP A.1) A.2.1 A.2.2
      obtain ⟨m, h, -⟩ := pieceA A.1 A.2.1
      rw [e, desc_lft c2 (by omega)] at h
      apply find_unique m h
      intro z hz hz'
      rcases attach z hz b _ (Or.inr ⟨rfl, by omega, rfl⟩) hz' with ⟨-, -, -, rfl⟩ | ⟨g1, g2, -, -⟩
      · rfl
      · exact absurd (e.trans g2.symm) (pn A.1 g1)
    · rw [ite_eq_right A]
      by_cases B : j0 + 1 < L.length ∧ prI a b i (nth L (j0 + 1)) ∧ ¬ nth L (j0 + 1) = (x1 - 1, x2)
      · rw [ite_eq_left B]
        obtain ⟨-, e⟩ := leftOf (adjN B.1) B.2.1 B.2.2
        obtain ⟨m, h, -⟩ := pieceB B.1 B.2.1
        rw [e, desc_lft c2 (by omega)] at h
        apply find_unique m h
        intro z hz hz'
        rcases attach z hz b _ (Or.inr ⟨rfl, by omega, rfl⟩) hz' with ⟨g1, g2, g3, -⟩ | ⟨-, -, -, rfl⟩
        · exact absurd ⟨g1, g2 ▸ g3, UL g2 (by omega)⟩ A
        · rfl
      · rw [ite_eq_right B]
        apply find_none
        intro z hz hz'
        rcases attach z hz b _ (Or.inr ⟨rfl, by omega, rfl⟩) hz' with ⟨g1, g2, g3, -⟩ | ⟨g1, g2, g3, -⟩
        · exact A ⟨g1, g2 ▸ g3, UL g2 (by omega)⟩
        · exact B ⟨g1, g2 ▸ g3, UL g2 (by omega)⟩
  have hL0 : x2 = 0 → kP.lftC = none ∧ kN.lftC = none := by
    intro hx0
    rw [lP, lN]
    refine ⟨ite_eq_right (fun h => ?_), ite_eq_right (fun h => ?_)⟩
    · have := leftOf (adjP h.1) h.2.1 h.2.2; omega
    · have := leftOf (adjN h.1) h.2.1 h.2.2; omega
  have upPos : ∀ {y : Coord}, Adjacent (x1, x2) y → prI a b i y → y = (x1 - 1, x2) → 0 < x1 :=
    fun {y} h hp hu => by
      rcases (proc h).mp hp with ⟨h0, -⟩ | ⟨h0, e⟩
      · exact h0
      · exact absurd hu (UL e h0)
  have hoU : ∀ c o, (kP = .up c o ∨ kN = .up c o) → other x2 c = o := by
    rintro c o (h | h)
    · rw [hkP] at h
      split_ifs at h with h0 hp hu hd; simp only [Kind.up.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨-, -, ho⟩ := pieceA (by omega) hp
      rw [hu, desc_up c1 (upPos (adjP (by omega)) hp hu)] at ho
      exact ho
    · rw [hkN] at h
      split_ifs at h with h0 hp hu hd; simp only [Kind.up.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨-, -, ho⟩ := pieceB (by omega) hp
      rw [hu, desc_up c1 (upPos (adjN (by omega)) hp hu)] at ho
      exact ho
  have hoL : ∀ c o, (kP = .lft c o ∨ kN = .lft c o) → other b c = o := by
    rintro c o (h | h)
    · rw [hkP] at h
      split_ifs at h with h0 hp hu hd; simp only [Kind.lft.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨-, -, ho⟩ := pieceA (by omega) hp
      obtain ⟨g0, ge⟩ := leftOf (adjP (by omega)) hp hu
      rw [ge, desc_lft c2 g0] at ho
      exact ho
    · rw [hkN] at h
      split_ifs at h with h0 hp hu hd; simp only [Kind.lft.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨-, -, ho⟩ := pieceB (by omega) hp
      obtain ⟨g0, ge⟩ := leftOf (adjN (by omega)) hp hu
      rw [ge, desc_lft c2 g0] at ho
      exact ho
  have tP : kP = .term ↔ j0 = 0 := by
    rw [hkP]
    by_cases h0 : j0 = 0
    · rw [ite_eq_left h0]; exact ⟨fun _ => h0, fun _ => rfl⟩
    · rw [ite_eq_right h0]; refine ⟨fun h => ?_, fun h => absurd h h0⟩
      split_ifs at h
  have tN : kN = .term ↔ j0 + 1 = L.length := by
    rw [hkN]
    by_cases h0 : j0 + 1 = L.length
    · rw [ite_eq_left h0]; exact ⟨fun _ => h0, fun _ => rfl⟩
    · rw [ite_eq_right h0]; refine ⟨fun h => ?_, fun h => absurd h h0⟩
      split_ifs at h
  have he' : e = if kP = .term ∨ kN = .term then some col else none := by
    rw [he]; simp only [tP, tN]
  have d1 : ¬ (kP = .term ∧ kN = .term) := by rw [tP, tN]; omega
  have d2 : ¬ (kP.upC.isSome ∧ kN.upC.isSome) := by
    rw [uP, uN]
    split_ifs with A B
    · exact fun _ => pn A.1 B.1 (A.2.2.trans B.2.2.symm)
    all_goals simp
  have d3 : ¬ (kP.lftC.isSome ∧ kN.lftC.isSome) := by
    rw [lP, lN]
    split_ifs with A B
    · exact fun _ => pn A.1 B.1 ((leftOf (adjP A.1) A.2.1 A.2.2).2.trans (leftOf (adjN B.1) B.2.1 B.2.2).2.symm)
    all_goals simp
  have dnP : kP = .dn → 0 < j0 ∧ nth L (j0 - 1) = (x1 + 1, x2) := fun h => by
    rw [hkP] at h; split_ifs at h with h0 hp hu hd; simp only [] at h; exact ⟨by omega, hd⟩
  have dnN : kN = .dn → j0 + 1 < L.length ∧ nth L (j0 + 1) = (x1 + 1, x2) := fun h => by
    rw [hkN] at h; split_ifs at h with h0 hp hu hd; simp only [] at h; exact ⟨by omega, hd⟩
  have rtP : kP = .rt → 0 < j0 ∧ nth L (j0 - 1) = (x1, x2 + 1) := fun h => by
    rw [hkP] at h; split_ifs at h with h0 hp hu hd; simp only [] at h
    refine ⟨by omega, ?_⟩
    rcases unproc (adjP (by omega)) hp (neX _ (by omega) (by omega)) with e | e
    · exact absurd e hd
    · exact e
  have rtN : kN = .rt → j0 + 1 < L.length ∧ nth L (j0 + 1) = (x1, x2 + 1) := fun h => by
    rw [hkN] at h; split_ifs at h with h0 hp hu hd; simp only [] at h
    refine ⟨by omega, ?_⟩
    rcases unproc (adjN (by omega)) hp (neX _ (by omega) (by omega)) with e | e
    · exact absurd e hd
    · exact e
  have d4 : ¬ (kP = .dn ∧ kN = .dn) := fun ⟨h, h'⟩ => by
    obtain ⟨g1, g2⟩ := dnP h; obtain ⟨g3, g4⟩ := dnN h'; exact pn g1 g3 (g2.trans g4.symm)
  have d5 : ¬ (kP = .rt ∧ kN = .rt) := fun ⟨h, h'⟩ => by
    obtain ⟨g1, g2⟩ := rtP h; obtain ⟨g3, g4⟩ := rtN h'; exact pn g1 g3 (g2.trans g4.symm)
  -- the two attached runs have different codes
  have cAB : 0 < j0 → j0 + 1 < L.length → prI a b i (nth L (j0 - 1)) → prI a b i (nth L (j0 + 1)) →
      cA ≠ cB := by
    intro h0 h1 hp hn e
    rcases sideL with ⟨-, -, r3, r4⟩ | ⟨-, r2⟩
    · rcases sideR with ⟨-, -, r7, r8⟩ | ⟨-, r6⟩
      · obtain ⟨-, -, e3, -⟩ := code_inj hS ha hb hi.le hL hL r4 r8 (fun c => by omega) (fun c => by omega)
          (by rw [← hcA, ← hcB, e])
        omega
      · rcases r6 with r6 | r6
        · omega
        · exact r6 hn
    · rcases r2 with r2 | r2
      · omega
      · exact r2 hp
  have uP' : ∀ c, kP.upC = some c → (0 < j0 ∧ prI a b i (nth L (j0 - 1)) ∧ nth L (j0 - 1) = (x1 - 1, x2)) ∧ c = cA := by
    intro c h; rw [uP] at h; split_ifs at h with A
    exact ⟨A, (Option.some.inj h).symm⟩
  have uN' : ∀ c, kN.upC = some c → (j0 + 1 < L.length ∧ prI a b i (nth L (j0 + 1)) ∧ nth L (j0 + 1) = (x1 - 1, x2)) ∧ c = cB := by
    intro c h; rw [uN] at h; split_ifs at h with A
    exact ⟨A, (Option.some.inj h).symm⟩
  have lP' : ∀ c, kP.lftC = some c → (0 < j0 ∧ prI a b i (nth L (j0 - 1)) ∧ ¬ nth L (j0 - 1) = (x1 - 1, x2)) ∧ c = cA := by
    intro c h; rw [lP] at h; split_ifs at h with A
    exact ⟨A, (Option.some.inj h).symm⟩
  have lN' : ∀ c, kN.lftC = some c → (j0 + 1 < L.length ∧ prI a b i (nth L (j0 + 1)) ∧ ¬ nth L (j0 + 1) = (x1 - 1, x2)) ∧ c = cB := by
    intro c h; rw [lN] at h; split_ifs at h with A
    exact ⟨A, (Option.some.inj h).symm⟩
  have d6 : ∀ c c', (kP.upC = some c ∨ kN.upC = some c) → (kP.lftC = some c' ∨ kN.lftC = some c') →
      c ≠ c' := by
    intro c c' hu hl
    rcases hu with hu | hu <;> rcases hl with hl | hl
    · exact absurd (uP' c hu).1.2.2 (lP' c' hl).1.2.2
    · obtain ⟨A, rfl⟩ := uP' c hu; obtain ⟨B, rfl⟩ := lN' c' hl
      exact cAB A.1 B.1 A.2.1 B.2.1
    · obtain ⟨A, rfl⟩ := uN' c hu; obtain ⟨B, rfl⟩ := lP' c' hl
      exact fun e => cAB B.1 A.1 B.2.1 A.2.1 e.symm
    · exact absurd (uN' c hu).1.2.2 (lN' c' hl).1.2.2
  -- the closed state
  have doneBit : (s.2 / 2 ^ col) % 2 = 0 := by
    have notAll : ¬ ∀ y ∈ L, prI a b i y := fun h => hxP (h _ (nth_mem hj0))
    rw [hs.2.2]
    unfold doneMask
    rcases hL with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [ite_eq_right notAll]; split_ifs <;> norm_num
    · rw [ite_eq_right notAll]; split_ifs <;> norm_num
  have tB : ∀ c, isTerm a b (termE a b c) = true := fun c => by unfold isTerm termE; simp
  have tC : ∀ c, colE a b (termE a b c) = c := fun c => by unfold colE termE; omega
  have mem := fun {s' : St} (h : closeP a b (endL a b col L sM) (endR a b col L eM)
      (restK s.1 (kP.upC <|> kN.upC) (kP.lftC <|> kN.lftC)) s.2 = some s') =>
    stepCell_kinds hU hU0 hLk hL0 hoU hoL he' d1 d2 d3 d4 d5 d6 (s' := s') (by rw [vP, vN]; exact h)
  -- the remaining pieces
  have attIff : ∀ z, ((kP.upC <|> kN.upC) = some z ∨ (kP.lftC <|> kN.lftC) = some z) ↔
      (((0 < j0 ∧ prI a b i (nth L (j0 - 1))) ∧ z = cA) ∨
        ((j0 + 1 < L.length ∧ prI a b i (nth L (j0 + 1))) ∧ z = cB)) := by
    intro z
    constructor
    · rintro (h | h) <;> rcases orElse_some.mp h with h | ⟨-, h⟩
      · obtain ⟨A, rfl⟩ := uP' z h; exact Or.inl ⟨⟨A.1, A.2.1⟩, rfl⟩
      · obtain ⟨A, rfl⟩ := uN' z h; exact Or.inr ⟨⟨A.1, A.2.1⟩, rfl⟩
      · obtain ⟨A, rfl⟩ := lP' z h; exact Or.inl ⟨⟨A.1, A.2.1⟩, rfl⟩
      · obtain ⟨A, rfl⟩ := lN' z h; exact Or.inr ⟨⟨A.1, A.2.1⟩, rfl⟩
    · rintro (⟨⟨h0, hp⟩, rfl⟩ | ⟨⟨h0, hp⟩, rfl⟩)
      · by_cases hu : nth L (j0 - 1) = (x1 - 1, x2)
        · left; rw [orElse_some, uP, ite_eq_left ⟨h0, hp, hu⟩]; exact Or.inl rfl
        · right; rw [orElse_some, lP, ite_eq_left ⟨h0, hp, hu⟩]; exact Or.inl rfl
      · by_cases hu : nth L (j0 + 1) = (x1 - 1, x2)
        · left; rw [orElse_some, uN, ite_eq_left ⟨h0, hp, hu⟩, uP]
          right; refine ⟨ite_eq_right (fun A => pn A.1 h0 (A.2.2.trans hu.symm)), rfl⟩
        · right; rw [orElse_some, lN, ite_eq_left ⟨h0, hp, hu⟩, lP]
          right; refine ⟨ite_eq_right (fun A => pn A.1 h0 ?_), rfl⟩
          exact (leftOf (adjP A.1) A.2.1 A.2.2).2.trans (leftOf (adjN h0) hp hu).2.symm
  have hne : ∀ c c', (kP.upC <|> kN.upC) = some c → (kP.lftC <|> kN.lftC) = some c' → c ≠ c' := by
    intro c c' hu hl
    apply d6
    · rcases orElse_some.mp hu with h | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    · rcases orElse_some.mp hl with h | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
  have restMem : ∀ z, z ∈ restK s.1 (kP.upC <|> kN.upC) (kP.lftC <|> kN.lftC) ↔ z ∈ s.1 ∧
      ¬ (((0 < j0 ∧ prI a b i (nth L (j0 - 1))) ∧ z = cA) ∨
        ((j0 + 1 < L.length ∧ prI a b i (nth L (j0 + 1))) ∧ z = cB)) := by
    intro z
    rw [restK_mem hs.1 hne]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, fun h => ((attIff z).mpr h).elim h2 h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun e => h2 ((attIff z).mp (Or.inl e)), fun e => h2 ((attIff z).mp (Or.inr e))⟩
  have notInM : ∀ {y : Coord}, y ∈ M → y ≠ nth L j0 := fun hy e => hxM (hnx ▸ e ▸ hy)
  have LM : L ≠ M := fun e => hxM (e ▸ hxL)
  -- old runs that miss `x` are new runs, and conversely
  have back : ∀ L'' col'' st en, PathC p q L'' col'' → IsRun (prI a b (i + 1)) L'' st en →
      ¬ (st = 0 ∧ en + 1 = L''.length) → ¬ (L'' = L ∧ st ≤ j0 ∧ j0 ≤ en) →
      runCode a b col'' L'' st en ∈ restK s.1 (kP.upC <|> kN.upC) (kP.lftC <|> kN.lftC) := by
    intro L'' col'' st en hp hr hinc hmiss
    rw [restMem]
    rcases hcov L'' col'' hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨r1, r2, r3⟩ := run_back nL hj0 hxP ((isRun_congr eP).mp hr) (fun h => hmiss ⟨rfl, h⟩)
      refine ⟨(hs.2.1 _).mpr ⟨L'', col'', st, en, hp, r1, hinc, rfl⟩, ?_⟩
      rintro (⟨⟨h0, hpv⟩, e⟩ | ⟨⟨h0, hpv⟩, e⟩)
      · rcases sideL with ⟨-, -, -, r4⟩ | ⟨-, r6⟩
        · obtain ⟨-, -, -, e4⟩ := code_inj hS ha hb hi.le hp hL r1 r4 hinc (fun c => by omega)
            (by rw [e, hcA])
          omega
        · rcases r6 with r6 | r6
          · omega
          · exact r6 hpv
      · rcases sideR with ⟨-, -, -, r4⟩ | ⟨-, r6⟩
        · obtain ⟨-, -, e3, -⟩ := code_inj hS ha hb hi.le hp hL r1 r4 hinc (fun c => by omega)
            (by rw [e, hcB])
          omega
        · rcases r6 with r6 | r6
          · omega
          · exact r6 hpv
    · have r1 := (run_other (P := prI a b i) (x := nth L j0) (by rw [hnx]; exact hxM)).mp
        ((isRun_congr eP).mp hr)
      refine ⟨(hs.2.1 _).mpr ⟨_, _, st, en, hp, r1, hinc, rfl⟩, ?_⟩
      rintro (⟨⟨h0, hpv⟩, e⟩ | ⟨⟨h0, hpv⟩, e⟩)
      · rcases sideL with ⟨-, -, -, r4⟩ | ⟨-, r6⟩
        · have := (code_inj hS ha hb hi.le hp hL r1 r4 hinc (fun c => by omega) (by rw [e, hcA])).1
          exact LM this.symm
        · rcases r6 with r6 | r6
          · omega
          · exact r6 hpv
      · rcases sideR with ⟨-, -, -, r4⟩ | ⟨-, r6⟩
        · have := (code_inj hS ha hb hi.le hp hL r1 r4 hinc (fun c => by omega) (by rw [e, hcB])).1
          exact LM this.symm
        · rcases r6 with r6 | r6
          · omega
          · exact r6 hpv
  have lift : ∀ z ∈ restK s.1 (kP.upC <|> kN.upC) (kP.lftC <|> kN.lftC),
      ∃ L'' col'' st en, PathC p q L'' col'' ∧ IsRun (prI a b (i + 1)) L'' st en ∧
        ¬ (st = 0 ∧ en + 1 = L''.length) ∧ z = runCode a b col'' L'' st en ∧
        ¬ (L'' = L ∧ st ≤ j0 ∧ j0 ≤ en) := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := (restMem z).mp hz
    obtain ⟨L'', col'', st, en, hp, hr, hinc, rfl⟩ := (hs.2.1 _).mp hz1
    refine ⟨L'', col'', st, en, hp, ?_, hinc, rfl, ?_⟩
    · rcases hcov L'' col'' hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hlt := hr.lt; have hle := hr.le
        have c0 : ¬ (st ≤ j0 ∧ j0 ≤ en) := fun h => hxP (hr.all j0 h.1 h.2)
        have r2 : en + 1 ≠ j0 := by
          intro e
          rcases sideL with ⟨g1, g2, g3, r4⟩ | ⟨-, r6⟩
          · obtain ⟨u1, -⟩ := run_unique hr r4 hle (le_refl _) (by omega) (by omega)
            exact hz2 (Or.inl ⟨⟨g1, g2⟩, by rw [hcA, ← u1, show en = j0 - 1 by omega]⟩)
          · rcases r6 with r6 | r6
            · omega
            · exact r6 (by rw [show j0 - 1 = en by omega]; exact hr.all en hle (le_refl _))
        have r3 : st ≠ j0 + 1 := by
          intro e
          rcases sideR with ⟨g1, g2, g3, r4⟩ | ⟨-, r6⟩
          · obtain ⟨-, u2⟩ := run_unique hr r4 (le_refl _) hle (by omega) (by omega)
            exact hz2 (Or.inr ⟨⟨g1, g2⟩, by rw [hcB, ← u2, e]⟩)
          · rcases r6 with r6 | r6
            · omega
            · exact r6 (by rw [← e]; exact hr.all st (le_refl _) hle)
        exact (isRun_congr eP).mpr (run_keep nL hj0 hr r2 r3)
      · exact (isRun_congr eP).mpr
          ((run_other (P := prI a b i) (x := nth L j0) (by rw [hnx]; exact hxM)).mpr hr)
    · rintro ⟨rfl, h1, h2⟩
      exact hxP (by
        rcases hcov _ _ hp with ⟨-, -⟩ | ⟨e, -⟩
        · exact hr.all j0 h1 h2
        · exact absurd e LM)
  -- the merged run
  have sj : sM ≤ j0 ∧ j0 ≤ eM := by
    constructor
    · rcases hsM with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
    · rcases heM with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have isMerge : ∀ L'' col'' st en, PathC p q L'' col'' → IsRun (prI a b (i + 1)) L'' st en →
      L'' = L → st ≤ j0 → j0 ≤ en → L'' = L ∧ col'' = col ∧ st = sM ∧ en = eM := by
    rintro L'' col'' st en hp hr rfl h1 h2
    obtain ⟨-, e⟩ := pathC_same hS hp hL (nth_mem hj0) (nth_mem hj0)
    obtain ⟨u1, u2⟩ := run_unique hr hmerge h1 h2 sj.1 sj.2
    exact ⟨rfl, e, u1, u2⟩
  have allL' : (∀ y ∈ L, prI a b (i + 1) y) ↔ (sM = 0 ∧ eM + 1 = L.length) := by
    constructor
    · intro h
      have r : IsRun (prI a b (i + 1)) L 0 (L.length - 1) :=
        ⟨by omega, by omega, fun k _ hk => h _ (nth_mem (by omega)), Or.inl rfl, Or.inl (by omega)⟩
      obtain ⟨u1, u2⟩ := run_unique r hmerge (Nat.zero_le _) (by omega) sj.1 sj.2
      omega
    · rintro ⟨h1, h2⟩ y hy
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
      rw [← nth_eq hk]
      exact hmerge.all k (by omega) (by omega)
  have hMeq : (∀ y ∈ M, prI a b (i + 1) y) ↔ (∀ y ∈ M, prI a b i y) :=
    ⟨fun h y hy => ((eP y).mp (h y hy)).resolve_right (notInM hy),
      fun h y hy => (eP y).mpr (Or.inl (h y hy))⟩
  have notAll : ¬ ∀ y ∈ L, prI a b i y := fun h => hxP (h _ (nth_mem hj0))
  have mask := doneMask_succ (a := a) (b := b) hL hM LM notAll hMeq
  by_cases hcomp : sM = 0 ∧ eM + 1 = L.length
  · have eL : endL a b col L sM = termE a b col := by unfold endL; rw [ite_eq_left hcomp.1]
    have eR : endR a b col L eM = termE a b col := by unfold endR; rw [ite_eq_left hcomp.2]
    have hcl : closeP a b (endL a b col L sM) (endR a b col L eM)
        (restK s.1 (kP.upC <|> kN.upC) (kP.lftC <|> kN.lftC)) s.2 =
        some (restK s.1 (kP.upC <|> kN.upC) (kP.lftC <|> kN.lftC), s.2 + 2 ^ col) := by
      rw [eL, eR]; unfold closeP; rw [tB, tC, doneBit]; simp
    refine ⟨_, mem hcl, restK_nodup hs.1 _ _, fun z => ⟨fun hz => ?_, fun hz => ?_⟩, ?_⟩
    · obtain ⟨L'', col'', st, en, hp, hr, hinc, rfl, -⟩ := lift z hz
      exact ⟨_, _, _, _, hp, hr, hinc, rfl⟩
    · obtain ⟨L'', col'', st, en, hp, hr, hinc, rfl⟩ := hz
      by_cases hc : L'' = L ∧ st ≤ j0 ∧ j0 ≤ en
      · obtain ⟨e0, -, e1, e2⟩ := isMerge _ _ _ _ hp hr hc.1 hc.2.1 hc.2.2
        exact absurd ⟨by rw [e1]; exact hcomp.1, by rw [e2, e0]; exact hcomp.2⟩ hinc
      · exact back _ _ _ _ hp hr hinc hc
    · show s.2 + 2 ^ col = doneMask a b (i + 1) p q
      rw [mask, hs.2.2, ite_eq_left (allL'.mpr hcomp)]
  · have nt : (isTerm a b (endL a b col L sM) && isTerm a b (endR a b col L eM)) = false := by
      rcases endL_cases cL hmerge col with ⟨h1, -⟩ | ⟨-, -, l1⟩
      · rcases endR_cases cL hmerge col with ⟨h2, -⟩ | ⟨-, -, l2⟩
        · exact absurd ⟨h1, h2⟩ hcomp
        · simp only [isTerm, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le]; right; exact l2
      · simp only [isTerm, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le]; left; exact l1
    have hcl : closeP a b (endL a b col L sM) (endR a b col L eM)
        (restK s.1 (kP.upC <|> kN.upC) (kP.lftC <|> kN.lftC)) s.2 =
        some (insSorted (runCode a b col L sM eM) (restK s.1 (kP.upC <|> kN.upC) (kP.lftC <|> kN.lftC)), s.2) := by
      unfold closeP; rw [nt]; rfl
    have notin : runCode a b col L sM eM ∉ restK s.1 (kP.upC <|> kN.upC) (kP.lftC <|> kN.lftC) := by
      intro hm
      obtain ⟨L'', col'', st, en, hp, hr, hinc, he, hmiss⟩ := lift _ hm
      obtain ⟨e0, -, e1, e2⟩ := code_inj hS ha hb (by omega) hp hL hr hmerge hinc hcomp he.symm
      exact hmiss ⟨e0, by omega, by omega⟩
    refine ⟨_, mem hcl, (insSorted_perm _ _).nodup_iff.mpr (List.nodup_cons.mpr ⟨notin, restK_nodup hs.1 _ _⟩),
      fun z => ?_, ?_⟩
    · show z ∈ insSorted _ _ ↔ _
      rw [(insSorted_perm _ _).mem_iff, List.mem_cons]
      constructor
      · rintro (rfl | hz)
        · exact ⟨L, col, sM, eM, hL, hmerge, hcomp, rfl⟩
        · obtain ⟨L'', col'', st, en, hp, hr, hinc, rfl, -⟩ := lift z hz
          exact ⟨_, _, _, _, hp, hr, hinc, rfl⟩
      · rintro ⟨L'', col'', st, en, hp, hr, hinc, rfl⟩
        by_cases hc : L'' = L ∧ st ≤ j0 ∧ j0 ≤ en
        · obtain ⟨rfl, rfl, rfl, rfl⟩ := isMerge _ _ _ _ hp hr hc.1 hc.2.1 hc.2.2
          exact Or.inl rfl
        · exact Or.inr (back _ _ _ _ hp hr hinc hc)
    · show s.2 = doneMask a b (i + 1) p q
      rw [mask, hs.2.2, ite_eq_right (fun h => hcomp (allL'.mp h))]; simp

end Core

end ZZN.Win

-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Thin.DP
import ZZN.Moves

/-!
# The plug DP is sound: an accepting run gives a solution

When the window is the whole grid (`a = J.w`, `b = J.h`), every state the DP reaches is backed by
actual segments: each piece code by a chain of processed cells whose ends match the code (an
endpoint of that colour, or a boundary edge into an unprocessed cell), each completed colour by a
full path, all of them disjoint and covering the processed cells (`W`). The accepting state
`([], 3)` then gives a solution.
-/

namespace ZZN.Thin

open GridHam

section Real

variable (a b : ℕ) (J : Inst)

/-- End code `e` is realized at cell `x`: an endpoint of that colour, or a boundary edge. -/
def EndOK (i e : ℕ) (x : Coord) : Prop :=
  (∃ col, e = termE a b col ∧ endCol J x = some col) ∨
  (∃ y, ¬ prI a b i y ∧ Adjacent x y ∧ desc a b x y = e)

/-- A segment from end code `e` (at its head) to end code `f` (at its last cell). -/
def SegE (i e f : ℕ) (L : List Coord) : Prop :=
  L.Nodup ∧ chainAdjacent L = true ∧ (∀ x ∈ L, prI a b i x) ∧
    ∃ u v, L.head? = some u ∧ L.getLast? = some v ∧ EndOK a b J i e u ∧ EndOK a b J i f v

/-- The endpoints of colour `col`. -/
def ends2 (col : ℕ) : Coord × Coord := if col = 0 then (J.s0, J.t0) else (J.s1, J.t1)

def bitOf (dn col : ℕ) : Bool := (dn / 2 ^ col) % 2 == 1

def doneCols (dn : ℕ) : List ℕ := (List.range 2).filter (fun col => bitOf dn col)

def allOf (sg dp : ℕ → List Coord) (s : St) : List Coord :=
  s.1.flatMap sg ++ (doneCols s.2).flatMap dp

/-- **The realizability invariant** after `i` cells. -/
def W (i : ℕ) (s : St) : Prop :=
  ∃ sg dp : ℕ → List Coord, s.1.Nodup ∧ s.2 < 4 ∧
    (∀ z ∈ s.1, lo z ≠ hi z ∧ SegE a b J i (lo z) (hi z) (sg z)) ∧
    (∀ col ∈ doneCols s.2, IsPath a b (ends2 J col).1 (ends2 J col).2 (dp col)) ∧
    (allOf sg dp s).Nodup ∧ (∀ x, prI a b i x ↔ x ∈ allOf sg dp s)

end Real

section Basic

variable {a b : ℕ} {J : Inst}

theorem head_rev {L : List Coord} {u : Coord} (h : L.getLast? = some u) : L.reverse.head? = some u := by
  rw [List.head?_reverse]; exact h

theorem last_rev {L : List Coord} {u : Coord} (h : L.head? = some u) : L.reverse.getLast? = some u := by
  rw [List.getLast?_reverse]; exact h

theorem SegE.rev {i e f : ℕ} {L : List Coord} (h : SegE a b J i e f L) : SegE a b J i f e L.reverse := by
  obtain ⟨hn, hc, hp, u, v, hu, hv, eu, ev⟩ := h
  exact ⟨List.nodup_reverse.mpr hn, chainAdjacent_reverse L hc, fun x hx => hp x (List.mem_reverse.mp hx),
    v, u, head_rev hv, last_rev hu, ev, eu⟩

theorem termE_ne_desc {i : ℕ} {u v : Coord} (hu : prI a b i u) (hv : ¬ prI a b i v) (h : Adjacent u v)
    (col : ℕ) : desc a b u v ≠ termE a b col := by
  have := desc_lt hu hv h; unfold termE; omega

/-- A plug code at a processed cell determines the boundary edge. -/
theorem plug_of {i e : ℕ} {u : Coord} (_hu : prI a b i u) (h : EndOK a b J i e u) (he : e < a + 2 * b + 1) :
    ∃ y, ¬ prI a b i y ∧ Adjacent u y ∧ desc a b u y = e := by
  rcases h with ⟨col, rfl, -⟩ | h
  · unfold termE at he; omega
  · exact h

theorem endOK_term {i col : ℕ} {u : Coord} (hu : prI a b i u) (h : EndOK a b J i (termE a b col) u) :
    endCol J u = some col := by
  rcases h with ⟨col', e, hc⟩ | ⟨y, hy, hadj, hd⟩
  · unfold termE at e; rw [show col = col' by omega]; exact hc
  · exact absurd hd (termE_ne_desc hu hy hadj col)

/-- In a nodup flatMap, a cell lies in the block of only one key. -/
theorem flatMap_unique {l : List ℕ} {f : ℕ → List Coord} (_hl : l.Nodup) (hn : (l.flatMap f).Nodup)
    {z z' : ℕ} (hz : z ∈ l) (hz' : z' ∈ l) {x : Coord} (hx : x ∈ f z) (hx' : x ∈ f z') : z = z' := by
  by_contra hne
  rw [List.nodup_flatMap] at hn
  have : Std.Symm (Function.onFun List.Disjoint f) := ⟨fun _ _ h => List.Disjoint.symm h⟩
  exact hn.2.forall hz hz' hne hx hx'

end Basic

section Uniq

variable {a b : ℕ} {J : Inst}

/-- Orient a piece's segment so that end `e` is last. -/
theorem orient {i z e : ℕ} {L : List Coord} (hz : SegE a b J i (lo z) (hi z) L) (he : hasEnd e z = true) :
    ∃ L', SegE a b J i (other e z) e L' ∧ (∀ x, x ∈ L' ↔ x ∈ L) ∧ L'.Perm L := by
  unfold hasEnd at he
  unfold other
  by_cases h : lo z = e
  · rw [ite_eq_left (by simp [h])]
    refine ⟨L.reverse, ?_, fun x => List.mem_reverse, List.reverse_perm _⟩
    rw [← h]; exact hz.rev
  · rw [ite_eq_right (by simp [h])]
    have : hi z = e := by simpa [h] using he
    exact ⟨L, this ▸ hz, fun _ => Iff.rfl, List.Perm.refl _⟩

theorem SegE.mem_last {i e f : ℕ} {L : List Coord} (h : SegE a b J i e f L) :
    ∃ v, L.getLast? = some v ∧ v ∈ L ∧ EndOK a b J i f v ∧ prI a b i v := by
  obtain ⟨-, -, hp, u, v, -, hv, -, ev⟩ := h
  have hm := List.mem_of_getLast? hv
  exact ⟨v, hv, hm, ev, hp v hm⟩

/-- **A plug code is the end of at most one piece.** -/
theorem plug_unique {i : ℕ} (hia : i ≤ a * b) {ps : List ℕ} {sg : ℕ → List Coord} (hn : ps.Nodup)
    (hseg : ∀ z ∈ ps, lo z ≠ hi z ∧ SegE a b J i (lo z) (hi z) (sg z)) (hall : (ps.flatMap sg).Nodup)
    {e z z' : ℕ} (hz : z ∈ ps) (hz' : z' ∈ ps) (he : e < a + 2 * b + 1)
    (h1 : hasEnd e z = true) (h2 : hasEnd e z' = true) : z = z' := by
  obtain ⟨L1, s1, m1, -⟩ := orient (hseg z hz).2 h1
  obtain ⟨L2, s2, m2, -⟩ := orient (hseg z' hz').2 h2
  obtain ⟨v1, -, vm1, ev1, pv1⟩ := s1.mem_last
  obtain ⟨v2, -, vm2, ev2, pv2⟩ := s2.mem_last
  obtain ⟨y1, ny1, ad1, d1⟩ := plug_of pv1 ev1 he
  obtain ⟨y2, ny2, ad2, d2⟩ := plug_of pv2 ev2 he
  obtain ⟨rfl, -⟩ := desc_inj hia pv1 ny1 ad1 pv2 ny2 ad2 (d1.trans d2.symm)
  exact flatMap_unique hn hall hz hz' ((m1 v1).mp vm1) ((m2 v1).mp vm2)

theorem endOK_succ {i e : ℕ} {x u : Coord} (hpr : ∀ y, prI a b (i + 1) y ↔ prI a b i y ∨ y = x)
    (h : EndOK a b J i e u) (hne : ∀ y, Adjacent u y → desc a b u y = e → ¬ prI a b i y → y ≠ x) :
    EndOK a b J (i + 1) e u := by
  rcases h with h | ⟨y, ny, ad, d⟩
  · exact Or.inl h
  · refine Or.inr ⟨y, ?_, ad, d⟩
    rw [hpr]; rintro (h | h)
    · exact ny h
    · exact hne y ad d ny h

end Uniq

section Assemble

variable {a b : ℕ} {J : Inst}

/-- From the local facts about a new state to the invariant. -/
theorem assemble {i : ℕ} {x : Coord} (hpr : ∀ y, prI a b (i + 1) y ↔ prI a b i y ∨ y = x)
    {s s' : St} {sg dp sg' dp' : ℕ → List Coord}
    (hnod : (allOf sg dp s).Nodup) (hcov : ∀ y, prI a b i y ↔ y ∈ allOf sg dp s) (hx : ¬ prI a b i x)
    (h1 : s'.1.Nodup) (h2 : s'.2 < 4)
    (h3 : ∀ z ∈ s'.1, lo z ≠ hi z ∧ SegE a b J (i + 1) (lo z) (hi z) (sg' z))
    (h4 : ∀ col ∈ doneCols s'.2, IsPath a b (ends2 J col).1 (ends2 J col).2 (dp' col))
    (h5 : (allOf sg' dp' s').Perm (allOf sg dp s ++ [x])) : W a b J (i + 1) s' := by
  refine ⟨sg', dp', h1, h2, h3, h4, ?_, ?_⟩
  · rw [h5.nodup_iff, List.nodup_append]
    refine ⟨hnod, List.nodup_singleton x, ?_⟩
    intro y hy z hz heq
    rw [List.mem_singleton] at hz
    rw [heq, hz] at hy
    exact hx ((hcov x).mpr hy)
  · intro y
    rw [hpr, h5.mem_iff, List.mem_append, List.mem_singleton, hcov]

end Assemble

section Close

variable {a b : ℕ} {J : Inst}

theorem doneCols_add {dn col : ℕ} (hdn : dn < 4) (hc : col < 2) (hb : ¬ (dn / 2 ^ col) % 2 = 1) :
    dn + 2 ^ col < 4 ∧ (doneCols (dn + 2 ^ col)).Perm (col :: doneCols dn) := by
  interval_cases dn <;> interval_cases col <;> simp_all (config := { decide := true }) []

theorem endCol_cases {y : Coord} {col : ℕ} (h : endCol J y = some col) :
    (col = 0 ∧ (y = J.s0 ∨ y = J.t0)) ∨ (col = 1 ∧ (y = J.s1 ∨ y = J.t1)) := by
  unfold endCol at h
  split_ifs at h with h1 h2
  · left; simp at h; exact ⟨h.symm, h1⟩
  · right; simp at h; exact ⟨h.symm, h2⟩

theorem head_ne_last {L : List Coord} (hn : L.Nodup) (hl : 2 ≤ L.length) {u v : Coord}
    (hu : L.head? = some u) (hv : L.getLast? = some v) : u ≠ v := by
  match L, hn, hl, hu, hv with
  | x :: y :: l, hn, _, hu, hv =>
    simp only [List.head?_cons, Option.some.injEq] at hu
    subst hu
    intro e
    subst e
    have hm : x ∈ (y :: l) := by
      have := List.mem_of_getLast? hv
      rw [List.getLast?_cons_cons] at hv
      exact List.mem_of_getLast? hv
    exact (List.nodup_cons.mp hn).1 hm

theorem isTerm_eq {E : ℕ} (h : isTerm a b E = true) : E = termE a b (colE a b E) := by
  unfold isTerm at h; unfold termE colE; simp at h; omega

/-- **One cell's outcome satisfies the invariant**: the new segment `Ln` through `x` absorbs the
pieces `K`; `closeP` either completes a colour or stores the new piece. -/
theorem close_W {i : ℕ} (hia : i + 1 ≤ a * b) {x : Coord}
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
    {s' : St} (hcl : closeP a b E1 E2 rest s.2 = some s') : W a b J (i + 1) s' := by
  have hold : (allOf sg dp s).Perm (K.flatMap sg ++ rest.flatMap sg ++ (doneCols s.2).flatMap dp) := by
    unfold allOf
    rw [← List.flatMap_append]
    exact (hperm.flatMap_right sg).append_right _
  have hnod' := hold.nodup_iff.mp hnod
  -- cells of rest pieces are old cells, so not `x`, and not in the absorbed pieces
  have hxo : x ∉ allOf sg dp s := fun h => hx ((hcov x).mpr h)
  have dKR : ∀ y, y ∈ K.flatMap sg → y ∉ rest.flatMap sg := by
    intro y h1 h2
    rw [List.nodup_append, List.nodup_append] at hnod'
    exact hnod'.1.2.2 y h1 y h2 rfl
  obtain ⟨hLn, hLc, hLp, u, v, hu, hv, eu, ev⟩ := hseg
  unfold closeP at hcl
  split_ifs at hcl with hT hc hbit
  -- a colour is completed
  · simp only [Option.some.injEq] at hcl
    subst hcl
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
    -- the path, from the first endpoint of the colour to the second
    have hpath : ∃ P, IsPath a b (ends2 J col).1 (ends2 J col).2 P ∧ P.Perm Ln := by
      have inb : ∀ y ∈ Ln, InBounds a b y := fun y hy => ⟨(hLp y hy).1, (hLp y hy).2.1⟩
      have pathF : IsPath a b u v Ln := ⟨hu, hv, hLn, inb, hLc⟩
      have key : (u = (ends2 J col).1 ∧ v = (ends2 J col).2) ∨ (u = (ends2 J col).2 ∧ v = (ends2 J col).1) := by
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
      rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨Ln, pathF, List.Perm.refl _⟩
      · exact ⟨Ln.reverse, pathF.reverse, List.reverse_perm _⟩
    obtain ⟨P, hP, hPp⟩ := hpath
    let dp' : ℕ → List Coord := fun c => if c = col then P else dp c
    have hnot : col ∉ doneCols s.2 := by
      intro h
      unfold doneCols at h
      rw [List.mem_filter] at h
      unfold bitOf at h
      exact hbit h.2
    refine assemble (sg := sg) (dp := dp) (sg' := sg) (dp' := dp') hpr hnod hcov hx hrn d4 hrest ?_ ?_
    · intro c hc'
      show IsPath a b _ _ (if c = col then P else dp c)
      by_cases hcc : c = col
      · rw [ite_eq_left hcc, hcc]; exact hP
      · rw [ite_eq_right hcc]
        rcases List.mem_cons.mp (dperm.mem_iff.mp hc') with h | h
        · exact absurd h hcc
        · exact hdone c h
    · unfold allOf
      dsimp only
      have hd : ((doneCols (s.2 + 2 ^ col)).flatMap dp').Perm (P ++ (doneCols s.2).flatMap dp) := by
        refine (dperm.flatMap_right dp').trans ?_
        rw [List.flatMap_cons]
        have e0 : dp' col = P := ite_eq_left rfl
        rw [e0]
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
    have hne := hneq hT'
    set z' := mkP E1 E2 with hz'
    -- a plug end of the new segment
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
    -- the segment, oriented with the smaller code first
    have hsegN : SegE a b J (i + 1) (lo z') (hi z') (if E1 ≤ E2 then Ln else Ln.reverse) := by
      have hs0 : SegE a b J (i + 1) E1 E2 Ln := ⟨hLn, hLc, hLp, u, v, hu, hv, eu, ev⟩
      rw [hz', mkP_lo, mkP_hi]
      split_ifs with h
      · rw [min_eq_left h, max_eq_right h]; exact hs0
      · rw [min_eq_right (by omega), max_eq_left (by omega)]; exact hs0.rev
    let sg' : ℕ → List Coord := fun z => if z = z' then (if E1 ≤ E2 then Ln else Ln.reverse) else sg z
    have hsg' : ∀ z ∈ rest, sg' z = sg z := fun z hz => ite_eq_right (fun (e : z = z') => hfresh (e ▸ hz))
    have hins := insSorted_perm z' rest
    refine assemble (sg := sg) (dp := dp) (sg' := sg') (dp' := dp) hpr hnod hcov hx ?_ hdn ?_ hdone ?_
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
      have hl : ((insSorted z' rest).flatMap sg').Perm ((if E1 ≤ E2 then Ln else Ln.reverse) ++ rest.flatMap sg) := by
        refine (hins.flatMap_right sg').trans ?_
        rw [List.flatMap_cons]
        have e0 : sg' z' = (if E1 ≤ E2 then Ln else Ln.reverse) := ite_eq_left rfl
        rw [e0]
        exact List.Perm.append_left _ (List.Perm.of_eq (List.flatMap_congr hsg'))
      have hLp' : (if E1 ≤ E2 then Ln else Ln.reverse).Perm Ln := by
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

section Build

variable {a b : ℕ} {J : Inst}

theorem SegE.succ {i e f : ℕ} {L : List Coord} {x : Coord}
    (hpr : ∀ y, prI a b (i + 1) y ↔ prI a b i y ∨ y = x) (h : SegE a b J i e f L)
    (he : ∀ u, L.head? = some u → EndOK a b J (i + 1) e u)
    (hf : ∀ v, L.getLast? = some v → EndOK a b J (i + 1) f v) : SegE a b J (i + 1) e f L := by
  obtain ⟨hn, hc, hp, u, v, hu, hv, -, -⟩ := h
  exact ⟨hn, hc, fun y hy => (hpr y).mpr (Or.inl (hp y hy)), u, v, hu, hv, he u hu, hf v hv⟩

theorem segE_single {i e f : ℕ} {x : Coord} (hpx : prI a b (i + 1) x)
    (he : EndOK a b J (i + 1) e x) (hf : EndOK a b J (i + 1) f x) : SegE a b J (i + 1) e f [x] :=
  ⟨List.nodup_singleton x, rfl, fun y hy => by rw [List.mem_singleton.mp hy]; exact hpx, x, x, rfl, rfl, he, hf⟩

/-- Extend a segment by the current cell. -/
theorem segE_snoc {i e c f : ℕ} {Lw : List Coord} {x w : Coord}
    (hpr : ∀ y, prI a b (i + 1) y ↔ prI a b i y ∨ y = x) (hx : ¬ prI a b i x)
    (hL : SegE a b J i e c Lw) (hw : Lw.getLast? = some w) (hadj : Adjacent w x)
    (he : ∀ u, Lw.head? = some u → EndOK a b J (i + 1) e u) (hf : EndOK a b J (i + 1) f x) :
    SegE a b J (i + 1) e f (Lw ++ [x]) := by
  obtain ⟨hn, hc, hp, u, v, hu, hv, -, -⟩ := hL
  refine ⟨?_, chainAdjacent_append_of hc rfl hw rfl hadj, ?_, u, x, ?_, ?_, he u hu, hf⟩
  · rw [List.nodup_append]
    refine ⟨hn, List.nodup_singleton x, fun y hy z hz e => ?_⟩
    rw [List.mem_singleton] at hz; rw [e, hz] at hy; exact hx (hp x hy)
  · intro y hy
    rcases List.mem_append.mp hy with h | h
    · exact (hpr y).mpr (Or.inl (hp y h))
    · rw [List.mem_singleton.mp h]; exact (hpr x).mpr (Or.inr rfl)
  · rw [List.head?_append, hu]; rfl
  · simp

/-- Join two segments through the current cell. -/
theorem segE_join {i e c f d : ℕ} {Lu Ll : List Coord} {x w w' : Coord}
    (hpr : ∀ y, prI a b (i + 1) y ↔ prI a b i y ∨ y = x) (hx : ¬ prI a b i x)
    (hU : SegE a b J i e c Lu) (hL : SegE a b J i f d Ll) (hdis : ∀ y ∈ Lu, y ∉ Ll)
    (hw : Lu.getLast? = some w) (hadj : Adjacent w x) (hw' : Ll.getLast? = some w') (hadj' : Adjacent x w')
    (he : ∀ u, Lu.head? = some u → EndOK a b J (i + 1) e u)
    (hf : ∀ u, Ll.head? = some u → EndOK a b J (i + 1) f u) :
    SegE a b J (i + 1) e f (Lu ++ [x] ++ Ll.reverse) := by
  obtain ⟨hn, hc, hp, u, v, hu, hv, -, -⟩ := hU
  obtain ⟨hn', hc', hp', u', v', hu', hv', -, -⟩ := hL
  have c1 : chainAdjacent (Lu ++ [x]) = true := chainAdjacent_append_of hc rfl hw rfl hadj
  have hr : Ll.reverse.head? = some w' := head_rev hw'
  refine ⟨?_, chainAdjacent_append_of c1 (chainAdjacent_reverse Ll hc') (by simp) hr hadj', ?_, u, u', ?_, ?_,
    he u hu, hf u' hu'⟩
  · rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨hn, List.nodup_singleton x, fun y hy z hz e => ?_⟩, List.nodup_reverse.mpr hn', ?_⟩
    · rw [List.mem_singleton] at hz; rw [e, hz] at hy; exact hx (hp x hy)
    · intro y hy z hz e
      rw [List.mem_reverse] at hz
      rw [e] at hy
      rcases List.mem_append.mp hy with h | h
      · exact hdis z h hz
      · rw [List.mem_singleton.mp h] at hz; exact hx (hp' x hz)
  · intro y hy
    rcases List.mem_append.mp hy with h | h
    · rcases List.mem_append.mp h with h | h
      · exact (hpr y).mpr (Or.inl (hp y h))
      · rw [List.mem_singleton.mp h]; exact (hpr x).mpr (Or.inr rfl)
    · exact (hpr y).mpr (Or.inl (hp' y (List.mem_reverse.mp h)))
  · rw [List.append_assoc, List.head?_append, hu]; rfl
  · rw [List.getLast?_append, List.getLast?_reverse, hu']; simp

/-- Two plug ends of a long segment differ. -/
theorem plug_ends_ne {i e : ℕ} (hia : i ≤ a * b) {L : List Coord} (h : SegE a b J i e e L)
    (hl : 2 ≤ L.length) (he : e < a + 2 * b + 1) : False := by
  obtain ⟨hn, -, hp, u, v, hu, hv, eu, ev⟩ := h
  have pu := hp u (List.mem_of_head? hu)
  have pv := hp v (List.mem_of_getLast? hv)
  obtain ⟨y1, n1, a1, d1⟩ := plug_of pu eu he
  obtain ⟨y2, n2, a2, d2⟩ := plug_of pv ev he
  obtain ⟨rfl, -⟩ := desc_inj hia pu n1 a1 pv n2 a2 (d1.trans d2.symm)
  exact head_ne_last hn hl hu hv rfl

end Build

section Step

variable {a b : ℕ} {J : Inst}

theorem hasEnd_other {e z : ℕ} (h : hasEnd e z = true) : hasEnd (other e z) z = true := by
  unfold hasEnd other at *
  split_ifs <;> simp_all

theorem other_ne {e z : ℕ} (h : hasEnd e z = true) (hne : lo z ≠ hi z) : other e z ≠ e := by
  unfold hasEnd other at *
  split_ifs with h1 <;> simp_all; omega

theorem hasEnd_lo (z : ℕ) : hasEnd (lo z) z = true := by unfold hasEnd; simp
theorem hasEnd_hi (z : ℕ) : hasEnd (hi z) z = true := by unfold hasEnd; simp

/-- **One DP step keeps the invariant.** -/
theorem step_W {tm : List ((ℕ × ℕ) × ℕ)} (htm : ∀ y : Coord, y.1 < a → y.2 < b → termAt tm y = endCol J y)
    {i : ℕ} (hlt : i < a * b) {s s' : St} (hW : W a b J i s)
    (hs : s' ∈ stepCell a b (termAt tm (cell b i)) (cell b i).1 (cell b i).2 s) : W a b J (i + 1) s' := by
  obtain ⟨c1, c2, c3⟩ := cell_spec hlt
  have hpr0 := fun y => prI_succ hlt (y := y)
  have hlex0 := fun y => prI_lex hlt (y := y)
  rcases hxc : cell b i with ⟨x1, x2⟩
  rw [hxc] at c1 c2 c3 hs hpr0 hlex0
  simp only at c1 c2 c3 hs hlex0
  have hpr : ∀ y, prI a b (i + 1) y ↔ prI a b i y ∨ y = (x1, x2) := hpr0
  have hlex : ∀ y : Coord, prI a b i y ↔ y.1 < a ∧ y.2 < b ∧ (y.1 < x1 ∨ (y.1 = x1 ∧ y.2 < x2)) := hlex0
  have hx : ¬ prI a b i (x1, x2) := by unfold prI; simp only; omega
  have hia : i + 1 ≤ a * b := hlt
  have hpx : prI a b (i + 1) (x1, x2) := (hpr _).mpr (Or.inr rfl)
  obtain ⟨sg, dp, hn, h4, hseg, hdone, hnod, hcov⟩ := hW
  have hflat : (s.1.flatMap sg).Nodup := (List.nodup_append.mp hnod).1
  have huniq := fun {e z z'} hz hz' he h1 h2 =>
    plug_unique (a := a) (b := b) (J := J) (le_of_lt hlt) hn hseg hflat (e := e) (z := z) (z' := z') hz hz' he h1 h2
  -- ends of old pieces stay valid unless they lead into the current cell
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
  -- the pieces plugged into the current cell, from above and from the left
  have fromUp : ∀ zu, x1 ≠ 0 → s.1.find? (hasEnd x2) = some zu → zu ∈ s.1 ∧ hasEnd x2 zu = true ∧
      ∃ Lu, SegE a b J i (other x2 zu) x2 Lu ∧ Lu.Perm (sg zu) ∧ Lu.getLast? = some (x1 - 1, x2) := by
    intro zu h0 hf
    have hz := List.mem_of_find?_eq_some hf
    have he := List.find?_some hf
    obtain ⟨Lu, sL, -, pL⟩ := orient (hseg zu hz).2 he
    obtain ⟨v, hv, -, ev, pv⟩ := sL.mem_last
    obtain ⟨y, ny, ad, d⟩ := plug_of pv ev (by omega)
    obtain ⟨-, rfl, -⟩ := bd_plug hlex c2 pv ny ad d
    exact ⟨hz, he, Lu, sL, pL, hv⟩
  have fromLeft : ∀ zl, x2 ≠ 0 → s.1.find? (hasEnd b) = some zl → zl ∈ s.1 ∧ hasEnd b zl = true ∧
      ∃ Ll, SegE a b J i (other b zl) b Ll ∧ Ll.Perm (sg zl) ∧ Ll.getLast? = some (x1, x2 - 1) := by
    intro zl h0 hf
    have hz := List.mem_of_find?_eq_some hf
    have he := List.find?_some hf
    obtain ⟨Ll, sL, -, pL⟩ := orient (hseg zl hz).2 he
    obtain ⟨v, hv, -, ev, pv⟩ := sL.mem_last
    obtain ⟨y, ny, ad, d⟩ := plug_of pv ev (by omega)
    obtain ⟨-, rfl, -⟩ := bd_left hlex pv ny ad d
    exact ⟨hz, he, Ll, sL, pL, hv⟩
  -- the ends at the current cell
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
  -- no piece attached
  have case0 : ∀ E1 E2, (x1 ≠ 0 → s.1.find? (hasEnd x2) = none) → (x2 ≠ 0 → s.1.find? (hasEnd b) = none) →
      EndOK a b J (i + 1) E1 (x1, x2) → EndOK a b J (i + 1) E2 (x1, x2) → E1 ≠ E2 →
      (isTerm a b E1 && isTerm a b E2) = false → closeP a b E1 E2 s.1 s.2 = some s' → W a b J (i + 1) s' := by
    intro E1 E2 nu nl e1 e2 hne hT hcl
    refine close_W hia hpr hx h4 hdone hnod hcov (K := []) (rest := s.1) (by simp) hn
      (fun z hz => ⟨(hseg z hz).1, keepSeg z hz (fun h => findNone (nu h) z hz) (fun h => findNone (nl h) z hz)⟩)
      (segE_single hpx e1 e2) (by simp) (fun h => by rw [hT] at h; simp at h) (fun _ => hne) hcl
  -- one piece attached from the left
  have caseL : ∀ zl E2, x2 ≠ 0 → s.1.find? (hasEnd b) = some zl → (x1 ≠ 0 → s.1.find? (hasEnd x2) = none) →
      EndOK a b J (i + 1) E2 (x1, x2) → closeP a b (other b zl) E2 (s.1.erase zl) s.2 = some s' →
      W a b J (i + 1) s' := by
    intro zl E2 h0 hf nu e2 hcl
    obtain ⟨hz, he, Ll, sL, pL, hv⟩ := fromLeft zl h0 hf
    have sL' := sL
    obtain ⟨-, -, hp, u, -, hu, -, eu, -⟩ := sL'
    have hseg' : SegE a b J (i + 1) (other b zl) E2 (Ll ++ [(x1, x2)]) := by
      refine segE_snoc hpr hx sL hv (by unfold Adjacent; omega) (fun u' hu' => ?_) e2
      rw [hu] at hu'; cases hu'
      refine keep (hp u (List.mem_of_head? hu)) eu (fun h e => ?_) (fun _ => other_ne he (hseg zl hz).1)
      have := findNone (nu h) zl hz
      rw [← e, hasEnd_other he] at this; simp at this
    refine close_W hia hpr hx h4 hdone hnod hcov (K := [zl]) (rest := s.1.erase zl)
      (List.perm_cons_erase hz) (restNodup zl) (fun z hz' => ?_) hseg' ?_ ?_ ?_ hcl
    · obtain ⟨hzne, hz2⟩ := (hn.mem_erase_iff).mp hz'
      refine ⟨(hseg z hz2).1, keepSeg z hz2 (fun h => findNone (nu h) z hz2) (fun _ => ?_)⟩
      by_contra hb
      exact hzne (huniq hz2 hz (by omega) (by simpa using hb) he)
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact pL.append_right _
    · intro _; have := lenPos hv; simp; omega
    · exact neqLong hseg' (by have := lenPos hv; simp; omega)
  -- one piece attached from above
  have caseU : ∀ zu E2, x1 ≠ 0 → s.1.find? (hasEnd x2) = some zu → (x2 ≠ 0 → s.1.find? (hasEnd b) = none) →
      EndOK a b J (i + 1) E2 (x1, x2) → closeP a b (other x2 zu) E2 (s.1.erase zu) s.2 = some s' →
      W a b J (i + 1) s' := by
    intro zu E2 h0 hf nl e2 hcl
    obtain ⟨hz, he, Lu, sL, pL, hv⟩ := fromUp zu h0 hf
    have sL' := sL
    obtain ⟨-, -, hp, u, -, hu, -, eu, -⟩ := sL'
    have hseg' : SegE a b J (i + 1) (other x2 zu) E2 (Lu ++ [(x1, x2)]) := by
      refine segE_snoc hpr hx sL hv (by unfold Adjacent; omega) (fun u' hu' => ?_) e2
      rw [hu] at hu'; cases hu'
      refine keep (hp u (List.mem_of_head? hu)) eu (fun _ => other_ne he (hseg zu hz).1) (fun h e => ?_)
      have := findNone (nl h) zu hz
      rw [← e, hasEnd_other he] at this; simp at this
    refine close_W hia hpr hx h4 hdone hnod hcov (K := [zu]) (rest := s.1.erase zu)
      (List.perm_cons_erase hz) (restNodup zu) (fun z hz' => ?_) hseg' ?_ ?_ ?_ hcl
    · obtain ⟨hzne, hz2⟩ := (hn.mem_erase_iff).mp hz'
      refine ⟨(hseg z hz2).1, keepSeg z hz2 (fun _ => ?_) (fun h => findNone (nl h) z hz2)⟩
      by_contra hb
      exact hzne (huniq hz2 hz (by omega) (by simpa using hb) he)
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact pL.append_right _
    · intro _; have := lenPos hv; simp; omega
    · exact neqLong hseg' (by have := lenPos hv; simp; omega)
  -- pieces attached from above and from the left
  have case2 : ∀ zu zl, x1 ≠ 0 → x2 ≠ 0 → s.1.find? (hasEnd x2) = some zu → s.1.find? (hasEnd b) = some zl →
      zu ≠ zl → closeP a b (other x2 zu) (other b zl) ((s.1.erase zu).erase zl) s.2 = some s' →
      W a b J (i + 1) s' := by
    intro zu zl h0 h0' hfu hfl hne hcl
    obtain ⟨hzu, heu, Lu, sU, pU, hvu⟩ := fromUp zu h0 hfu
    obtain ⟨hzl, hel, Ll, sLl, pLl, hvl⟩ := fromLeft zl h0' hfl
    have sU' := sU
    obtain ⟨-, -, hpu', uu, -, huu, -, euu, -⟩ := sU'
    have sLl' := sLl
    obtain ⟨-, -, hpl', ul, -, hul, -, eul, -⟩ := sLl'
    have hdis : ∀ y ∈ Lu, y ∉ Ll := by
      intro y h1 h2
      exact hne (flatMap_unique hn hflat hzu hzl (pU.mem_iff.mp h1) (pLl.mem_iff.mp h2))
    have hseg' : SegE a b J (i + 1) (other x2 zu) (other b zl) (Lu ++ [(x1, x2)] ++ Ll.reverse) := by
      refine segE_join hpr hx sU sLl hdis hvu (by unfold Adjacent; omega) hvl (by unfold Adjacent; omega)
        (fun u' hu' => ?_) (fun u' hu' => ?_)
      · rw [huu] at hu'; cases hu'
        refine keep (hpu' uu (List.mem_of_head? huu)) euu (fun _ => other_ne heu (hseg zu hzu).1) (fun _ e => ?_)
        exact hne (huniq hzu hzl (by omega) (by rw [← e]; exact hasEnd_other heu) hel)
      · rw [hul] at hu'; cases hu'
        refine keep (hpl' ul (List.mem_of_head? hul)) eul (fun _ e => ?_) (fun _ => other_ne hel (hseg zl hzl).1)
        exact hne (huniq hzu hzl (by omega) heu (by rw [← e]; exact hasEnd_other hel))
    have hzl' : zl ∈ s.1.erase zu := (hn.mem_erase_iff).mpr ⟨Ne.symm hne, hzl⟩
    have hperm : s.1.Perm ([zu, zl] ++ (s.1.erase zu).erase zl) :=
      (List.perm_cons_erase hzu).trans (List.Perm.cons _ (List.perm_cons_erase hzl'))
    refine close_W hia hpr hx h4 hdone hnod hcov (K := [zu, zl]) (rest := (s.1.erase zu).erase zl)
      hperm ((restNodup zu).erase zl) (fun z hz' => ?_) hseg' ?_ ?_ ?_ hcl
    · obtain ⟨hz1, hz2⟩ := ((restNodup zu).mem_erase_iff).mp hz'
      obtain ⟨hz3, hz4⟩ := (hn.mem_erase_iff).mp hz2
      refine ⟨(hseg z hz4).1, keepSeg z hz4 (fun _ => ?_) (fun _ => ?_)⟩
      · by_contra hb; exact hz3 (huniq hz4 hzu (by omega) (by simpa using hb) heu)
      · by_contra hb; exact hz1 (huniq hz4 hzl (by omega) (by simpa using hb) hel)
    · rw [List.perm_iff_count]; intro y
      have h1 := pU.count_eq y
      have h2 := pLl.count_eq y
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_append, List.count_reverse] at h1 h2 ⊢
      omega
    · intro _; have := lenPos hvu; simp; omega
    · exact neqLong hseg' (by have := lenPos hvu; simp; omega)
  -- the DP's cases
  unfold stepCell at hs
  dsimp only at hs
  generalize hpu : (if x1 = 0 then none else s.1.find? (hasEnd x2)) = pu at hs
  generalize hpl : (if x2 = 0 then none else s.1.find? (hasEnd b)) = pl at hs
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
      Bool.false_and, Bool.true_and, beq_iff_eq] at hs
  · simp at hs
    exact case0 _ _ (nuOf rfl) (nlOf rfl) endD endR (by unfold exitE; split_ifs <;> omega)
      (by rw [isT_plug _ plugD]; simp) hs
  · rename_i zl
    obtain ⟨h0, hf⟩ := slOf zl rfl
    simp at hs
    rcases hs with hs | hs
    · exact caseL zl _ h0 hf (nuOf rfl) endD hs
    · exact caseL zl _ h0 hf (nuOf rfl) endR hs
  · rename_i zu
    obtain ⟨h0, hf⟩ := suOf zu rfl
    simp at hs
    rcases hs with hs | hs
    · exact caseU zu _ h0 hf (nlOf rfl) endD hs
    · exact caseU zu _ h0 hf (nlOf rfl) endR hs
  · rename_i zu zl
    obtain ⟨h0, hf⟩ := suOf zu rfl
    obtain ⟨h0', hf'⟩ := slOf zl rfl
    by_cases hne : zu = zl
    · simp [hne] at hs
    · simp [hne] at hs
      exact case2 zu zl h0 h0' hf hf' hne hs
  · rename_i col
    simp at hs
    rcases hs with hs | hs
    · exact case0 _ _ (nuOf rfl) (nlOf rfl) (endT col rfl) endD (tT col _ plugD)
        (by rw [isT_plug _ plugD]; simp) hs
    · exact case0 _ _ (nuOf rfl) (nlOf rfl) (endT col rfl) endR (tT col _ plugR)
        (by rw [isT_plug _ plugR]; simp) hs
  · rename_i col zl
    obtain ⟨h0, hf⟩ := slOf zl rfl
    simp at hs
    exact caseL zl _ h0 hf (nuOf rfl) (endT col rfl) hs
  · rename_i col zu
    obtain ⟨h0, hf⟩ := suOf zu rfl
    simp at hs
    exact caseU zu _ h0 hf (nlOf rfl) (endT col rfl) hs
  · simp at hs

end Step

section Final

variable {a b : ℕ} {J : Inst}

theorem W_zero : W a b J 0 ([], 0) := by
  refine ⟨fun _ => [], fun _ => [], List.nodup_nil, by omega, by simp, ?_, ?_, ?_⟩
  · intro col h; simp [doneCols, bitOf] at h
  · simp [allOf, doneCols, bitOf]
  · intro x; simp [allOf, doneCols, bitOf, prI]

/-- **Every final state of the DP is realizable.** -/
theorem inside_sound {tm : List ((ℕ × ℕ) × ℕ)} (htm : ∀ y : Coord, y.1 < a → y.2 < b → termAt tm y = endCol J y) :
    ∀ s ∈ inside a b tm, W a b J (a * b) s := by
  unfold inside
  suffices h : ∀ n, n ≤ a * b → ∀ s ∈ (List.range n).foldl (stage a b tm) [([], 0)], W a b J n s from
    h _ (le_refl _)
  intro n
  induction n with
  | zero => intro _ s hs; rw [List.mem_singleton.mp hs]; exact W_zero
  | succ n ih =>
    intro hn s hs
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hs
    unfold stage at hs
    rw [mem_normS, List.mem_flatMap] at hs
    obtain ⟨s0, h0, h1⟩ := hs
    exact step_W htm (by omega) (ih (by omega) s0 h0) h1

/-- **An accepting run gives a solution.** -/
theorem solvable_of_accept {tm : List ((ℕ × ℕ) × ℕ)}
    (htm : ∀ y : Coord, y.1 < J.w → y.2 < J.h → termAt tm y = endCol J y)
    (h : (([], 3) : St) ∈ inside J.w J.h tm) : Solvable J := by
  obtain ⟨sg, dp, -, -, -, hdone, hnod, hcov⟩ := inside_sound htm _ h
  have hd : doneCols 3 = [0, 1] := by decide
  simp only [hd, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hdone
  obtain ⟨p0, p1⟩ := hdone
  simp only [ends2, ite_true, show (1 : ℕ) ≠ 0 by omega, ite_false] at p0 p1
  have ha : allOf sg dp (([], 3) : St) = dp 0 ++ dp 1 := by simp [allOf, hd]
  rw [ha] at hnod hcov
  refine ⟨dp 0, dp 1, p0, p1, fun v hv hv' => ?_, fun v hv => ?_⟩
  · exact List.disjoint_of_nodup_append hnod hv hv'
  · have := (hcov v).mp (prI_all.mpr ⟨hv.1, hv.2⟩)
    exact List.mem_append.mp this

/-- At the end, a solution leaves no open pieces and both colours done. -/
theorem accept_of_solvable {tm : List ((ℕ × ℕ) × ℕ)} (hwf : J.WellFormed)
    (htm : ∀ y : Coord, y.1 < J.w → y.2 < J.h → termAt tm y = endCol J y) (hS : Solvable J) :
    (([], 3) : St) ∈ inside J.w J.h tm := by
  obtain ⟨p, q, hsol⟩ := hS
  obtain ⟨s, hs, hn, hm, hd⟩ := inside_complete hsol hwf (le_refl _) (le_refl _) htm
  have allP : ∀ y ∈ p, prI J.w J.h (J.w * J.h) y := fun y hy => prI_all.mpr (hsol.1.2.2.2.1 y hy)
  have allQ : ∀ y ∈ q, prI J.w J.h (J.w * J.h) y := fun y hy => prI_all.mpr (hsol.2.1.2.2.2.1 y hy)
  have hnil : s.1 = [] := by
    rcases hs1 : s.1 with _ | ⟨z, l⟩
    · rfl
    · exfalso
      obtain ⟨L, col, st, en, hL, hr, hinc, -⟩ := (hm z).mp (by rw [hs1]; exact List.mem_cons_self)
      have allL : ∀ y ∈ L, prI J.w J.h (J.w * J.h) y := by
        rcases hL with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact allP
        · exact allQ
      apply hinc
      constructor
      · rcases hr.left with h | h
        · exact h
        · exact absurd (allL _ (nth_mem (by have := hr.le; have := hr.lt; omega))) h
      · rcases hr.right with h | h
        · exact h
        · by_contra hne
          exact h (allL _ (nth_mem (by have := hr.lt; omega)))
  have h3 : s.2 = 3 := by
    rw [hd]; unfold doneMask; rw [ite_eq_left allP, ite_eq_left allQ]
  have : s = ([], 3) := by
    obtain ⟨s1, s2⟩ := s
    simp only at hnil h3
    rw [hnil, h3]
  rw [← this]; exact hs

end Final

/-! ### The decision procedure -/

def tmOf (J : Inst) : List ((ℕ × ℕ) × ℕ) := [(J.s0, 0), (J.t0, 0), (J.s1, 1), (J.t1, 1)]

theorem termAt_tmOf (J : Inst) (y : Coord) : termAt (tmOf J) y = endCol J y := by
  unfold termAt tmOf endCol
  by_cases h0 : y = J.s0
  · subst h0; simp
  by_cases h1 : y = J.t0
  · subst h1; simp [Ne.symm h0]
  by_cases h2 : y = J.s1
  · subst h2; simp [Ne.symm h0, Ne.symm h1]; exact ⟨h0, h1⟩
  by_cases h3 : y = J.t1
  · subst h3; simp [Ne.symm h0, Ne.symm h1, Ne.symm h2]; exact ⟨h0, h1⟩
  simp [Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3, h0, h1, h2, h3]

/-- The plug DP accepts. -/
def dpAccept (J : Inst) : Bool := (inside J.w J.h (tmOf J)).contains ([], 3)

/-- **The plug DP decides solvability** (any rectangle; it is fast when `J.h` is small). -/
theorem dpAccept_iff {J : Inst} (hwf : J.WellFormed) : dpAccept J = true ↔ Solvable J := by
  unfold dpAccept
  rw [List.contains_iff_mem]
  exact ⟨solvable_of_accept (fun y _ _ => termAt_tmOf J y),
    accept_of_solvable hwf (fun y _ _ => termAt_tmOf J y)⟩

/-- Rows along the longer side, so the frontier is the short side. -/
def thinB (J : Inst) : Bool := if J.h ≤ J.w then dpAccept J else dpAccept J.transpose

theorem thinB_iff {J : Inst} (hwf : J.WellFormed) : thinB J = true ↔ Solvable J := by
  unfold thinB
  split_ifs
  · exact dpAccept_iff hwf
  · rw [dpAccept_iff (wf_transpose hwf), solvable_transpose_iff]

end ZZN.Thin

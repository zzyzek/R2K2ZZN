-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.WinOut
import ZZN.SoundRMain

/-!
# Window certificates: outside runs do not cross

Each outside run, joined to the perimeter by staircase routes through the doubled window, is a chain
between perimeter points of the doubled grid; `t1_core` forbids two of them from crossing.
-/

namespace ZZN.Win

open GridHam

/-! ### Staircase routes from the exits -/

/-- Point `t` of the staircase from the right exit of row `r`: up on even steps, left on odd. -/
def stairPt (k r t : ℕ) : Coord :=
  if t % 2 = 0 then (2 * r - t / 2, 2 * k - 1 - t / 2) else (2 * r - 1 - t / 2, 2 * k - 1 - t / 2)

/-- The route from the right exit of row `r`: from `(2r, 2k−1)` to `(0, 2k−1−2r)`. -/
def routeR (k r : ℕ) : List Coord := (List.range (4 * r + 1)).map (stairPt k r)

/-- The route from exit slot `σ`: right exits as above, bottom exits transposed. -/
def route (k σ : ℕ) : List Coord :=
  if σ < k then routeR k σ else (routeR k (2 * k - 1 - σ)).map Prod.swap

theorem chain_range_map (f : ℕ → Coord) :
    ∀ n, (∀ t, t + 1 < n → Adjacent (f t) (f (t + 1))) → chainAdjacent ((List.range n).map f) = true
  | 0, _ => rfl
  | 1, _ => rfl
  | n + 2, h => by
    rw [List.range_succ, List.map_append]
    apply chainAdjacent_append_of (chain_range_map f (n + 1) (fun t ht => h t (by omega))) rfl
      (b := f (n + 1)) (a := f n)
    · rw [List.range_succ, List.map_append]; simp
    · rfl
    · exact h n (by omega)

theorem routeR_chain {k r : ℕ} (hr : r < k) : chainAdjacent (routeR k r) = true := by
  apply chain_range_map
  intro t ht
  unfold stairPt Adjacent
  rcases Nat.even_or_odd t with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [ite_eq_left (by omega), ite_eq_right (by omega)]
    simp only
    have : (i + i) / 2 = i := by omega
    have : (i + i + 1) / 2 = i := by omega
    omega
  · rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    simp only
    have : (2 * i + 1) / 2 = i := by omega
    have : (2 * i + 1 + 1) / 2 = i + 1 := by omega
    omega

theorem mem_routeR {k r : ℕ} (hr : r < k) {z : Coord} (h : z ∈ routeR k r) :
    z.1 ≤ 2 * r ∧ (z.2 + 2 * r + 1 = z.1 + 2 * k ∨ (z.2 + 2 * r = z.1 + 2 * k ∧ z.1 + 1 ≤ 2 * r)) := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h
  rw [List.mem_range] at ht
  unfold stairPt
  split_ifs with h0 <;> simp only <;> omega

theorem routeR_head {k r : ℕ} : (routeR k r).head? = some (2 * r, 2 * k - 1) := by
  unfold routeR
  rw [List.range_succ_eq_map]
  simp [stairPt]

theorem routeR_last {k r : ℕ} : (routeR k r).getLast? = some (0, 2 * k - 1 - 2 * r) := by
  have e : stairPt k r (4 * r) = (0, 2 * k - 1 - 2 * r) := by
    unfold stairPt; rw [ite_eq_left (by omega)]; congr 1 <;> omega
  unfold routeR
  rw [List.range_succ, List.map_append, List.getLast?_append]
  simp [e]

/-- Where the route from slot `σ` meets the perimeter of the doubled grid. -/
def routeEnd (k σ : ℕ) : Coord := if σ < k then (0, 2 * k - 1 - 2 * σ) else (2 * σ - 2 * k + 1, 0)

section Route

variable {k σ : ℕ} (hk : 1 ≤ k) (hσ : σ < 2 * k)
include hk hσ

omit hk in
theorem route_chain : chainAdjacent (route k σ) = true := by
  unfold route
  split_ifs with h
  · exact routeR_chain h
  · exact chainAdjacent_map_swap _ (routeR_chain (by omega))

omit hk in
theorem mem_route {z : Coord} (h : z ∈ route k σ) :
    (σ < k ∧ z.1 ≤ 2 * σ ∧ (z.2 + 2 * σ + 1 = z.1 + 2 * k ∨ (z.2 + 2 * σ = z.1 + 2 * k ∧ z.1 + 1 ≤ 2 * σ))) ∨
      (k ≤ σ ∧ z.2 ≤ 2 * (2 * k - 1 - σ) ∧
        (z.1 + 2 * (2 * k - 1 - σ) + 1 = z.2 + 2 * k ∨
          (z.1 + 2 * (2 * k - 1 - σ) = z.2 + 2 * k ∧ z.2 + 1 ≤ 2 * (2 * k - 1 - σ)))) := by
  unfold route at h
  split_ifs at h with hs
  · exact Or.inl ⟨hs, mem_routeR hs h⟩
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
    have := mem_routeR (by omega) hw
    exact Or.inr ⟨by omega, this.1, this.2⟩

theorem route_box {z : Coord} (h : z ∈ route k σ) : z.1 ≤ 2 * k - 1 ∧ z.2 ≤ 2 * k - 1 := by
  rcases mem_route hσ h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega

theorem route_head : (route k σ).head? = some (dm (inCell k σ) (exitCell k k σ)) := by
  unfold route inCell exitCell dm
  split_ifs with h
  · rw [routeR_head]; simp only [Option.some.injEq, Prod.mk.injEq]; omega
  · rw [List.head?_map, routeR_head]; simp only [Option.map_some, Prod.swap_prod_mk, Option.some.injEq,
      Prod.mk.injEq]; omega

omit hk in
theorem route_last : (route k σ).getLast? = some (routeEnd k σ) := by
  unfold route routeEnd
  by_cases h : σ < k
  · rw [ite_eq_left h, ite_eq_left h]; exact routeR_last
  · rw [ite_eq_right h, ite_eq_right h, List.getLast?_map, routeR_last]
    simp only [Option.map_some, Prod.swap_prod_mk, Option.some.injEq, Prod.mk.injEq, and_true]
    omega

end Route

theorem route_disj {k σ σ' : ℕ} (_hk : 1 ≤ k) (hσ : σ < 2 * k) (hσ' : σ' < 2 * k) (hne : σ ≠ σ') {z : Coord}
    (h : z ∈ route k σ) (h' : z ∈ route k σ') : False := by
  rcases mem_route hσ h with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ <;>
    rcases mem_route hσ' h' with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩ <;> omega

/-! ### Anchors of the outside ends -/

section Anc

variable {k w h : ℕ} (hk : 1 ≤ k) (hkw : k < w) (hkh : k < h)
include hk hkw hkh

theorem anc_routeEnd {σ : ℕ} (hσ : σ < 2 * k) :
    Planar.anc (2 * w - 1) (2 * h - 1) (routeEnd k σ) =
      if σ < k then 2 * k - 2 * σ else 2 * (2 * h - 1) + 2 * (2 * w - 1) + 2 + 2 * k - 2 * σ := by
  unfold routeEnd Planar.anc
  by_cases hs : σ < k
  · rw [ite_eq_left hs, ite_eq_left hs]; simp only; rw [ite_eq_left trivial]; omega
  · rw [ite_eq_right hs, ite_eq_right hs]; simp only
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]; omega

theorem routeEnd_perim {σ : ℕ} (hσ : σ < 2 * k) :
    OnPerim (2 * w - 1) (2 * h - 1) (routeEnd k σ) ∧ (routeEnd k σ).1 < 2 * w - 1 ∧ (routeEnd k σ).2 < 2 * h - 1 := by
  unfold routeEnd OnPerim
  by_cases hs : σ < k
  · rw [ite_eq_left hs]; exact ⟨Or.inl rfl, by simp only; omega, by simp only; omega⟩
  · rw [ite_eq_right hs]; exact ⟨Or.inr (Or.inr (Or.inl rfl)), by simp only; omega, by simp only; omega⟩

/-- F's anchor lies strictly between the right exits' and the bottom exits'. -/
theorem anc_F {E : Coord} (hE1 : E.1 < w) (hE2 : E.2 < h) (hout : ¬ (E.1 < k ∧ E.2 < k))
    (hp : E.1 = 0 ∨ E.2 = 0 ∨ E.1 = w - 1 ∨ E.2 = h - 1) :
    2 * k < Planar.anc (2 * w - 1) (2 * h - 1) (dd E) ∧
      Planar.anc (2 * w - 1) (2 * h - 1) (dd E) < 2 * (2 * h - 1) + 2 * (2 * w - 1) + 4 - 2 * k := by
  obtain ⟨e1, e2⟩ := E
  simp only at hE1 hE2 hout hp
  unfold dd Planar.anc
  simp only
  split_ifs <;> omega

omit hk hkw hkh in
theorem dd_perim {E : Coord} (hE1 : E.1 < w) (hE2 : E.2 < h)
    (hp : E.1 = 0 ∨ E.2 = 0 ∨ E.1 = w - 1 ∨ E.2 = h - 1) :
    OnPerim (2 * w - 1) (2 * h - 1) (dd E) ∧ (dd E).1 < 2 * w - 1 ∧ (dd E).2 < 2 * h - 1 := by
  obtain ⟨e1, e2⟩ := E
  simp only at hE1 hE2 hp
  unfold dd OnPerim; simp only; omega

end Anc

/-! ### Outside runs and their doubled chains -/

def segOf (L : List Coord) (a b : ℕ) : List Coord := (L.drop a).take (b + 1 - a)

section Seg

variable {L : List Coord} {a b : ℕ} (hab : a ≤ b) (hb : b < L.length)
include hab hb

omit hab in
theorem segOf_length : (segOf L a b).length = b + 1 - a := by
  unfold segOf; simp; omega

theorem segOf_getD {i : ℕ} (hi : i ≤ b - a) : (segOf L a b).getD i (0, 0) = nth L (a + i) := by
  unfold segOf nth
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by omega)]
  simp

theorem mem_segOf {z : Coord} : z ∈ segOf L a b ↔ ∃ j, a ≤ j ∧ j ≤ b ∧ z = nth L j := by
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
    rw [segOf_length hb] at hi
    refine ⟨a + i, by omega, by omega, ?_⟩
    rw [← segOf_getD hab hb (i := i) (by omega), List.getD_eq_getElem _ _ (by rw [segOf_length hb]; omega)]
  · rintro ⟨j, h1, h2, rfl⟩
    rw [← show a + (j - a) = j by omega, ← segOf_getD hab hb (i := j - a) (by omega)]
    rw [List.getD_eq_getElem _ _ (by rw [segOf_length hb]; omega)]
    exact List.getElem_mem _

omit hab hb in
theorem segOf_infix : segOf L a b <:+: L := by
  unfold segOf
  exact (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix

theorem segOf_head : (segOf L a b).head? = some (nth L a) := by
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by rw [segOf_length hb]; omega)]
  congr 1
  have := segOf_getD hab hb (i := 0) (by omega)
  rw [List.getD_eq_getElem _ _ (by rw [segOf_length hb]; omega)] at this
  simpa using this

theorem segOf_last : (segOf L a b).getLast? = some (nth L b) := by
  have hl := segOf_length (L := L) (a := a) hb
  have h : (segOf L a b).length - 1 < (segOf L a b).length := by omega
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem h]
  congr 1
  rw [← List.getD_eq_getElem _ (0, 0) h, hl, show b + 1 - a - 1 = b - a by omega,
    segOf_getD hab hb (le_refl _), show a + (b - a) = b by omega]

end Seg

/-- Doubled points of cells outside the window, and of edges between them, lie outside the doubled
window. -/
theorem dpN_out {k : ℕ} {S : List Coord} (hc : chainAdjacent S = true) (hS : ∀ y ∈ S, ¬ (y.1 < k ∧ y.2 < k))
    {z : Coord} (hz : z ∈ dpN S) : 2 * k ≤ z.1 ∨ 2 * k ≤ z.2 := by
  rcases mem_dpN hc hz with ⟨y, hy, rfl⟩ | ⟨y, hy, y', hy', ha, rfl⟩
  · have := hS y hy; unfold dd; simp only; omega
  · have h1 := hS y hy; have h2 := hS y' hy'
    obtain ⟨y1, y2⟩ := y; obtain ⟨y1', y2'⟩ := y'
    unfold Adjacent at ha; unfold dm; simp only at *; omega

theorem adj_dm_dd {u v : Coord} (h : Adjacent u v) : Adjacent (dm u v) (dd v) := by
  obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v
  unfold Adjacent at *; unfold dm dd; simp only at *; omega

/-- The doubled chain of an outside run `[a, b]` of `L`, joined to the perimeter by the routes of
its crossings. -/
def runChain (k : ℕ) (L : List Coord) (a b : ℕ) : List Coord :=
  (if a = 0 then [] else (route k (crossSlot k L (a - 1))).reverse) ++ dpN (segOf L a b) ++
    (if b + 1 = L.length then [] else route k (crossSlot k L b))

section RunChain

variable {k : ℕ} {L : List Coord} {a b : ℕ} (hk : 1 ≤ k) (hc : chainAdjacent L = true)
  (hab : a ≤ b) (hb : b < L.length) (hout : ∀ j, a ≤ j → j ≤ b → inWb k (nth L j) = false)
  (hleft : a = 0 ∨ IsCross k L (a - 1)) (hright : b + 1 = L.length ∨ IsCross k L b)
include hk hc hab hb hout hleft hright

omit hk hc hb hright in
theorem crossEdge_left (ha : a ≠ 0) : crossEdge k L (a - 1) = (nth L (a - 1), nth L a) := by
  have hcr := hleft.resolve_left ha
  have h1 := hout a (le_refl _) hab
  have e : a - 1 + 1 = a := by omega
  unfold crossEdge
  have h0 : inWb k (nth L (a - 1)) = true := by
    have := hcr.2; rw [e, h1] at this; cases g : inWb k (nth L (a - 1)) <;> simp_all
  rw [ite_eq_left h0, e]

omit hk hc hb hleft in
theorem crossEdge_right (hr : b + 1 ≠ L.length) : crossEdge k L b = (nth L (b + 1), nth L b) := by
  have hcr := hright.resolve_left hr
  have h1 := hout b hab (le_refl _)
  unfold crossEdge
  rw [ite_eq_right (by rw [h1]; simp)]

theorem runChain_props :
    chainAdjacent (runChain k L a b) = true ∧
      (runChain k L a b).head? = some (if a = 0 then dd (nth L a) else routeEnd k (crossSlot k L (a - 1))) ∧
      (runChain k L a b).getLast? =
        some (if b + 1 = L.length then dd (nth L b) else routeEnd k (crossSlot k L b)) ∧
      ∀ z ∈ runChain k L a b, (a ≠ 0 ∧ z ∈ route k (crossSlot k L (a - 1))) ∨
        (b + 1 ≠ L.length ∧ z ∈ route k (crossSlot k L b)) ∨ z ∈ dpN (segOf L a b) := by
  have cS := chain_infix (segOf_infix (a := a) (b := b)) hc
  have cD := dpN_chain _ cS
  have sh := segOf_head (L := L) hab hb
  have sl := segOf_last (L := L) hab hb
  obtain ⟨rest, hrest⟩ : ∃ rest, segOf L a b = nth L a :: rest := by
    cases h : segOf L a b with
    | nil => rw [h] at sh; simp at sh
    | cons x r => rw [h] at sh; simp at sh; exact ⟨r, by rw [sh]⟩
  obtain ⟨T, hT⟩ := dpN_head (nth L a) rest
  have dH : (dpN (segOf L a b)).head? = some (dd (nth L a)) := by rw [hrest, hT]; rfl
  have dL : (dpN (segOf L a b)).getLast? = some (dd (nth L b)) := by
    rw [hrest, dpN_last]
    congr 2
    rw [hrest] at sl
    rw [List.getLast?_cons] at sl
    simpa using sl
  -- the left part
  have left : chainAdjacent ((if a = 0 then [] else (route k (crossSlot k L (a - 1))).reverse) ++
      dpN (segOf L a b)) = true ∧
      ((if a = 0 then [] else (route k (crossSlot k L (a - 1))).reverse) ++ dpN (segOf L a b)).head? =
        some (if a = 0 then dd (nth L a) else routeEnd k (crossSlot k L (a - 1))) := by
    by_cases ha : a = 0
    · rw [ite_eq_left ha, ite_eq_left ha]; exact ⟨cD, dH⟩
    · rw [ite_eq_right ha, ite_eq_right ha]
      have hcr := hleft.resolve_left ha
      have hσ := crossSlot_lt hc hcr
      have ex := cross_exit hc hcr
      have ce := crossEdge_left hab hout hleft ha
      rw [ce] at ex
      have rh := route_head hk hσ
      unfold crossSlot at rh
      rw [ce] at rh
      dsimp only at rh
      rw [inCell_slot ex, exitCell_slot ex] at rh
      refine ⟨chainAdjacent_append_of (chainAdjacent_reverse _ (route_chain hσ)) cD
        (by rw [List.getLast?_reverse]; unfold crossSlot; rw [ce]; exact rh) dH (adj_dm_dd ex.2.2.2), ?_⟩
      rw [List.head?_append, List.head?_reverse, route_last hσ]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases hr : b + 1 = L.length
    · rw [runChain, ite_eq_left hr, List.append_nil]; exact left.1
    · rw [runChain, ite_eq_right hr]
      have hcr := hright.resolve_left hr
      have hσ := crossSlot_lt hc hcr
      have ex := cross_exit hc hcr
      have ce := crossEdge_right hab hout hright hr
      rw [ce] at ex
      have rh := route_head hk hσ
      unfold crossSlot at rh
      rw [ce] at rh
      dsimp only at rh
      rw [inCell_slot ex, exitCell_slot ex] at rh
      have lastL : ((if a = 0 then [] else (route k (crossSlot k L (a - 1))).reverse) ++
          dpN (segOf L a b)).getLast? = some (dd (nth L b)) := by
        rw [List.getLast?_append, dL]; rfl
      refine chainAdjacent_append_of left.1 (route_chain hσ) lastL (by unfold crossSlot; rw [ce]; exact rh) ?_
      exact adj_symm (adj_dm_dd ex.2.2.2)
  · rw [runChain, List.append_assoc, List.head?_append]
    by_cases ha : a = 0
    · rw [ite_eq_left ha, ite_eq_left ha, List.head?_append, dH]; rfl
    · rw [ite_eq_right ha, ite_eq_right ha, List.head?_reverse, route_last (crossSlot_lt hc (hleft.resolve_left ha))]
      rfl
  · by_cases hr : b + 1 = L.length
    · rw [runChain, ite_eq_left hr, List.append_nil, List.getLast?_append, dL, ite_eq_left hr]; rfl
    · rw [runChain, ite_eq_right hr, ite_eq_right hr, List.getLast?_append, route_last (crossSlot_lt hc (hright.resolve_left hr))]
      rfl
  · intro z hz
    unfold runChain at hz
    simp only [List.mem_append] at hz
    rcases hz with (h | h) | h
    · by_cases ha : a = 0
      · rw [ite_eq_left ha] at h; simp at h
      · rw [ite_eq_right ha, List.mem_reverse] at h; exact Or.inl ⟨ha, h⟩
    · exact Or.inr (Or.inr h)
    · by_cases hr : b + 1 = L.length
      · rw [ite_eq_left hr] at h; simp at h
      · rw [ite_eq_right hr] at h; exact Or.inr (Or.inl ⟨hr, h⟩)

end RunChain

/-! ### Matched pairs are outside runs -/

section Pairs

variable {k : ℕ} {s : St} {L : List Coord}

/-- **A matched pair of a chain is the pair of ends of an outside run.** -/
theorem pair_run (hL : 0 < L.length) {t : ℕ} (ht : 2 * t + 1 < (chainOf k s L).length) :
    ∃ a b, a ≤ b ∧ b < L.length ∧ (∀ j, a ≤ j → j ≤ b → inWb k (nth L j) = false) ∧
      (a = 0 ∨ IsCross k L (a - 1)) ∧ (b + 1 = L.length ∨ IsCross k L b) ∧
      (chainOf k s L).getD (2 * t) 0 =
        (if a = 0 then (usedOf k k s).length else (usedOf k k s).idxOf (crossSlot k L (a - 1))) ∧
      (chainOf k s L).getD (2 * t + 1) 0 =
        (if b + 1 = L.length then (usedOf k k s).length else (usedOf k k s).idxOf (crossSlot k L b)) := by
  have hlen := chainOf_length (k := k) (s := s) (L := L)
  have hev := chainOf_even (k := k) (s := s) hL
  have e := status_end (k := k) hL
  have oL : offL k L = 0 ∨ offL k L = 1 := by unfold offL; split_ifs <;> simp
  have oR : offR k L = 0 ∨ offR k L = 1 := by unfold offR; split_ifs <;> simp
  set r := (CI k L).length with hr
  -- the left end
  have left : ∃ a, (a = 0 ∧ offL k L = 1 ∧ t = 0 ∧ (chainOf k s L).getD 0 0 = (usedOf k k s).length) ∨
      (0 < a ∧ ∃ i, i < r ∧ 2 * t = offL k L + i ∧ a = (CI k L).getD i 0 + 1) := by
    by_cases h : offL k L = 1 ∧ t = 0
    · exact ⟨0, Or.inl ⟨rfl, h.1, h.2, chainOf_first h.1⟩⟩
    · refine ⟨(CI k L).getD (2 * t - offL k L) 0 + 1, Or.inr ⟨by omega, 2 * t - offL k L, ?_, ?_, rfl⟩⟩
      · omega
      · omega
  -- outside after a crossing at an even chain position
  have outAfter : ∀ i, i < r → 2 * t = offL k L + i → inWb k (nth L ((CI k L).getD i 0 + 1)) = false := by
    intro i hi h2
    rw [status_after hi hL]
    unfold offL at h2
    split_ifs at h2 with g <;> split_ifs with g' <;> simp_all <;> omega
  -- the run from `a` to the next crossing, or to the end
  have runTo : ∀ a0, (a0 = 0 ∨ IsCross k L (a0 - 1)) → inWb k (nth L a0) = false →
      ∀ i', a0 ≤ (CI k L).getD i' 0 → i' < r → (∀ j, a0 ≤ j → j < (CI k L).getD i' 0 → ¬ IsCross k L j) →
        ∀ j, a0 ≤ j → j ≤ (CI k L).getD i' 0 → inWb k (nth L j) = false := by
    intro a0 _ h0 i' h1 hi' hgap j hj1 hj2
    have hc := CI_mem (k := k) (L := L) hi'
    rw [status_const (L := L) (a := a0) j hj1 (by have := hc.1; omega) (fun j' a' b' => hgap j' a' (by omega))]
    exact h0
  obtain ⟨a, ha⟩ := left
  rcases ha with ⟨rfl, hoff, rfl, hN0⟩ | ⟨hapos, i, hi, h2t, rfl⟩
  · -- F starts the run
    have h0 : inWb k (nth L 0) = false := by
      unfold offL at hoff; split_ifs at hoff with g; simpa using g
    by_cases hr0 : r = 0
    · -- no crossing: the whole path is outside
      have hR : offR k L = 1 := by omega
      refine ⟨0, L.length - 1, Nat.zero_le _, by omega, fun j _ hj => ?_, Or.inl rfl, Or.inl (by omega), ?_, ?_⟩
      · rw [status_const (L := L) (a := 0) j (Nat.zero_le _) (by omega) (fun j' _ _ => CI_none hr0 j')]; exact h0
      · simpa using hN0
      · rw [ite_eq_left (by omega)]
        have := chainOf_last (k := k) (s := s) hR
        rw [show (chainOf k s L).length - 1 = 2 * 0 + 1 by omega] at this
        exact this
    · have hc := CI_mem (k := k) (L := L) (i := 0) (by omega)
      refine ⟨0, (CI k L).getD 0 0, Nat.zero_le _, by have := hc.1; omega, ?_, Or.inl rfl,
        Or.inr hc, by simpa using hN0, ?_⟩
      · intro j _ hj
        rw [status_const (L := L) (a := 0) j (Nat.zero_le _) (by have := hc.1; omega)
          (fun j' _ b' => CI_before (by omega) (by omega))]
        exact h0
      · rw [ite_eq_right (by have := hc.1; omega)]
        have := chainOf_mid (k := k) (s := s) (L := L) (i := 0) (by omega)
        rw [hoff] at this; simpa using this
  · -- a crossing starts the run
    have hc := CI_mem (k := k) (L := L) hi
    have hout0 := outAfter i hi h2t
    have nA : (chainOf k s L).getD (2 * t) 0 = (usedOf k k s).idxOf (crossSlot k L ((CI k L).getD i 0)) := by
      rw [h2t]; exact chainOf_mid hi
    by_cases hlast : i + 1 < r
    · have hc' := CI_mem (k := k) (L := L) hlast
      have lt := CI_get_lt (k := k) (L := L) hlast (Nat.lt_succ_self i)
      refine ⟨(CI k L).getD i 0 + 1, (CI k L).getD (i + 1) 0, by omega, hc'.1.trans' (by omega),
        runTo _ (Or.inr (by simpa using hc)) hout0 (i + 1) (by omega) hlast
          (fun j a' b' => CI_gap hlast (by omega) b'),
        Or.inr (by simpa using hc), Or.inr hc', ?_, ?_⟩
      · rw [ite_eq_right (by omega), Nat.add_sub_cancel]; exact nA
      · rw [ite_eq_right (by have := hc'.1; omega)]
        rw [show 2 * t + 1 = offL k L + (i + 1) by omega]; exact chainOf_mid hlast
    · -- the last crossing: F ends the run
      have hi1 : i = r - 1 := by omega
      have hR : offR k L = 1 := by omega
      refine ⟨(CI k L).getD i 0 + 1, L.length - 1, by have := hc.1; omega, by omega, ?_,
        Or.inr (by simpa using hc), Or.inl (by omega), ?_, ?_⟩
      · intro j h1 h2
        rw [status_const (L := L) (a := (CI k L).getD i 0 + 1) j h1 (by omega)
          (fun j' a' b' => CI_after (by omega) (by rw [← hi1]; omega))]
        exact hout0
      · rw [ite_eq_right (by omega), Nat.add_sub_cancel]; exact nA
      · rw [ite_eq_left (by omega)]
        have := chainOf_last (k := k) (s := s) hR
        rw [show (chainOf k s L).length - 1 = 2 * t + 1 by omega] at this
        exact this

end Pairs

/-! ### Two matched pairs never cross -/

/-- The perimeter anchor of an outside end: a route end for an exit, the doubled F cell for F. -/
def Kof (k w h : ℕ) (s : St) (E : Coord) (i : ℕ) : ℕ :=
  if i < (usedOf k k s).length then Planar.anc (2 * w - 1) (2 * h - 1) (routeEnd k ((usedOf k k s).getD i 0))
  else Planar.anc (2 * w - 1) (2 * h - 1) (dd E)

theorem Kof_slot {k w h : ℕ} {s : St} {E : Coord} {σ : ℕ} (hσ : σ ∈ usedOf k k s) :
    Kof k w h s E ((usedOf k k s).idxOf σ) = Planar.anc (2 * w - 1) (2 * h - 1) (routeEnd k σ) := by
  have lt := List.idxOf_lt_length_iff.mpr hσ
  unfold Kof; rw [ite_eq_left lt, List.getD_eq_getElem _ _ lt, List.getElem_idxOf lt]

theorem Kof_F {k w h : ℕ} {s : St} {E : Coord} :
    Kof k w h s E (usedOf k k s).length = Planar.anc (2 * w - 1) (2 * h - 1) (dd E) := by
  unfold Kof; rw [ite_eq_right (lt_irrefl _)]

section PairOK

variable {k : ℕ} {J : Inst} {p q : List Coord} {F : FSpec} {s : St}
  (W : WinSetup k J p q F) (hinv : Inv k k (k * k) p q s)
include W hinv

omit W hinv in
/-- An outside run, as a run of the outside cells. -/
theorem outRun {L : List Coord} {a b : ℕ} (hab : a ≤ b) (hb : b < L.length)
    (hout : ∀ j, a ≤ j → j ≤ b → inWb k (nth L j) = false)
    (hl : a = 0 ∨ IsCross k L (a - 1)) (hr : b + 1 = L.length ∨ IsCross k L b) :
    IsRun (fun y => inWb k y = false) L a b := by
  refine ⟨hab, hb, hout, ?_, ?_⟩
  · by_cases h0 : a = 0
    · exact Or.inl h0
    · have h := hl.resolve_left h0
      right; intro c
      have := h.2; rw [show a - 1 + 1 = a by omega, c, hout a (le_refl _) hab] at this; exact this rfl
  · rcases hr with h | h
    · exact Or.inl h
    · right; intro c
      have := h.2; rw [c, hout b hab (le_refl _)] at this; exact this rfl

/-- **Two matched pairs with distinct nodes do not cross.** -/
theorem pair_ok {E : Coord} (hEq : ∀ x, IsEnd J x → ¬ (x.1 < k ∧ x.2 < k) → x = E)
    (hEp : ∀ x, IsEnd J x → ¬ (x.1 < k ∧ x.2 < k) → x.1 = 0 ∨ x.2 = 0 ∨ x.1 = J.w - 1 ∨ x.2 = J.h - 1)
    {L L' : List Coord} {col col' t t' : ℕ} (hp : PathC p q L col) (hp' : PathC p q L' col')
    (ht : 2 * t + 1 < (chainOf k s L).length) (ht' : 2 * t' + 1 < (chainOf k s L').length)
    (d13 : (chainOf k s L).getD (2 * t) 0 ≠ (chainOf k s L').getD (2 * t') 0)
    (d14 : (chainOf k s L).getD (2 * t) 0 ≠ (chainOf k s L').getD (2 * t' + 1) 0)
    (d23 : (chainOf k s L).getD (2 * t + 1) 0 ≠ (chainOf k s L').getD (2 * t') 0)
    (d24 : (chainOf k s L).getD (2 * t + 1) 0 ≠ (chainOf k s L').getD (2 * t' + 1) 0)
    (n1 : Kof k J.w J.h s E ((chainOf k s L).getD (2 * t) 0) ≠ Kof k J.w J.h s E ((chainOf k s L).getD (2 * t + 1) 0))
    (n2 : Kof k J.w J.h s E ((chainOf k s L').getD (2 * t') 0) ≠ Kof k J.w J.h s E ((chainOf k s L).getD (2 * t) 0))
    (n3 : Kof k J.w J.h s E ((chainOf k s L').getD (2 * t') 0) ≠ Kof k J.w J.h s E ((chainOf k s L).getD (2 * t + 1) 0))
    (n4 : Kof k J.w J.h s E ((chainOf k s L').getD (2 * t' + 1) 0) ≠ Kof k J.w J.h s E ((chainOf k s L).getD (2 * t) 0))
    (n5 : Kof k J.w J.h s E ((chainOf k s L').getD (2 * t' + 1) 0) ≠ Kof k J.w J.h s E ((chainOf k s L).getD (2 * t + 1) 0)) :
    ¬ Crosses (Kof k J.w J.h s E ((chainOf k s L).getD (2 * t) 0)) (Kof k J.w J.h s E ((chainOf k s L).getD (2 * t + 1) 0))
      (Kof k J.w J.h s E ((chainOf k s L').getD (2 * t') 0)) (Kof k J.w J.h s E ((chainOf k s L').getD (2 * t' + 1) 0)) := by
  have hk : 1 ≤ k := by have := W.k2; omega
  obtain ⟨hL, -⟩ := pathC_ends W hp
  obtain ⟨hL', -⟩ := pathC_ends W hp'
  obtain ⟨nL, cL, -⟩ := pathC_facts W.sol hp
  obtain ⟨nL', cL', -⟩ := pathC_facts W.sol hp'
  obtain ⟨a, b, hab, hb, hout, hl, hr, e1, e2⟩ := pair_run (s := s) hL ht
  obtain ⟨a', b', hab', hb', hout', hl', hr', e1', e2'⟩ := pair_run (s := s) hL' ht'
  obtain ⟨cA, hA, lA, mA⟩ := runChain_props hk cL hab hb hout hl hr
  obtain ⟨cQ, hQ, lQ, mQ⟩ := runChain_props hk cL' hab' hb' hout' hl' hr'
  -- cells of the grid
  have inG : ∀ {M : List Coord} {c : ℕ}, PathC p q M c → ∀ v ∈ M, v.1 < J.w ∧ v.2 < J.h := by
    intro M c hM v hv
    rcases hM with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact W.sol.1.2.2.2.1 v hv
    · exact W.sol.2.1.2.2.2.1 v hv
  -- the ends and their keys
  have endE : ∀ {M : List Coord} {c : ℕ}, PathC p q M c → ∀ j, (j = 0 ∨ j + 1 = M.length) → j < M.length →
      inWb k (nth M j) = false → nth M j = E ∧ (nth M j).1 < J.w ∧ (nth M j).2 < J.h ∧
        ((nth M j).1 = 0 ∨ (nth M j).2 = 0 ∨ (nth M j).1 = J.w - 1 ∨ (nth M j).2 = J.h - 1) := by
    intro M c hM j hj hjl hw
    obtain ⟨-, s0, t0, -, hs, ht0, -, hc⟩ := pathC_ends W hM
    have isE : IsEnd J (nth M j) := by
      rcases hj with rfl | e
      · rw [hs]; rcases hc with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> unfold IsEnd <;> simp
      · rw [show j = M.length - 1 by omega, ht0]; rcases hc with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> unfold IsEnd <;> simp
    have no : ¬ ((nth M j).1 < k ∧ (nth M j).2 < k) := fun c' => by rw [inWb_iff.mpr c'] at hw; exact absurd hw (by simp)
    exact ⟨hEq _ isE no, (inG hM _ (nth_mem hjl)).1, (inG hM _ (nth_mem hjl)).2, hEp _ isE no⟩
  have usedA : a ≠ 0 → crossSlot k L (a - 1) ∈ usedOf k k s := fun h =>
    (used_iff W.k8 W.sol hinv _).mpr ⟨L, col, a - 1, hp, hl.resolve_left h, rfl⟩
  have usedB : b + 1 ≠ L.length → crossSlot k L b ∈ usedOf k k s := fun h =>
    (used_iff W.k8 W.sol hinv _).mpr ⟨L, col, b, hp, hr.resolve_left h, rfl⟩
  have usedA' : a' ≠ 0 → crossSlot k L' (a' - 1) ∈ usedOf k k s := fun h =>
    (used_iff W.k8 W.sol hinv _).mpr ⟨L', col', a' - 1, hp', hl'.resolve_left h, rfl⟩
  have usedB' : b' + 1 ≠ L'.length → crossSlot k L' b' ∈ usedOf k k s := fun h =>
    (used_iff W.k8 W.sol hinv _).mpr ⟨L', col', b', hp', hr'.resolve_left h, rfl⟩
  -- keys are anchors of the chain ends
  have kA1 : Kof k J.w J.h s E ((chainOf k s L).getD (2 * t) 0) =
      Planar.anc (2 * J.w - 1) (2 * J.h - 1) (if a = 0 then dd (nth L a) else routeEnd k (crossSlot k L (a - 1))) := by
    rw [e1]; split_ifs with h0
    · rw [Kof_F, (endE hp a (Or.inl h0) (by omega) (hout a le_rfl hab)).1]
    · rw [Kof_slot (usedA h0)]
  have kA2 : Kof k J.w J.h s E ((chainOf k s L).getD (2 * t + 1) 0) =
      Planar.anc (2 * J.w - 1) (2 * J.h - 1) (if b + 1 = L.length then dd (nth L b) else routeEnd k (crossSlot k L b)) := by
    rw [e2]; split_ifs with h0
    · rw [Kof_F, (endE hp b (Or.inr h0) (by omega) (hout b hab le_rfl)).1]
    · rw [Kof_slot (usedB h0)]
  have kQ1 : Kof k J.w J.h s E ((chainOf k s L').getD (2 * t') 0) =
      Planar.anc (2 * J.w - 1) (2 * J.h - 1) (if a' = 0 then dd (nth L' a') else routeEnd k (crossSlot k L' (a' - 1))) := by
    rw [e1']; split_ifs with h0
    · rw [Kof_F, (endE hp' a' (Or.inl h0) (by omega) (hout' a' le_rfl hab')).1]
    · rw [Kof_slot (usedA' h0)]
  have kQ2 : Kof k J.w J.h s E ((chainOf k s L').getD (2 * t' + 1) 0) =
      Planar.anc (2 * J.w - 1) (2 * J.h - 1) (if b' + 1 = L'.length then dd (nth L' b') else routeEnd k (crossSlot k L' b')) := by
    rw [e2']; split_ifs with h0
    · rw [Kof_F, (endE hp' b' (Or.inr h0) (by omega) (hout' b' hab' le_rfl)).1]
    · rw [Kof_slot (usedB' h0)]
  rw [kA1, kA2] at n1
  rw [kQ1, kA1] at n2
  rw [kQ1, kA2] at n3
  rw [kQ2, kA1] at n4
  rw [kQ2, kA2] at n5
  rw [kA1, kA2, kQ1, kQ2]
  have cS := chain_infix (segOf_infix (a := a) (b := b)) cL
  have cS' := chain_infix (segOf_infix (a := a') (b := b')) cL'
  have segIn : ∀ {M : List Coord} {c : ℕ}, PathC p q M c → ∀ {a0 b0 : ℕ}, a0 ≤ b0 → b0 < M.length →
      ∀ v ∈ segOf M a0 b0, v.1 < J.w ∧ v.2 < J.h := by
    intro M c hM a0 b0 h1 h2 v hv
    obtain ⟨j, -, hj, rfl⟩ := (mem_segOf h1 h2).mp hv
    exact inG hM _ (nth_mem (by omega))
  have segOut : ∀ {M : List Coord} {a0 b0 : ℕ}, a0 ≤ b0 → b0 < M.length →
      (∀ j, a0 ≤ j → j ≤ b0 → inWb k (nth M j) = false) → ∀ y ∈ segOf M a0 b0, ¬ (y.1 < k ∧ y.2 < k) := by
    intro M a0 b0 h1 h2 ho y hy c
    obtain ⟨j, hj1, hj2, rfl⟩ := (mem_segOf h1 h2).mp hy
    have := ho j hj1 hj2
    rw [inWb_iff.mpr c] at this; exact absurd this (by simp)
  have inA : ∀ {M : List Coord} {c : ℕ} (hM : PathC p q M c) {a0 b0 : ℕ} (h1 : a0 ≤ b0) (h2 : b0 < M.length),
      ∀ v, ((a0 ≠ 0 ∧ v ∈ route k (crossSlot k M (a0 - 1))) ∨ (b0 + 1 ≠ M.length ∧ v ∈ route k (crossSlot k M b0)) ∨
        v ∈ dpN (segOf M a0 b0)) → (a0 ≠ 0 → crossSlot k M (a0 - 1) < 2 * k) → (b0 + 1 ≠ M.length → crossSlot k M b0 < 2 * k) →
        v.1 < 2 * J.w - 1 ∧ v.2 < 2 * J.h - 1 := by
    intro M c hM a0 b0 h1 h2 v hv s1 s2
    have kw := W.kw; have kh := W.kh
    rcases hv with ⟨g, h⟩ | ⟨g, h⟩ | h
    · have := route_box hk (s1 g) h; omega
    · have := route_box hk (s2 g) h; omega
    · obtain ⟨-, cM, -⟩ := pathC_facts W.sol hM
      exact dpN_inb (segIn hM h1 h2) (chain_infix (segOf_infix (a := a0) (b := b0)) cM) v h
  have sA : a ≠ 0 → crossSlot k L (a - 1) < 2 * k := fun h => crossSlot_lt cL (hl.resolve_left h)
  have sB : b + 1 ≠ L.length → crossSlot k L b < 2 * k := fun h => crossSlot_lt cL (hr.resolve_left h)
  have sA' : a' ≠ 0 → crossSlot k L' (a' - 1) < 2 * k := fun h => crossSlot_lt cL' (hl'.resolve_left h)
  have sB' : b' + 1 ≠ L'.length → crossSlot k L' b' < 2 * k := fun h => crossSlot_lt cL' (hr'.resolve_left h)
  -- distinct nodes have distinct slots
  have slotne : ∀ {σ σ' : ℕ}, σ ∈ usedOf k k s → σ' ∈ usedOf k k s →
      (usedOf k k s).idxOf σ ≠ (usedOf k k s).idxOf σ' → σ ≠ σ' := fun _ _ h e => h (by rw [e])
  -- the outside runs are disjoint
  have segdisj : ∀ v ∈ segOf L a b, v ∉ segOf L' a' b' := by
    intro v hv hv'
    obtain ⟨j, j1, j2, rfl⟩ := (mem_segOf hab hb).mp hv
    obtain ⟨j', j1', j2', e⟩ := (mem_segOf hab' hb').mp hv'
    obtain ⟨rfl, rfl⟩ := pathC_same W.sol hp hp' (nth_mem (L := L) (j := j) (by omega))
      (by rw [e]; exact nth_mem (L := L') (j := j') (by omega))
    have := nth_inj nL (by omega) (by omega) e
    subst this
    obtain ⟨u1, u2⟩ := run_unique (outRun hab hb hout hl hr) (outRun hab' hb' hout' hl' hr') j1 j2 j1' j2'
    subst u1; subst u2
    exact d13 (by rw [e1, e1'])
  have hdis : ∀ v ∈ runChain k L a b, v ∉ runChain k L' a' b' := by
    intro v hv hv'
    have kw := W.kw; have kh := W.kh
    rcases mA v hv with ⟨ga, ha⟩ | ⟨gb, hb0⟩ | hd <;> rcases mQ v hv' with ⟨ga', ha'⟩ | ⟨gb', hb0'⟩ | hd'
    · exact route_disj hk (sA ga) (sA' ga') (slotne (usedA ga) (usedA' ga') (by
        have := d13; rw [e1, e1', ite_eq_right ga, ite_eq_right ga'] at this; exact this)) ha ha'
    · exact route_disj hk (sA ga) (sB' gb') (slotne (usedA ga) (usedB' gb') (by
        have := d14; rw [e1, e2', ite_eq_right ga, ite_eq_right gb'] at this; exact this)) ha hb0'
    · have := route_box hk (sA ga) ha; have := dpN_out cS' (segOut hab' hb' hout') hd'; omega
    · exact route_disj hk (sB gb) (sA' ga') (slotne (usedB gb) (usedA' ga') (by
        have := d23; rw [e2, e1', ite_eq_right gb, ite_eq_right ga'] at this; exact this)) hb0 ha'
    · exact route_disj hk (sB gb) (sB' gb') (slotne (usedB gb) (usedB' gb') (by
        have := d24; rw [e2, e2', ite_eq_right gb, ite_eq_right gb'] at this; exact this)) hb0 hb0'
    · have := route_box hk (sB gb) hb0; have := dpN_out cS' (segOut hab' hb' hout') hd'; omega
    · have := route_box hk (sA' ga') ha'; have := dpN_out cS (segOut hab hb hout) hd; omega
    · have := route_box hk (sB' gb') hb0'; have := dpN_out cS (segOut hab hb hout) hd; omega
    · exact dpN_disj cS cS' segdisj hd hd'
  have perimL : ∀ {M : List Coord} {c : ℕ} (hM : PathC p q M c) {a0 b0 : ℕ} (h1 : a0 ≤ b0) (h2 : b0 < M.length)
      (ho : ∀ j, a0 ≤ j → j ≤ b0 → inWb k (nth M j) = false) (hl0 : a0 = 0 ∨ IsCross k M (a0 - 1)),
      OnPerim (2 * J.w - 1) (2 * J.h - 1)
        (if a0 = 0 then dd (nth M a0) else routeEnd k (crossSlot k M (a0 - 1))) := by
    intro M c hM a0 b0 h1 h2 ho hl0
    obtain ⟨-, cM, -⟩ := pathC_facts W.sol hM
    split_ifs with h0
    · obtain ⟨-, g1, g2, g3⟩ := endE hM a0 (Or.inl h0) (by omega) (ho a0 le_rfl h1)
      exact (dd_perim g1 g2 g3).1
    · exact (routeEnd_perim hk W.kw W.kh (crossSlot_lt cM (hl0.resolve_left h0))).1
  have perimR : ∀ {M : List Coord} {c : ℕ} (hM : PathC p q M c) {a0 b0 : ℕ} (h1 : a0 ≤ b0) (h2 : b0 < M.length)
      (ho : ∀ j, a0 ≤ j → j ≤ b0 → inWb k (nth M j) = false) (hr0 : b0 + 1 = M.length ∨ IsCross k M b0),
      OnPerim (2 * J.w - 1) (2 * J.h - 1)
        (if b0 + 1 = M.length then dd (nth M b0) else routeEnd k (crossSlot k M b0)) := by
    intro M c hM a0 b0 h1 h2 ho hr0
    obtain ⟨-, cM, -⟩ := pathC_facts W.sol hM
    split_ifs with h0
    · obtain ⟨-, g1, g2, g3⟩ := endE hM b0 (Or.inr h0) (by omega) (ho b0 h1 le_rfl)
      exact (dd_perim g1 g2 g3).1
    · exact (routeEnd_perim hk W.kw W.kh (crossSlot_lt cM (hr0.resolve_left h0))).1
  exact t1_use (R := 2 * J.w - 1) (C := 2 * J.h - 1) (by have := W.kw; omega) (by have := W.kh; omega) cA cQ
    (fun v hv => inA hp hab hb v (mA v hv) sA sB) (fun v hv => inA hp' hab' hb' v (mQ v hv) sA' sB') hdis
    hA lA hQ lQ (perimL hp hab hb hout hl) (perimR hp hab hb hout hr) (perimL hp' hab' hb' hout' hl')
    (perimR hp' hab' hb' hout' hr') n1 n2 n3 n4 n5

end PairOK

/-! ### Keys follow the node order, rotated -/

theorem prefix_lt : ∀ {l : List ℕ}, l.Pairwise (· < ·) → ∀ (c i : ℕ), i < l.length →
    (l.getD i 0 < c ↔ i < (l.filter (· < c)).length)
  | [], _, c, i, h => by simp at h
  | a :: l, hs, c, i, h => by
    rw [List.pairwise_cons] at hs
    have ih := prefix_lt hs.2 c
    by_cases ha : a < c
    · rw [List.filter_cons, ite_eq_left (by simpa using ha), List.length_cons]
      cases i with
      | zero => simp [ha]
      | succ i =>
        simp only [List.getD_cons_succ]
        rw [ih i (by simp at h; omega)]; omega
    · rw [List.filter_cons, ite_eq_right (by simpa using ha)]
      have nil : l.filter (· < c) = [] := by
        rw [List.filter_eq_nil_iff]; intro x hx; have := hs.1 x hx; simp; omega
      rw [nil]
      cases i with
      | zero => simp; omega
      | succ i =>
        simp only [List.getD_cons_succ, List.length_nil]
        have := hs.1 (l.getD i 0) (by rw [List.getD_eq_getElem _ _ (by simp at h; omega)]; exact List.getElem_mem _)
        omega

theorem crosses_anti (f : ℕ → ℕ) {a b c d : ℕ}
    (h : ∀ x ∈ [a, b, c, d], ∀ y ∈ [a, b, c, d], x < y ↔ f y < f x) :
    Crosses a b c d ↔ Crosses (f a) (f b) (f c) (f d) := by
  unfold Crosses
  rw [h a (by simp) c (by simp), h c (by simp) b (by simp), h b (by simp) c (by simp), h c (by simp) a (by simp),
    h a (by simp) d (by simp), h d (by simp) b (by simp), h b (by simp) d (by simp), h d (by simp) a (by simp)]
  constructor <;> intro g <;> constructor <;> intro g' <;>
    (have := g.mp (by tauto); tauto)

theorem crosses_rel {a b c d a' b' c' d' : ℕ} (h1 : a < c ↔ c' < a') (h2 : c < b ↔ b' < c')
    (h3 : b < c ↔ c' < b') (h4 : c < a ↔ a' < c') (h5 : a < d ↔ d' < a') (h6 : d < b ↔ b' < d')
    (h7 : b < d ↔ d' < b') (h8 : d < a ↔ a' < d') : Crosses a b c d ↔ Crosses a' b' c' d' := by
  unfold Crosses
  rw [h1, h2, h3, h4, h5, h6, h7, h8]
  have e1 : ((c' < a' ∧ b' < c') ∨ (c' < b' ∧ a' < c')) ↔ ((a' < c' ∧ c' < b') ∨ (b' < c' ∧ c' < a')) := by
    constructor <;> intro g <;> omega
  have e2 : ((d' < a' ∧ b' < d') ∨ (d' < b' ∧ a' < d')) ↔ ((a' < d' ∧ d' < b') ∨ (b' < d' ∧ d' < a')) := by
    constructor <;> intro g <;> omega
  rw [e1, e2]

theorem idxOf_range {m i : ℕ} (h : i < m) : (List.range m).idxOf i = i := by
  have := (List.nodup_range (n := m)).idxOf_getElem i (by simpa using h)
  simpa using this

section NoCross

variable {k : ℕ} {J : Inst} {p q : List Coord} {F : FSpec} {s : St}
  (W : WinSetup k J p q F) (hinv : Inv k k (k * k) p q s)
include W hinv

omit W hinv in
theorem used_sorted : (usedOf k k s).Pairwise (· < ·) := by
  unfold usedOf; exact List.pairwise_lt_range.filter _

omit hinv in
/-- **Keys strictly decrease along the node order, rotated to start at the bottom exits.** -/
theorem key_order {E : Coord}
    (hF : F.isSome → 2 * k < Planar.anc (2 * J.w - 1) (2 * J.h - 1) (dd E) ∧
      Planar.anc (2 * J.w - 1) (2 * J.h - 1) (dd E) < 2 * (2 * J.h - 1) + 2 * (2 * J.w - 1) + 4 - 2 * k)
    {i j : ℕ} (hi : i < mOf k k F s) (hj : j < mOf k k F s) :
    Kof k J.w J.h s E i < Kof k J.w J.h s E j ↔
      rotK ((usedOf k k s).filter (· < k)).length (mOf k k F s) j <
        rotK ((usedOf k k s).filter (· < k)).length (mOf k k F s) i := by
  have hk : 1 ≤ k := by have := W.k2; omega
  by_cases hij : i = j
  · subst hij; simp
  obtain ⟨U, eU⟩ : ∃ U, (usedOf k k s).length = U := ⟨_, rfl⟩
  obtain ⟨UR, eUR⟩ : ∃ UR, ((usedOf k k s).filter (· < k)).length = UR := ⟨_, rfl⟩
  have hUR : UR ≤ U := by rw [← eU, ← eUR]; exact List.length_filter_le _ _
  have hm : mOf k k F s = U + (if F.isSome then 1 else 0) := by unfold mOf; rw [eU]
  rw [eUR]
  have bound : ∀ x ∈ usedOf k k s, x < 2 * k := fun x hx => by
    unfold usedOf at hx; rw [List.mem_filter, List.mem_range] at hx; omega
  have slot_lt : ∀ i, i < U → (usedOf k k s).getD i 0 < 2 * k := fun i hi => by
    apply bound
    rw [List.getD_eq_getElem _ _ (by rw [eU]; exact hi)]; exact List.getElem_mem _
  have desc : ∀ i, i < mOf k k F s →
      (i < UR ∧ (usedOf k k s).getD i 0 < k ∧ Kof k J.w J.h s E i = 2 * k - 2 * (usedOf k k s).getD i 0) ∨
      (UR ≤ i ∧ i < U ∧ k ≤ (usedOf k k s).getD i 0 ∧ (usedOf k k s).getD i 0 < 2 * k ∧
        Kof k J.w J.h s E i = 2 * (2 * J.h - 1) + 2 * (2 * J.w - 1) + 2 + 2 * k - 2 * (usedOf k k s).getD i 0) ∨
      (i = U ∧ 2 * k < Kof k J.w J.h s E i ∧
        Kof k J.w J.h s E i < 2 * (2 * J.h - 1) + 2 * (2 * J.w - 1) + 4 - 2 * k) := by
    intro i hi
    by_cases hu : i < U
    · have hσ := slot_lt i hu
      have pre := prefix_lt (used_sorted) k i (by rw [eU]; exact hu)
      rw [eUR] at pre
      unfold Kof; rw [ite_eq_left (by rw [eU]; exact hu), anc_routeEnd hk W.kw W.kh hσ]
      by_cases hk' : (usedOf k k s).getD i 0 < k
      · left; rw [ite_eq_left hk']; exact ⟨pre.mp hk', hk', rfl⟩
      · right; left; rw [ite_eq_right hk']; exact ⟨by rw [← not_lt, ← pre]; exact hk', hu, by omega, hσ, rfl⟩
    · have hiU : i = U := by unfold mOf at hi; split_ifs at hi <;> omega
      have hFs : F.isSome = true := by
        by_contra c; unfold mOf at hi; rw [ite_eq_right c] at hi; omega
      right; right
      unfold Kof; rw [ite_eq_right (by rw [eU]; exact hu)]
      exact ⟨hiU, (hF hFs).1, (hF hFs).2⟩
  have sorted : ∀ i j, i < j → j < U → (usedOf k k s).getD i 0 < (usedOf k k s).getD j 0 := fun i j h1 h2 => by
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    exact List.pairwise_iff_getElem.mp (used_sorted) i j (by omega) (by omega) h1
  have cmp : (i < j ∧ j < U ∧ (usedOf k k s).getD i 0 < (usedOf k k s).getD j 0) ∨
      (j < i ∧ i < U ∧ (usedOf k k s).getD j 0 < (usedOf k k s).getD i 0) ∨ i = j ∨
      (i < j ∧ U ≤ j) ∨ (j < i ∧ U ≤ i) := by
    rcases Nat.lt_trichotomy i j with c | c | c
    · by_cases hU : j < U
      · exact Or.inl ⟨c, hU, sorted i j c hU⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c, by omega⟩)))
    · exact Or.inr (Or.inr (Or.inl c))
    · by_cases hU : i < U
      · exact Or.inr (Or.inl ⟨c, hU, sorted j i c hU⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨c, by omega⟩)))
  have di := desc i hi
  have dj := desc j hj
  obtain ⟨m, em⟩ : ∃ m, mOf k k F s = m := ⟨_, rfl⟩
  have hmv : m = U ∨ m = U + 1 := by rw [← em, hm]; split_ifs <;> simp
  rw [em] at hi hj ⊢
  have gval : ∀ x, x < m → (x < UR ∧ rotK UR m x + UR = x + m) ∨ (UR ≤ x ∧ rotK UR m x + UR = x) := by
    intro x hx; unfold rotK; split_ifs <;> omega
  have gi := gval i hi
  have gj := gval j hj
  have kw := W.kw
  have kh := W.kh
  generalize rotK UR m i = Gi at gi ⊢
  generalize rotK UR m j = Gj at gj ⊢
  rcases di with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3, a4, a5⟩ | ⟨a1, a2, a3⟩ <;>
    rcases dj with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3, b4, b5⟩ | ⟨b1, b2, b3⟩ <;>
    rcases cmp with ⟨c1, c2, c3⟩ | ⟨c1, c2, c3⟩ | c1 | ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>
    rcases gi with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> rcases gj with ⟨g3, g4⟩ | ⟨g3, g4⟩ <;> omega

/-- A node and its partner are the two ends of a matched pair of a chain. -/
theorem node_pair {i : ℕ} (hi : i < mOf k k F s) :
    ∃ L col t, PathC p q L col ∧ 2 * t + 1 < (chainOf k s L).length ∧
      (((chainOf k s L).getD (2 * t) 0 = i ∧ (chainOf k s L).getD (2 * t + 1) 0 = muOf k s p q i) ∨
       ((chainOf k s L).getD (2 * t + 1) 0 = i ∧ (chainOf k s L).getD (2 * t) 0 = muOf k s p q i)) := by
  have go : ∀ {L : List Coord} {col : ℕ}, PathC p q L col → i ∈ chainOf k s L →
      ∃ t, 2 * t + 1 < (chainOf k s L).length ∧
        (((chainOf k s L).getD (2 * t) 0 = i ∧ (chainOf k s L).getD (2 * t + 1) 0 = muOf k s p q i) ∨
         ((chainOf k s L).getD (2 * t + 1) 0 = i ∧ (chainOf k s L).getD (2 * t) 0 = muOf k s p q i)) := by
    intro L col hp hiL
    have hn := chain_nodup W hinv hp
    have hev := chain_even (s := s) W hp
    have lt := List.idxOf_lt_length_iff.mpr hiL
    have gi : (chainOf k s L).getD ((chainOf k s L).idxOf i) 0 = i := by
      rw [List.getD_eq_getElem _ _ lt]; exact List.getElem_idxOf lt
    rw [mu_on W hinv hp hiL]
    rcases Nat.even_or_odd ((chainOf k s L).idxOf i) with ⟨t, ht⟩ | ⟨t, ht⟩
    · have e : (chainOf k s L).idxOf i = 2 * t := by omega
      rw [e] at gi lt
      refine ⟨t, by omega, Or.inl ⟨gi, ?_⟩⟩
      rw [← gi, (partner_pos hn (by omega)).1]
    · rw [ht] at gi lt
      refine ⟨t, lt, Or.inr ⟨gi, ?_⟩⟩
      rw [← gi, (partner_pos hn lt).2]
  rcases chains_cover W hinv i hi with h | h
  · obtain ⟨t, ht, e⟩ := go (Or.inl ⟨rfl, rfl⟩) h; exact ⟨p, 0, t, Or.inl ⟨rfl, rfl⟩, ht, e⟩
  · obtain ⟨t, ht, e⟩ := go (Or.inr ⟨rfl, rfl⟩) h; exact ⟨q, 1, t, Or.inr ⟨rfl, rfl⟩, ht, e⟩

omit W hinv in
theorem rotK_inj {UR m i j : ℕ} (hi : i < m) (hj : j < m) (hU : UR ≤ m) (h : rotK UR m i = rotK UR m j) :
    i = j := by
  unfold rotK at h; split_ifs at h <;> omega

/-- **No two matched pairs cross.** -/
theorem window_nocross : NoCross (muOf k s p q) (List.range (mOf k k F s)) := by
  have hk : 1 ≤ k := by have := W.k2; omega
  -- F's cell and its anchor
  obtain ⟨E, hEq, hEp, hFb⟩ : ∃ E : Coord, (∀ x, IsEnd J x → ¬ (x.1 < k ∧ x.2 < k) → x = E) ∧
      (∀ x, IsEnd J x → ¬ (x.1 < k ∧ x.2 < k) → x.1 = 0 ∨ x.2 = 0 ∨ x.1 = J.w - 1 ∨ x.2 = J.h - 1) ∧
      (F.isSome → 2 * k < Planar.anc (2 * J.w - 1) (2 * J.h - 1) (dd E) ∧
        Planar.anc (2 * J.w - 1) (2 * J.h - 1) (dd E) < 2 * (2 * J.h - 1) + 2 * (2 * J.w - 1) + 4 - 2 * k) := by
    rcases W.ends with ⟨hF, hin⟩ | ⟨E, fc, fs, fsl, hF, hE, hEo, -, hoth, hper, -, -⟩
    · exact ⟨(0, 0), fun x hx ho => absurd (hin x hx) ho, fun x hx ho => absurd (hin x hx) ho,
        fun h => by rw [hF] at h; simp at h⟩
    · have hEg : E.1 < J.w ∧ E.2 < J.h := by
        obtain ⟨b0, b1, b2, b3, -⟩ := W.wf
        rcases hE with rfl | rfl | rfl | rfl
        · exact b0
        · exact b1
        · exact b2
        · exact b3
      refine ⟨E, fun x hx ho => by_contra fun ne => ho (hoth x hx ne), fun x hx ho => ?_,
        fun _ => anc_F hk W.kw W.kh hEg.1 hEg.2 hEo hper⟩
      have : x = E := by_contra fun ne => ho (hoth x hx ne)
      rw [this]; exact hper
  intro x hx y hy ⟨h1, h2, h3⟩
  have hx' := List.mem_range.mp hx
  have hy' := List.mem_range.mp hy
  have inv := mu_invo W hinv
  have mx := List.mem_range.mp (inv x hx).1
  have my := List.mem_range.mp (inv y hy).1
  rw [idxOf_range hx', idxOf_range hy'] at h1
  rw [idxOf_range hy', idxOf_range mx] at h2
  rw [idxOf_range mx, idxOf_range my] at h3
  have hUR : ((usedOf k k s).filter (· < k)).length ≤ mOf k k F s := by
    have := List.length_filter_le (· < k) (usedOf k k s)
    unfold mOf; omega
  have ord := fun {i j : ℕ} (hi : i < (mOf k k F s)) (hj : j < (mOf k k F s)) => key_order W hFb (i := i) (j := j) hi hj
  -- the crossing in node order carries over to the keys
  have cIdx : Crosses x ((muOf k s p q) x) y ((muOf k s p q) y) := by unfold Crosses; omega
  have cRot := (crosses_rot (m := ((usedOf k k s).filter (· < k)).length) (n := mOf k k F s) hUR hx' mx hy' my (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)).mpr cIdx
  have cK : Crosses ((Kof k J.w J.h s E) x) ((Kof k J.w J.h s E) ((muOf k s p q) x)) ((Kof k J.w J.h s E) y) ((Kof k J.w J.h s E) ((muOf k s p q) y)) := by
    refine (crosses_rel ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).mp cRot
    · exact (ord hy' hx').symm
    · exact (ord (mx) hy').symm
    · exact (ord hy' mx).symm
    · exact (ord hx' hy').symm
    · exact (ord my hx').symm
    · exact (ord mx my).symm
    · exact (ord my mx).symm
    · exact (ord hx' my).symm
  -- keys of distinct nodes differ
  have kne : ∀ {i j : ℕ}, i < (mOf k k F s) → j < (mOf k k F s) → i ≠ j → (Kof k J.w J.h s E) i ≠ (Kof k J.w J.h s E) j := by
    intro i j hi hj hne e
    have a1 : ¬ ((Kof k J.w J.h s E) i < (Kof k J.w J.h s E) j) := by rw [e]; exact lt_irrefl _
    have a2 : ¬ ((Kof k J.w J.h s E) j < (Kof k J.w J.h s E) i) := by rw [e]; exact lt_irrefl _
    have b1 := (ord hi hj).not.mp a1
    have b2 := (ord hj hi).not.mp a2
    exact hne (rotK_inj hi hj hUR (by omega))
  obtain ⟨L, col, t, hp, ht, ex⟩ := node_pair W hinv hx'
  obtain ⟨L', col', t', hp', ht', ey⟩ := node_pair W hinv hy'
  have pk := fun (d13 d14 d23 d24 : _) (n1 n2 n3 n4 n5 : _) =>
    pair_ok W hinv hEq hEp hp hp' ht ht' (E := E) d13 d14 d23 d24 n1 n2 n3 n4 n5
  rcases ex with ⟨ex1, ex2⟩ | ⟨ex1, ex2⟩ <;> rcases ey with ⟨ey1, ey2⟩ | ⟨ey1, ey2⟩ <;>
    rw [ex1, ex2, ey1, ey2] at pk
  · exact pk (by omega) (by omega) (by omega) (by omega) (kne hx' mx (by omega)) (kne hy' hx' (by omega))
      (kne hy' mx (by omega)) (kne my hx' (by omega)) (kne my mx (by omega)) cK
  · exact pk (by omega) (by omega) (by omega) (by omega) (kne hx' mx (by omega)) (kne my hx' (by omega))
      (kne my mx (by omega)) (kne hy' hx' (by omega)) (kne hy' mx (by omega)) (crosses_swap23.mp cK)
  · exact pk (by omega) (by omega) (by omega) (by omega) (kne mx hx' (by omega)) (kne hy' mx (by omega))
      (kne hy' hx' (by omega)) (kne my mx (by omega)) (kne my hx' (by omega)) (crosses_swap01.mp cK)
  · exact pk (by omega) (by omega) (by omega) (by omega) (kne mx hx' (by omega)) (kne my mx (by omega))
      (kne my hx' (by omega)) (kne hy' mx (by omega)) (kne hy' hx' (by omega))
      (crosses_swap23.mp (crosses_swap01.mp cK))

end NoCross

end ZZN.Win

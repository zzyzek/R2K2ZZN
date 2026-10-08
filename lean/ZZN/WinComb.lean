-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.WinCheck
import Mathlib.Data.List.Sort

/-!
# Window certificates: combinatorics of the outside test

The walk along a chain of nodes, the structure test, and completeness of the non-crossing matching
enumeration.
-/

namespace ZZN.Win

/-! ### Walking a chain -/

/-- A chain of nodes from a terminal: consecutive nodes alternate between a matched pair and an
inside link, and it stops at the next terminal. -/
def ChainN (m : ℕ) (link : ℕ → ℕ) (mt : List (ℕ × ℕ)) : List ℕ → Prop
  | [] => False
  | [_] => False
  | [x, y] => mate mt x = y ∧ m ≤ link y
  | x :: y :: z :: l => mate mt x = y ∧ link y = z ∧ link y < m ∧ ChainN m link mt (z :: l)

theorem walk_chain {m : ℕ} {link : ℕ → ℕ} {mt : List (ℕ × ℕ)} :
    ∀ (l : List ℕ) (x f : ℕ), ChainN m link mt (x :: l) → l.length ≤ 2 * f →
      walk m link mt f x = some (l.getLastD 0, l)
  | [], _, _, h, _ => by simp [ChainN] at h
  | [y], x, f, h, hf => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    obtain ⟨h1, h2⟩ := h
    simp [walk, h1, h2]
  | y :: z :: l, x, f, h, hf => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    obtain ⟨h1, h2, h3, h4⟩ := h
    have ih := walk_chain l z f h4 (by simp at hf; omega)
    cases l with
    | nil => simp [ChainN] at h4
    | cons w l =>
      simp only [walk, h1, h2]
      rw [ite_eq_right (by omega), ih]
      simp

/-- A chain in symmetric form, by positions: matched pairs `(2t, 2t+1)`, inside links
`(2t+1, 2t+2)`, terminals at both ends. -/
structure Alt (m : ℕ) (link : ℕ → ℕ) (mt : List (ℕ × ℕ)) (N : List ℕ) : Prop where
  even : N.length % 2 = 0
  two : 2 ≤ N.length
  mates : ∀ t, 2 * t + 1 < N.length →
    mate mt (N.getD (2 * t) 0) = N.getD (2 * t + 1) 0 ∧ mate mt (N.getD (2 * t + 1) 0) = N.getD (2 * t) 0
  links : ∀ t, 2 * t + 2 < N.length →
    link (N.getD (2 * t + 1) 0) = N.getD (2 * t + 2) 0 ∧ link (N.getD (2 * t + 2) 0) = N.getD (2 * t + 1) 0 ∧
      N.getD (2 * t + 1) 0 < m ∧ N.getD (2 * t + 2) 0 < m
  first : m ≤ link (N.getD 0 0)
  last : m ≤ link (N.getD (N.length - 1) 0)

theorem alt_chain' {m : ℕ} {link : ℕ → ℕ} {mt : List (ℕ × ℕ)} :
    ∀ (N : List ℕ), N.length % 2 = 0 → 2 ≤ N.length →
      (∀ t, 2 * t + 1 < N.length → mate mt (N.getD (2 * t) 0) = N.getD (2 * t + 1) 0) →
      (∀ t, 2 * t + 2 < N.length →
        link (N.getD (2 * t + 1) 0) = N.getD (2 * t + 2) 0 ∧ N.getD (2 * t + 2) 0 < m) →
      m ≤ link (N.getD (N.length - 1) 0) → ChainN m link mt N
  | [], _, h2, _, _, _ => by simp at h2
  | [_], _, h2, _, _, _ => by simp at h2
  | [x, y], _, _, hm, _, hl => ⟨by simpa using hm 0 (by simp), by simpa using hl⟩
  | [x, y, z], he, _, _, _, _ => by simp at he
  | x :: y :: z :: w :: l, he, _, hm, hk, hl => by
    have e1 := (hk 0 (by simp)).1
    have e2 := (hk 0 (by simp)).2
    simp at e1 e2
    refine ⟨by simpa using hm 0 (by simp), e1, by rw [e1]; exact e2, ?_⟩
    apply alt_chain' (z :: w :: l) (by simp at he ⊢; omega) (by simp)
    · intro t ht
      have := hm (t + 1) (by simp at ht ⊢; omega)
      simpa [show 2 * (t + 1) = 2 * t + 2 by ring, show 2 * (t + 1) + 1 = 2 * t + 3 by ring] using this
    · intro t ht
      have := hk (t + 1) (by simp at ht ⊢; omega)
      simpa [show 2 * (t + 1) + 1 = 2 * t + 3 by ring, show 2 * (t + 1) + 2 = 2 * t + 4 by ring] using this
    · simpa using hl

theorem alt_chain {m : ℕ} {link : ℕ → ℕ} {mt : List (ℕ × ℕ)} (N : List ℕ) (h : Alt m link mt N) :
    ChainN m link mt N :=
  alt_chain' N h.even h.two (fun t ht => (h.mates t ht).1)
    (fun t ht => ⟨(h.links t ht).1, (h.links t ht).2.2.2⟩) h.last

theorem alt_reverse {m : ℕ} {link : ℕ → ℕ} {mt : List (ℕ × ℕ)} {N : List ℕ} (h : Alt m link mt N) :
    Alt m link mt N.reverse := by
  have hl := h.even
  have h2 := h.two
  have rv : ∀ j, j < N.length → N.reverse.getD j 0 = N.getD (N.length - 1 - j) 0 := fun j hj => by
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by omega),
      List.getElem_reverse]
  refine ⟨by simpa using hl, by simpa using h2, fun t ht => ?_, fun t ht => ?_, ?_, ?_⟩
  · simp only [List.length_reverse] at ht
    rw [rv _ (by omega), rv _ (by omega)]
    obtain ⟨t', ht'⟩ : ∃ t', N.length - 1 - (2 * t + 1) = 2 * t' := ⟨(N.length - 2 - 2 * t) / 2, by omega⟩
    have e2 : N.length - 1 - 2 * t = 2 * t' + 1 := by omega
    rw [ht', e2]
    have := h.mates t' (by omega)
    exact ⟨this.2, this.1⟩
  · simp only [List.length_reverse] at ht
    rw [rv _ (by omega), rv _ (by omega)]
    obtain ⟨t', ht'⟩ : ∃ t', N.length - 1 - (2 * t + 2) = 2 * t' + 1 := ⟨(N.length - 4 - 2 * t) / 2, by omega⟩
    have e2 : N.length - 1 - (2 * t + 1) = 2 * t' + 2 := by omega
    rw [ht', e2]
    have := h.links t' (by omega)
    exact ⟨this.2.1, this.1, this.2.2.2, this.2.2.1⟩
  · rw [rv _ (by omega), show N.length - 1 - 0 = N.length - 1 by omega]; exact h.last
  · simp only [List.length_reverse]
    rw [rv _ (by omega), show N.length - 1 - (N.length - 1) = 0 by omega]; exact h.first

/-! ### The structure test -/

theorem two_sorted : ∀ {l : List ℕ}, l.Pairwise (· < ·) → ∀ {x y : ℕ}, x < y →
    (∀ z, z ∈ l ↔ z = x ∨ z = y) → l = [x, y]
  | [], _, x, _, _, hm => by have := (hm x).mpr (Or.inl rfl); simp at this
  | [a], _, x, y, hxy, hm => by
    have h1 := (hm x).mpr (Or.inl rfl); have h2 := (hm y).mpr (Or.inr rfl)
    simp at h1 h2; omega
  | a :: b :: l, hs, x, y, hxy, hm => by
    rw [List.pairwise_cons] at hs
    have ha := (hm a).mp (by simp)
    have hb := (hm b).mp (by simp)
    have hab := hs.1 b (by simp)
    have hax : a = x := by omega
    have hby : b = y := by omega
    subst hax; subst hby
    cases l with
    | nil => rfl
    | cons c l =>
      have hc := (hm c).mp (by simp)
      have := hs.2
      rw [List.pairwise_cons] at this
      have := this.1 c (by simp)
      have := hs.1 c (by simp)
      omega

theorem len_le_of_lt {N : List ℕ} {m : ℕ} (hn : N.Nodup) (hb : ∀ i ∈ N, i < m) : N.length ≤ m := by
  have := (hn.subperm (l₂ := List.range m) (fun i hi => List.mem_range.mpr (hb i hi))).length_le
  simpa using this

theorem getD_last_cons {x : ℕ} {rest : List ℕ} (h : rest ≠ []) :
    (x :: rest).getD ((x :: rest).length - 1) 0 = rest.getLastD 0 := by
  obtain ⟨y, r, rfl⟩ : ∃ y r, rest = y :: r := by cases rest with | nil => exact absurd rfl h | cons y r => exact ⟨y, r, rfl⟩
  simp only [List.length_cons, Nat.add_sub_cancel, List.getD_cons_succ]
  rw [List.getLastD_eq_getLast? , List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]
  simp

/-- The walk along a chain, from its first node. -/
theorem walk_alt {m : ℕ} {link : ℕ → ℕ} {mt : List (ℕ × ℕ)} {K : List ℕ} (h : Alt m link mt K)
    (hb : ∀ i ∈ K, i < m) (hn : K.Nodup) :
    walk m link mt (m + 1) (K.getD 0 0) = some (K.getD (K.length - 1) 0, K.tail) := by
  have hlen := len_le_of_lt hn hb
  obtain ⟨x, rest, rfl⟩ : ∃ x rest, K = x :: rest := by
    cases K with | nil => have := h.two; simp at this | cons x r => exact ⟨x, r, rfl⟩
  have hr : rest ≠ [] := by intro e; subst e; have := h.two; simp at this
  have := walk_chain rest x (m + 1) (alt_chain _ h) (by simp at hlen; omega)
  simp only [List.getD_cons_zero, List.tail_cons]
  rw [this, getD_last_cons hr]

/-- **The structure test passes** for two colour chains covering all nodes. -/
theorem structOK_ok {m : ℕ} {link : ℕ → ℕ} {mt : List (ℕ × ℕ)} {dn : ℕ} (N : ℕ → List ℕ)
    (hN : ∀ c, c ≤ 1 → ((N c = [] ∧ (dn / 2 ^ c) % 2 = 1) ∨
      (Alt m link mt (N c) ∧ (dn / 2 ^ c) % 2 = 0 ∧ link ((N c).getD 0 0) = m + c ∧
        link ((N c).getD ((N c).length - 1) 0) = m + c)))
    (hT : ∀ i, i < m → ∀ c, c ≤ 1 → link i = m + c →
      i ∈ N c ∧ (i = (N c).getD 0 0 ∨ i = (N c).getD ((N c).length - 1) 0))
    (hb : ∀ c, c ≤ 1 → ∀ i ∈ N c, i < m)
    (hcov : ∀ i, i < m → i ∈ N 0 ∨ i ∈ N 1)
    (hnd : ∀ c, c ≤ 1 → (N c).Nodup) :
    structOK m link mt dn = true := by
  have vis : ∀ c, c ≤ 1 → ∃ v, visC m link mt c = some v ∧ (∀ i ∈ N c, i ∈ v) ∧
      (((dn / 2 ^ c) % 2 == 1) == ((List.range m).filter (fun i => link i == m + c)).isEmpty) = true := by
    intro c hc
    rcases hN c hc with ⟨h0, hd⟩ | ⟨ha, hd, hf, hl⟩
    · have e : (List.range m).filter (fun i => link i == m + c) = [] := by
        rw [List.filter_eq_nil_iff]
        intro i hi
        simp only [beq_iff_eq]
        intro e
        have := (hT i (List.mem_range.mp hi) c hc e).1
        rw [h0] at this; simp at this
      unfold visC
      rw [e]
      refine ⟨[], rfl, fun i hi => by rw [h0] at hi; simp at hi, ?_⟩
      simp [hd]
    · have hn := hnd c hc
      have h2 := ha.two
      set K := N c with hK
      have fl : K.getD 0 0 ≠ K.getD (K.length - 1) 0 := by
        intro e
        rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at e
        have := (List.Nodup.getElem_inj_iff hn).mp e
        omega
      have mf : K.getD 0 0 ∈ K := by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
      have ml : K.getD (K.length - 1) 0 ∈ K := by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
      have memF : ∀ z, z ∈ (List.range m).filter (fun i => link i == m + c) ↔
          z = K.getD 0 0 ∨ z = K.getD (K.length - 1) 0 := by
        intro z
        simp only [List.mem_filter, List.mem_range, beq_iff_eq]
        constructor
        · rintro ⟨h1, h2⟩; exact (hT z h1 c hc h2).2
        · rintro (rfl | rfl)
          · exact ⟨hb c hc _ mf, hf⟩
          · exact ⟨hb c hc _ ml, hl⟩
      have sorted := (List.pairwise_lt_range (n := m)).filter (fun i => link i == m + c)
      have ne : ((List.range m).filter (fun i => link i == m + c)).isEmpty = false := by
        rw [List.isEmpty_eq_false_iff_exists_mem]
        exact ⟨_, (memF _).mpr (Or.inl rfl)⟩
      unfold visC
      rw [ne]
      rcases Nat.lt_or_gt_of_ne fl with lt | gt
      · rw [two_sorted sorted lt memF]
        dsimp only
        rw [walk_alt ha (hb c hc) hn]
        dsimp only
        rw [ite_eq_left (by simp)]
        refine ⟨_, rfl, fun i hi => ?_, ?_⟩
        · have hK2 : K.getD 0 0 :: K.tail = K := by
            cases hk : K with
            | nil => rw [hk] at h2; simp at h2
            | cons x r => simp
          rw [hK2]; exact hi
        · simp [hd]
      · rw [two_sorted sorted gt (fun z => (memF z).trans or_comm)]
        dsimp only
        have har := alt_reverse ha
        have hbr : ∀ i ∈ K.reverse, i < m := fun i hi => hb c hc i (List.mem_reverse.mp hi)
        have w := walk_alt har hbr (List.nodup_reverse.mpr hn)
        have r0 : K.reverse.getD 0 0 = K.getD (K.length - 1) 0 := by
          rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by omega), List.getElem_reverse]
          congr 1
        have r1 : K.reverse.getD (K.reverse.length - 1) 0 = K.getD 0 0 := by
          rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by omega), List.getElem_reverse]
          congr 1; simp
        rw [r0, r1] at w
        rw [w]
        dsimp only
        rw [ite_eq_left (by simp)]
        refine ⟨_, rfl, fun i hi => ?_, ?_⟩
        · have : K.reverse = K.reverse.getD 0 0 :: K.reverse.tail := by
            cases hk : K.reverse with | nil => simp at hk; rw [hk] at h2; simp at h2 | cons x r => rfl
          rw [← r0, ← this]; exact List.mem_reverse.mpr hi
        · simp [hd]
  obtain ⟨v0, e0, m0, b0⟩ := vis 0 (by omega)
  obtain ⟨v1, e1, m1, b1⟩ := vis 1 le_rfl
  unfold structOK
  rw [e0, e1]
  dsimp only
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨⟨b0, b1⟩, ?_⟩
  rw [List.all_eq_true]
  intro i hi
  rcases hcov i (List.mem_range.mp hi) with h | h
  · simp [m0 i h]
  · simp [m1 i h]

/-! ### Non-crossing matchings are enumerated -/

section NCM

variable (μ : ℕ → ℕ)

/-- `μ` is a fixed-point-free involution on `l`. -/
def Invo (l : List ℕ) : Prop := ∀ x ∈ l, μ x ∈ l ∧ μ x ≠ x ∧ μ (μ x) = x

/-- No two pairs of `μ` cross, in the order of `l`. -/
def NoCross (l : List ℕ) : Prop :=
  ∀ x ∈ l, ∀ y ∈ l, ¬ (l.idxOf x < l.idxOf y ∧ l.idxOf y < l.idxOf (μ x) ∧ l.idxOf (μ x) < l.idxOf (μ y))

theorem invo_even : ∀ (n : ℕ) (l : List ℕ), l.length = n → l.Nodup → Invo μ l → n % 2 = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hl hn hi
    cases l with
    | nil => simp at hl; omega
    | cons x rest =>
      obtain ⟨hy, hyx, hyy⟩ := hi x (by simp)
      have hy' : μ x ∈ rest := by rcases List.mem_cons.mp hy with e | e; exact absurd e hyx; exact e
      have hxr : x ∉ rest := (List.nodup_cons.mp hn).1
      have hnr := (List.nodup_cons.mp hn).2
      have hlen : (rest.erase (μ x)).length = n - 2 := by
        rw [List.length_erase_of_mem hy']; simp at hl; omega
      have := ih (n - 2) (by simp at hl; have := List.length_pos_of_mem hy'; omega) (rest.erase (μ x)) hlen
        (hnr.erase _) (fun z hz => by
          have hzr : z ∈ rest := List.mem_of_mem_erase hz
          have hzy : z ≠ μ x := fun e => by rw [e] at hz; exact (List.Nodup.not_mem_erase hnr) hz
          obtain ⟨a1, a2, a3⟩ := hi z (by simp [hzr])
          have nx : μ z ≠ x := fun e => hzy (by rw [← e, a3])
          have ny : μ z ≠ μ x := fun e => by
            have := congrArg μ e; rw [a3, hyy] at this; exact hxr (this ▸ hzr)
          refine ⟨(List.Nodup.mem_erase_iff hnr).mpr ⟨ny, ?_⟩, a2, a3⟩
          rcases List.mem_cons.mp a1 with e | e
          · exact absurd e nx
          · exact e)
      have hp := List.length_pos_of_mem hy'
      simp only [List.length_cons] at hl
      omega

omit μ in
theorem idxOf_app_mem' {x : ℕ} : ∀ {l1 : List ℕ} (l2 : List ℕ), x ∈ l1 → (l1 ++ l2).idxOf x = l1.idxOf x
  | [], _, h => by simp at h
  | a :: l1, l2, h => by
    by_cases ha : a = x
    · subst ha; simp [List.idxOf_cons_self]
    · have : x ∈ l1 := by rcases List.mem_cons.mp h with e | e; exact absurd e.symm ha; exact e
      rw [List.cons_append, List.idxOf_cons_ne _ ha, List.idxOf_cons_ne _ ha, idxOf_app_mem' l2 this]

omit μ in
theorem idxOf_app_not_mem' {x : ℕ} : ∀ {l1 : List ℕ} (l2 : List ℕ), x ∉ l1 →
    (l1 ++ l2).idxOf x = l1.length + l2.idxOf x
  | [], _, _ => by simp
  | a :: l1, l2, h => by
    have ha : a ≠ x := fun e => h (e ▸ List.mem_cons_self)
    have : x ∉ l1 := fun e => h (List.mem_cons_of_mem _ e)
    rw [List.cons_append, List.idxOf_cons_ne _ ha, idxOf_app_not_mem' l2 this, List.length_cons]
    omega

omit μ in
theorem mate_head (x y : ℕ) (mt : List (ℕ × ℕ)) : mate ((x, y) :: mt) x = y := by
  simp [mate]

omit μ in
theorem mate_head' {x y : ℕ} (h : x ≠ y) (mt : List (ℕ × ℕ)) : mate ((x, y) :: mt) y = x := by
  simp [mate, h]

omit μ in
theorem mate_skip {x y z : ℕ} (hx : z ≠ x) (hy : z ≠ y) (mt : List (ℕ × ℕ)) :
    mate ((x, y) :: mt) z = mate mt z := by
  unfold mate; simp [Ne.symm hx, Ne.symm hy]

omit μ in
theorem mate_app_left {l1 l2 : List (ℕ × ℕ)} {z : ℕ} (h : mate l1 z ≠ z) :
    mate (l1 ++ l2) z = mate l1 z := by
  unfold mate at *
  rw [List.find?_append]
  cases hf : l1.find? (fun pr => pr.1 == z || pr.2 == z) with
  | none => rw [hf] at h; simp at h
  | some pr => simp

omit μ in
theorem mate_app_right {l1 l2 : List (ℕ × ℕ)} {z : ℕ} (h : ∀ pr ∈ l1, pr.1 ≠ z ∧ pr.2 ≠ z) :
    mate (l1 ++ l2) z = mate l2 z := by
  unfold mate
  rw [List.find?_append]
  have : l1.find? (fun pr => pr.1 == z || pr.2 == z) = none := by
    rw [List.find?_eq_none]; intro pr hpr; have := h pr hpr; simp [this.1, this.2]
  rw [this]; simp

/-- **Every non-crossing perfect matching is enumerated by `ncm`.** -/
theorem ncm_complete : ∀ (f : ℕ) (l : List ℕ), l.length ≤ f → l.Nodup → Invo μ l → NoCross μ l →
    ∃ mt ∈ ncm f l, (∀ z ∈ l, mate mt z = μ z) ∧ (∀ pr ∈ mt, pr.1 ∈ l ∧ pr.2 ∈ l) := by
  intro f
  induction f with
  | zero =>
    intro l hl _ _ _
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨[], by simp [ncm], by simp, by simp⟩
  | succ f ih =>
    intro l hl hn hi hc
    cases l with
    | nil => exact ⟨[], by simp [ncm], by simp, by simp⟩
    | cons x rest =>
      obtain ⟨hy, hyx, hyy⟩ := hi x (by simp)
      have hy' : μ x ∈ rest := by rcases List.mem_cons.mp hy with e | e; exact absurd e hyx; exact e
      have hxr : x ∉ rest := (List.nodup_cons.mp hn).1
      have hnr := (List.nodup_cons.mp hn).2
      have hjl : rest.idxOf (μ x) < rest.length := List.idxOf_lt_length_iff.mpr hy'
      have gy : rest.getD (rest.idxOf (μ x)) 0 = μ x := by
        rw [List.getD_eq_getElem _ _ hjl]; exact List.getElem_idxOf hjl
      have split : rest = rest.take (rest.idxOf (μ x)) ++ μ x :: rest.drop (rest.idxOf (μ x) + 1) := by
        conv_lhs => rw [← List.take_append_drop (rest.idxOf (μ x)) rest]
        rw [List.drop_eq_getElem_cons hjl, List.getElem_idxOf hjl]
      obtain ⟨A, hA⟩ : ∃ A, A = rest.take (rest.idxOf (μ x)) := ⟨_, rfl⟩
      obtain ⟨B, hB⟩ : ∃ B, B = rest.drop (rest.idxOf (μ x) + 1) := ⟨_, rfl⟩
      rw [← hA, ← hB] at split
      have hAl : A.length = rest.idxOf (μ x) := by rw [hA, List.length_take]; omega
      have hnd : (A ++ μ x :: B).Nodup := split ▸ hnr
      rw [List.nodup_append] at hnd
      obtain ⟨nA, nyB, dAB⟩ := hnd
      have yA : μ x ∉ A := fun h => dAB _ h _ List.mem_cons_self rfl
      have yB : μ x ∉ B := (List.nodup_cons.mp nyB).1
      have nB := (List.nodup_cons.mp nyB).2
      have AB : ∀ z ∈ A, z ∉ B := fun z hz hz' => dAB _ hz _ (List.mem_cons_of_mem _ hz') rfl
      have xA : x ∉ A := fun h => hxr (by rw [split]; exact List.mem_append_left _ h)
      have xB : x ∉ B := fun h => hxr (by rw [split]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h))
      have hl' : x :: rest = x :: (A ++ μ x :: B) := by rw [← split]
      -- positions in the whole list
      have pA : ∀ z ∈ A, (x :: rest).idxOf z = 1 + A.idxOf z := fun z hz => by
        rw [hl', List.idxOf_cons_ne _ (fun e => xA (by rw [e]; exact hz)), idxOf_app_mem' _ hz]; omega
      have pY : (x :: rest).idxOf (μ x) = 1 + A.length := by
        rw [hl', List.idxOf_cons_ne _ hyx.symm, idxOf_app_not_mem' _ yA, List.idxOf_cons_self]; omega
      have pB : ∀ z ∈ B, (x :: rest).idxOf z = 2 + A.length + B.idxOf z := fun z hz => by
        have zy : μ x ≠ z := fun e => yB (by rw [e]; exact hz)
        rw [hl', List.idxOf_cons_ne _ (fun e => xB (by rw [e]; exact hz)), idxOf_app_not_mem' _ (fun h => AB z h hz),
          List.idxOf_cons_ne _ zy]; omega
      have memL : ∀ z, z ∈ x :: rest ↔ z = x ∨ z ∈ A ∨ z = μ x ∨ z ∈ B := by
        intro z; rw [split]; simp
      have lenA : ∀ z ∈ A, A.idxOf z < A.length := fun z hz => List.idxOf_lt_length_iff.mpr hz
      -- each side is closed under `μ`
      have closeA : ∀ z ∈ A, μ z ∈ A := by
        intro z hz
        obtain ⟨a1, -, a3⟩ := hi z ((memL z).mpr (Or.inr (Or.inl hz)))
        rcases (memL _).mp a1 with e | e | e | e
        · exact absurd (by rw [← a3, e] : z = μ x) (fun h => yA (h ▸ hz))
        · exact e
        · exact absurd (by rw [← a3, e, hyy] : z = x) (fun h => xA (h ▸ hz))
        · exfalso
          apply hc x (by simp) z ((memL z).mpr (Or.inr (Or.inl hz)))
          rw [List.idxOf_cons_self, pA z hz, pY, pB _ e]
          have := lenA z hz
          omega
      have closeB : ∀ z ∈ B, μ z ∈ B := by
        intro z hz
        obtain ⟨a1, -, a3⟩ := hi z ((memL z).mpr (Or.inr (Or.inr (Or.inr hz))))
        rcases (memL _).mp a1 with e | e | e | e
        · exact absurd (by rw [← a3, e] : z = μ x) (fun h => yB (h ▸ hz))
        · exact absurd (by rw [← a3]; exact closeA _ e : z ∈ A) (fun h => AB z h hz)
        · exact absurd (by rw [← a3, e, hyy] : z = x) (fun h => xB (h ▸ hz))
        · exact e
      have invA : Invo μ A := fun z hz =>
        ⟨closeA z hz, (hi z ((memL z).mpr (Or.inr (Or.inl hz)))).2.1, (hi z ((memL z).mpr (Or.inr (Or.inl hz)))).2.2⟩
      have invB : Invo μ B := fun z hz =>
        ⟨closeB z hz, (hi z ((memL z).mpr (Or.inr (Or.inr (Or.inr hz))))).2.1,
          (hi z ((memL z).mpr (Or.inr (Or.inr (Or.inr hz))))).2.2⟩
      have ncA : NoCross μ A := by
        intro z hz w hw h
        apply hc z ((memL z).mpr (Or.inr (Or.inl hz))) w ((memL w).mpr (Or.inr (Or.inl hw)))
        rw [pA z hz, pA w hw, pA _ (closeA z hz), pA _ (closeA w hw)]
        omega
      have ncB : NoCross μ B := by
        intro z hz w hw h
        apply hc z ((memL z).mpr (Or.inr (Or.inr (Or.inr hz)))) w ((memL w).mpr (Or.inr (Or.inr (Or.inr hw))))
        rw [pB z hz, pB w hw, pB _ (closeB z hz), pB _ (closeB w hw)]
        omega
      have even := invo_even μ A.length A rfl nA invA
      have lenR : rest.length = A.length + 1 + B.length := by rw [split]; simp; omega
      obtain ⟨mA, hmA, mateA, subA⟩ := ih A (by simp at hl; omega) nA invA ncA
      obtain ⟨mB, hmB, mateB, subB⟩ := ih B (by simp at hl; omega) nB invB ncB
      refine ⟨(x, μ x) :: (mA ++ mB), ?_, fun z hz => ?_, fun pr hpr => ?_⟩
      · unfold ncm
        rw [List.mem_flatMap]
        refine ⟨rest.idxOf (μ x), List.mem_range.mpr hjl, ?_⟩
        rw [ite_eq_left (by rw [← hAl]; exact even), List.mem_flatMap]
        refine ⟨mA, by rw [← hA]; exact hmA, ?_⟩
        rw [List.mem_map]
        exact ⟨mB, by rw [← hB]; exact hmB, by rw [gy]⟩
      · rcases (memL z).mp hz with rfl | e | rfl | e
        · exact mate_head _ _ _
        · rw [mate_skip (fun h => xA (by rw [← h]; exact e)) (fun h => yA (by rw [← h]; exact e)), mate_app_left (by rw [mateA z e]; exact (invA z e).2.1),
            mateA z e]
        · rw [mate_head' hyx.symm, hyy]
        · rw [mate_skip (fun h => xB (by rw [← h]; exact e)) (fun h => yB (by rw [← h]; exact e)), mate_app_right, mateB z e]
          intro pr hpr
          obtain ⟨s1, s2⟩ := subA pr hpr
          exact ⟨fun h => AB _ s1 (h ▸ e), fun h => AB _ s2 (h ▸ e)⟩
      · rcases List.mem_cons.mp hpr with rfl | hpr
        · exact ⟨by simp, by simp [hy']⟩
        · rcases List.mem_append.mp hpr with h | h
          · obtain ⟨s1, s2⟩ := subA pr h
            exact ⟨(memL _).mpr (Or.inr (Or.inl s1)), (memL _).mpr (Or.inr (Or.inl s2))⟩
          · obtain ⟨s1, s2⟩ := subB pr h
            exact ⟨(memL _).mpr (Or.inr (Or.inr (Or.inr s1))), (memL _).mpr (Or.inr (Or.inr (Or.inr s2)))⟩

end NCM

/-! ### The outside test passes -/

/-- A chain with the matching given as a function. -/
structure AltF (m : ℕ) (link : ℕ → ℕ) (mf : ℕ → ℕ) (N : List ℕ) : Prop where
  even : N.length % 2 = 0
  two : 2 ≤ N.length
  mates : ∀ t, 2 * t + 1 < N.length →
    mf (N.getD (2 * t) 0) = N.getD (2 * t + 1) 0 ∧ mf (N.getD (2 * t + 1) 0) = N.getD (2 * t) 0
  links : ∀ t, 2 * t + 2 < N.length →
    link (N.getD (2 * t + 1) 0) = N.getD (2 * t + 2) 0 ∧ link (N.getD (2 * t + 2) 0) = N.getD (2 * t + 1) 0 ∧
      N.getD (2 * t + 1) 0 < m ∧ N.getD (2 * t + 2) 0 < m
  first : m ≤ link (N.getD 0 0)
  last : m ≤ link (N.getD (N.length - 1) 0)

theorem altF_alt {m : ℕ} {link link' : ℕ → ℕ} {mf : ℕ → ℕ} {mt : List (ℕ × ℕ)} {N : List ℕ}
    (h : AltF m link mf N) (hm : ∀ i ∈ N, mate mt i = mf i) (hl : ∀ i ∈ N, link' i = link i) :
    Alt m link' mt N := by
  have mem : ∀ j, j < N.length → N.getD j 0 ∈ N := fun j hj => by
    rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
  refine ⟨h.even, h.two, fun t ht => ?_, fun t ht => ?_, ?_, ?_⟩
  · rw [hm _ (mem _ (by omega)), hm _ (mem _ ht)]; exact h.mates t ht
  · rw [hl _ (mem _ (by omega)), hl _ (mem _ ht)]; exact h.links t ht
  · rw [hl _ (mem _ (by have := h.two; omega))]; exact h.first
  · rw [hl _ (mem _ (by have := h.two; omega))]; exact h.last

/-- **The outside test passes**, given the outside data of a solution. -/
theorem outsideOK_of {a b odd : ℕ} {F : FSpec} {s : St} (linkF μ : ℕ → ℕ) (N : ℕ → List ℕ)
    (hlink : ∀ i, i < mOf a b F s → linkOf a b F s i = some (linkF i))
    (hm0 : mOf a b F s ≠ 0)
    (hpar : parOf a b F s = 2 * (odd : Int))
    (hinv : Invo μ (List.range (mOf a b F s)))
    (hnc : NoCross μ (List.range (mOf a b F s)))
    (hfr : ∀ i, fxOf a b F s = some i → i < mOf a b F s ∧ μ i = mOf a b F s - 1)
    (hN : ∀ c, c ≤ 1 → ((N c = [] ∧ (s.2 / 2 ^ c) % 2 = 1) ∨
      (AltF (mOf a b F s) linkF μ (N c) ∧ (s.2 / 2 ^ c) % 2 = 0 ∧
        linkF ((N c).getD 0 0) = mOf a b F s + c ∧
        linkF ((N c).getD ((N c).length - 1) 0) = mOf a b F s + c)))
    (hT : ∀ i, i < mOf a b F s → ∀ c, c ≤ 1 → linkF i = mOf a b F s + c →
      i ∈ N c ∧ (i = (N c).getD 0 0 ∨ i = (N c).getD ((N c).length - 1) 0))
    (hb : ∀ c, c ≤ 1 → ∀ i ∈ N c, i < mOf a b F s)
    (hcov : ∀ i, i < mOf a b F s → i ∈ N 0 ∨ i ∈ N 1)
    (hnd : ∀ c, c ≤ 1 → (N c).Nodup) :
    outsideOK a b odd F s = true := by
  unfold outsideOK
  dsimp only
  have hall : ((List.range (mOf a b F s)).map (linkOf a b F s)).any (·.isNone) = false := by
    rw [List.any_eq_false]
    intro o ho
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ho
    rw [hlink i (List.mem_range.mp hi)]; simp
  rw [ite_eq_right (by rw [hall]; simp)]
  have hlk : ∀ i, i < mOf a b F s →
      ((((List.range (mOf a b F s)).map (linkOf a b F s)).getD i none).getD 0) = linkF i := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range, hlink i hi]
    rfl
  have heven := invo_even μ _ _ (List.length_range) List.nodup_range hinv
  obtain ⟨mt, hmt, hmate, -⟩ := ncm_complete μ (mOf a b F s) (List.range (mOf a b F s)) (by simp) List.nodup_range hinv hnc
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.any_eq_true]
  refine ⟨⟨⟨hm0, by simpa using heven⟩, hpar⟩, mt, hmt, ?_, ?_⟩
  · cases hfx : fxOf a b F s with
    | none => rfl
    | some i =>
      obtain ⟨h1, h2⟩ := hfr i hfx
      simp only [beq_iff_eq]
      rw [hmate i (List.mem_range.mpr h1), h2]
  · apply structOK_ok N
    · intro c hc
      rcases hN c hc with h | ⟨ha, hd, hf, hl⟩
      · exact Or.inl h
      · have hbc := hb c hc
        refine Or.inr ⟨altF_alt ha (fun i hi => hmate i (List.mem_range.mpr (hbc i hi)))
          (fun i hi => hlk i (hbc i hi)), hd, ?_, ?_⟩
        · rw [hlk _ (hbc _ (by
            rw [List.getD_eq_getElem _ _ (by have := ha.two; omega)]; exact List.getElem_mem _))]; exact hf
        · rw [hlk _ (hbc _ (by
            rw [List.getD_eq_getElem _ _ (by have := ha.two; omega)]; exact List.getElem_mem _))]; exact hl
    · intro i hi c hc e
      rw [hlk i hi] at e
      exact hT i hi c hc e
    · exact hb
    · exact hcov
    · exact hnd

end ZZN.Win

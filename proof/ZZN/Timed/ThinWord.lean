/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Timed.ThinMatch

@[expose] public section

/-!
# Counting reached states by their frontier words

The word of a state after `n` cells has one letter per frontier place `k ≤ b`: `0` if no piece
uses the plug there, `1` if a piece joins it to a later place, `2` to an earlier place, `3 + col`
if a piece joins it to an endpoint of colour `col`; then the colour mask. Pieces do not cross
(`fold_NC`), so the places joined by pieces form a non-crossing matching, fixed by its letters
`1, 2` (`match_eq`). Every piece has a plug end (`fold_NoTT`), so the word fixes the state
(`word_inj`).

The word is a valid bracket word: every prefix has at most as many `2` as `1`, and the whole word
equally many. At most two letters name each colour (two endpoints per colour, `tcount_le`), and
none does once the colour is done (`dn_bit`). The valid words are counted by `wcnt`
(`card_wset_le`), so a duplicate-free list of reached states has at most `wcnt (b + 1) 0 0 0`
entries (`card_sw`).
-/

namespace ZZN.T

open ZZN ZZN.Thin GridHam

/-! ### Every piece has a plug end -/

/-- No piece joins two endpoint codes. -/
def NoTT (a b : ℕ) (s : St) : Prop := ∀ z ∈ s.1, ¬ (isTerm a b (lo z) = true ∧ isTerm a b (hi z) = true)

lemma closeP_NoTT {a b x y : ℕ} {rest : List ℕ} {dn : ℕ} {s' : St}
    (h : closeP a b x y rest dn = some s') (hr : NoTT a b (rest, dn)) : NoTT a b s' := by
  unfold closeP at h
  split_ifs at h with h1
  · cases h; exact hr
  · cases h
    intro z hz
    rcases (mem_insSorted _ rest z).mp hz with rfl | hz
    · rw [lo_mkP, hi_mkP]
      rintro ⟨h2, h3⟩
      apply h1
      unfold isTerm at *
      simp only [decide_eq_true_eq, Bool.and_eq_true] at *
      omega
    · exact hr z hz

lemma stepCell_NoTT {a b : ℕ} {e : Option ℕ} {r c : ℕ} {s s' : St}
    (h : s' ∈ stepCell a b e r c s) (hs : NoTT a b s) : NoTT a b s' := by
  have hrest : NoTT a b (restK s.1 (puOf s r c) (plOf b s c), s.2) :=
    fun z hz => hs z ((restK_sublist _ _ _).subset hz)
  rw [ZZN.Thin.stepCell_eq] at h
  split_ifs at h
  · simp at h
  · simp at h
  · rw [List.mem_filterMap] at h
    obtain ⟨outs, -, ho⟩ := h
    split at ho
    · exact closeP_NoTT ho hrest
    · cases ho

/-- **No reached state has a piece joining two endpoint codes.** -/
theorem fold_NoTT (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) :
    ∀ n, ∀ s ∈ (List.range n).foldl (stageF a b tm) [([], 0)], NoTT a b s := by
  intro n
  induction n with
  | zero => intro s hs; rw [List.mem_singleton.mp hs]; intro z hz; simp at hz
  | succ n ih =>
    intro s hs
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hs
    unfold stageF stage at hs
    rw [List.mem_filter, mem_normS, List.mem_flatMap] at hs
    obtain ⟨⟨s0, h0, h1⟩, -⟩ := hs
    exact stepCell_NoTT h1 (ih s0 h0)

/-! ### Places and codes -/

/-- The plug code at frontier place `k`. -/
def codeAt (b n k : ℕ) : ℕ := if k < n % b then k else if k = n % b then b else k - 1

section Places
variable {b n : ℕ}

lemma posP_codeAt (hb : 0 < b) {k : ℕ} (hk : k ≤ b) : posP b n (codeAt b n k) = k := by
  have := Nat.mod_lt n hb; unfold posP codeAt; split_ifs <;> omega

lemma codeAt_posP (hb : 0 < b) {j : ℕ} : codeAt b n (posP b n j) = j := by
  have := Nat.mod_lt n hb; unfold posP codeAt; split_ifs <;> omega

lemma posP_le (hb : 0 < b) {j : ℕ} (hj : j ≤ b) : posP b n j ≤ b := by
  have := Nat.mod_lt n hb; unfold posP; split_ifs <;> omega

lemma codeAt_le (hb : 0 < b) {k : ℕ} (hk : k ≤ b) : codeAt b n k ≤ b := by
  have := Nat.mod_lt n hb; unfold codeAt; split_ifs <;> omega

end Places

/-! ### The matching of a state -/

/-- Places `p, q` hold the two plug ends of one piece. -/
def Ms (b n : ℕ) (ps : List ℕ) (p q : ℕ) : Prop :=
  ∃ z ∈ ps, hi z ≤ b ∧ ((posP b n (lo z) = p ∧ posP b n (hi z) = q) ∨
    (posP b n (lo z) = q ∧ posP b n (hi z) = p))

/-- The facts about a reached state used for counting. -/
structure SW (a b n : ℕ) (s : St) : Prop where
  good : Good2 a b s
  nc : NC b n s.1
  plug : ∀ z ∈ s.1, lo z ≤ b
  pos : 0 < b

section Match
variable {a b n : ℕ} {s : St}

lemma ms_mtch (h : SW a b n s) : Mtch (Ms b n s.1) := by
  obtain ⟨⟨⟨-, -, -⟩, -, hlt, hPD⟩, hNC, hpl, hb⟩ := h
  have hne : ∀ z ∈ s.1, posP b n (lo z) ≠ posP b n (hi z) := fun z hz h' =>
    absurd (posP_inj hb h') (by have := hlt z hz; omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro p q ⟨z, hz, hzb, h' | h'⟩
    · exact ⟨z, hz, hzb, Or.inr h'⟩
    · exact ⟨z, hz, hzb, Or.inl h'⟩
  · rintro p q q' ⟨z, hz, hzb, hq⟩ ⟨z', hz', hzb', hq'⟩
    have l1 := hpl z hz
    have l2 := hpl z' hz'
    have e : z = z' := by
      rcases hq with ⟨h1, -⟩ | ⟨-, h1⟩ <;> rcases hq' with ⟨h2, -⟩ | ⟨-, h2⟩
      · exact hPD z hz z' hz' (lo z) l1 (Or.inl rfl) (Or.inl (posP_inj hb (h2.trans h1.symm)))
      · exact hPD z hz z' hz' (lo z) l1 (Or.inl rfl) (Or.inr (posP_inj hb (h2.trans h1.symm)))
      · exact hPD z hz z' hz' (hi z) hzb (Or.inr rfl) (Or.inl (posP_inj hb (h2.trans h1.symm)))
      · exact hPD z hz z' hz' (hi z) hzb (Or.inr rfl) (Or.inr (posP_inj hb (h2.trans h1.symm)))
    subst e
    have := hne z hz
    omega
  · rintro p ⟨z, hz, -, h' | h'⟩
    · exact hne z hz (h'.1.trans h'.2.symm)
    · exact hne z hz (h'.1.trans h'.2.symm)
  · rintro p q u v ⟨z, hz, hzb, hq⟩ ⟨z', hz', hzb', hv⟩ hpu hpv
    have hzz : z ≠ z' := by
      rintro rfl
      rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hv with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
    have k := hNC z hz z' hz' hzz (hpl z hz) hzb (hpl z' hz') hzb'
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact k
    · rwa [cross_swap']
    · rwa [cross_swap]
    · rwa [cross_swap, cross_swap']

end Match

/-! ### Letters -/

/-- The letter at frontier place `k`. -/
def letter (a b n : ℕ) (ps : List ℕ) (k : ℕ) : ℕ :=
  match pieceAt ps (codeAt b n k) with
  | none => 0
  | some z =>
    if otherAt z (codeAt b n k) ≤ b then
      (if k < posP b n (otherAt z (codeAt b n k)) then 1 else 2)
    else 3 + colE a b (otherAt z (codeAt b n k))

/-- The word of a state: one letter per place `0 .. b`, then the colour mask. -/
def wordOf (a b n : ℕ) (s : St) : List ℕ := (List.range (b + 1)).map (letter a b n s.1) ++ [s.2]

lemma pieceAt_mem {ps : List ℕ} {j z : ℕ} (h : pieceAt ps j = some z) : z ∈ ps ∧ (lo z = j ∨ hi z = j) := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have hp := List.find?_some h
  simp only [Bool.or_eq_true, beq_iff_eq] at hp
  exact hp

section Letters
variable {a b n : ℕ} {s : St}

lemma pieceAt_of (h : SW a b n s) {z j : ℕ} (hz : z ∈ s.1) (hj : lo z = j ∨ hi z = j) (hjb : j ≤ b) :
    pieceAt s.1 j = some z := by
  obtain ⟨z', h1, hm, hj'⟩ := pieceAt_some hz hj
  rw [h1, h.good.2.2.2 z' hm z hz j hjb hj' hj]

lemma otherAt_ends {z j : ℕ} (hj : lo z = j ∨ hi z = j) (hlt : lo z < hi z) :
    (lo z = j ∧ hi z = otherAt z j) ∨ (hi z = j ∧ lo z = otherAt z j) := by
  unfold otherAt
  rcases hj with rfl | rfl
  · left; simp
  · right; simp only [show lo z ≠ hi z by omega, ↓reduceIte]; simp

lemma op_iff (h : SW a b n s) {k : ℕ} (hk : k ≤ b) : Op (Ms b n s.1) k ↔ letter a b n s.1 k = 1 := by
  have hb := h.pos
  have hlt := h.good.2.2.1
  constructor
  · rintro ⟨q, hkq, z, hz, hzb, hq⟩
    have l1 := h.plug z hz
    rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hc : codeAt b n k = lo z := by rw [← h1, codeAt_posP hb]
      have hp := pieceAt_of h hz (Or.inl hc.symm) (by omega)
      unfold letter; rw [hp]
      have ho : otherAt z (codeAt b n k) = hi z := by rw [hc]; unfold otherAt; simp
      simp only [ho, hzb, ↓reduceIte, h2, hkq]
    · have hc : codeAt b n k = hi z := by rw [← h2, codeAt_posP hb]
      have hp := pieceAt_of h hz (Or.inr hc.symm) (by rw [hc]; exact hzb)
      unfold letter; rw [hp]
      have ho : otherAt z (codeAt b n k) = lo z := by
        rw [hc]; unfold otherAt; simp [show lo z ≠ hi z by have := hlt z hz; omega]
      simp only [ho, l1, ↓reduceIte, h1, hkq]
  · intro hl
    unfold letter at hl
    split at hl
    · cases hl
    · rename_i z hp
      obtain ⟨hz, hj⟩ := pieceAt_mem hp
      split_ifs at hl with ho hkp
      rotate_left
      · omega
      · omega
      refine ⟨_, hkp, z, hz, ?_, ?_⟩
      · rcases otherAt_ends hj (hlt z hz) with ⟨-, e⟩ | ⟨e, -⟩
        · rw [e]; exact ho
        · rw [e]; exact codeAt_le hb hk
      · rcases otherAt_ends hj (hlt z hz) with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · left; rw [e1, e2, posP_codeAt hb hk]; exact ⟨rfl, rfl⟩
        · right; rw [e1, e2, posP_codeAt hb hk]; exact ⟨rfl, rfl⟩

lemma cl_iff (h : SW a b n s) {k : ℕ} (hk : k ≤ b) : Cl (Ms b n s.1) k ↔ letter a b n s.1 k = 2 := by
  have hb := h.pos
  have hlt := h.good.2.2.1
  constructor
  · rintro ⟨q, hkq, z, hz, hzb, hq⟩
    have l1 := h.plug z hz
    rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hc : codeAt b n k = lo z := by rw [← h1, codeAt_posP hb]
      have hp := pieceAt_of h hz (Or.inl hc.symm) (by omega)
      unfold letter; rw [hp]
      have ho : otherAt z (codeAt b n k) = hi z := by rw [hc]; unfold otherAt; simp
      simp only [ho, hzb, ↓reduceIte, h2, show ¬ k < q by omega]
    · have hc : codeAt b n k = hi z := by rw [← h2, codeAt_posP hb]
      have hp := pieceAt_of h hz (Or.inr hc.symm) (by rw [hc]; exact hzb)
      unfold letter; rw [hp]
      have ho : otherAt z (codeAt b n k) = lo z := by
        rw [hc]; unfold otherAt; simp [show lo z ≠ hi z by have := hlt z hz; omega]
      simp only [ho, l1, ↓reduceIte, h1, show ¬ k < q by omega]
  · intro hl
    unfold letter at hl
    split at hl
    · cases hl
    · rename_i z hp
      obtain ⟨hz, hj⟩ := pieceAt_mem hp
      split_ifs at hl with ho hkp
      · omega
      rotate_left
      · omega
      have hne : k ≠ posP b n (otherAt z (codeAt b n k)) := by
        intro e
        have := congrArg (codeAt b n) e
        rw [codeAt_posP hb] at this
        rcases otherAt_ends hj (hlt z hz) with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · have := hlt z hz; omega
        · have := hlt z hz; omega
      refine ⟨posP b n (otherAt z (codeAt b n k)), by omega, z, hz, ?_, ?_⟩
      · rcases otherAt_ends hj (hlt z hz) with ⟨-, e⟩ | ⟨e, -⟩
        · rw [e]; exact ho
        · rw [e]; exact codeAt_le hb hk
      · rcases otherAt_ends hj (hlt z hz) with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · left; rw [e1, e2, posP_codeAt hb hk]; exact ⟨rfl, rfl⟩
        · right; rw [e1, e2, posP_codeAt hb hk]; exact ⟨rfl, rfl⟩

lemma ms_le (h : SW a b n s) {p q : ℕ} (hm : Ms b n s.1 p q) : p ≤ b ∧ q ≤ b := by
  obtain ⟨z, hz, hzb, hq⟩ := hm
  have l1 := posP_le (n := n) h.pos (h.plug z hz)
  have l2 := posP_le (n := n) h.pos hzb
  rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by omega, by omega⟩

lemma letter_lt (h : SW a b n s) (k : ℕ) : letter a b n s.1 k < 5 := by
  unfold letter
  split
  · omega
  · rename_i z hp
    obtain ⟨hz, -⟩ := pieceAt_mem hp
    have hg := goodEnd_other (h.good.1.2.2 z hz) (codeAt b n k)
    split_ifs with ho
    · omega
    · omega
    · unfold GoodEnd at hg
      unfold colE termE at *
      omega

end Letters

/-! ### The word fixes the state -/

section Inj
variable {a b n : ℕ} {s s' : St}

lemma mem_of_letters (h : SW a b n s) (h' : SW a b n s')
    (heq : ∀ k ≤ b, letter a b n s.1 k = letter a b n s'.1 k) {z : ℕ} (hz : z ∈ s.1) : z ∈ s'.1 := by
  have hb := h.pos
  have hlt := h.good.2.2.1
  have hlt' := h'.good.2.2.1
  have hop : ∀ k, Op (Ms b n s.1) k ↔ Op (Ms b n s'.1) k := by
    intro k
    by_cases hk : k ≤ b
    · rw [op_iff h hk, op_iff h' hk, heq k hk]
    · exact iff_of_false (fun ⟨q, _, hm⟩ => hk (ms_le h hm).1) (fun ⟨q, _, hm⟩ => hk (ms_le h' hm).1)
  have hcl : ∀ k, Cl (Ms b n s.1) k ↔ Cl (Ms b n s'.1) k := by
    intro k
    by_cases hk : k ≤ b
    · rw [cl_iff h hk, cl_iff h' hk, heq k hk]
    · exact iff_of_false (fun ⟨q, _, hm⟩ => hk (ms_le h hm).1) (fun ⟨q, _, hm⟩ => hk (ms_le h' hm).1)
  have l1 := h.plug z hz
  by_cases hzb : hi z ≤ b
  · have hm : Ms b n s.1 (posP b n (lo z)) (posP b n (hi z)) := ⟨z, hz, hzb, Or.inl ⟨rfl, rfl⟩⟩
    obtain ⟨z', hz', hzb', hq⟩ := match_eq (ms_mtch h) (ms_mtch h') hop hcl hm
    have l1' := h'.plug z' hz'
    rcases hq with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have := piece_eq (posP_inj hb e1) (posP_inj hb e2)
      rw [← this]; exact hz'
    · have a1 := posP_inj hb e1
      have a2 := posP_inj hb e2
      have := hlt z hz
      have := hlt' z' hz'
      omega
  · -- A piece from a plug to an endpoint.
    have hc : codeAt b n (posP b n (lo z)) = lo z := codeAt_posP hb
    have hk := posP_le (n := n) hb l1
    have e := heq _ hk
    have hp := pieceAt_of h hz (Or.inl rfl) l1
    have ho : otherAt z (lo z) = hi z := by unfold otherAt; simp
    unfold letter at e
    rw [hc, hp] at e
    simp only [ho, hzb, ↓reduceIte] at e
    split at e
    · omega
    · rename_i z' hp'
      obtain ⟨hz', hj'⟩ := pieceAt_mem hp'
      split_ifs at e with ho'
      · omega
      · omega
      · have hg := (h.good.1.2.2 z hz).2
        have hg' := goodEnd_other (h'.good.1.2.2 z' hz') (lo z)
        have hoe : otherAt z' (lo z) = hi z := by
          unfold GoodEnd at hg hg'
          unfold colE termE at *
          omega
        rcases otherAt_ends hj' (hlt' z' hz') with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · have := piece_eq e1 (e2.trans hoe)
          exact this ▸ hz'
        · have := hlt' z' hz'
          omega

/-- **The word of a reached state fixes the state.** -/
theorem word_inj (h : SW a b n s) (h' : SW a b n s') (he : wordOf a b n s = wordOf a b n s') : s = s' := by
  unfold wordOf at he
  obtain ⟨hl, hd⟩ := List.append_inj he (by simp)
  have heq : ∀ k ≤ b, letter a b n s.1 k = letter a b n s'.1 k := by
    intro k hk
    have := congrArg (fun l => l[k]?) hl
    simp only [List.getElem?_map, List.getElem?_range (by omega : k < b + 1), Option.map_some,
      Option.some.injEq] at this
    exact this
  have hm : ∀ z, z ∈ s.1 ↔ z ∈ s'.1 := fun z =>
    ⟨fun hz => mem_of_letters h h' heq hz,
      fun hz => mem_of_letters h' h (fun k hk => (heq k hk).symm) hz⟩
  obtain ⟨⟨⟨hn, -, -⟩, hsort, -, -⟩, -, -, -⟩ := h
  obtain ⟨⟨⟨hn', -, -⟩, hsort', -, -⟩, -, -, -⟩ := h'
  have hp : s.1.Perm s'.1 := (List.perm_ext_iff_of_nodup hn hn').mpr hm
  have e1 : s.1 = s'.1 := List.Perm.eq_of_pairwise' hsort hsort' hp
  have e2 : s.2 = s'.2 := by simpa using hd
  exact Prod.ext e1 e2

end Inj

/-! ### Valid words and their number -/

/-- The number of valid word tails: `m` letters left, `d` open pairs, `u` and `v` letters of
colours `0` and `1` used so far; then the colour mask. -/
def wcnt : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, d, u, v => if d = 0 then (if u = 0 then 2 else 1) * (if v = 0 then 2 else 1) else 0
  | m + 1, d, u, v => wcnt m d u v + wcnt m (d + 1) u v + (if 0 < d then wcnt m (d - 1) u v else 0) +
      (if u < 2 then wcnt m d (u + 1) v else 0) + (if v < 2 then wcnt m d u (v + 1) else 0)

/-- The valid word tails. -/
def wset : ℕ → ℕ → ℕ → ℕ → Finset (List ℕ)
  | 0, d, u, v => if d = 0 then
      ((Finset.range 4).filter (fun dn => (dn % 2 = 1 → u = 0) ∧ (dn / 2 % 2 = 1 → v = 0))).image
        (fun dn => [dn])
    else ∅
  | m + 1, d, u, v => (wset m d u v).image (List.cons 0) ∪ (wset m (d + 1) u v).image (List.cons 1) ∪
      (if 0 < d then (wset m (d - 1) u v).image (List.cons 2) else ∅) ∪
      (if u < 2 then (wset m d (u + 1) v).image (List.cons 3) else ∅) ∪
      (if v < 2 then (wset m d u (v + 1)).image (List.cons 4) else ∅)

lemma card_ite_image {c : Prop} [Decidable c] {X : Finset (List ℕ)} {f : List ℕ → List ℕ} {k : ℕ}
    (h : X.card ≤ k) : (if c then X.image f else ∅).card ≤ if c then k else 0 := by
  split_ifs
  · exact Finset.card_image_le.trans h
  · simp

theorem card_wset_le : ∀ m d u v, (wset m d u v).card ≤ wcnt m d u v
  | 0, d, u, v => by
    unfold wset wcnt
    by_cases hd : d = 0
    · simp only [hd, ↓reduceIte]
      refine Finset.card_image_le.trans ?_
      by_cases hu : u = 0 <;> by_cases hv : v = 0
      · simp only [hu, hv, ↓reduceIte]; exact (Finset.card_filter_le _ _).trans (by simp)
      · simp only [hu, hv, ↓reduceIte]
        refine (Finset.card_le_card (t := {0, 1}) ?_).trans (by simp)
        intro dn hdn
        simp only [Finset.mem_filter, Finset.mem_range] at hdn
        obtain ⟨h4, -, h1⟩ := hdn; have := mt h1 id
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      · simp only [hu, hv, ↓reduceIte]
        refine (Finset.card_le_card (t := {0, 2}) ?_).trans (by simp)
        intro dn hdn
        simp only [Finset.mem_filter, Finset.mem_range] at hdn
        obtain ⟨h4, h0, -⟩ := hdn; have := mt h0 id
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      · simp only [hu, hv, ↓reduceIte]
        refine (Finset.card_le_card (t := {0}) ?_).trans (by simp)
        intro dn hdn
        simp only [Finset.mem_filter, Finset.mem_range] at hdn
        obtain ⟨h4, h0, h1⟩ := hdn; have := mt h0 id; have := mt h1 id
        simp only [Finset.mem_singleton]; omega
    · simp [hd]
  | m + 1, d, u, v => by
    unfold wset wcnt
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add (le_trans (Finset.card_union_le _ _)
      (Nat.add_le_add (le_trans (Finset.card_union_le _ _) (Nat.add_le_add (le_trans
        (Finset.card_union_le _ _) (Nat.add_le_add ?_ ?_)) ?_)) ?_)) ?_)
    · exact Finset.card_image_le.trans (card_wset_le m d u v)
    · exact Finset.card_image_le.trans (card_wset_le m (d + 1) u v)
    · exact card_ite_image (card_wset_le m (d - 1) u v)
    · exact card_ite_image (card_wset_le m d (u + 1) v)
    · exact card_ite_image (card_wset_le m d u (v + 1))

/-- A valid word tail, letter by letter. -/
def Wok : List ℕ → ℕ → ℕ → ℕ → ℕ → Prop
  | [], d, u, v, dn => d = 0 ∧ dn < 4 ∧ (dn % 2 = 1 → u = 0) ∧ (dn / 2 % 2 = 1 → v = 0)
  | x :: L, d, u, v, dn => (x = 0 ∧ Wok L d u v dn) ∨ (x = 1 ∧ Wok L (d + 1) u v dn) ∨
      (x = 2 ∧ 0 < d ∧ Wok L (d - 1) u v dn) ∨ (x = 3 ∧ u < 2 ∧ Wok L d (u + 1) v dn) ∨
      (x = 4 ∧ v < 2 ∧ Wok L d u (v + 1) dn)

theorem mem_wset : ∀ (L : List ℕ) (d u v dn : ℕ), Wok L d u v dn → L ++ [dn] ∈ wset L.length d u v
  | [], d, u, v, dn, ⟨hd, h4, h0, h1⟩ => by
    show [dn] ∈ wset 0 d u v
    unfold wset
    simp only [hd, ↓reduceIte]
    exact Finset.mem_image.mpr ⟨dn, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h4, h0, h1⟩, rfl⟩
  | x :: L, d, u, v, dn, h => by
    simp only [List.length_cons, List.cons_append]
    unfold wset
    simp only [Finset.mem_union, Finset.mem_image, List.cons.injEq]
    rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, hd, h⟩ | ⟨rfl, hu, h⟩ | ⟨rfl, hv, h⟩
    · left; left; left; left; exact ⟨_, mem_wset L d u v dn h, rfl, rfl⟩
    · left; left; left; right; exact ⟨_, mem_wset L (d + 1) u v dn h, rfl, rfl⟩
    · left; left; right; simp only [hd, ↓reduceIte]; exact Finset.mem_image.mpr ⟨_, mem_wset L _ u v dn h, rfl⟩
    · left; right; simp only [hu, ↓reduceIte]; exact Finset.mem_image.mpr ⟨_, mem_wset L d _ v dn h, rfl⟩
    · right; simp only [hv, ↓reduceIte]; exact Finset.mem_image.mpr ⟨_, mem_wset L d u _ dn h, rfl⟩

lemma count_cons' (x y : ℕ) (L : List ℕ) : (x :: L).count y = L.count y + if x = y then 1 else 0 := by
  rw [List.count_cons]; simp

/-- Counting conditions give a valid word tail. -/
theorem wok_of : ∀ (L : List ℕ) (d u v dn : ℕ), (∀ x ∈ L, x < 5) →
    (∀ k, (L.take k).count 2 ≤ d + (L.take k).count 1) → L.count 2 = d + L.count 1 →
    u + L.count 3 ≤ 2 → v + L.count 4 ≤ 2 → dn < 4 → (dn % 2 = 1 → u + L.count 3 = 0) →
    (dn / 2 % 2 = 1 → v + L.count 4 = 0) → Wok L d u v dn
  | [], d, u, v, dn, _, _, ht, _, _, h4, h0, h1 => by
    simp only [List.count_nil, add_zero] at ht h0 h1
    exact ⟨by omega, h4, h0, h1⟩
  | x :: L, d, u, v, dn, hx, hp, ht, hu, hv, h4, h0, h1 => by
    have hx5 : x < 5 := hx x (by simp)
    have hL : ∀ y ∈ L, y < 5 := fun y hy => hx y (by simp [hy])
    have hpre : ∀ k, ((x :: L).take (k + 1)).count 2 ≤ d + ((x :: L).take (k + 1)).count 1 := fun k => hp (k + 1)
    simp only [List.take_succ_cons, count_cons'] at hpre
    simp only [count_cons'] at ht hu hv h0 h1
    have h1d := hp 1
    simp only [List.take_succ_cons, List.take_zero, count_cons', List.count_nil] at h1d
    unfold Wok
    rcases (show x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 by omega) with rfl | rfl | rfl | rfl | rfl
    · left
      exact ⟨rfl, wok_of L d u v dn hL (fun k => by have := hpre k; simpa using this) (by simpa using ht)
        (by simpa using hu) (by simpa using hv) h4 (by simpa using h0) (by simpa using h1)⟩
    · right; left
      refine ⟨rfl, wok_of L (d + 1) u v dn hL (fun k => ?_) (by simp at ht; omega)
        (by simpa using hu) (by simpa using hv) h4 (by simpa using h0) (by simpa using h1)⟩
      have := hpre k; simp at this; omega
    · right; right; left
      simp at h1d
      refine ⟨rfl, by omega, wok_of L (d - 1) u v dn hL (fun k => ?_) (by simp at ht; omega)
        (by simpa using hu) (by simpa using hv) h4 (by simpa using h0) (by simpa using h1)⟩
      have := hpre k; simp at this; omega
    · right; right; right; left
      simp at hu
      refine ⟨rfl, by omega, wok_of L d (u + 1) v dn hL (fun k => by have := hpre k; simpa using this)
        (by simpa using ht) (by omega) (by simpa using hv) h4 (fun h => by have := h0 h; simp at this)
        (by simpa using h1)⟩
    · right; right; right; right
      simp at hv
      refine ⟨rfl, by omega, wok_of L d u (v + 1) dn hL (fun k => by have := hpre k; simpa using this)
        (by simpa using ht) (by simpa using hu) (by omega) h4 (by simpa using h0)
        (fun h => by have := h1 h; simp at this)⟩

end ZZN.T

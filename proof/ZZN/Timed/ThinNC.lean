/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Timed.ThinCost

@[expose] public section

/-!
# Pieces of a reached state do not cross

After `n` cells the next cell is `(r, c) = (n / b, n % b)`. The plug codes lie on the frontier in
the order: codes `0 .. c-1`, then code `b`, then codes `c .. b-1`. `posP b n j` is the place of code
`j` in that order. Two pieces whose ends are both plugs never interleave in that order (`NC`,
`fold_NC`).

The step keeps this: the cell consumes the plugs at places `c` (code `b`) and `c + 1` (code `c`),
and its new plugs take the same two places (down plug `c`, right plug `b`). Codes of the other
pieces keep their places, all shifted by one when the row ends.
-/

namespace ZZN.T

open ZZN ZZN.Thin GridHam

/-- The place of plug code `j` on the frontier after `n` cells. -/
def posP (b n j : ℕ) : ℕ := if j = b then n % b else if j < n % b then j else j + 1

/-- `u` lies strictly between `x` and `y`. -/
def sep (x y u : ℕ) : Prop := (x < u ∧ u < y) ∨ (y < u ∧ u < x)

/-- The chords `{x, y}` and `{u, v}` interleave. -/
def Cross (x y u v : ℕ) : Prop := (sep x y u ∧ ¬ sep x y v) ∨ (¬ sep x y u ∧ sep x y v)

/-- No two pieces with plug ends only interleave. -/
def NC (b n : ℕ) (ps : List ℕ) : Prop :=
  ∀ z ∈ ps, ∀ z' ∈ ps, z ≠ z' → lo z ≤ b → hi z ≤ b → lo z' ≤ b → hi z' ≤ b →
    ¬ Cross (posP b n (lo z)) (posP b n (hi z)) (posP b n (lo z')) (posP b n (hi z'))

lemma posP_inj {b n j j' : ℕ} (hb : 0 < b) (h : posP b n j = posP b n j') :
    j = j' := by
  have := Nat.mod_lt n hb
  unfold posP at h; split_ifs at h <;> omega

lemma succ_mod {b n : ℕ} (hb : 0 < b) : (n + 1) % b = if n % b + 1 < b then n % b + 1 else 0 := by
  have h1 := Nat.mod_lt n hb
  have h2 := Nat.div_add_mod n b
  split_ifs with h
  · rw [show n + 1 = (n % b + 1) + b * (n / b) by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt h]
  · rw [show n + 1 = b * (n / b + 1) by rw [Nat.mul_add]; omega, Nat.mul_mod_right]

lemma sep_pivot {c A p : ℕ} (hp : p ≠ c ∧ p ≠ c + 1) : sep A c p ↔ sep A (c + 1) p := by
  unfold sep; omega

lemma sep_split {x y z p : ℕ} (hx : p ≠ x) (hy : p ≠ y) (hz : p ≠ z) :
    sep x y p ↔ (sep x z p ↔ ¬ sep y z p) := by
  unfold sep; omega

lemma sep_c {c p : ℕ} : ¬ sep (c + 1) c p := by
  unfold sep; omega

lemma sep_cc {c p : ℕ} : ¬ sep c c p := by
  unfold sep; omega

/-- An end of the new piece: one of the two consumed places, or an old end `X` whose piece did not
cross the chord `{p, q}`. -/
def NewEnd (c p q X : ℕ) : Prop :=
  X ≠ p ∧ X ≠ q ∧ (X = c ∨ X = c + 1 ∨ (¬ Cross X (c + 1) p q ∨ ¬ Cross X c p q))

lemma newEnd_iff {c p q X : ℕ} (hp : p ≠ c ∧ p ≠ c + 1) (hq : q ≠ c ∧ q ≠ c + 1) (h : NewEnd c p q X) :
    (sep X c p ↔ sep X c q) := by
  obtain ⟨-, -, h | h | h | h⟩ := h
  · subst h; exact iff_of_false sep_cc sep_cc
  · subst h; exact iff_of_false sep_c sep_c
  · unfold Cross at h; rw [← sep_pivot hp, ← sep_pivot hq] at h
    exact ⟨fun u => by_contra fun v => h (Or.inl ⟨u, v⟩), fun v => by_contra fun u => h (Or.inr ⟨u, v⟩)⟩
  · unfold Cross at h
    exact ⟨fun u => by_contra fun v => h (Or.inl ⟨u, v⟩), fun v => by_contra fun u => h (Or.inr ⟨u, v⟩)⟩

/-- The new piece against an old one. -/
lemma cross_core {c p q X Y : ℕ} (hp : p ≠ c ∧ p ≠ c + 1) (hq : q ≠ c ∧ q ≠ c + 1)
    (hX : NewEnd c p q X) (hY : NewEnd c p q Y) : ¬ Cross X Y p q := by
  have gX := newEnd_iff hp hq hX
  have gY := newEnd_iff hp hq hY
  have ip := sep_split (z := c) hX.1.symm hY.1.symm hp.1
  have iq := sep_split (z := c) hX.2.1.symm hY.2.1.symm hq.1
  unfold Cross; rw [ip, iq]; tauto

lemma cross_comm {x y u v : ℕ} (h1 : x ≠ u) (h2 : x ≠ v) (h3 : y ≠ u) (h4 : y ≠ v) :
    Cross x y u v ↔ Cross u v x y := by
  unfold Cross sep; omega

lemma cross_new {δ c p q X Y X0 Y0 : ℕ} (hp : p ≠ c ∧ p ≠ c + 1) (hq : q ≠ c ∧ q ≠ c + 1)
    (hX : X = X0 + δ ∧ NewEnd c p q X0) (hY : Y = Y0 + δ ∧ NewEnd c p q Y0) :
    ¬ Cross X Y (p + δ) (q + δ) ∧ ¬ Cross (p + δ) (q + δ) X Y := by
  obtain ⟨rfl, hX⟩ := hX
  obtain ⟨rfl, hY⟩ := hY
  have k := cross_core hp hq hX hY
  have k' : ¬ Cross (X0 + δ) (Y0 + δ) (p + δ) (q + δ) := by
    intro h; apply k; unfold Cross sep at h ⊢; omega
  refine ⟨k', fun h => k' ((cross_comm ?_ ?_ ?_ ?_).mpr h)⟩
  · have := hX.1; omega
  · have := hX.2.1; omega
  · have := hY.1; omega
  · have := hY.2.1; omega

lemma cross_shift {δ x y u v : ℕ} (h : ¬ Cross x y u v) : ¬ Cross (x + δ) (y + δ) (u + δ) (v + δ) := by
  unfold Cross sep at *; omega

lemma cross_swap {x y u v : ℕ} : Cross x y u v ↔ Cross y x u v := by
  unfold Cross sep; omega

lemma cross_swap' {x y u v : ℕ} : Cross x y u v ↔ Cross x y v u := by
  unfold Cross sep; omega

section
variable {a b : ℕ} {J : Inst}

/-- A plug code of a reached state names an existing frontier edge: code `b` only inside a row,
codes `j ≥ c` only below the first row. -/
lemma live_of_W {n : ℕ} {s : St} (hW : W a b J n s) {z : ℕ} (hz : z ∈ s.1) {e : ℕ}
    (he : lo z = e ∨ hi z = e) (heb : e ≤ b) :
    (e = b → n % b ≠ 0) ∧ (e < b → e < n % b ∨ b ≤ n) := by
  obtain ⟨sg, dp, -, -, hseg, -⟩ := hW
  obtain ⟨-, -, -, hp, u, v, hu, hv, eu, ev⟩ := hseg z hz
  have hum : u ∈ sg z := List.mem_of_mem_head? hu
  have hvm : v ∈ sg z := List.mem_of_mem_getLast? hv
  have key : ∃ x ∈ sg z, prI a b n x ∧ EndOK a b J n e x := by
    rcases he with rfl | rfl
    · exact ⟨u, hum, hp u hum, eu⟩
    · exact ⟨v, hvm, hp v hvm, ev⟩
  obtain ⟨x, -, hx, hE⟩ := key
  obtain ⟨y, hy, hadj, hd⟩ := plug_of hx hE (by omega)
  obtain ⟨x1, x2⟩ := x
  obtain ⟨hx1, hx2, hx3⟩ := hx
  simp only at hx1 hx2 hx3
  have hb : 0 < b := by omega
  have hdm := Nat.div_add_mod n b
  have hml := Nat.mod_lt n hb
  rcases bd_dir ⟨hx1, hx2, hx3⟩ hy hadj with rfl | rfl
  · have hd' : desc a b (x1, x2) (x1 + 1, x2) = if x1 + 1 < a then x2 else exitE b (a + (b - 1 - x2)) := by
      simp [desc]
    simp only at hd hy
    rw [hd'] at hd
    split_ifs at hd with ha
    · subst hd
      have hny : ¬ ((x1 + 1) * b + x2 < n) := fun h => hy ⟨ha, hx2, h⟩
      rw [Nat.add_mul, one_mul] at hny
      refine ⟨fun h => by omega, fun _ => ?_⟩
      by_cases hn : n < b
      · left; rw [Nat.mod_eq_of_lt hn]
        have : 0 ≤ x1 * b := Nat.zero_le _
        omega
      · right; omega
    · unfold exitE at hd; omega
  · have hd' : desc a b (x1, x2) (x1, x2 + 1) = if x2 + 1 < b then b else exitE b x1 := by
      simp [desc]
    simp only at hd hy
    rw [hd'] at hd
    split_ifs at hd with hc
    · subst hd
      have hny : ¬ (x1 * b + (x2 + 1) < n) := fun h => hy ⟨hx1, hc, h⟩
      refine ⟨fun _ => ?_, fun h => by omega⟩
      have hn : n = (x2 + 1) + b * x1 := by rw [mul_comm]; omega
      rw [hn, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]; omega
    · unfold exitE at hd; omega

lemma restK_ne {ps : List ℕ} (hn : ps.Nodup) {pu pl : Option ℕ} {z : ℕ} (hz : z ∈ restK ps pu pl) :
    pu ≠ some z ∧ pl ≠ some z := by
  unfold restK at hz
  split_ifs at hz with h1 h2 h2
  · have hn' := hn.erase (pu.getD 0)
    rw [hn'.mem_erase_iff, hn.mem_erase_iff] at hz
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp_all
  · rw [hn.mem_erase_iff] at hz
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp_all
  · rw [hn.mem_erase_iff] at hz
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp_all
  · refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp_all

lemma find_hasEnd_some {ps : List ℕ} {e z : ℕ} (h : ps.find? (hasEnd e) = some z) :
    z ∈ ps ∧ hasEnd e z = true :=
  ⟨List.mem_of_find?_eq_some h, List.find?_some h⟩

lemma find_hasEnd_none {ps : List ℕ} {e z : ℕ} (h : ps.find? (hasEnd e) = none) (hz : z ∈ ps) :
    hasEnd e z = false := by
  simpa using List.find?_eq_none.mp h z hz

lemma hasEnd_iff {e z : ℕ} : hasEnd e z = true ↔ (lo z = e ∨ hi z = e) := by
  simp only [hasEnd, Bool.or_eq_true, beq_iff_eq]

lemma other_ends {e z : ℕ} (h : hasEnd e z = true) :
    (lo z = e ∧ hi z = other e z) ∨ (hi z = e ∧ lo z = other e z) := by
  unfold other; rw [hasEnd_iff] at h
  by_cases h' : lo z = e
  · left; simp [h']
  · right; simp only [beq_iff_eq, h', ite_false]; tauto

lemma mem_optsOf {a b r c : ℕ} {e pu pl : Option ℕ} {outs : List ℕ} (h : outs ∈ optsOf a b r c e pu pl)
    {x : ℕ} (hx : x ∈ outs) : x = (if r + 1 < a then c else exitE b (a + (b - 1 - c))) ∨
      x = (if c + 1 < b then b else exitE b r) := by
  unfold optsOf at h
  split at h <;> simp only [List.mem_cons, List.mem_nil_iff, or_false] at h <;>
    rcases h with rfl | rfl <;> simp_all

/-- **One cell keeps the pieces from crossing.** -/
theorem step_NC {tm : List ((ℕ × ℕ) × ℕ)}
    (htm : ∀ y : Coord, y.1 < a → y.2 < b → termAt tm y = endCol J y)
    {n : ℕ} (hn : n < a * b) {s s' : St} (hW : W a b J n s) (hNC : NC b n s.1)
    (h : s' ∈ stepCell a b (termAt tm (cell b n)) (cell b n).1 (cell b n).2 s) : NC b (n + 1) s'.1 := by
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · subst h0; simp at hn
    · exact h0
  have hW' := step_W htm hn hW h
  have hnd : s.1.Nodup := hW.choose_spec.choose_spec.1
  have hPD := plugDisj_of_W hn.le hW
  have hlh := lo_ne_hi_of_W hW
  have hlh' := lo_ne_hi_of_W hW'
  set e := termAt tm (cell b n)
  set r := (cell b n).1 with hr
  set c := (cell b n).2 with hc
  have hrv : r = n / b := rfl
  have hcv : c = n % b := rfl
  have hcb : c < b := by rw [hcv]; exact Nat.mod_lt n hb
  have hdm := Nat.div_add_mod n b
  set δ := if c + 1 < b then 0 else 1 with hδ
  -- Places after the cell, for codes other than `c` and `b`.
  have shift : ∀ j, j ≤ b → j ≠ c → j ≠ b → posP b (n + 1) j = posP b n j + δ ∧
      posP b n j ≠ c ∧ posP b n j ≠ c + 1 := by
    intro j hj h1 h2
    unfold posP
    rw [succ_mod hb, ← hcv]
    simp only [hδ]
    split_ifs <;> omega
  have pos_c : posP b n c = c + 1 := by unfold posP; rw [← hcv]; split_ifs <;> omega
  have pos_b : posP b n b = c := by unfold posP; rw [← hcv]; simp
  have pos_c' : posP b (n + 1) c = c + δ := by
    unfold posP; rw [succ_mod hb, ← hcv]; simp only [hδ]; split_ifs <;> omega
  have pos_b' : c + 1 < b → posP b (n + 1) b = c + 1 + δ := by
    intro h; unfold posP; rw [succ_mod hb, ← hcv]; simp only [hδ]; split_ifs <;> omega
  -- The attached pieces.
  have hpu : ∀ zu, puOf s r c = some zu → zu ∈ s.1 ∧ hasEnd c zu = true := by
    intro zu h; unfold puOf at h; split_ifs at h; exact find_hasEnd_some h
  have hpl : ∀ zl, plOf b s c = some zl → zl ∈ s.1 ∧ hasEnd b zl = true := by
    intro zl h; unfold plOf at h; split_ifs at h; exact find_hasEnd_some h
  -- A plug end `c` or `b` belongs to the attached piece.
  have own_c : ∀ z ∈ s.1, hasEnd c z = true → puOf s r c = some z := by
    intro z hz hcz
    have hl := live_of_W hW hz (hasEnd_iff.mp hcz) hcb.le
    have hr1 : r ≠ 0 := by
      have := hl.2 hcb; rw [hrv]; intro h0
      rcases this with h' | h'
      · rw [← hcv] at h'; omega
      · have : 1 ≤ n / b := (Nat.one_le_div_iff hb).mpr h'; omega
    unfold puOf; simp only [hr1, ↓reduceIte]
    rcases hf : s.1.find? (hasEnd c) with _ | zu
    · rw [find_hasEnd_none hf hz] at hcz; cases hcz
    · obtain ⟨hzu, hcu⟩ := find_hasEnd_some hf
      rw [hPD zu hzu z hz c hcb.le (hasEnd_iff.mp hcu) (hasEnd_iff.mp hcz)]
  have own_b : ∀ z ∈ s.1, hasEnd b z = true → plOf b s c = some z := by
    intro z hz hbz
    have hl := live_of_W hW hz (hasEnd_iff.mp hbz) le_rfl
    have hc0 : c ≠ 0 := by rw [hcv]; exact hl.1 rfl
    unfold plOf; simp only [hc0, ↓reduceIte]
    rcases hf : s.1.find? (hasEnd b) with _ | zl
    · rw [find_hasEnd_none hf hz] at hbz; cases hbz
    · obtain ⟨hzl, hbl⟩ := find_hasEnd_some hf
      rw [hPD zl hzl z hz b le_rfl (hasEnd_iff.mp hbl) (hasEnd_iff.mp hbz)]
  have hns : ¬ ((puOf s r c).isSome && puOf s r c == plOf b s c) = true := by
    intro hh; rw [ZZN.Thin.stepCell_eq] at h; split_ifs at h <;> simp_all
  set rest := restK s.1 (puOf s r c) (plOf b s c) with hrest
  have rest_sub : ∀ z ∈ rest, z ∈ s.1 := fun z hz => (restK_sublist _ _ _).subset hz
  -- Plug ends of the remaining pieces avoid `c` and `b`.
  have rest_ends : ∀ z ∈ rest, ∀ j, (lo z = j ∨ hi z = j) → j ≤ b → j ≠ c ∧ j ≠ b := by
    intro z hz j hj hjb
    obtain ⟨n1, n2⟩ := restK_ne hnd hz
    refine ⟨fun h => n1 (own_c z (rest_sub z hz) (hasEnd_iff.mpr (h ▸ hj))),
      fun h => n2 (own_b z (rest_sub z hz) (hasEnd_iff.mpr (h ▸ hj)))⟩
  -- Old pieces in the rest keep their order.
  have rest_rest : ∀ z ∈ rest, ∀ z' ∈ rest, z ≠ z' → lo z ≤ b → hi z ≤ b → lo z' ≤ b → hi z' ≤ b →
      ¬ Cross (posP b (n + 1) (lo z)) (posP b (n + 1) (hi z))
        (posP b (n + 1) (lo z')) (posP b (n + 1) (hi z')) := by
    intro z hz z' hz' hne h1 h2 h3 h4
    have e1 := rest_ends z hz _ (Or.inl rfl) h1
    have e2 := rest_ends z hz _ (Or.inr rfl) h2
    have e3 := rest_ends z' hz' _ (Or.inl rfl) h3
    have e4 := rest_ends z' hz' _ (Or.inr rfl) h4
    rw [(shift _ h1 e1.1 e1.2).1, (shift _ h2 e2.1 e2.2).1, (shift _ h3 e3.1 e3.2).1,
      (shift _ h4 e4.1 e4.2).1]
    exact cross_shift (hNC z (rest_sub z hz) z' (rest_sub z' hz') hne h1 h2 h3 h4)
  -- The places of the new piece's plug ends.
  have new_end : ∀ z ∈ rest, lo z ≤ b → hi z ≤ b → ∀ x,
      (x ∈ insOf a b c e (puOf s r c) (plOf b s c) ∨
        x = (if r + 1 < a then c else exitE b (a + (b - 1 - c))) ∨
          x = (if c + 1 < b then b else exitE b r)) → x ≤ b →
      ∃ X0, posP b (n + 1) x = X0 + δ ∧ NewEnd c (posP b n (lo z)) (posP b n (hi z)) X0 := by
    intro z hz hz1 hz2 x hx hxb
    have e1 := rest_ends z hz _ (Or.inl rfl) hz1
    have e2 := rest_ends z hz _ (Or.inr rfl) hz2
    obtain ⟨-, sp1, sp2⟩ := shift _ hz1 e1.1 e1.2
    obtain ⟨-, sq1, sq2⟩ := shift _ hz2 e2.1 e2.2
    obtain ⟨n1, n2⟩ := restK_ne hnd hz
    -- An attached piece `w` with end `k` (place `P`), other end `x`.
    have attached : ∀ w ∈ s.1, ∀ k, hasEnd k w = true → w ≠ z → x = other k w → (k = c ∨ k = b) →
        (∀ w', w' ∈ s.1 → hasEnd (c + b - k) w' = true → w' ≠ w) →
        ∃ X0, posP b (n + 1) x = X0 + δ ∧ NewEnd c (posP b n (lo z)) (posP b n (hi z)) X0 := by
      intro w hw k hk hwz hxo hkc hother
      have hxk : x ≠ k := by
        rw [hxo]
        rcases other_ends hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← h2, ← h1]; exact (hlh w hw).symm
        · rw [← h2, ← h1]; exact hlh w hw
      have hxe : lo w = x ∨ hi w = x := by
        rcases other_ends hk with ⟨-, h2⟩ | ⟨-, h2⟩
        · right; rw [h2, hxo]
        · left; rw [h2, hxo]
      have hxc : x ≠ c ∧ x ≠ b := by
        rcases hkc with rfl | rfl
        · refine ⟨hxk, fun hxb' => ?_⟩
          have := hother w hw (by rw [show c + b - c = b by omega, hasEnd_iff, ← hxb']; exact hxe)
          exact this rfl
        · refine ⟨fun hxc' => ?_, hxk⟩
          have := hother w hw (by rw [show c + k - k = c by omega, hasEnd_iff, ← hxc']; exact hxe)
          exact this rfl
      obtain ⟨sx, -, -⟩ := shift x hxb hxc.1 hxc.2
      refine ⟨posP b n x, sx, ?_, ?_, Or.inr (Or.inr ?_)⟩
      · intro h
        have := posP_inj hb h
        exact hwz (hPD w hw z (rest_sub z hz) x hxb hxe (Or.inl this.symm))
      · intro h
        have := posP_inj hb h
        exact hwz (hPD w hw z (rest_sub z hz) x hxb hxe (Or.inr this.symm))
      · have hkb : k ≤ b := by rcases hkc with rfl | rfl <;> omega
        have hcr := hNC w hw z (rest_sub z hz) hwz
        have hpk : posP b n k = (if k = c then c + 1 else c) := by
          rcases hkc with rfl | rfl
          · rw [pos_c]; simp
          · rw [pos_b]; simp [show k ≠ c by omega]
        rcases other_ends hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2, ← hxo] at hcr
          have := hcr hkb hxb hz1 hz2
          rw [hpk] at this
          split_ifs at this
          · left; rwa [cross_swap]
          · right; rwa [cross_swap]
        · rw [h1, h2, ← hxo] at hcr
          have := hcr hxb hkb hz1 hz2
          rw [hpk] at this
          split_ifs at this
          · left; exact this
          · right; exact this
    simp only [insOf, List.mem_append] at hx
    rcases hx with ((hx | hx) | hx) | hx | hx
    · obtain ⟨zu, hzu, rfl⟩ := Option.mem_map.mp (Option.mem_toList.mp hx)
      obtain ⟨m1, m2⟩ := hpu zu hzu
      refine attached zu m1 c m2 (fun h => n1 (h ▸ hzu)) rfl (Or.inl rfl) (fun w' hw' hb' => ?_)
      intro hww; subst hww
      rw [show c + b - c = b by omega] at hb'
      have := own_b w' hw' hb'
      exact hns (by rw [hzu, this]; simp)
    · obtain ⟨zl, hzl, rfl⟩ := Option.mem_map.mp (Option.mem_toList.mp hx)
      obtain ⟨m1, m2⟩ := hpl zl hzl
      refine attached zl m1 b m2 (fun h => n2 (h ▸ hzl)) rfl (Or.inr rfl) (fun w' hw' hc' => ?_)
      intro hww; subst hww
      rw [show c + b - b = c by omega] at hc'
      have := own_c w' hw' hc'
      exact hns (by rw [hzl, this]; simp)
    · obtain ⟨col, -, rfl⟩ := Option.mem_map.mp (Option.mem_toList.mp hx)
      unfold termE at hxb; omega
    · split_ifs at hx with ha
      · exact ⟨c, by rw [hx, pos_c'], fun h => sp1 h.symm, fun h => sq1 h.symm, Or.inl rfl⟩
      · unfold exitE at hx; omega
    · split_ifs at hx with hc1
      · exact ⟨c + 1, by rw [hx, pos_b' hc1], fun h => sp2 h.symm, fun h => sq2 h.symm,
          Or.inr (Or.inl rfl)⟩
      · unfold exitE at hx; omega
  -- Assemble.
  rw [ZZN.Thin.stepCell_eq] at h
  split_ifs at h with hd
  · simp at h
  rw [List.mem_filterMap] at h
  obtain ⟨outs, hout, ho⟩ := h
  split at ho
  rename_i x y hxy
  · have hxm : x ∈ insOf a b c e (puOf s r c) (plOf b s c) ∨
        x = (if r + 1 < a then c else exitE b (a + (b - 1 - c))) ∨
          x = (if c + 1 < b then b else exitE b r) := by
      have : x ∈ insOf a b c e (puOf s r c) (plOf b s c) ++ outs := by rw [hxy]; simp
      rcases List.mem_append.mp this with h' | h'
      · exact Or.inl h'
      · exact Or.inr (mem_optsOf hout h')
    have hym : y ∈ insOf a b c e (puOf s r c) (plOf b s c) ∨
        y = (if r + 1 < a then c else exitE b (a + (b - 1 - c))) ∨
          y = (if c + 1 < b then b else exitE b r) := by
      have : y ∈ insOf a b c e (puOf s r c) (plOf b s c) ++ outs := by rw [hxy]; simp
      rcases List.mem_append.mp this with h' | h'
      · exact Or.inl h'
      · exact Or.inr (mem_optsOf hout h')
    unfold closeP at ho
    split_ifs at ho
    · cases ho
      exact fun z hz z' hz' => rest_rest z hz z' hz'
    · cases ho
      · simp only at hW' hlh' ⊢
        -- The new piece against a piece of the rest.
        have newp : ∀ z ∈ rest, lo z ≤ b → hi z ≤ b → lo (mkP x y) ≤ b → hi (mkP x y) ≤ b →
            ¬ Cross (posP b (n + 1) (lo (mkP x y))) (posP b (n + 1) (hi (mkP x y)))
              (posP b (n + 1) (lo z)) (posP b (n + 1) (hi z)) ∧
            ¬ Cross (posP b (n + 1) (lo z)) (posP b (n + 1) (hi z))
              (posP b (n + 1) (lo (mkP x y))) (posP b (n + 1) (hi (mkP x y))) := by
          intro z hz h1 h2 h3 h4
          rw [lo_mkP] at h3 ⊢; rw [hi_mkP] at h4 ⊢
          have hxb : x ≤ b := by omega
          have hyb : y ≤ b := by omega
          have e1 := rest_ends z hz _ (Or.inl rfl) h1
          have e2 := rest_ends z hz _ (Or.inr rfl) h2
          obtain ⟨sp, sp1, sp2⟩ := shift _ h1 e1.1 e1.2
          obtain ⟨sq, sq1, sq2⟩ := shift _ h2 e2.1 e2.2
          obtain ⟨X0, hX0, nX⟩ := new_end z hz h1 h2 x hxm hxb
          obtain ⟨Y0, hY0, nY⟩ := new_end z hz h1 h2 y hym hyb
          have key := cross_new ⟨sp1, sp2⟩ ⟨sq1, sq2⟩ ⟨hX0, nX⟩ ⟨hY0, nY⟩
          rw [← sp, ← sq] at key
          rcases le_total x y with hle | hle
          · rw [min_eq_left hle, max_eq_right hle]; exact key
          · rw [min_eq_right hle, max_eq_left hle, cross_swap, @cross_swap' _ _ (posP b (n + 1) y)]
            exact key
        intro z hz z' hz' hne h1 h2 h3 h4
        rcases (mem_insSorted _ _ _).mp hz with rfl | hz <;>
          rcases (mem_insSorted _ _ _).mp hz' with rfl | hz'
        · exact absurd rfl hne
        · exact (newp z' hz' h3 h4 h1 h2).1
        · exact (newp z hz h1 h2 h3 h4).2
        · exact rest_rest z hz z' hz' hne h1 h2 h3 h4
  · cases ho

/-- **Pieces of every reached state do not cross.** -/
theorem fold_NC {tm : List ((ℕ × ℕ) × ℕ)}
    (htm : ∀ y : Coord, y.1 < a → y.2 < b → termAt tm y = endCol J y) :
    ∀ n, n ≤ a * b → ∀ s ∈ (List.range n).foldl (stageF a b tm) [([], 0)], NC b n s.1 := by
  intro n
  induction n with
  | zero =>
    intro _ s hs; rw [List.mem_singleton.mp hs]
    intro z hz; simp at hz
  | succ n ih =>
    intro hn s hs
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hs
    unfold stageF stage at hs
    rw [List.mem_filter, mem_normS, List.mem_flatMap] at hs
    obtain ⟨⟨s0, h0, h1⟩, -⟩ := hs
    exact step_NC htm (by omega) (fold_W htm n (by omega) s0 h0) (ih (by omega) s0 h0) h1

end

end ZZN.T

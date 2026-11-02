-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Timed.Thin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range

/-!
# How many DP states there can be

After the exit filter, every end of every piece is a plug code `≤ b` or the endpoint code of a
colour (`termE a b 0` or `termE a b 1`). Compressing such an end to a number `< b + 3`, a piece to
a number `< Q b = (b + 3)²`, and a state (a duplicate-free list of pieces and a colour mask `< 4`)
to a number `< Nst b = 4 (Q b + 1) ^ Q b`, is injective. So a duplicate-free list of such states
has at most `Nst b` entries (`card_good`). The bound depends on the short side `b` only.
-/

namespace ZZN.T

open ZZN ZZN.Thin GridHam

/-- An admissible end code: a plug code `≤ b`, or the endpoint code of colour 0 or 1. -/
def GoodEnd (a b e : ℕ) : Prop := e ≤ b ∨ e = termE a b 0 ∨ e = termE a b 1

/-- A state whose pieces are distinct and whose ends are admissible. -/
def Good (a b : ℕ) (s : St) : Prop :=
  s.1.Nodup ∧ s.2 < 4 ∧ ∀ z ∈ s.1, GoodEnd a b (lo z) ∧ GoodEnd a b (hi z)

def Q (b : ℕ) : ℕ := (b + 3) ^ 2

def Nst (b : ℕ) : ℕ := 4 * (Q b + 1) ^ Q b

/-- Compressed end code. -/
def cmpE (a b e : ℕ) : ℕ := if e ≤ b then e else b + 1 + colE a b e

lemma cmpE_lt {a b e : ℕ} (h : GoodEnd a b e) : cmpE a b e < b + 3 := by
  unfold GoodEnd termE at h; unfold cmpE colE
  rcases h with h | h | h <;> split_ifs <;> omega

lemma digit_inj {B x y x' y' : ℕ} (hy : y < B) (hy' : y' < B) (h : x * B + y = x' * B + y') :
    x = x' ∧ y = y' := by
  rcases lt_trichotomy x x' with hx | hx | hx
  · exfalso; have : (x + 1) * B ≤ x' * B := Nat.mul_le_mul_right _ hx; nlinarith
  · subst hx; omega
  · exfalso; have : (x' + 1) * B ≤ x * B := Nat.mul_le_mul_right _ hx; nlinarith

lemma cmpE_inj {a b e e' : ℕ} (h : GoodEnd a b e) (h' : GoodEnd a b e') (he : cmpE a b e = cmpE a b e') :
    e = e' := by
  unfold cmpE colE at he; unfold GoodEnd termE at h h'
  split_ifs at he <;> omega

/-- Compressed piece code. -/
def pcode (a b z : ℕ) : ℕ := cmpE a b (lo z) * (b + 3) + cmpE a b (hi z)

lemma pcode_lt {a b z : ℕ} (h1 : GoodEnd a b (lo z)) (h2 : GoodEnd a b (hi z)) : pcode a b z < Q b := by
  have := cmpE_lt h1; have := cmpE_lt h2
  unfold pcode Q
  nlinarith

lemma pcode_inj {a b z z' : ℕ} (h1 : GoodEnd a b (lo z)) (h2 : GoodEnd a b (hi z))
    (h1' : GoodEnd a b (lo z')) (h2' : GoodEnd a b (hi z')) (h : pcode a b z = pcode a b z') : z = z' := by
  unfold pcode at h
  obtain ⟨hd, hm⟩ := digit_inj (cmpE_lt h2) (cmpE_lt h2') h
  have e1 := cmpE_inj h1 h1' hd
  have e2 := cmpE_inj h2 h2' hm
  have : Nat.unpair z = Nat.unpair z' := Prod.ext e1 e2
  rw [← Nat.pair_unpair z, ← Nat.pair_unpair z', this]

/-- A list of numbers `< B` as one number, in base `B + 1` with digits shifted by one. -/
def lcode (B : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: l => (x + 1) + (B + 1) * lcode B l

lemma lcode_lt (B : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, x < B) → lcode B l < (B + 1) ^ l.length
  | [] => fun _ => by simp [lcode]
  | x :: l => fun h => by
    have ih := lcode_lt B l (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    simp only [lcode, List.length_cons, pow_succ]
    nlinarith

lemma lcode_inj (B : ℕ) : ∀ l l' : List ℕ, (∀ x ∈ l, x < B) → (∀ x ∈ l', x < B) →
    lcode B l = lcode B l' → l = l'
  | [], [], _, _, _ => rfl
  | [], x :: l', _, _, h => by simp [lcode] at h; omega
  | x :: l, [], _, _, h => by simp [lcode] at h
  | x :: l, y :: l', h1, h2, h => by
    have hx := h1 x (by simp); have hy := h2 y (by simp)
    simp only [lcode] at h
    have h' : lcode B l * (B + 1) + (x + 1) = lcode B l' * (B + 1) + (y + 1) := by
      rw [Nat.mul_comm (lcode B l), Nat.mul_comm (lcode B l')]; omega
    obtain ⟨hl, hxy⟩ := digit_inj (show x + 1 < B + 1 by omega) (show y + 1 < B + 1 by omega) h'
    have hxy' : x = y := by omega
    subst hxy'
    rw [lcode_inj B l l' (fun z hz => h1 z (by simp [hz])) (fun z hz => h2 z (by simp [hz])) hl]

lemma map_inj_on {α β : Type} (f : α → β) (P : α → Prop) (hf : ∀ x y, P x → P y → f x = f y → x = y) :
    ∀ l l' : List α, (∀ x ∈ l, P x) → (∀ x ∈ l', P x) → l.map f = l'.map f → l = l'
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: l, y :: l', h1, h2, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hf x y (h1 x (by simp)) (h2 y (by simp)) h.1,
      map_inj_on f P hf l l' (fun z hz => h1 z (by simp [hz])) (fun z hz => h2 z (by simp [hz])) h.2]

/-- A duplicate-free list of numbers below `B` has at most `B` entries. -/
lemma nodup_len_le (B : ℕ) (l : List ℕ) (hn : l.Nodup) (h : ∀ x ∈ l, x < B) : l.length ≤ B := by
  have : l.toFinset ⊆ Finset.range B := fun x hx => Finset.mem_range.2 (h x (List.mem_toFinset.1 hx))
  have := Finset.card_le_card this
  rw [List.toFinset_card_of_nodup hn, Finset.card_range] at this
  exact this

lemma good_len {a b : ℕ} {s : St} (hs : Good a b s) : s.1.length ≤ Q b := by
  obtain ⟨hn, -, he⟩ := hs
  have hmap : (s.1.map (pcode a b)).Nodup :=
    List.Nodup.map_on (fun x hx y hy h => pcode_inj (he x hx).1 (he x hx).2 (he y hy).1 (he y hy).2 h) hn
  have := nodup_len_le (Q b) _ hmap (fun x hx => by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
    exact pcode_lt (he z hz).1 (he z hz).2)
  simpa using this

/-- Code of a state. -/
def scode (a b : ℕ) (s : St) : ℕ := 4 * lcode (Q b) (s.1.map (pcode a b)) + s.2

lemma scode_lt {a b : ℕ} {s : St} (hs : Good a b s) : scode a b s < Nst b := by
  have hl := good_len hs
  obtain ⟨-, h4, he⟩ := hs
  have h1 := lcode_lt (Q b) (s.1.map (pcode a b)) (fun x hx => by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
    exact pcode_lt (he z hz).1 (he z hz).2)
  rw [List.length_map] at h1
  have h2 : (Q b + 1) ^ s.1.length ≤ (Q b + 1) ^ Q b := Nat.pow_le_pow_right (by omega) hl
  unfold scode Nst
  omega

lemma scode_inj {a b : ℕ} {s s' : St} (hs : Good a b s) (hs' : Good a b s')
    (h : scode a b s = scode a b s') : s = s' := by
  obtain ⟨-, h4, he⟩ := hs
  obtain ⟨-, h4', he'⟩ := hs'
  unfold scode at h
  have h2 : s.2 = s'.2 := by omega
  have hl : lcode (Q b) (s.1.map (pcode a b)) = lcode (Q b) (s'.1.map (pcode a b)) := by omega
  have hl2 := lcode_inj (Q b) _ _
    (fun x hx => by obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx; exact pcode_lt (he z hz).1 (he z hz).2)
    (fun x hx => by obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx; exact pcode_lt (he' z hz).1 (he' z hz).2) hl
  have := map_inj_on (pcode a b) (fun z => GoodEnd a b (lo z) ∧ GoodEnd a b (hi z))
    (fun x y hx hy hxy => pcode_inj hx.1 hx.2 hy.1 hy.2 hxy) s.1 s'.1 he he' hl2
  exact Prod.ext this h2

/-- **A duplicate-free list of good states has at most `Nst b` entries.** -/
theorem card_good {a b : ℕ} (S : List St) (hn : S.Nodup) (hg : ∀ s ∈ S, Good a b s) :
    S.length ≤ Nst b := by
  have hmap : (S.map (scode a b)).Nodup :=
    List.Nodup.map_on (fun x hx y hy h => scode_inj (hg x hx) (hg y hy) h) hn
  have := nodup_len_le (Nst b) _ hmap (fun x hx => by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
    exact scode_lt (hg s hs))
  simpa using this

end ZZN.T

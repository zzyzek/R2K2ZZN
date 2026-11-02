-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.WinK.Shared

/-!
# Step checks without the decode round trip

`stepOK` re-decodes the code of every successor and compares it with the successor. Decoding
undoes encoding for every state whose piece codes lie in `1 … 1023`, with at most 32 pieces and a
done mask below 4 (`dec_enc`), so `stepOKW` checks those bounds in place of the round trip.
-/

namespace ZZN.WinK

open ZZN ZZN.Win

/-- Piece codes in `1 … 1023`. -/
def wfP : List ℕ → Bool
  | [] => true
  | p :: ps => (decide (0 < p) && decide (p < 1024)) && wfP ps

def wfS (s : St) : Bool := decide (s.2 < 4) && decide (s.1.length ≤ 32) && wfP s.1

theorem decP_encP : ∀ (ps : List ℕ) (f : ℕ), wfP ps = true → ps.length ≤ f → decP f (encP ps) = ps
  | [], 0, _, _ => rfl
  | [], f + 1, _, _ => by simp [decP, encP]
  | p :: ps, f, h, hl => by
    simp only [wfP, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h0, h1⟩, h2⟩ := h
    obtain ⟨k, rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by simp at hl; omega⟩
    simp only [List.length_cons, Nat.add_le_add_iff_right] at hl
    have hm : (p + 1024 * encP ps) % 1024 = p := by omega
    have hd : (p + 1024 * encP ps) / 1024 = encP ps := by omega
    have hne : encP (p :: ps) ≠ 0 := by simp only [encP]; omega
    have he : encP (p :: ps) = p + 1024 * encP ps := rfl
    unfold decP
    simp only [hne, ↓reduceIte]
    rw [he, hm, hd, decP_encP ps k h2 hl]

theorem dec_enc {s : St} (h : wfS s = true) : dec (enc s) = s := by
  obtain ⟨ps, dn⟩ := s
  simp only [wfS, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [dec, enc]
  have e1 : (dn + 4 * encP ps) / 4 = encP ps := by omega
  have e2 : (dn + 4 * encP ps) % 4 = dn := by omega
  rw [e1, e2, decP_encP ps 32 h3 h2]

/-- `stepOK` with the bound test in place of the decode round trip. -/
def stepOKW (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (i : ℕ) (arr n : ℕ) (L : KSet) (firsts nb : ℕ) :
    Bool :=
  (List.range n).all fun k =>
    (stepCell a b (termAt tm (cell b i)) (cell b i).1 (cell b i).2 (dec (getW arr k))).all fun s' =>
      wfS s' && memL L (pick firsts nb (enc s')) (enc s')

theorem stepOKW_le {a b : ℕ} {tm : List ((ℕ × ℕ) × ℕ)} {i arr n : ℕ} {L : KSet} {firsts nb : ℕ}
    (h : stepOKW a b tm i arr n L firsts nb = true) : stepOK a b tm i arr n L firsts nb = true := by
  unfold stepOKW at h
  unfold stepOK
  rw [List.all_eq_true] at h ⊢
  intro k hk
  have h1 := List.all_eq_true.mp (h k hk)
  rw [List.all_eq_true]
  intro s' hs'
  have h2 := h1 s' hs'
  simp only [Bool.and_eq_true] at h2 ⊢
  exact ⟨by rw [dec_enc h2.1]; simp, h2.2⟩

end ZZN.WinK

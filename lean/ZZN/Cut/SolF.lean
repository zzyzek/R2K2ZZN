-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Solve

/-!
# Explicit solutions, checked in linear time

`solF I p q` checks a pair of paths like `solB`, with the duplicate and bounds tests done by one
walk over `p ++ q` that marks each cell in a bitmask (`maskOK`), in place of the quadratic
`List.Nodup` test. `solvable_of_solF`.
-/

namespace ZZN

open GridHam

/-- The walk over `l` from mask `m`: every cell in bounds and not yet marked. -/
def maskOK (w h : ℕ) : ℕ → List Coord → Bool
  | _, [] => true
  | m, v :: vs =>
    decide (v.1 < w) && decide (v.2 < h) && !m.testBit (v.1 * h + v.2) &&
      maskOK w h (m ||| 2 ^ (v.1 * h + v.2)) vs

theorem maskOK_spec {w h : ℕ} : ∀ (m : ℕ) (l : List Coord), maskOK w h m l = true →
    l.Nodup ∧ (∀ v ∈ l, InBounds w h v) ∧ ∀ v ∈ l, m.testBit (v.1 * h + v.2) = false
  | _, [], _ => by simp
  | m, v :: vs, hok => by
    simp only [maskOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hok
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hok
    obtain ⟨n, b, f⟩ := maskOK_spec _ vs h4
    have key : ∀ u ∈ vs, u ≠ v ∧ m.testBit (u.1 * h + u.2) = false := by
      intro u hu
      have hf := f u hu
      rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hf
      refine ⟨fun e => hf.2 (by rw [e]), hf.1⟩
    refine ⟨List.nodup_cons.mpr ⟨fun hv => (key v hv).1 rfl, n⟩, ?_, ?_⟩
    · intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ⟨h1, h2⟩
      · exact b u hu
    · intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact h3
      · exact (key u hu).2

/-- `p, q` solve `I`, checked in linear time. -/
def solF (I : Inst) (p q : List Coord) : Bool :=
  (p.head? == some I.s0) && (p.getLast? == some I.t0) && chainAdjacent p &&
    (q.head? == some I.s1) && (q.getLast? == some I.t1) && chainAdjacent q &&
    maskOK I.w I.h 0 (p ++ q) && (p.length + q.length == I.w * I.h)

theorem solF_sound {I : Inst} {p q : List Coord} (hs : solF I p q = true) : IsSolution I p q := by
  simp only [solF, Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨hp1, hp2⟩, hp3⟩, hq1⟩, hq2⟩, hq3⟩, hm⟩, hl⟩ := hs
  obtain ⟨hn, hb, -⟩ := maskOK_spec 0 (p ++ q) hm
  have hpn : p.Nodup := (List.nodup_append.mp hn).1
  have hqn : q.Nodup := (List.nodup_append.mp hn).2.1
  have hpb : ∀ v ∈ p, InBounds I.w I.h v := fun v hv => hb v (List.mem_append_left _ hv)
  have hqb : ∀ v ∈ q, InBounds I.w I.h v := fun v hv => hb v (List.mem_append_right _ hv)
  refine ⟨⟨hp1, hp2, hpn, hpb, hp3⟩, ⟨hq1, hq2, hqn, hqb, hq3⟩, fun v hv hv' => ?_, fun v hv => ?_⟩
  · exact (List.nodup_append.mp hn).2.2 v hv v hv' rfl
  · have := cover_of_card hn hb (by rw [List.length_append]; exact hl) hv
    exact List.mem_append.mp this

theorem solvable_of_solF {I : Inst} {p q : List Coord} (h : solF I p q = true) : Solvable I :=
  ⟨p, q, solF_sound h⟩

/-- A path packed one cell per byte, `16 * row + column`, first cell lowest: `n` cells of `code`. -/
def decPath (n code : ℕ) : List Coord :=
  (List.range n).map fun k => let b := code / 256 ^ k % 256; (b / 16, b % 16)

end ZZN

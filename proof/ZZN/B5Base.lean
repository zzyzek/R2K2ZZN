/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.B5R

@[expose] public section

/-!
# Base sizes for `b5_all`

Sides 11–14 (even area), every frame: R fires on every match of a `b5q` entry with the fourth
cell on the perimeter outside the window. One theorem per frame and size (12 sizes, 8 frames),
each checked by `decide +kernel`; `b5_base` collects them.
-/

namespace ZZN.Win

open GridHam

/-- The cells of an `H × W` grid. -/
def cellsHW (H W : ℕ) : List Coord := (List.range H).flatMap fun r => (List.range W).map fun c => (r, c)

theorem mem_cellsHW {H W : ℕ} {x : Coord} (h1 : x.1 < H) (h2 : x.2 < W) : x ∈ cellsHW H W := by
  simp only [cellsHW, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨x.1, h1, x.2, h2, rfl⟩

theorem b5b_fff_11_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 11 12 ⟨false, false, false⟩) (Frame.W 11 12 ⟨false, false, false⟩),
    perimOut (Frame.H 11 12 ⟨false, false, false⟩) (Frame.W 11 12 ⟨false, false, false⟩) x = true →
      effAlt3 11 12 (b5pts ⟨false, false, false⟩ 11 12 e x) = true := by
  decide +kernel

theorem b5b_fft_11_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 11 12 ⟨false, false, true⟩) (Frame.W 11 12 ⟨false, false, true⟩),
    perimOut (Frame.H 11 12 ⟨false, false, true⟩) (Frame.W 11 12 ⟨false, false, true⟩) x = true →
      effAlt3 11 12 (b5pts ⟨false, false, true⟩ 11 12 e x) = true := by
  decide +kernel

theorem b5b_ftf_11_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 11 12 ⟨false, true, false⟩) (Frame.W 11 12 ⟨false, true, false⟩),
    perimOut (Frame.H 11 12 ⟨false, true, false⟩) (Frame.W 11 12 ⟨false, true, false⟩) x = true →
      effAlt3 11 12 (b5pts ⟨false, true, false⟩ 11 12 e x) = true := by
  decide +kernel

theorem b5b_ftt_11_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 11 12 ⟨false, true, true⟩) (Frame.W 11 12 ⟨false, true, true⟩),
    perimOut (Frame.H 11 12 ⟨false, true, true⟩) (Frame.W 11 12 ⟨false, true, true⟩) x = true →
      effAlt3 11 12 (b5pts ⟨false, true, true⟩ 11 12 e x) = true := by
  decide +kernel

theorem b5b_tff_11_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 11 12 ⟨true, false, false⟩) (Frame.W 11 12 ⟨true, false, false⟩),
    perimOut (Frame.H 11 12 ⟨true, false, false⟩) (Frame.W 11 12 ⟨true, false, false⟩) x = true →
      effAlt3 11 12 (b5pts ⟨true, false, false⟩ 11 12 e x) = true := by
  decide +kernel

theorem b5b_tft_11_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 11 12 ⟨true, false, true⟩) (Frame.W 11 12 ⟨true, false, true⟩),
    perimOut (Frame.H 11 12 ⟨true, false, true⟩) (Frame.W 11 12 ⟨true, false, true⟩) x = true →
      effAlt3 11 12 (b5pts ⟨true, false, true⟩ 11 12 e x) = true := by
  decide +kernel

theorem b5b_ttf_11_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 11 12 ⟨true, true, false⟩) (Frame.W 11 12 ⟨true, true, false⟩),
    perimOut (Frame.H 11 12 ⟨true, true, false⟩) (Frame.W 11 12 ⟨true, true, false⟩) x = true →
      effAlt3 11 12 (b5pts ⟨true, true, false⟩ 11 12 e x) = true := by
  decide +kernel

theorem b5b_ttt_11_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 11 12 ⟨true, true, true⟩) (Frame.W 11 12 ⟨true, true, true⟩),
    perimOut (Frame.H 11 12 ⟨true, true, true⟩) (Frame.W 11 12 ⟨true, true, true⟩) x = true →
      effAlt3 11 12 (b5pts ⟨true, true, true⟩ 11 12 e x) = true := by
  decide +kernel

theorem b5b_fff_11_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 11 14 ⟨false, false, false⟩) (Frame.W 11 14 ⟨false, false, false⟩),
    perimOut (Frame.H 11 14 ⟨false, false, false⟩) (Frame.W 11 14 ⟨false, false, false⟩) x = true →
      effAlt3 11 14 (b5pts ⟨false, false, false⟩ 11 14 e x) = true := by
  decide +kernel

theorem b5b_fft_11_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 11 14 ⟨false, false, true⟩) (Frame.W 11 14 ⟨false, false, true⟩),
    perimOut (Frame.H 11 14 ⟨false, false, true⟩) (Frame.W 11 14 ⟨false, false, true⟩) x = true →
      effAlt3 11 14 (b5pts ⟨false, false, true⟩ 11 14 e x) = true := by
  decide +kernel

theorem b5b_ftf_11_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 11 14 ⟨false, true, false⟩) (Frame.W 11 14 ⟨false, true, false⟩),
    perimOut (Frame.H 11 14 ⟨false, true, false⟩) (Frame.W 11 14 ⟨false, true, false⟩) x = true →
      effAlt3 11 14 (b5pts ⟨false, true, false⟩ 11 14 e x) = true := by
  decide +kernel

theorem b5b_ftt_11_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 11 14 ⟨false, true, true⟩) (Frame.W 11 14 ⟨false, true, true⟩),
    perimOut (Frame.H 11 14 ⟨false, true, true⟩) (Frame.W 11 14 ⟨false, true, true⟩) x = true →
      effAlt3 11 14 (b5pts ⟨false, true, true⟩ 11 14 e x) = true := by
  decide +kernel

theorem b5b_tff_11_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 11 14 ⟨true, false, false⟩) (Frame.W 11 14 ⟨true, false, false⟩),
    perimOut (Frame.H 11 14 ⟨true, false, false⟩) (Frame.W 11 14 ⟨true, false, false⟩) x = true →
      effAlt3 11 14 (b5pts ⟨true, false, false⟩ 11 14 e x) = true := by
  decide +kernel

theorem b5b_tft_11_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 11 14 ⟨true, false, true⟩) (Frame.W 11 14 ⟨true, false, true⟩),
    perimOut (Frame.H 11 14 ⟨true, false, true⟩) (Frame.W 11 14 ⟨true, false, true⟩) x = true →
      effAlt3 11 14 (b5pts ⟨true, false, true⟩ 11 14 e x) = true := by
  decide +kernel

theorem b5b_ttf_11_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 11 14 ⟨true, true, false⟩) (Frame.W 11 14 ⟨true, true, false⟩),
    perimOut (Frame.H 11 14 ⟨true, true, false⟩) (Frame.W 11 14 ⟨true, true, false⟩) x = true →
      effAlt3 11 14 (b5pts ⟨true, true, false⟩ 11 14 e x) = true := by
  decide +kernel

theorem b5b_ttt_11_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 11 14 ⟨true, true, true⟩) (Frame.W 11 14 ⟨true, true, true⟩),
    perimOut (Frame.H 11 14 ⟨true, true, true⟩) (Frame.W 11 14 ⟨true, true, true⟩) x = true →
      effAlt3 11 14 (b5pts ⟨true, true, true⟩ 11 14 e x) = true := by
  decide +kernel

theorem b5b_fff_12_11 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 11 ⟨false, false, false⟩) (Frame.W 12 11 ⟨false, false, false⟩),
    perimOut (Frame.H 12 11 ⟨false, false, false⟩) (Frame.W 12 11 ⟨false, false, false⟩) x = true →
      effAlt3 12 11 (b5pts ⟨false, false, false⟩ 12 11 e x) = true := by
  decide +kernel

theorem b5b_fft_12_11 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 11 ⟨false, false, true⟩) (Frame.W 12 11 ⟨false, false, true⟩),
    perimOut (Frame.H 12 11 ⟨false, false, true⟩) (Frame.W 12 11 ⟨false, false, true⟩) x = true →
      effAlt3 12 11 (b5pts ⟨false, false, true⟩ 12 11 e x) = true := by
  decide +kernel

theorem b5b_ftf_12_11 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 11 ⟨false, true, false⟩) (Frame.W 12 11 ⟨false, true, false⟩),
    perimOut (Frame.H 12 11 ⟨false, true, false⟩) (Frame.W 12 11 ⟨false, true, false⟩) x = true →
      effAlt3 12 11 (b5pts ⟨false, true, false⟩ 12 11 e x) = true := by
  decide +kernel

theorem b5b_ftt_12_11 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 11 ⟨false, true, true⟩) (Frame.W 12 11 ⟨false, true, true⟩),
    perimOut (Frame.H 12 11 ⟨false, true, true⟩) (Frame.W 12 11 ⟨false, true, true⟩) x = true →
      effAlt3 12 11 (b5pts ⟨false, true, true⟩ 12 11 e x) = true := by
  decide +kernel

theorem b5b_tff_12_11 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 11 ⟨true, false, false⟩) (Frame.W 12 11 ⟨true, false, false⟩),
    perimOut (Frame.H 12 11 ⟨true, false, false⟩) (Frame.W 12 11 ⟨true, false, false⟩) x = true →
      effAlt3 12 11 (b5pts ⟨true, false, false⟩ 12 11 e x) = true := by
  decide +kernel

theorem b5b_tft_12_11 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 11 ⟨true, false, true⟩) (Frame.W 12 11 ⟨true, false, true⟩),
    perimOut (Frame.H 12 11 ⟨true, false, true⟩) (Frame.W 12 11 ⟨true, false, true⟩) x = true →
      effAlt3 12 11 (b5pts ⟨true, false, true⟩ 12 11 e x) = true := by
  decide +kernel

theorem b5b_ttf_12_11 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 11 ⟨true, true, false⟩) (Frame.W 12 11 ⟨true, true, false⟩),
    perimOut (Frame.H 12 11 ⟨true, true, false⟩) (Frame.W 12 11 ⟨true, true, false⟩) x = true →
      effAlt3 12 11 (b5pts ⟨true, true, false⟩ 12 11 e x) = true := by
  decide +kernel

theorem b5b_ttt_12_11 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 11 ⟨true, true, true⟩) (Frame.W 12 11 ⟨true, true, true⟩),
    perimOut (Frame.H 12 11 ⟨true, true, true⟩) (Frame.W 12 11 ⟨true, true, true⟩) x = true →
      effAlt3 12 11 (b5pts ⟨true, true, true⟩ 12 11 e x) = true := by
  decide +kernel

theorem b5b_fff_12_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 12 ⟨false, false, false⟩) (Frame.W 12 12 ⟨false, false, false⟩),
    perimOut (Frame.H 12 12 ⟨false, false, false⟩) (Frame.W 12 12 ⟨false, false, false⟩) x = true →
      effAlt3 12 12 (b5pts ⟨false, false, false⟩ 12 12 e x) = true := by
  decide +kernel

theorem b5b_fft_12_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 12 ⟨false, false, true⟩) (Frame.W 12 12 ⟨false, false, true⟩),
    perimOut (Frame.H 12 12 ⟨false, false, true⟩) (Frame.W 12 12 ⟨false, false, true⟩) x = true →
      effAlt3 12 12 (b5pts ⟨false, false, true⟩ 12 12 e x) = true := by
  decide +kernel

theorem b5b_ftf_12_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 12 ⟨false, true, false⟩) (Frame.W 12 12 ⟨false, true, false⟩),
    perimOut (Frame.H 12 12 ⟨false, true, false⟩) (Frame.W 12 12 ⟨false, true, false⟩) x = true →
      effAlt3 12 12 (b5pts ⟨false, true, false⟩ 12 12 e x) = true := by
  decide +kernel

theorem b5b_ftt_12_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 12 ⟨false, true, true⟩) (Frame.W 12 12 ⟨false, true, true⟩),
    perimOut (Frame.H 12 12 ⟨false, true, true⟩) (Frame.W 12 12 ⟨false, true, true⟩) x = true →
      effAlt3 12 12 (b5pts ⟨false, true, true⟩ 12 12 e x) = true := by
  decide +kernel

theorem b5b_tff_12_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 12 ⟨true, false, false⟩) (Frame.W 12 12 ⟨true, false, false⟩),
    perimOut (Frame.H 12 12 ⟨true, false, false⟩) (Frame.W 12 12 ⟨true, false, false⟩) x = true →
      effAlt3 12 12 (b5pts ⟨true, false, false⟩ 12 12 e x) = true := by
  decide +kernel

theorem b5b_tft_12_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 12 ⟨true, false, true⟩) (Frame.W 12 12 ⟨true, false, true⟩),
    perimOut (Frame.H 12 12 ⟨true, false, true⟩) (Frame.W 12 12 ⟨true, false, true⟩) x = true →
      effAlt3 12 12 (b5pts ⟨true, false, true⟩ 12 12 e x) = true := by
  decide +kernel

theorem b5b_ttf_12_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 12 ⟨true, true, false⟩) (Frame.W 12 12 ⟨true, true, false⟩),
    perimOut (Frame.H 12 12 ⟨true, true, false⟩) (Frame.W 12 12 ⟨true, true, false⟩) x = true →
      effAlt3 12 12 (b5pts ⟨true, true, false⟩ 12 12 e x) = true := by
  decide +kernel

theorem b5b_ttt_12_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 12 ⟨true, true, true⟩) (Frame.W 12 12 ⟨true, true, true⟩),
    perimOut (Frame.H 12 12 ⟨true, true, true⟩) (Frame.W 12 12 ⟨true, true, true⟩) x = true →
      effAlt3 12 12 (b5pts ⟨true, true, true⟩ 12 12 e x) = true := by
  decide +kernel

theorem b5b_fff_12_13 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 13 ⟨false, false, false⟩) (Frame.W 12 13 ⟨false, false, false⟩),
    perimOut (Frame.H 12 13 ⟨false, false, false⟩) (Frame.W 12 13 ⟨false, false, false⟩) x = true →
      effAlt3 12 13 (b5pts ⟨false, false, false⟩ 12 13 e x) = true := by
  decide +kernel

theorem b5b_fft_12_13 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 13 ⟨false, false, true⟩) (Frame.W 12 13 ⟨false, false, true⟩),
    perimOut (Frame.H 12 13 ⟨false, false, true⟩) (Frame.W 12 13 ⟨false, false, true⟩) x = true →
      effAlt3 12 13 (b5pts ⟨false, false, true⟩ 12 13 e x) = true := by
  decide +kernel

theorem b5b_ftf_12_13 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 13 ⟨false, true, false⟩) (Frame.W 12 13 ⟨false, true, false⟩),
    perimOut (Frame.H 12 13 ⟨false, true, false⟩) (Frame.W 12 13 ⟨false, true, false⟩) x = true →
      effAlt3 12 13 (b5pts ⟨false, true, false⟩ 12 13 e x) = true := by
  decide +kernel

theorem b5b_ftt_12_13 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 13 ⟨false, true, true⟩) (Frame.W 12 13 ⟨false, true, true⟩),
    perimOut (Frame.H 12 13 ⟨false, true, true⟩) (Frame.W 12 13 ⟨false, true, true⟩) x = true →
      effAlt3 12 13 (b5pts ⟨false, true, true⟩ 12 13 e x) = true := by
  decide +kernel

theorem b5b_tff_12_13 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 13 ⟨true, false, false⟩) (Frame.W 12 13 ⟨true, false, false⟩),
    perimOut (Frame.H 12 13 ⟨true, false, false⟩) (Frame.W 12 13 ⟨true, false, false⟩) x = true →
      effAlt3 12 13 (b5pts ⟨true, false, false⟩ 12 13 e x) = true := by
  decide +kernel

theorem b5b_tft_12_13 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 13 ⟨true, false, true⟩) (Frame.W 12 13 ⟨true, false, true⟩),
    perimOut (Frame.H 12 13 ⟨true, false, true⟩) (Frame.W 12 13 ⟨true, false, true⟩) x = true →
      effAlt3 12 13 (b5pts ⟨true, false, true⟩ 12 13 e x) = true := by
  decide +kernel

theorem b5b_ttf_12_13 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 13 ⟨true, true, false⟩) (Frame.W 12 13 ⟨true, true, false⟩),
    perimOut (Frame.H 12 13 ⟨true, true, false⟩) (Frame.W 12 13 ⟨true, true, false⟩) x = true →
      effAlt3 12 13 (b5pts ⟨true, true, false⟩ 12 13 e x) = true := by
  decide +kernel

theorem b5b_ttt_12_13 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 13 ⟨true, true, true⟩) (Frame.W 12 13 ⟨true, true, true⟩),
    perimOut (Frame.H 12 13 ⟨true, true, true⟩) (Frame.W 12 13 ⟨true, true, true⟩) x = true →
      effAlt3 12 13 (b5pts ⟨true, true, true⟩ 12 13 e x) = true := by
  decide +kernel

theorem b5b_fff_12_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 14 ⟨false, false, false⟩) (Frame.W 12 14 ⟨false, false, false⟩),
    perimOut (Frame.H 12 14 ⟨false, false, false⟩) (Frame.W 12 14 ⟨false, false, false⟩) x = true →
      effAlt3 12 14 (b5pts ⟨false, false, false⟩ 12 14 e x) = true := by
  decide +kernel

theorem b5b_fft_12_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 14 ⟨false, false, true⟩) (Frame.W 12 14 ⟨false, false, true⟩),
    perimOut (Frame.H 12 14 ⟨false, false, true⟩) (Frame.W 12 14 ⟨false, false, true⟩) x = true →
      effAlt3 12 14 (b5pts ⟨false, false, true⟩ 12 14 e x) = true := by
  decide +kernel

theorem b5b_ftf_12_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 14 ⟨false, true, false⟩) (Frame.W 12 14 ⟨false, true, false⟩),
    perimOut (Frame.H 12 14 ⟨false, true, false⟩) (Frame.W 12 14 ⟨false, true, false⟩) x = true →
      effAlt3 12 14 (b5pts ⟨false, true, false⟩ 12 14 e x) = true := by
  decide +kernel

theorem b5b_ftt_12_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 14 ⟨false, true, true⟩) (Frame.W 12 14 ⟨false, true, true⟩),
    perimOut (Frame.H 12 14 ⟨false, true, true⟩) (Frame.W 12 14 ⟨false, true, true⟩) x = true →
      effAlt3 12 14 (b5pts ⟨false, true, true⟩ 12 14 e x) = true := by
  decide +kernel

theorem b5b_tff_12_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 14 ⟨true, false, false⟩) (Frame.W 12 14 ⟨true, false, false⟩),
    perimOut (Frame.H 12 14 ⟨true, false, false⟩) (Frame.W 12 14 ⟨true, false, false⟩) x = true →
      effAlt3 12 14 (b5pts ⟨true, false, false⟩ 12 14 e x) = true := by
  decide +kernel

theorem b5b_tft_12_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 14 ⟨true, false, true⟩) (Frame.W 12 14 ⟨true, false, true⟩),
    perimOut (Frame.H 12 14 ⟨true, false, true⟩) (Frame.W 12 14 ⟨true, false, true⟩) x = true →
      effAlt3 12 14 (b5pts ⟨true, false, true⟩ 12 14 e x) = true := by
  decide +kernel

theorem b5b_ttf_12_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 14 ⟨true, true, false⟩) (Frame.W 12 14 ⟨true, true, false⟩),
    perimOut (Frame.H 12 14 ⟨true, true, false⟩) (Frame.W 12 14 ⟨true, true, false⟩) x = true →
      effAlt3 12 14 (b5pts ⟨true, true, false⟩ 12 14 e x) = true := by
  decide +kernel

theorem b5b_ttt_12_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 12 14 ⟨true, true, true⟩) (Frame.W 12 14 ⟨true, true, true⟩),
    perimOut (Frame.H 12 14 ⟨true, true, true⟩) (Frame.W 12 14 ⟨true, true, true⟩) x = true →
      effAlt3 12 14 (b5pts ⟨true, true, true⟩ 12 14 e x) = true := by
  decide +kernel

theorem b5b_fff_13_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 13 12 ⟨false, false, false⟩) (Frame.W 13 12 ⟨false, false, false⟩),
    perimOut (Frame.H 13 12 ⟨false, false, false⟩) (Frame.W 13 12 ⟨false, false, false⟩) x = true →
      effAlt3 13 12 (b5pts ⟨false, false, false⟩ 13 12 e x) = true := by
  decide +kernel

theorem b5b_fft_13_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 13 12 ⟨false, false, true⟩) (Frame.W 13 12 ⟨false, false, true⟩),
    perimOut (Frame.H 13 12 ⟨false, false, true⟩) (Frame.W 13 12 ⟨false, false, true⟩) x = true →
      effAlt3 13 12 (b5pts ⟨false, false, true⟩ 13 12 e x) = true := by
  decide +kernel

theorem b5b_ftf_13_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 13 12 ⟨false, true, false⟩) (Frame.W 13 12 ⟨false, true, false⟩),
    perimOut (Frame.H 13 12 ⟨false, true, false⟩) (Frame.W 13 12 ⟨false, true, false⟩) x = true →
      effAlt3 13 12 (b5pts ⟨false, true, false⟩ 13 12 e x) = true := by
  decide +kernel

theorem b5b_ftt_13_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 13 12 ⟨false, true, true⟩) (Frame.W 13 12 ⟨false, true, true⟩),
    perimOut (Frame.H 13 12 ⟨false, true, true⟩) (Frame.W 13 12 ⟨false, true, true⟩) x = true →
      effAlt3 13 12 (b5pts ⟨false, true, true⟩ 13 12 e x) = true := by
  decide +kernel

theorem b5b_tff_13_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 13 12 ⟨true, false, false⟩) (Frame.W 13 12 ⟨true, false, false⟩),
    perimOut (Frame.H 13 12 ⟨true, false, false⟩) (Frame.W 13 12 ⟨true, false, false⟩) x = true →
      effAlt3 13 12 (b5pts ⟨true, false, false⟩ 13 12 e x) = true := by
  decide +kernel

theorem b5b_tft_13_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 13 12 ⟨true, false, true⟩) (Frame.W 13 12 ⟨true, false, true⟩),
    perimOut (Frame.H 13 12 ⟨true, false, true⟩) (Frame.W 13 12 ⟨true, false, true⟩) x = true →
      effAlt3 13 12 (b5pts ⟨true, false, true⟩ 13 12 e x) = true := by
  decide +kernel

theorem b5b_ttf_13_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 13 12 ⟨true, true, false⟩) (Frame.W 13 12 ⟨true, true, false⟩),
    perimOut (Frame.H 13 12 ⟨true, true, false⟩) (Frame.W 13 12 ⟨true, true, false⟩) x = true →
      effAlt3 13 12 (b5pts ⟨true, true, false⟩ 13 12 e x) = true := by
  decide +kernel

theorem b5b_ttt_13_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 13 12 ⟨true, true, true⟩) (Frame.W 13 12 ⟨true, true, true⟩),
    perimOut (Frame.H 13 12 ⟨true, true, true⟩) (Frame.W 13 12 ⟨true, true, true⟩) x = true →
      effAlt3 13 12 (b5pts ⟨true, true, true⟩ 13 12 e x) = true := by
  decide +kernel

theorem b5b_fff_13_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 13 14 ⟨false, false, false⟩) (Frame.W 13 14 ⟨false, false, false⟩),
    perimOut (Frame.H 13 14 ⟨false, false, false⟩) (Frame.W 13 14 ⟨false, false, false⟩) x = true →
      effAlt3 13 14 (b5pts ⟨false, false, false⟩ 13 14 e x) = true := by
  decide +kernel

theorem b5b_fft_13_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 13 14 ⟨false, false, true⟩) (Frame.W 13 14 ⟨false, false, true⟩),
    perimOut (Frame.H 13 14 ⟨false, false, true⟩) (Frame.W 13 14 ⟨false, false, true⟩) x = true →
      effAlt3 13 14 (b5pts ⟨false, false, true⟩ 13 14 e x) = true := by
  decide +kernel

theorem b5b_ftf_13_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 13 14 ⟨false, true, false⟩) (Frame.W 13 14 ⟨false, true, false⟩),
    perimOut (Frame.H 13 14 ⟨false, true, false⟩) (Frame.W 13 14 ⟨false, true, false⟩) x = true →
      effAlt3 13 14 (b5pts ⟨false, true, false⟩ 13 14 e x) = true := by
  decide +kernel

theorem b5b_ftt_13_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 13 14 ⟨false, true, true⟩) (Frame.W 13 14 ⟨false, true, true⟩),
    perimOut (Frame.H 13 14 ⟨false, true, true⟩) (Frame.W 13 14 ⟨false, true, true⟩) x = true →
      effAlt3 13 14 (b5pts ⟨false, true, true⟩ 13 14 e x) = true := by
  decide +kernel

theorem b5b_tff_13_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 13 14 ⟨true, false, false⟩) (Frame.W 13 14 ⟨true, false, false⟩),
    perimOut (Frame.H 13 14 ⟨true, false, false⟩) (Frame.W 13 14 ⟨true, false, false⟩) x = true →
      effAlt3 13 14 (b5pts ⟨true, false, false⟩ 13 14 e x) = true := by
  decide +kernel

theorem b5b_tft_13_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 13 14 ⟨true, false, true⟩) (Frame.W 13 14 ⟨true, false, true⟩),
    perimOut (Frame.H 13 14 ⟨true, false, true⟩) (Frame.W 13 14 ⟨true, false, true⟩) x = true →
      effAlt3 13 14 (b5pts ⟨true, false, true⟩ 13 14 e x) = true := by
  decide +kernel

theorem b5b_ttf_13_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 13 14 ⟨true, true, false⟩) (Frame.W 13 14 ⟨true, true, false⟩),
    perimOut (Frame.H 13 14 ⟨true, true, false⟩) (Frame.W 13 14 ⟨true, true, false⟩) x = true →
      effAlt3 13 14 (b5pts ⟨true, true, false⟩ 13 14 e x) = true := by
  decide +kernel

theorem b5b_ttt_13_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 13 14 ⟨true, true, true⟩) (Frame.W 13 14 ⟨true, true, true⟩),
    perimOut (Frame.H 13 14 ⟨true, true, true⟩) (Frame.W 13 14 ⟨true, true, true⟩) x = true →
      effAlt3 13 14 (b5pts ⟨true, true, true⟩ 13 14 e x) = true := by
  decide +kernel

theorem b5b_fff_14_11 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 11 ⟨false, false, false⟩) (Frame.W 14 11 ⟨false, false, false⟩),
    perimOut (Frame.H 14 11 ⟨false, false, false⟩) (Frame.W 14 11 ⟨false, false, false⟩) x = true →
      effAlt3 14 11 (b5pts ⟨false, false, false⟩ 14 11 e x) = true := by
  decide +kernel

theorem b5b_fft_14_11 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 11 ⟨false, false, true⟩) (Frame.W 14 11 ⟨false, false, true⟩),
    perimOut (Frame.H 14 11 ⟨false, false, true⟩) (Frame.W 14 11 ⟨false, false, true⟩) x = true →
      effAlt3 14 11 (b5pts ⟨false, false, true⟩ 14 11 e x) = true := by
  decide +kernel

theorem b5b_ftf_14_11 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 11 ⟨false, true, false⟩) (Frame.W 14 11 ⟨false, true, false⟩),
    perimOut (Frame.H 14 11 ⟨false, true, false⟩) (Frame.W 14 11 ⟨false, true, false⟩) x = true →
      effAlt3 14 11 (b5pts ⟨false, true, false⟩ 14 11 e x) = true := by
  decide +kernel

theorem b5b_ftt_14_11 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 11 ⟨false, true, true⟩) (Frame.W 14 11 ⟨false, true, true⟩),
    perimOut (Frame.H 14 11 ⟨false, true, true⟩) (Frame.W 14 11 ⟨false, true, true⟩) x = true →
      effAlt3 14 11 (b5pts ⟨false, true, true⟩ 14 11 e x) = true := by
  decide +kernel

theorem b5b_tff_14_11 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 11 ⟨true, false, false⟩) (Frame.W 14 11 ⟨true, false, false⟩),
    perimOut (Frame.H 14 11 ⟨true, false, false⟩) (Frame.W 14 11 ⟨true, false, false⟩) x = true →
      effAlt3 14 11 (b5pts ⟨true, false, false⟩ 14 11 e x) = true := by
  decide +kernel

theorem b5b_tft_14_11 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 11 ⟨true, false, true⟩) (Frame.W 14 11 ⟨true, false, true⟩),
    perimOut (Frame.H 14 11 ⟨true, false, true⟩) (Frame.W 14 11 ⟨true, false, true⟩) x = true →
      effAlt3 14 11 (b5pts ⟨true, false, true⟩ 14 11 e x) = true := by
  decide +kernel

theorem b5b_ttf_14_11 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 11 ⟨true, true, false⟩) (Frame.W 14 11 ⟨true, true, false⟩),
    perimOut (Frame.H 14 11 ⟨true, true, false⟩) (Frame.W 14 11 ⟨true, true, false⟩) x = true →
      effAlt3 14 11 (b5pts ⟨true, true, false⟩ 14 11 e x) = true := by
  decide +kernel

theorem b5b_ttt_14_11 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 11 ⟨true, true, true⟩) (Frame.W 14 11 ⟨true, true, true⟩),
    perimOut (Frame.H 14 11 ⟨true, true, true⟩) (Frame.W 14 11 ⟨true, true, true⟩) x = true →
      effAlt3 14 11 (b5pts ⟨true, true, true⟩ 14 11 e x) = true := by
  decide +kernel

theorem b5b_fff_14_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 12 ⟨false, false, false⟩) (Frame.W 14 12 ⟨false, false, false⟩),
    perimOut (Frame.H 14 12 ⟨false, false, false⟩) (Frame.W 14 12 ⟨false, false, false⟩) x = true →
      effAlt3 14 12 (b5pts ⟨false, false, false⟩ 14 12 e x) = true := by
  decide +kernel

theorem b5b_fft_14_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 12 ⟨false, false, true⟩) (Frame.W 14 12 ⟨false, false, true⟩),
    perimOut (Frame.H 14 12 ⟨false, false, true⟩) (Frame.W 14 12 ⟨false, false, true⟩) x = true →
      effAlt3 14 12 (b5pts ⟨false, false, true⟩ 14 12 e x) = true := by
  decide +kernel

theorem b5b_ftf_14_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 12 ⟨false, true, false⟩) (Frame.W 14 12 ⟨false, true, false⟩),
    perimOut (Frame.H 14 12 ⟨false, true, false⟩) (Frame.W 14 12 ⟨false, true, false⟩) x = true →
      effAlt3 14 12 (b5pts ⟨false, true, false⟩ 14 12 e x) = true := by
  decide +kernel

theorem b5b_ftt_14_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 12 ⟨false, true, true⟩) (Frame.W 14 12 ⟨false, true, true⟩),
    perimOut (Frame.H 14 12 ⟨false, true, true⟩) (Frame.W 14 12 ⟨false, true, true⟩) x = true →
      effAlt3 14 12 (b5pts ⟨false, true, true⟩ 14 12 e x) = true := by
  decide +kernel

theorem b5b_tff_14_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 12 ⟨true, false, false⟩) (Frame.W 14 12 ⟨true, false, false⟩),
    perimOut (Frame.H 14 12 ⟨true, false, false⟩) (Frame.W 14 12 ⟨true, false, false⟩) x = true →
      effAlt3 14 12 (b5pts ⟨true, false, false⟩ 14 12 e x) = true := by
  decide +kernel

theorem b5b_tft_14_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 12 ⟨true, false, true⟩) (Frame.W 14 12 ⟨true, false, true⟩),
    perimOut (Frame.H 14 12 ⟨true, false, true⟩) (Frame.W 14 12 ⟨true, false, true⟩) x = true →
      effAlt3 14 12 (b5pts ⟨true, false, true⟩ 14 12 e x) = true := by
  decide +kernel

theorem b5b_ttf_14_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 12 ⟨true, true, false⟩) (Frame.W 14 12 ⟨true, true, false⟩),
    perimOut (Frame.H 14 12 ⟨true, true, false⟩) (Frame.W 14 12 ⟨true, true, false⟩) x = true →
      effAlt3 14 12 (b5pts ⟨true, true, false⟩ 14 12 e x) = true := by
  decide +kernel

theorem b5b_ttt_14_12 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 12 ⟨true, true, true⟩) (Frame.W 14 12 ⟨true, true, true⟩),
    perimOut (Frame.H 14 12 ⟨true, true, true⟩) (Frame.W 14 12 ⟨true, true, true⟩) x = true →
      effAlt3 14 12 (b5pts ⟨true, true, true⟩ 14 12 e x) = true := by
  decide +kernel

theorem b5b_fff_14_13 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 13 ⟨false, false, false⟩) (Frame.W 14 13 ⟨false, false, false⟩),
    perimOut (Frame.H 14 13 ⟨false, false, false⟩) (Frame.W 14 13 ⟨false, false, false⟩) x = true →
      effAlt3 14 13 (b5pts ⟨false, false, false⟩ 14 13 e x) = true := by
  decide +kernel

theorem b5b_fft_14_13 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 13 ⟨false, false, true⟩) (Frame.W 14 13 ⟨false, false, true⟩),
    perimOut (Frame.H 14 13 ⟨false, false, true⟩) (Frame.W 14 13 ⟨false, false, true⟩) x = true →
      effAlt3 14 13 (b5pts ⟨false, false, true⟩ 14 13 e x) = true := by
  decide +kernel

theorem b5b_ftf_14_13 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 13 ⟨false, true, false⟩) (Frame.W 14 13 ⟨false, true, false⟩),
    perimOut (Frame.H 14 13 ⟨false, true, false⟩) (Frame.W 14 13 ⟨false, true, false⟩) x = true →
      effAlt3 14 13 (b5pts ⟨false, true, false⟩ 14 13 e x) = true := by
  decide +kernel

theorem b5b_ftt_14_13 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 13 ⟨false, true, true⟩) (Frame.W 14 13 ⟨false, true, true⟩),
    perimOut (Frame.H 14 13 ⟨false, true, true⟩) (Frame.W 14 13 ⟨false, true, true⟩) x = true →
      effAlt3 14 13 (b5pts ⟨false, true, true⟩ 14 13 e x) = true := by
  decide +kernel

theorem b5b_tff_14_13 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 13 ⟨true, false, false⟩) (Frame.W 14 13 ⟨true, false, false⟩),
    perimOut (Frame.H 14 13 ⟨true, false, false⟩) (Frame.W 14 13 ⟨true, false, false⟩) x = true →
      effAlt3 14 13 (b5pts ⟨true, false, false⟩ 14 13 e x) = true := by
  decide +kernel

theorem b5b_tft_14_13 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 13 ⟨true, false, true⟩) (Frame.W 14 13 ⟨true, false, true⟩),
    perimOut (Frame.H 14 13 ⟨true, false, true⟩) (Frame.W 14 13 ⟨true, false, true⟩) x = true →
      effAlt3 14 13 (b5pts ⟨true, false, true⟩ 14 13 e x) = true := by
  decide +kernel

theorem b5b_ttf_14_13 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 13 ⟨true, true, false⟩) (Frame.W 14 13 ⟨true, true, false⟩),
    perimOut (Frame.H 14 13 ⟨true, true, false⟩) (Frame.W 14 13 ⟨true, true, false⟩) x = true →
      effAlt3 14 13 (b5pts ⟨true, true, false⟩ 14 13 e x) = true := by
  decide +kernel

theorem b5b_ttt_14_13 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 13 ⟨true, true, true⟩) (Frame.W 14 13 ⟨true, true, true⟩),
    perimOut (Frame.H 14 13 ⟨true, true, true⟩) (Frame.W 14 13 ⟨true, true, true⟩) x = true →
      effAlt3 14 13 (b5pts ⟨true, true, true⟩ 14 13 e x) = true := by
  decide +kernel

theorem b5b_fff_14_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 14 ⟨false, false, false⟩) (Frame.W 14 14 ⟨false, false, false⟩),
    perimOut (Frame.H 14 14 ⟨false, false, false⟩) (Frame.W 14 14 ⟨false, false, false⟩) x = true →
      effAlt3 14 14 (b5pts ⟨false, false, false⟩ 14 14 e x) = true := by
  decide +kernel

theorem b5b_fft_14_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 14 ⟨false, false, true⟩) (Frame.W 14 14 ⟨false, false, true⟩),
    perimOut (Frame.H 14 14 ⟨false, false, true⟩) (Frame.W 14 14 ⟨false, false, true⟩) x = true →
      effAlt3 14 14 (b5pts ⟨false, false, true⟩ 14 14 e x) = true := by
  decide +kernel

theorem b5b_ftf_14_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 14 ⟨false, true, false⟩) (Frame.W 14 14 ⟨false, true, false⟩),
    perimOut (Frame.H 14 14 ⟨false, true, false⟩) (Frame.W 14 14 ⟨false, true, false⟩) x = true →
      effAlt3 14 14 (b5pts ⟨false, true, false⟩ 14 14 e x) = true := by
  decide +kernel

theorem b5b_ftt_14_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 14 ⟨false, true, true⟩) (Frame.W 14 14 ⟨false, true, true⟩),
    perimOut (Frame.H 14 14 ⟨false, true, true⟩) (Frame.W 14 14 ⟨false, true, true⟩) x = true →
      effAlt3 14 14 (b5pts ⟨false, true, true⟩ 14 14 e x) = true := by
  decide +kernel

theorem b5b_tff_14_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 14 ⟨true, false, false⟩) (Frame.W 14 14 ⟨true, false, false⟩),
    perimOut (Frame.H 14 14 ⟨true, false, false⟩) (Frame.W 14 14 ⟨true, false, false⟩) x = true →
      effAlt3 14 14 (b5pts ⟨true, false, false⟩ 14 14 e x) = true := by
  decide +kernel

theorem b5b_tft_14_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 14 ⟨true, false, true⟩) (Frame.W 14 14 ⟨true, false, true⟩),
    perimOut (Frame.H 14 14 ⟨true, false, true⟩) (Frame.W 14 14 ⟨true, false, true⟩) x = true →
      effAlt3 14 14 (b5pts ⟨true, false, true⟩ 14 14 e x) = true := by
  decide +kernel

theorem b5b_ttf_14_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 14 ⟨true, true, false⟩) (Frame.W 14 14 ⟨true, true, false⟩),
    perimOut (Frame.H 14 14 ⟨true, true, false⟩) (Frame.W 14 14 ⟨true, true, false⟩) x = true →
      effAlt3 14 14 (b5pts ⟨true, true, false⟩ 14 14 e x) = true := by
  decide +kernel

theorem b5b_ttt_14_14 : ∀ e ∈ b5q, ∀ x ∈ cellsHW (Frame.H 14 14 ⟨true, true, true⟩) (Frame.W 14 14 ⟨true, true, true⟩),
    perimOut (Frame.H 14 14 ⟨true, true, true⟩) (Frame.W 14 14 ⟨true, true, true⟩) x = true →
      effAlt3 14 14 (b5pts ⟨true, true, true⟩ 14 14 e x) = true := by
  decide +kernel

/-- **The base sizes**, all frames. -/
theorem b5_base {R C : ℕ} (hR : 11 ≤ R) (hR' : R ≤ 14) (hC : 11 ≤ C) (hC' : C ≤ 14) (hp : (R * C) % 2 = 0)
    (f : Frame) {e : Coord × Coord × Coord} (he : e ∈ b5q) {x : Coord}
    (hx : perimOut (f.H R C) (f.W R C) x = true) : effAlt3 R C (b5pts f R C e x) = true := by
  have hxc : x ∈ cellsHW (f.H R C) (f.W R C) := by
    simp only [perimOut, Bool.and_eq_true, decide_eq_true_eq] at hx
    exact mem_cellsHW hx.1.1.1 hx.1.1.2
  obtain ⟨fr, fc, tr⟩ := f
  interval_cases R <;> interval_cases C <;> (try omega) <;>
    cases fr <;> cases fc <;> cases tr
  · exact b5b_fff_11_12 e he x hxc hx
  · exact b5b_fft_11_12 e he x hxc hx
  · exact b5b_ftf_11_12 e he x hxc hx
  · exact b5b_ftt_11_12 e he x hxc hx
  · exact b5b_tff_11_12 e he x hxc hx
  · exact b5b_tft_11_12 e he x hxc hx
  · exact b5b_ttf_11_12 e he x hxc hx
  · exact b5b_ttt_11_12 e he x hxc hx
  · exact b5b_fff_11_14 e he x hxc hx
  · exact b5b_fft_11_14 e he x hxc hx
  · exact b5b_ftf_11_14 e he x hxc hx
  · exact b5b_ftt_11_14 e he x hxc hx
  · exact b5b_tff_11_14 e he x hxc hx
  · exact b5b_tft_11_14 e he x hxc hx
  · exact b5b_ttf_11_14 e he x hxc hx
  · exact b5b_ttt_11_14 e he x hxc hx
  · exact b5b_fff_12_11 e he x hxc hx
  · exact b5b_fft_12_11 e he x hxc hx
  · exact b5b_ftf_12_11 e he x hxc hx
  · exact b5b_ftt_12_11 e he x hxc hx
  · exact b5b_tff_12_11 e he x hxc hx
  · exact b5b_tft_12_11 e he x hxc hx
  · exact b5b_ttf_12_11 e he x hxc hx
  · exact b5b_ttt_12_11 e he x hxc hx
  · exact b5b_fff_12_12 e he x hxc hx
  · exact b5b_fft_12_12 e he x hxc hx
  · exact b5b_ftf_12_12 e he x hxc hx
  · exact b5b_ftt_12_12 e he x hxc hx
  · exact b5b_tff_12_12 e he x hxc hx
  · exact b5b_tft_12_12 e he x hxc hx
  · exact b5b_ttf_12_12 e he x hxc hx
  · exact b5b_ttt_12_12 e he x hxc hx
  · exact b5b_fff_12_13 e he x hxc hx
  · exact b5b_fft_12_13 e he x hxc hx
  · exact b5b_ftf_12_13 e he x hxc hx
  · exact b5b_ftt_12_13 e he x hxc hx
  · exact b5b_tff_12_13 e he x hxc hx
  · exact b5b_tft_12_13 e he x hxc hx
  · exact b5b_ttf_12_13 e he x hxc hx
  · exact b5b_ttt_12_13 e he x hxc hx
  · exact b5b_fff_12_14 e he x hxc hx
  · exact b5b_fft_12_14 e he x hxc hx
  · exact b5b_ftf_12_14 e he x hxc hx
  · exact b5b_ftt_12_14 e he x hxc hx
  · exact b5b_tff_12_14 e he x hxc hx
  · exact b5b_tft_12_14 e he x hxc hx
  · exact b5b_ttf_12_14 e he x hxc hx
  · exact b5b_ttt_12_14 e he x hxc hx
  · exact b5b_fff_13_12 e he x hxc hx
  · exact b5b_fft_13_12 e he x hxc hx
  · exact b5b_ftf_13_12 e he x hxc hx
  · exact b5b_ftt_13_12 e he x hxc hx
  · exact b5b_tff_13_12 e he x hxc hx
  · exact b5b_tft_13_12 e he x hxc hx
  · exact b5b_ttf_13_12 e he x hxc hx
  · exact b5b_ttt_13_12 e he x hxc hx
  · exact b5b_fff_13_14 e he x hxc hx
  · exact b5b_fft_13_14 e he x hxc hx
  · exact b5b_ftf_13_14 e he x hxc hx
  · exact b5b_ftt_13_14 e he x hxc hx
  · exact b5b_tff_13_14 e he x hxc hx
  · exact b5b_tft_13_14 e he x hxc hx
  · exact b5b_ttf_13_14 e he x hxc hx
  · exact b5b_ttt_13_14 e he x hxc hx
  · exact b5b_fff_14_11 e he x hxc hx
  · exact b5b_fft_14_11 e he x hxc hx
  · exact b5b_ftf_14_11 e he x hxc hx
  · exact b5b_ftt_14_11 e he x hxc hx
  · exact b5b_tff_14_11 e he x hxc hx
  · exact b5b_tft_14_11 e he x hxc hx
  · exact b5b_ttf_14_11 e he x hxc hx
  · exact b5b_ttt_14_11 e he x hxc hx
  · exact b5b_fff_14_12 e he x hxc hx
  · exact b5b_fft_14_12 e he x hxc hx
  · exact b5b_ftf_14_12 e he x hxc hx
  · exact b5b_ftt_14_12 e he x hxc hx
  · exact b5b_tff_14_12 e he x hxc hx
  · exact b5b_tft_14_12 e he x hxc hx
  · exact b5b_ttf_14_12 e he x hxc hx
  · exact b5b_ttt_14_12 e he x hxc hx
  · exact b5b_fff_14_13 e he x hxc hx
  · exact b5b_fft_14_13 e he x hxc hx
  · exact b5b_ftf_14_13 e he x hxc hx
  · exact b5b_ftt_14_13 e he x hxc hx
  · exact b5b_tff_14_13 e he x hxc hx
  · exact b5b_tft_14_13 e he x hxc hx
  · exact b5b_ttf_14_13 e he x hxc hx
  · exact b5b_ttt_14_13 e he x hxc hx
  · exact b5b_fff_14_14 e he x hxc hx
  · exact b5b_fft_14_14 e he x hxc hx
  · exact b5b_ftf_14_14 e he x hxc hx
  · exact b5b_ftt_14_14 e he x hxc hx
  · exact b5b_tff_14_14 e he x hxc hx
  · exact b5b_tft_14_14 e he x hxc hx
  · exact b5b_ttf_14_14 e he x hxc hx
  · exact b5b_ttt_14_14 e he x hxc hx

end ZZN.Win

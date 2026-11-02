/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import BoxKGen.N11x11.Main
public import BoxKGen.N11x12.Main
public import BoxKGen.N11x13.Main
public import BoxKGen.N11x14.Main
public import BoxKGen.N11x15.Main
public import BoxKGen.N11x16.Main
public import BoxKGen.N12x12.Main
public import BoxKGen.N12x13.Main
public import BoxKGen.N12x14.Main
public import BoxKGen.N12x15.Main
public import BoxKGen.N12x16.Main
public import BoxKGen.N13x13.Main
public import BoxKGen.N13x14.Main
public import BoxKGen.N13x15.Main
public import BoxKGen.N13x16.Main
public import BoxKGen.N14x14.Main
public import BoxKGen.N14x15.Main
public import BoxKGen.N14x16.Main
public import BoxKGen.N15x15.Main
public import BoxKGen.N15x16.Main
public import BoxKGen.N16x16.Main
public import WinKU.Facts
public import ZZN.BoxK.None

@[expose] public section

namespace ZZN

theorem boxes_allK : ∀ w h, 11 ≤ w → w ≤ h → h ≤ 16 → BoxK.BoxCert w h := by
  intro w h h1 h2 h3
  have h4 : w ≤ 16 := by omega
  interval_cases w <;> interval_cases h
  exacts [BoxKGen.N11x11.box, BoxKGen.N11x12.box, BoxKGen.N11x13.box, BoxKGen.N11x14.box, BoxKGen.N11x15.box, BoxKGen.N11x16.box, BoxKGen.N12x12.box, BoxKGen.N12x13.box, BoxKGen.N12x14.box, BoxKGen.N12x15.box, BoxKGen.N12x16.box, BoxKGen.N13x13.box, BoxKGen.N13x14.box, BoxKGen.N13x15.box, BoxKGen.N13x16.box, BoxKGen.N14x14.box, BoxKGen.N14x15.box, BoxKGen.N14x16.box, BoxKGen.N15x15.box, BoxKGen.N15x16.box, BoxKGen.N16x16.box]

/-- **Passing the catalogue is equivalent to solvability**, for both sides at least 11,
with every finite fact checked by the kernel. -/
theorem passes_iff_solvable_K (I : Inst) (hwf : I.WellFormed) (hw : 11 ≤ I.w) (hh : 11 ≤ I.h) :
    Passes I ↔ Solvable I :=
  ⟨fun hP => BoxK.theoremA_boxes boxes_allK BoxK.none_all I ⟨hw, hh, hwf⟩ hP,
   WinKU.theoremB_K ⟨hw, hh, hwf⟩⟩

end ZZN

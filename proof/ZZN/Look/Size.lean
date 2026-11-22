/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Look.CheckT
public import ZZN.BoxK.SliceC

@[expose] public section

/-!
# Size bounds of a slice certificate

`szOK d`: at most 163 templates, each of cost at most 1333 and at most 16 leaves, and at most 418
stored pairs of paths, each at most 256 cells long. Checked on every table entry by the kernel
(`tabSz` in the generated modules).
-/

namespace ZZN.Look

open ZZN.T ZZN.BoxK

def szOK (d : CData) : Bool :=
  decide (d.2.2.1.length ≤ 163) && decide (d.2.2.2.2.length ≤ 418) &&
    d.2.2.1.all (fun e => decide (tcost e.1 ≤ 1333) && decide (tleaves e.1 ≤ 16)) &&
    d.2.2.2.2.all (fun e => decide (e.2.1 ≤ 256) && decide (e.2.2.2.1 ≤ 256))

end ZZN.Look

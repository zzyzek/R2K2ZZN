-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Defs
import Std.Data.HashMap

/-!
# A solver that returns explicit solutions, and a checked test for them

`solveInst` is a port of the C plug DP (as in `lib/c/zzn.c`: cell-by-cell, 3-bit bracket-encoded
frontier in a `UInt64`, sweep along the longer side). It keeps every layer with predecessor
indices and traces back from the final empty state.

Nothing about the solver is proved: a solution it returns is accepted only through `solB`, and
`solB_sound` shows `solB I p q = true → IsSolution I p q`.
-/

namespace ZZN

open GridHam

/-! ### The checked test -/

instance (w h : ℕ) (s t : Coord) (p : List Coord) : Decidable (IsPath w h s t p) := by
  unfold IsPath InBounds; infer_instance

/-- `p, q` solve `I`; coverage is checked by counting. -/
def solB (I : Inst) (p q : List Coord) : Bool :=
  decide (IsPath I.w I.h I.s0 I.t0 p) && decide (IsPath I.w I.h I.s1 I.t1 q) &&
    decide ((p ++ q).Nodup) && (p.length + q.length == I.w * I.h)

/-- A duplicate-free list of `w * h` cells of the grid contains every cell. -/
theorem cover_of_card {w h : ℕ} {l : List Coord} (hn : l.Nodup) (hb : ∀ v ∈ l, InBounds w h v)
    (hl : l.length = w * h) {v : Coord} (hv : InBounds w h v) : v ∈ l := by
  classical
  have hsub : l.toFinset ⊆ Finset.range w ×ˢ Finset.range h := by
    intro u hu
    have := hb u (List.mem_toFinset.mp hu)
    simp only [Finset.mem_product, Finset.mem_range]
    exact this
  have hcard : (Finset.range w ×ˢ Finset.range h).card ≤ l.toFinset.card := by
    rw [List.toFinset_card_of_nodup hn, hl, Finset.card_product, Finset.card_range,
      Finset.card_range]
  have he := Finset.eq_of_subset_of_card_le hsub hcard
  have : v ∈ Finset.range w ×ˢ Finset.range h := by
    simp only [Finset.mem_product, Finset.mem_range]
    exact hv
  rw [← he] at this
  exact List.mem_toFinset.mp this

theorem solB_sound {I : Inst} {p q : List Coord} (h : solB I p q = true) : IsSolution I p q := by
  simp only [solB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨hp, hq⟩, hn⟩, hl⟩ := h
  refine ⟨hp, hq, fun v hv hv' => ?_, fun v hv => ?_⟩
  · exact (List.nodup_append.mp hn).2.2 v hv v hv' rfl
  · have hb : ∀ u ∈ p ++ q, InBounds I.w I.h u := by
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact hp.2.2.2.1 u hu
      · exact hq.2.2.2.1 u hu
    have := cover_of_card hn hb (by rw [List.length_append]; exact hl) hv
    exact List.mem_append.mp this

theorem solvable_of_solB {I : Inst} {p q : List Coord} (h : solB I p q = true) : Solvable I :=
  ⟨p, q, solB_sound h⟩

/-! ### The solver (unverified) -/

namespace Solve

@[inline] def gv (s : UInt64) (i : Nat) : UInt64 := (s >>> (3 * i).toUInt64) &&& 7
@[inline] def sv (s : UInt64) (i : Nat) (v : UInt64) : UInt64 :=
  (s &&& ~~~((7 : UInt64) <<< (3 * i).toUInt64)) ||| (v <<< (3 * i).toUInt64)
@[inline] def isAnchor (v : UInt64) : Bool := v == 1 || v == 2
@[inline] def isOpen (v : UInt64) : Bool := v == 3 || v == 5
@[inline] def isClose (v : UInt64) : Bool := v == 4 || v == 6
@[inline] def colorOf (v : UInt64) : UInt64 := if isAnchor v then v - 1 else (v - 3) >>> 1
@[inline] def anchorV (c : UInt64) : UInt64 := 1 + c
@[inline] def openV (c : UInt64) : UInt64 := 3 + 2 * c
@[inline] def closeV (c : UInt64) : UInt64 := 4 + 2 * c

/-- The slot holding the other end of the bracket at slot `i`. -/
def partner (s : UInt64) (i n : Nat) : Nat := Id.run do
  let v := gv s i
  let mut depth := 0
  if isOpen v then
    for j in [i + 1:n] do
      let w := gv s j
      if isOpen w then depth := depth + 1
      else if isClose w then
        if depth == 0 then return j
        depth := depth - 1
  else
    for k in [0:i] do
      let j := i - 1 - k
      let w := gv s j
      if isClose w then depth := depth + 1
      else if isOpen w then
        if depth == 0 then return j
        depth := depth - 1
  return n

/-- Successors of state `s` at cell row `r`; `tc` is the endpoint color at the cell, if any. -/
def stepCell (s : UInt64) (r n : Nat) (tc : Option UInt64) (canR canD : Bool) : Array UInt64 :=
  Id.run do
  let budget := if tc.isSome then 1 else 2
  let navail := (if canR then 1 else 0) + (if canD then 1 else 0)
  let up := gv s r
  let lf := gv s (r + 1)
  let have_ := (if up != 0 then 1 else 0) + (if lf != 0 then 1 else 0)
  if have_ > budget then return #[]
  let need := budget - have_
  if need > navail then return #[]
  let base := sv (sv s r 0) (r + 1) 0
  let mut out : Array UInt64 := #[]
  if have_ == 0 then
    match tc with
    | some c =>
      let v := anchorV c
      if canR then out := out.push (sv base r v)
      if canD then out := out.push (sv base (r + 1) v)
    | none =>
      for col in [0, 1] do
        out := out.push (sv (sv base r (openV col)) (r + 1) (closeV col))
  else if have_ == 1 then
    let p := if up != 0 then up else lf
    let pos := if up != 0 then r else r + 1
    let pc := colorOf p
    if need == 0 then
      if some pc != tc then return #[]
      if isAnchor p then out := out.push base
      else out := out.push (sv base (partner s pos n) (anchorV pc))
    else
      if canR then out := out.push (sv base r p)
      if canD then out := out.push (sv base (r + 1) p)
  else
    let col := colorOf up
    if col != colorOf lf then return #[]
    if isAnchor up && isAnchor lf then out := out.push base
    else if isAnchor up || isAnchor lf then
      let bpos := if isAnchor up then r + 1 else r
      out := out.push (sv base (partner s bpos n) (anchorV col))
    else if isOpen up && isClose lf then return #[]
    else if isClose up && isOpen lf then out := out.push base
    else if isOpen up then out := out.push (sv base (partner s (r + 1) n) (openV col))
    else out := out.push (sv base (partner s r n) (closeV col))
  return out

/-- Solve on an `R × C` grid of (row, column) cells, `R ≤ C`; `term` gives the endpoint color.
Returns, per cell (row-major index `r * C + c`), the colors on its rgt and dwn edges. -/
def solveRC (R C : Nat) (term : Nat → Nat → Option UInt64) :
    Option (Array (Option UInt64) × Array (Option UInt64)) := Id.run do
  let n := R + 1
  let mask : UInt64 := ((1 : UInt64) <<< (3 * n).toUInt64) - 1
  -- layers[k] = states after k cells (column-major), with predecessor indices
  let mut keys : Array (Array UInt64) := #[#[0]]
  let mut preds : Array (Array UInt32) := #[#[0]]
  for c in [0:C] do
    for r in [0:R] do
      let cur := keys.back!
      let mut nk : Array UInt64 := #[]
      let mut np : Array UInt32 := #[]
      let mut seen : Std.HashMap UInt64 Unit := {}
      let tc := term r c
      for d in [0:cur.size] do
        let s0 := cur[d]!
        let s := if r == 0 && c > 0 then (s0 <<< 3) &&& mask else s0
        for t in stepCell s r n tc (c + 1 < C) (r + 1 < R) do
          if !seen.contains t then
            seen := seen.insert t ()
            nk := nk.push t
            np := np.push d.toUInt32
      if nk.isEmpty then return none
      keys := keys.push nk
      preds := preds.push np
  let last := keys.back!
  let mut idx := 0
  match last.findIdx? (fun x => x == 0) with
  | some i => idx := i
  | none => return none
  let mut rgt : Array (Option UInt64) := Array.replicate (R * C) none
  let mut dwn : Array (Option UInt64) := Array.replicate (R * C) none
  for j in [0:R * C] do
    let k := R * C - j
    let c := (k - 1) / R
    let r := (k - 1) % R
    let st := (keys[k]!)[idx]!
    let ru := gv st r
    let dn := gv st (r + 1)
    rgt := if ru != 0 then rgt.set! (r * C + c) (some (colorOf ru)) else rgt
    dwn := if dn != 0 then dwn.set! (r * C + c) (some (colorOf dn)) else dwn
    idx := ((preds[k]!)[idx]!).toNat
  return some (rgt, dwn)

/-- Walk color `col` from `a` to `b` along the chosen edges. -/
def walk (R C : Nat) (rgt dwn : Array (Option UInt64)) (col : UInt64) (a b : Nat × Nat) :
    List (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := #[a]
  let mut cur := a
  let mut prev : Nat × Nat := (R + 5, C + 5)
  for _ in [0:R * C] do
    if cur == b then break
    let (r, c) := cur
    let cands : List ((Nat × Nat) × Option UInt64) :=
      [((r, c + 1), rgt[r * C + c]!), ((r + 1, c), dwn[r * C + c]!),
       ((r, c - 1), if c > 0 then rgt[r * C + c - 1]! else none),
       ((r - 1, c), if r > 0 then dwn[(r - 1) * C + c]! else none)]
    match cands.find? (fun x => x.2 == some col && x.1 != prev) with
    | some (nxt, _) => prev := cur; cur := nxt; out := out.push nxt
    | none => break
  return out.toList

end Solve

open Solve in
/-- Solve an instance, returning the two paths (unverified; check with `solB`). -/
def solveInst (I : Inst) : Option (List Coord × List Coord) :=
  -- rows run along the shorter side: cell (r, c) is (c, r) when h ≤ w, else (r, c)
  let tp := I.w < I.h
  let R := if tp then I.w else I.h
  let C := if tp then I.h else I.w
  let toRC : Coord → Nat × Nat := fun v => if tp then (v.1, v.2) else (v.2, v.1)
  let ofRC : Nat × Nat → Coord := fun v => if tp then (v.1, v.2) else (v.2, v.1)
  let term : Nat → Nat → Option UInt64 := fun r c =>
    if toRC I.s0 == (r, c) || toRC I.t0 == (r, c) then some 0
    else if toRC I.s1 == (r, c) || toRC I.t1 == (r, c) then some 1 else none
  match solveRC R C term with
  | none => none
  | some (rgt, dwn) =>
    some ((walk R C rgt dwn 0 (toRC I.s0) (toRC I.t0)).map ofRC,
      (walk R C rgt dwn 1 (toRC I.s1) (toRC I.t1)).map ofRC)

/-- Solve and check. -/
def solveCheck (I : Inst) : Bool :=
  match solveInst I with
  | some (p, q) => solB I p q
  | none => false

theorem solvable_of_solveCheck {I : Inst} (h : solveCheck I = true) : Solvable I := by
  unfold solveCheck at h
  split at h
  · exact solvable_of_solB h
  · exact absurd h (by simp)

end ZZN

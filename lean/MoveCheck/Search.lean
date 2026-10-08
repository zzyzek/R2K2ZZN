-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Moves

/-!
Cross-check of `Facts.finite` against the C computations: for each instance (stdin, "R C s0r s0c
t0r t0c s1r s1c t1r t1c"), search for a `CanonMove` of a symmetric image using only the Lean
definitions (Lean catalogue for non-thin pieces, GridHam's IPS acceptability for one-path pieces).
Thin two-path pieces are printed for an exact solver to confirm.

Output per instance: `OK <desc> | <thin pieces>` or `NONE`.
-/

open ZZN GridHam

instance (I : Inst) : Decidable I.WellFormed := by
  unfold Inst.WellFormed InBounds; infer_instance

def thin (J : Inst) : Bool := J.w ≤ 10 || J.h ≤ 10

/-- `some pending` if the two-path piece is OK given that the pending thin pieces are solvable. -/
def pieceStatus (J : Inst) : Option (List Inst) :=
  if thin J then some [J]
  else if decide J.WellFormed && !(fires3 J.w J.h J.s0 J.t0 J.s1 J.t1) then some []
  else none

def oneOK (w h : ℕ) (s t : Coord) : Bool :=
  if s = t then w * h == 1
  else decide (InBounds w h s) && decide (InBounds w h t) && decide (IsAcceptable w h s t)

def showI (J : Inst) : String :=
  s!"{J.w} {J.h} {J.s0.1} {J.s0.2} {J.t0.1} {J.t0.2} {J.s1.1} {J.s1.2} {J.t1.1} {J.t1.2}"

/-- Search the canonical moves of `I` (cut at `x = p`). -/
def searchCanon (I : Inst) (cap : ℕ) : List (String × List Inst) := Id.run do
  let mut acc : List (String × List Inst) := []
  for p in List.range I.w do
    if p == 0 then continue
    -- strip
    if I.s0.1 < p && I.t0.1 < p && I.s1.1 < p && I.t1.1 < p && 2 ≤ I.w - p &&
        ((I.w - p) * I.h) % 2 == 0 && 5 ≤ I.h then
      match pieceStatus ⟨p, I.h, I.s0, I.t0, I.s1, I.t1⟩ with
      | some pend => if pend.isEmpty then return [(s!"strip p={p}", [])] else acc := acc ++ [(s!"strip p={p}", pend)]
      | none => pure ()
    -- 2/2 same
    if I.s0.1 < p && I.t0.1 < p && p ≤ I.s1.1 && p ≤ I.t1.1 &&
        oneOK p I.h I.s0 I.t0 && oneOK (I.w - p) I.h (I.s1.1 - p, I.s1.2) (I.t1.1 - p, I.t1.2) then
      return [(s!"same p={p}", [])]
    -- 1/3
    if I.s0.1 < p && p ≤ I.t0.1 && p ≤ I.s1.1 && p ≤ I.t1.1 then
      for y in List.range I.h do
        if oneOK p I.h I.s0 (p - 1, y) then
          match pieceStatus ⟨I.w - p, I.h, (0, y), unX p I.t0, unX p I.s1, unX p I.t1⟩ with
          | some pend => if pend.isEmpty then return [(s!"13 p={p} y={y}", [])] else acc := acc ++ [(s!"13 p={p} y={y}", pend)]
          | none => pure ()
    -- 2/2 cross
    if I.s0.1 < p && I.s1.1 < p && p ≤ I.t0.1 && p ≤ I.t1.1 then
      for y0 in List.range I.h do
        for y1 in List.range I.h do
          match pieceStatus ⟨p, I.h, I.s0, (p - 1, y0), I.s1, (p - 1, y1)⟩ with
          | none => pure ()
          | some pL =>
            match pieceStatus ⟨I.w - p, I.h, (0, y0), unX p I.t0, (0, y1), unX p I.t1⟩ with
            | some pR => if (pL ++ pR).isEmpty then return [(s!"cross p={p} y0={y0} y1={y1}", [])] else if acc.length < cap then acc := acc ++ [(s!"cross p={p} y0={y0} y1={y1}", pL ++ pR)]
            | none => pure ()
    -- excursion
    if I.s0.1 < p && I.t0.1 < p && p ≤ I.s1.1 && p ≤ I.t1.1 then
      for ya in List.range I.h do
        for yb in List.range I.h do
          match pieceStatus ⟨p, I.h, I.s0, (p - 1, ya), (p - 1, yb), I.t0⟩ with
          | none => pure ()
          | some pN =>
            match pieceStatus ⟨I.w - p, I.h, unX p I.s1, unX p I.t1, (0, ya), (0, yb)⟩ with
            | some pF => if (pN ++ pF).isEmpty then return [(s!"exc p={p} ya={ya} yb={yb}", [])] else if acc.length < cap then acc := acc ++ [(s!"exc p={p} ya={ya} yb={yb}", pN ++ pF)]
            | none => pure ()
  return acc

def allSyms : List Sym :=
  [false, true].flatMap fun tr => [false, true].flatMap fun rx => [false, true].flatMap fun ry =>
    [false, true].flatMap fun r0 => [false, true].flatMap fun r1 => [false, true].map fun sw =>
      ⟨tr, rx, ry, r0, r1, sw⟩

/-- A move with no thin pieces if there is one (`[(d, [])]`); otherwise up to `cap` candidates
per symmetry, each with the thin pieces it needs. -/
def search (I : Inst) (cap : ℕ) : List (String × List Inst) := Id.run do
  let mut all : List (String × List Inst) := []
  for σ in allSyms do
    let cs := searchCanon (σ.apply I) cap
    let tag := s!"sym={σ.tr},{σ.rx},{σ.ry},{σ.r0},{σ.r1},{σ.sw}"
    match cs with
    | [(d, [])] => return [(s!"{tag} {d}", [])]
    | _ => all := all ++ cs.map (fun c => (s!"{tag} {c.1}", c.2))
  return all

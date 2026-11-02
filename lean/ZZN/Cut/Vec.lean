-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Cut.Sym

/-!
# Formulas on a row slice: column atoms as shared masks

Lanes `j < C^4` are the column 4-tuples (base `C` digits of `j`). Within a slice the rows are
numbers, so an atom reduces to a column-only linear test, whose mask (`atomMask`) is computed
with bit-plane arithmetic. Masks are read from a lazily built trie (`Trie`) indexed by the test,
so the kernel computes each mask once per declaration and shares it.
-/

namespace ZZN.Cut

open ZZN.Lane

/-- The input planes of column `i` (bit `k` of digit `i`). -/
def rep (x L : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => x ||| (rep x L n <<< L)

def blk (C st k : ℕ) : ℕ → ℕ
  | 0 => 0
  | y + 1 => blk C st k y ||| (if y.testBit k then (2 ^ st - 1) <<< (y * st) else 0)

def plane (C i k : ℕ) : ℕ :=
  let st := C ^ (3 - i)
  rep (blk C st k C) (C * st) (C ^ i)

def colV (C i : ℕ) : List ℕ := (List.range 5).map (plane C i)

/-- `q * Y` for a small coefficient by repeated addition. -/
def scale (Y : List ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => addc Y (scale Y n) 0

/-- The test `Σ q_i y_i + c ⋈ 0` (op 0: `<`, 1: `=`, 2: odd) on all lanes. -/
def atomMask (C : ℕ) (q : Fin 4 → ℤ) (c : ℤ) (op : ℕ) : ℕ :=
  let N := C ^ 4
  let term := fun (i : Fin 4) (pos : Bool) =>
    if (pos && decide (0 < q i)) || (!pos && decide (q i < 0)) then scale (colV C i) (q i).natAbs else []
  let P := addc (addc (term 0 true) (term 1 true) 0) (addc (term 2 true) (term 3 true) 0) 0
  let Q := addc (addc (term 0 false) (term 1 false) 0) (addc (term 2 false) (term 3 false) 0) 0
  let P := addc P (cst N (if 0 < c then c.natAbs else 0)) 0
  let Q := addc Q (cst N (if c < 0 then c.natAbs else 0)) 0
  if op = 0 then lt N P Q
  else if op = 1 then nt N (lt N P Q ||| lt N Q P)
  else hd (addc P Q 0)

/-- Key of a column test: coefficients in `-3..3`, constant in `-200..200`, op. -/
def keyOf (q : Fin 4 → ℤ) (c : ℤ) (op : ℕ) : ℕ :=
  (((((q 0 + 3).toNat * 7 + (q 1 + 3).toNat) * 7 + (q 2 + 3).toNat) * 7 + (q 3 + 3).toNat) * 401 +
    (c + 200).toNat) * 3 + op

def keyQ (key : ℕ) : Fin 4 → ℤ := fun i =>
  let base := key / 3 / 401
  ((base / 7 ^ (3 - i.val)) % 7 : ℕ) - 3

def keyC (key : ℕ) : ℤ := ((key / 3) % 401 : ℕ) - 200

inductive Trie where
  | leaf (m : ℕ)
  | node (l r : Trie)

def Trie.build (f : ℕ → ℕ) : ℕ → ℕ → Trie
  | 0, k => Trie.leaf (f k)
  | d + 1, k => Trie.node (Trie.build f d (2 * k)) (Trie.build f d (2 * k + 1))

/-- Look up `k` (most significant bit first, `d` bits). -/
def Trie.get : Trie → ℕ → ℕ → ℕ
  | Trie.leaf m, _, _ => m
  | Trie.node l r, d, k => if (k >>> (d - 1)) % 2 = 0 then Trie.get l (d - 1) k else Trie.get r (d - 1) k

def keyBits : ℕ := 24

def table (C : ℕ) : Trie :=
  Trie.build (fun key => atomMask C (keyQ key) (keyC key) (key % 3)) keyBits 0

/-- Lane Boolean: a constant or a mask. -/
def evalS (C : ℕ) (tbl : Trie) (x : Fin 5 → ℤ) (h : ℤ) : Form → LB
  | Form.tt => LB.b true
  | Form.ff => LB.b false
  | Form.and a b => LB.and (evalS C tbl x h a) (evalS C tbl x h b)
  | Form.or a b => LB.or (evalS C tbl x h a) (evalS C tbl x h b)
  | Form.not a => LB.not (C ^ 4) (evalS C tbl x h a)
  | Form.lt L => atom C tbl x h L 0
  | Form.eq L => atom C tbl x h L 1
  | Form.odd L => atom C tbl x h L 2
where
  atom (C : ℕ) (tbl : Trie) (x : Fin 5 → ℤ) (h : ℤ) (L : Lin) (op : ℕ) : LB :=
    let c := L.c + (L.r0 * x 0 + L.r1 * x 1 + L.r2 * x 2 + L.r3 * x 3 + L.r4 * x 4) + L.q4 * h
    if L.q0 = 0 ∧ L.q1 = 0 ∧ L.q2 = 0 ∧ L.q3 = 0 then
      LB.b (if op = 0 then decide (c < 0) else if op = 1 then decide (c = 0) else decide (c % 2 = 1))
    else LB.m (tbl.get keyBits (keyOf ![L.q0, L.q1, L.q2, L.q3] c op))

end ZZN.Cut

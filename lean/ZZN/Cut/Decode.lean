-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Cut.Template

/-!
# Templates as a byte stream

A list of templates is stored as one natural number read in base 256 (least significant byte
first), which elaborates instantly however long it is. No lemma is needed about the decoder:
every decoded tree is checked by `tcheck`, which is sound for any tree.

Format of a tree: `0` = leaf; `1 v a o k` + `k` kinds + left + right = a cut (`v` = 1 for a
column cut, position anchor `a`, offset `o - 16`). A kind is `0 s` (stay), `1 s a o` (cross),
`2 s a o a' o'` (excursion), with side `s`. A list is `count` (two bytes) then the trees.
-/

namespace ZZN.Cut

def rdPos (n : ℕ) : TPos × ℕ := ((n % 256, ((n / 256) % 256 : ℕ) - (16 : ℤ)), n / 65536)

def decKinds : ℕ → ℕ → List (Kind TPos) × ℕ
  | 0, n => ([], n)
  | c + 1, n =>
    let t := n % 256
    let s := decide ((n / 256) % 256 = 1)
    let m := n / 65536
    let (k, m) : Kind TPos × ℕ :=
      if t = 0 then (Kind.stay s, m)
      else if t = 1 then let (p, m) := rdPos m; (Kind.cross s p, m)
      else let (p, m) := rdPos m; let (q, m) := rdPos m; (Kind.exc s p q, m)
    let (ks, m) := decKinds c m
    (k :: ks, m)

def decTree : ℕ → ℕ → CTree TPos × ℕ
  | 0, n => (CTree.leaf, n)
  | f + 1, n =>
    if n % 256 = 0 then (CTree.leaf, n / 256)
    else
      let m := n / 256
      let v := decide (m % 256 = 1)
      let (p, m) := rdPos (m / 256)
      let c := m % 256
      let (ks, m) := decKinds c (m / 256)
      let (l, m) := decTree f m
      let (r, m) := decTree f m
      (CTree.cut v p ks l r, m)

def decList : ℕ → ℕ → List (CTree TPos)
  | 0, _ => []
  | c + 1, n => let (t, m) := decTree 64 n; t :: decList c m

def decodeAll (blob : ℕ) : List (CTree TPos) := decList (blob % 65536) (blob / 65536)

end ZZN.Cut

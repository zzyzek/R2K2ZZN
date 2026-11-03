# Lowering the constants in the Lean step bounds

Working notes for anyone (human or agent) picking up this work. Status and log at the end.

## 1. Where the constants are

The registered step bounds (`proof/Challenge.lean`, `proof/ZZN/TimedStatement.lean`):

| Theorem | Bound | Constant |
|---|---|---|
| `ZZN.T.solvableBT_main` | `Cdec · (RC + R + C + 1)` | `Cdec = Kst 10 + Nst 10 + 300003` ≈ 10^756 |
| `ZZN.T.solveZZNT_main` | `(w + h + 1) (1100 (M + 1)⁴ + (M² + 1)² · Kw 22 + 10)`, `M = max w h` | `Kw 22` ≈ 10^3500 |

Both come from the plug DP algorithm for thin rectangles (`thinBFT`, `ZZN/Timed/Thin.lean`, and
its witness-carrying version `ZZN/Timed/ThinWit.lean`). Everything else in the bounds is small.

```
Q b   = (b + 3)²                        -- number of possible piece codes
Nst b = 4 · (Q b + 1)^(Q b)             -- bound on the number of states
Kst b = 5 + Nst·(6Q + 19) + 4·Nst² + 1 + 2·Nst·(Q + 2)                 -- one cell, decision
Ks  b = 4 + Nst·(9Q + 31) + 2·Nst·(Q + 2) + 2·Nst·(2·Nst·(Q + 2) + 1) + 9·Nst   -- one cell, witness
Kw  b = Ks b + Nst b + 4
```

Two separate sources of size:

1. **State count.** `Nst b` comes from `card_good` (`ZZN/Timed/ThinCount.lean`). A state is
   `(pieces, mask)`: a duplicate-free list of piece codes and a colour mask `< 4`. Each piece code
   compresses to a number `< Q b`, the list is read as a base-`(Q b + 1)` number of at most `Q b`
   digits. This counts every list, in every order, of every length up to `Q b`.
2. **Quadratic deduplication.** `stageT` (`ZZN/TimedStatement.lean`) cleans the state list with
   `ldedupT`, cost `|l|² + 1`. That gives the `Nst²` terms, which dominate `Kst` and `Ks`. The plain
   procedure (`stage` in `ZZN/Statement.lean`) already uses merge sort plus adjacent deduplication
   (`normS = dedupAdj (msortS 64 l)`); the counted version switched to `ldedupT` to keep the cost
   proof simple.

Size of `log10 Nst b` today and under the bounds proposed below (`b` = short side):

| b | Q b | current `Nst` | sorted subset `4·2^Q` | plug map `4·(b+4)^(b+1)` |
|---|---|---|---|---|
| 10 | 169 | 377.5 | 51.5 | 13.2 |
| 16 | 361 | 924.3 | 109.3 | 22.7 |
| 22 | 625 | 1748.5 | 188.7 | 33.1 |

For comparison, the C implementation keeps about 10^5 states at width 10 (`docs/PLUGDP.md` §4).

## 2. Levers

### A. Plug-map state count (largest gain, recommended first)

Facts about the states the DP algorithm keeps (`stepCell`, `closeP` in `ZZN/Statement.lean`):

- Each end of a piece is a plug code `≤ b` (a frontier position) or the endpoint code of a colour
  (`termE a b 0`, `termE a b 1`) (`GoodEnd`, already proved via the exit filter).
- A piece with two endpoint codes is closed at once by `closeP` (same colour: the colour is marked
  done; different colours: the state is dropped). So every stored piece has at least one plug end.
- Pieces are stored in sorted order (`insSorted`; `List.erase` keeps a sorted list sorted).
- **Needed new invariant:** no plug code is an end of two pieces. It should follow from the
  realizability invariant `W` (`ZZN/Thin/Sound.lean`): pieces are vertex-disjoint segments
  (`(allOf sg dp s).Nodup`), and a plug code names the frontier cell where a segment ends, so two
  pieces with the same plug code would share a cell. Not yet checked in Lean.

With the invariant, a state is determined by its mask and, for each plug code `0..b`, the other
end of the piece using it (another plug, an endpoint code, or none): at most `b + 4` values for
each of `b + 1` plugs. New bound: `Nst' b = 4 · (b + 4)^(b + 1)`.

Work: prove sortedness and the plug-disjointness invariant for `foldT` states (alongside
`good_of_W`), add them to `Good`, and replace the encoding in `ThinCount.lean` (`scode`,
`scode_lt`, `scode_inj`, `card_good`) by a base-`(b + 4)` encoding of the plug map. Then change the
definitions of `Q`/`Nst` in `TimedStatement.lean` and `Challenge.lean`; the cost lemmas in
`ThinCost.lean` and `ThinWitCost.lean` take `Nst` as a parameter and should need only the new
monotonicity lemma (`Nst_mono`). Piece-length bounds (`good_len`, `≤ Q b`) can stay as they are,
or drop to `b + 1`.

The sorted-subset bound `4 · 2^(Q b)` needs only sortedness, a smaller step, but saves much less.

### B. Sort-based deduplication (removes the square)

Replace `ldedupT` in `stageT` (and the witness version's dedup by key) with counted versions of
`msortS`/`dedupAdj`. Needs a counted merge sort and its time lemma, about `n · ⌈log₂ n⌉`
comparisons, each at most `Q b + 1` steps (`ltS` walks the piece list). The membership lemma for
`normS` (`mem_normS`) already exists.

Caution: `msortS 64` sorts only lists shorter than about `2^64`. Under lever A, `2 · Nst' 10` ≈
10^13.5 fits; `2 · Nst' 22` ≈ 10^33.4 does not. Either give the counted sort fuel from the list
length, or keep the quadratic dedup for the witness version.

### C. Width 22 to 16 in the construction (smaller gain)

`solveZZNT_time` uses `Kw 22` because `ZZN/Timed/Solve.lean` charges every leaf with a side at
most 22 to the thin solver. Irreducible instances have both sides at most 16
(`ZZN/BoxK/None.lean` covers sides 17 to 22). If the leaves of the counted recursion can be shown
to have a side at most 16, the constant becomes `Kw 16`. Not checked: the leaf condition in
`Solve.lean` may be needed as stated.

### D. Noncrossing count (not recommended)

Pieces are planar, so the plug map is a noncrossing partial matching with labelled ends (a
Motzkin-type count), close to the real 10^5 states. The planarity invariant is a large proof.

## 3. Expected results (estimates, not proved)

| Levers | `log10 Cdec` | `log10` construction constant |
|---|---|---|
| none (today) | 756 | 3500 |
| A | about 27 | about 70 |
| A + B | about 18 | about 38 (if the witness sort fuel is solved) |
| A + B + C | about 18 | about 28 |

These are dominated by the state bound; the bound is still about 10^8 above the real count at
width 10.

## 4. Process

- Lean edits are in `ZZN/Timed/*`, `ZZN/TimedStatement.lean` and `Challenge.lean`; certificates
  and `BoxK`/`WinKU` are untouched, so a rebuild is far shorter than the full 5.4 CPU-h build.
  Build with a memory cap (`systemd-run --user --scope -p MemoryMax=… -p MemorySwapMax=0`), never a
  bare `lake build` of everything.
- `Challenge.lean` is 998 lines and must stay under 1 000. New counted definitions (lever B) need
  room found elsewhere in it.
- `Challenge.lean` must stay identical in statement to `ZZN/TimedStatement.lean` and
  `ZZN/Statement.lean`; rerun `lake comparator` (config `proof/comparator.json`) before submitting.
- Update `proof/formalization.yaml` (`status.scope` quotes the constants), `proof/README.md`,
  `docs/PROOF.md` and the paper's Lean section with the new values.
- A change to `Cdec` or the definitions is a new Palomar submission.

## 5. Status

- 2026-11-03: analysis above. No Lean changes made. Plan: register the current result first, then
  A, then B, then C.

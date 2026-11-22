# zzn libraries

Decide and solve two-colour Zig-Zag Numberlink on rectangles, in three languages with identical
behaviour and output:

| | Directory | Command line |
|---|---|---|
| Python 3.8+ (reference) | [`python/`](python/) | `python3 python/zzn_cli.py R C s0r s0c t0r t0c s1r s1c t1r t1c` |
| JavaScript (Node or browser) | [`js/`](js/) | `node js/cli.js ...` |
| C11 | [`c/`](c/) | `make -C c && c/zzn ...` |

`decide(I)`: the plug DP algorithm when a side is at most 10, else the catalogue (`fires3` in
`proof/ZZN/Statement.lean`).

`solve(I)`:
- **A side is at most 10:** the plug DP algorithm ([`docs/PLUGDP.md`](../docs/PLUGDP.md)).
- **The catalogue fires:** unsolvable.
- **Otherwise:** the Lean construction `solveZ3 (leafL thinSolveW2 tabAll)`, whose soundness and
  completeness are `solveZ3L_main` (`proof/ZZN/Look/Main.lean`). It has three layers, each
  transcribed and checked against the Lean definitions evaluated in Lean (Tests below):
  1. Block deletion (`solveR`, `proof/ZZN/Constr/Round.lean`; `python/zzn/blocks.py`). It
     deletes blocks of 2k free lines until no block is left, leaving sides at most 37.
  2. Two-line reductions (`solveRec2`, `proof/ZZN/Constr/Solve2.lean`;
     `python/zzn/reduce2.py`). It deletes two lines by `RedX` or `RedB` until neither applies on
     either axis, leaving both sides in 11–16.
  3. The leaf (`leafL`, `proof/ZZN/Look/Complete.lean`). With both sides 11–16 it is the
     certificate lookup `lookJ tabAll` (`proof/ZZN/Look/Leaf.lean`; `python/zzn/look.py`). The
     table `tabAll` is exported from the Lean sources to `data/look.json.gz` (1.8 MB) by
     `tools/export_look.py`.

  The solution is then lifted back through the reductions and the blocks. With both sides at
  least 11 at the start, the leaf always has both sides 11–16, so only the lookup is used. Every
  solution is checked before it is returned.

Each library also has an optimized solver for thin instances (`--optimized` on the command line):
guessed splits with the plug DP as the fallback, exact, and much faster on long thin grids.

## Performance

The bounds in this table describe the library code. They are not proved; Lean proves step bounds
only for its own counted procedures ([`docs/PROOF.md`](../docs/PROOF.md) §2).

| Region | Time | Memory |
|---|---|---|
| A side at most 10 | O(L), L the long side (plug DP algorithm) | O(L) |
| Both sides at least 11, catalogue fires | O(1) | O(1) |
| Both sides at least 11, passing | O(R·C): blocks and lifts O(R·C); reductions and the lookup on at most 37 × 37 | O(R·C), plus the table |

`solve` on M × M and M × 2M grids, from `python3 tests/bench.py` (one process per instance, peak
resident memory, every solution checked). Each cell gives the medians of 3 instances, as a range
over three endpoint layouts: random endpoints; all four in a 5 × 5 corner; and one endpoint per
fifth of each axis. The largest single time and memory are in `tests/bench_results.md`.

| Size | C | JavaScript (Node) | Python |
|---|---|---|---|
| 160 × 160 | 0.05 s | 0.22–0.23 s | 0.71–0.84 s |
| 640 × 640 | 0.10 s | 0.43–0.55 s | 1.3–1.6 s |
| 1280 × 1280 | 0.24–0.25 s, ≤ 51 MB | 1.3–1.6 s, ≤ 0.8 GB | 3.0–4.3 s, ≤ 0.5 GB |
| 2560 × 2560 | 0.83–0.87 s, ≤ 126 MB | 5.3–6.9 s, ≤ 2.2 GB | 10.0–14.6 s, ≤ 1.9 GB |
| 1280 × 2560 | 0.43–0.45 s | 2.5–3.1 s | 5.2–8.3 s |
| 2560 × 5120 | 1.6–1.7 s, ≤ 226 MB | 11.8 s, 2.4 GB (corner layout only) | 18.9–29.8 s, ≤ 3.8 GB |

- **Loading the lookup table** happens once per process: about 0.05 s in C, 0.15 s in JavaScript
  and 0.3 s in Python. It dominates the times below 640 × 640.
- **Growth:** from 1280 to 2560 the time grows by 3.3–3.7 times in C, 3.4–4.0 in Python and
  4.2–4.8 in JavaScript. R·C grows by 4 times.
- **JavaScript on 2560 × 5120:** with the random and spread layouts it stops at Node's default
  heap limit (about 2 GB here); `node --max-old-space-size=4096` raises it.
- **`decide`** with both sides at least 11 is the catalogue: under 0.04 s at every size. On thin
  grids (6 × M), `decide` and `solve` are linear in M.

Measured on one core of a 4-core machine, 2026-11-17.

## Tests

`tests/run_all.sh` runs the suite below (about 4 minutes on one core).
- `tests/run_all.sh --boxes` adds the exhaustive lookup test (about 2.5 CPU-minutes).
- `tests/run_all.sh --lean=DIR` adds the comparisons with Lean. DIR is a `proof/` directory with
  `ZZN.Look.Table` built. Lean uses about 7 GB.

- `python3 tests/compare.py N SEED [RMIN RMAX] [--trace] [--optimized] [--irreducible] [--layouts]
  [--programs=c,js]`: runs the command-line programs on the same random instances, requires
  identical output, and checks every solution. `--irreducible` draws leaves answered by the lookup
  (sides 11–16); `--layouts` draws passing instances with the three endpoint layouts of
  `bench.py`.
- `python3 python/tests/test_random.py N SEED [RMIN RMAX] [--exact PROG]`: Python, including
  agreement with an exact solver.
- `python3 tests/blocks_test.py N SEED MMIN MMAX`: deletes the blocks of each instance and lifts
  them back one at a time, checking the solution at every level.
- `python3 tests/look_test.py [N] [SEED]` checks three things:
  - N irreducible leaves for each of the 36 shapes 11–16 × 11–16;
  - all 8,444 stored solutions of the table;
  - random leaves.

  Every answer is checked.
- `tests/boxes.sh [JOBS]`: every passing instance of 11 × 11, 11 × 12 and 12 × 12, one per symmetry
  class: 6,688,495 instances. All are leaves, all are answered by the C lookup, and all answers are
  checked.

Against the Lean definitions, evaluated in Lean on the libraries' data (`--proof=DIR`, a built
`proof/`):
- `tests/lean_blocks.py`: `blkX`, `Blk.del`, `Blk.lift`. Run on 3,500 instances with sides
  11–150, 11,274 steps: no difference.
- `tests/lean_reduce2.py`: `findRed2`, `liftE`, and the leaf condition. Run on 1,500 instances
  with sides 11–150, 13,901 steps: no difference.
- `tests/look_lean.py`:
  - the exported table, read back from Lean's elaborated definitions: 28,102 lines, no difference;
  - `lookJ`, on a table rebuilt in Lean from the export;
  - `entryP`, `tcheck`, `tsol`, `Sym.apply`, `unSym`, `key2` with `argminS`, `decPath`, `solF`,
    `accB` and `ipsP`: 19,175 cases, no difference.

  `tabAll` itself is noncomputable in Lean, so `lookJ tabAll` was not evaluated directly.
- C and JavaScript are compared with Python by `compare.py`. `js/look_check.js` and the C
  `--leaf` flag compare the lookup alone.
- `tests/lean_catalogue.py`: the Python catalogue (`fires`) and each of its entries against
  `fires3` and its entries. 100,000 instances (sides 1–40, patterns planted near corners and on
  the border): 46,227 fire, and there are no differences. JavaScript and C are compared with
  Python by `compare.py`.

Other tools:
- `python3 tests/bench.py [--sizes=...] [--programs=...] [--modes=...] [--layouts=...]
  [--shapes=...]`: the timing table above.
- `python3 tests/dp_cost.py`: the plug DP algorithm on whole instances.

## License

CC0 1.0 Universal: to the extent possible under law, the author has waived all copyright and
related or neighboring rights to this work. See [`LICENSE`](../LICENSE).

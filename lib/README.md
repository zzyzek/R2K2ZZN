# zzn libraries

Decide and solve two-colour Zig-Zag Numberlink on rectangles, in three languages with identical
behaviour and output:

| | Directory | Command line |
|---|---|---|
| Python 3.8+ (reference) | [`python/`](python/) | `python3 python/zzn_cli.py R C s0r s0c t0r t0c s1r s1c t1r t1c` |
| JavaScript (Node or browser) | [`js/`](js/) | `node js/cli.js ...` |
| C11 | [`c/`](c/) | `make -C c && c/zzn ...` |

The algorithm: [`docs/ALGORITHM.md`](../docs/ALGORITHM.md) and [`docs/PLUGDP.md`](../docs/PLUGDP.md).
Each library also has an optimized solver for thin instances (`--optimized` on the command line):
guessed splits with the plug DP as the fallback, exact, and much faster on long thin grids.
Its correctness is proved in Lean ([`proof/`](../proof/)); the libraries implement the same
decision procedure and the constructive steps of the proof.

## Tests

`tests/run_all.sh` runs the suite below (about 4 minutes on one core); `tests/run_all.sh --boxes`
adds the exhaustive test (about one CPU-hour).

- `python3 tests/compare.py N SEED [RMIN RMAX] [--trace] [--optimized] [--irreducible]
  [--programs=c,js]`: runs the command-line programs on the same random instances; requires
  identical output and checks every solution. `--irreducible` draws passing instances with sides
  11–22 that no reduction applies to, so each reaches the same-colour split or the move search.
- `python3 python/tests/test_random.py N SEED [RMIN RMAX] [--exact PROG]`: Python, including
  agreement with an exact solver.
- `tests/boxes.sh [JOBS]`: every passing instance of 11 × 11, 11 × 12 and 12 × 12, one per symmetry
  class (about 6.7 million), solved by the C library. With both sides at most 12 no reduction
  applies, so every instance reaches the same-colour split or the move search.
- The catalogue (`fires`) of all three agrees with the Lean definition `fires3` on 60,000 instances.

When no valid move is found, `solve` falls back to the exact plug DP algorithm on the whole
instance. The proof finds a single valid move for every passing irreducible instance except in the
boxes 11 × 11, 11 × 12 and 12 × 12, where it shows each instance solvable directly
([`docs/PROOF.md`](../docs/PROOF.md) §5.1); `tests/boxes.sh` checks those boxes. Setting
`ZZN_SKIP_MOVES=1` in the environment skips the move search, so the fallback can be tested. At width
11–12 it takes seconds in C and JavaScript and minutes in Python.

## License

CC0 1.0 Universal: to the extent possible under law, the author has waived all copyright and
related or neighboring rights to this work. See [`LICENSE`](../LICENSE).

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
Its correctness is proved in Lean ([`lean/`](../lean/)); the libraries implement the same
decision procedure and the constructive steps of the proof.

## Tests

- `python3 tests/compare.py N SEED [RMIN RMAX] [--trace] [--optimized]`: runs all three
  command-line programs on the same random instances; requires identical output and checks every
  solution.
- `python3 python/tests/test_random.py N SEED [RMIN RMAX] [--exact PROG]`: Python, including
  agreement with an exact solver.
- The catalogue (`fires`) of all three agrees with the Lean definition `fires3` on 60,000 instances.

## License

CC0 1.0 Universal: to the extent possible under law, the author has waived all copyright and
related or neighboring rights to this work. See [`LICENSE`](../LICENSE).

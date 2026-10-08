# zzn (C)

Decide and solve two-colour Zig-Zag Numberlink on rectangles. C11, no dependencies. Same
algorithm and the same results as the Python and JavaScript libraries
([`docs/ALGORITHM.md`](../../docs/ALGORITHM.md)).

## Build

```
make            # libzzn.a, the command-line program ./zzn, and ./example
```

## Library

```c
#include "zzn.h"

zzn_instance in = {12, 12, {0, 0}, {0, 11}, {11, 0}, {11, 11}};   /* R, C, s0, t0, s1, t1 (row, col) */
zzn_solution sol;
int r = zzn_solve(&in, &sol);
if (r == ZZN_SOLVED) {
  /* sol.a: s0 -> t0, sol.b: s1 -> t1; cells in sol.a.cells[0 .. sol.a.len-1] */
  char *pic = zzn_render(&in, &sol);
  puts(pic);
  free(pic);
  zzn_solution_free(&sol);
} else if (r == ZZN_UNSOLVABLE) {
  puts(zzn_explain(&in));          /* e.g. "catalogue entry T1 fires" */
}
```

Compile with `cc -O2 -std=c11 yourprog.c libzzn.a`. See `example.c`.

| Function | |
|---|---|
| `int zzn_decide(const zzn_instance *)` | 1 solvable, 0 unsolvable, `ZZN_INVALID` |
| `int zzn_solve(const zzn_instance *, zzn_solution *)` | `ZZN_SOLVED` (free with `zzn_solution_free`), `ZZN_UNSOLVABLE`, `ZZN_INVALID`, `ZZN_INTERNAL` |
| `int zzn_solve_trace(..., char **trace)` | as `zzn_solve`, plus a malloc'd text of the steps |
| `const char *zzn_fires(R, C, s0, t0, s1, t1)` | the catalogue alone: entry name or `NULL` |
| `const char *zzn_explain(const zzn_instance *)` | which entry fires, or that the DP decided |
| `int zzn_acceptable(R, C, s, t)`, `int zzn_hamiltonian_path(R, C, s, t, zzn_path *)` | Hamiltonian paths (IPS); free `out->cells` |
| `int zzn_check_solution(...)`, `char *zzn_render(...)`, `int zzn_well_formed(...)` | utilities |

Solutions are checked before they are returned; `ZZN_INTERNAL` would signal a bug (never observed).

**Optimized versions (thin instances).** `zzn_decide_optimized`, `zzn_solve_optimized` and
`zzn_solve_optimized_trace` take the same arguments and are much faster on thin instances (a side
≤ 10): the grid is cut into pieces at guessed splits well away from the endpoints, and the plug DP
only runs on pieces with a short side. If the guesses fail, the plug DP decides, so the answers are
exact and the same as `zzn_decide`; the paths can differ from `zzn_solve`'s (they are the same as
the Python and JavaScript optimized versions). Instances with both sides ≥ 11 go to the ordinary
solver. The method is described in `lib/python/zzn/optimized.py`.
The library is reentrant across threads (thread-local error state).

## Command line

```
./zzn R C s0r s0c t0r t0c s1r s1c t1r t1c [--decide] [--grid] [--trace] [--json] [--optimized]
./zzn [options] < instances.txt         # one instance per line
```

```
$ ./zzn 12 12 0 0 0 11 11 0 11 11 --json
{"solvable": true, "paths": [[[0,0],[0,1], ... ]]}
$ ./zzn 12 12 0 0 11 11 0 11 11 0 --decide
unsolvable: catalogue entry T1 fires
```

## Performance

20,000 random instances with sides 11–60 solve in about 8 s. Thin instances that fail the parity
check are rejected at once; otherwise the plug DP at width 10 takes about 1–2 s for lengths 20–40
and about 5 s at length 80 (random instances; the cost depends on where the endpoints are).
Width 9 is several times faster (about 0.3 s at 9 × 40).

The optimized solver (`zzn_solve_optimized`) on random thin instances that pass the parity check,
widths 8–10 and lengths 12–320 (180 instances): median about 480× faster than `zzn_solve`, about
1,000–5,000× at width 10 (a few milliseconds instead of seconds); total time 8.7 s instead of
738 s. Its worst case is about twice `zzn_solve` (an unsolvable instance whose pieces must all be
proved unsolvable by the plug DP).

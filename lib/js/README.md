# zzn (JavaScript)

Decide and solve two-colour Zig-Zag Numberlink on rectangles; one file, no dependencies, Node 14+
or a browser. Same algorithm and the same results as the Python and C libraries
([`docs/ALGORITHM.md`](../../docs/ALGORITHM.md)).

## Library

```js
const zzn = require("./zzn.js");          // in a browser: <script src="zzn.js"></script>, then window.zzn

// cells are [row, col]; an instance is {R, C, s0, t0, s1, t1}
const inst = zzn.Instance(12, 12, [0, 0], [0, 11], [11, 0], [11, 11]);
zzn.decide(inst);                          // true
const [a, b] = zzn.solve(inst);            // a: s0 -> t0 (12 cells), b: s1 -> t1 (132 cells)
console.log(zzn.render(inst, [a, b]));

const bad = { R: 12, C: 12, s0: [0, 0], t0: [11, 11], s1: [0, 11], t1: [11, 0] };
zzn.decide(bad);                           // false
zzn.solve(bad);                            // null
zzn.explain(bad);                          // 'catalogue entry T1 fires'

const trace = [];
zzn.solve(zzn.Instance(16, 13, [5, 2], [12, 10], [6, 9], [13, 3]), trace);
// trace[0] = ["reduce", instance, axis, d], then moves and thin solves
```

| Function | |
|---|---|
| `decide(inst)` | solvability (plug DP if a side ≤ 10, else the catalogue) |
| `solve(inst, trace?)` | `[pathA, pathB]` or `null`; the solution is checked before it is returned |
| `explain(inst)` | which catalogue entry fires, or that the DP decided |
| `fires(R, C, s0, t0, s1, t1)` | the catalogue alone: an entry name or `null` |
| `acceptable(R, C, s, t)`, `hamiltonianPath(R, C, s, t)` | Hamiltonian paths in rectangles (IPS) |
| `solvePaths(R, C, [[[r, c], colour], ...])` | the plug DP for one or two colours |
| `checkSolution(inst, sol)`, `render(inst, sol)`, `wellFormed(inst)` | utilities |

An instance whose endpoints are not four distinct cells of the grid throws an `Error`.

### Optimized version (thin instances)

`zzn.optimized.decide`, `zzn.optimized.solve` and `zzn.optimized.solvePaths` are much faster on
thin instances (a side ≤ 10): the grid is cut into pieces at guessed splits well away from the
endpoints, and the plug DP only runs on pieces with a short side. If the guesses fail, the plug DP
decides, so the answers are exact and the same as `decide`; the paths can differ from `solve`'s
(they are the same as the Python and C optimized versions). Instances with both sides ≥ 11 go to
the ordinary solver. The method is described in `lib/python/zzn/optimized.py`.

```js
zzn.optimized.solve(zzn.Instance(10, 80, [2, 65], [3, 11], [4, 36], [0, 45]));   // milliseconds
```

## Command line

```
node cli.js R C s0r s0c t0r t0c s1r s1c t1r t1c [--decide] [--grid] [--trace] [--json] [--optimized]
node cli.js [options] < instances.txt        # one instance per line
```

```
$ node cli.js 12 12 0 0 11 11 0 11 11 0
unsolvable: catalogue entry T1 fires
$ node cli.js 16 13 5 2 12 10 6 9 13 3 --trace | tail -6
  reduce 16x13: delete rows 0,1
  move 14x13: strip, cut between rows 11 and 12
  move 12x13: strip, cut between columns 10 and 11
  move 11x12: 2/2 cross, cut between rows 4 and 5
  thin 5x12
  thin 6x12
```

The output is identical to the Python and C programs (`lib/tests/compare.py`).

## Performance

Like the Python version, fast for both sides ≥ 11. Thin instances that fail the parity check are
rejected at once; otherwise the plug DP at width 10 takes about 6 s at length 20–40 and 20 s at
length 80, about 4× the C library's time. The optimized solver (`zzn.optimized`) takes about
6 ms at 10 × 20 and 16 ms at 10 × 80 instead of 4.5 s and 27 s (median about 700× and 1,700×).

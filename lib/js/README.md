# zzn (JavaScript)

Decide and solve two-colour Zig-Zag Numberlink on rectangles; one file plus the lookup table
`lib/data/look.json.gz`, no dependencies, Node 14+ or a browser. Same algorithm and the same results as the Python and C libraries
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
// trace[0] = ["block", instance, axis, ["left", 1]], then reductions and the leaf lookup
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
| `setLookData(textOrObject)` | supply the lookup table (needed in a browser, see below) |

An instance whose endpoints are not four distinct cells of the grid throws an `Error`.

### Lookup table

After block deletion and two-line reductions, `solve` answers the remaining leaf (both sides
11-16) from the certificate table `lib/data/look.json.gz`, as the Lean leaf solver `lookJ tabAll`
does (the transcription is `lib/python/zzn/look.py`; the format is in
`lib/tools/export_look.py`). `decide`, `explain` and thin instances never need it.

- Node: the table is read once, on first use, from `../data/look.json.gz` relative to `zzn.js`
  (about 0.15 s); the environment variable `ZZN_LOOK_DATA` names another file.
- Browser: the page supplies the table before the first `solve` that reaches a leaf, else that
  call throws an `Error`. Pass the gunzipped JSON **text**: the stored path codes are integers of
  up to 1352 bits, which `JSON.parse` would round, so `setLookData` parses the text itself and keeps
  them exact. An already parsed object is accepted only if its codes are strings or `BigInt`s; an
  object whose codes were rounded by `JSON.parse` is rejected with an `Error`.

```js
const gz = await (await fetch("look.json.gz")).arrayBuffer();
const text = await new Response(new Blob([gz]).stream().pipeThrough(new DecompressionStream("gzip"))).text();
zzn.setLookData(text);
```

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
$ node cli.js 16 13 5 2 12 10 6 9 13 3 --trace | tail -4
  block 16x13: delete rows 0..1
  reduce 14x13: delete rows 5,6
  reduce 12x13: delete columns 5,6
  leaf 11x12
```

The output is identical to the Python and C programs (`lib/tests/compare.py`).
The leaf lookup alone is compared with Python's `look_j` (paths, symmetry, slice and entry) by
`python3 js/look_dump.py 60 7 /tmp/look.json --lanes && node js/look_check.js /tmp/look.json`
(from `lib/`).

## Performance

Both sides ≥ 11: time grows as R·C. Median times are 1.3–1.6 s at 1280 × 1280 and 5.3–6.9 s at
2560 × 2560 (`lib/README.md`). Node's default heap limit (about 2 GB here) is reached near
2560 × 5120; `node --max-old-space-size=4096 cli.js ...` raises it. Thin instances that fail the parity check are
rejected at once; otherwise the plug DP at width 10 takes about 6 s at length 20–40 and 20 s at
length 80, about 4× the C library's time. The optimized solver (`zzn.optimized`) takes about
6 ms at 10 × 20 and 16 ms at 10 × 80 instead of 4.5 s and 27 s (median about 700× and 1,700×).

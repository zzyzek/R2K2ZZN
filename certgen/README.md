# Certificate generation

The Lean proof in [`proof/`](../proof/) checks certificates with the kernel. Nothing here is
trusted: a wrong certificate fails the build. This directory records how the certificates were
made, so they can be regenerated or improved.

| Path | Contents |
|---|---|
| `certs/c{W}x{H}.txt.xz` | Theorem A slice certificates, one per box `W × H` (11 ≤ W ≤ H ≤ 16) |
| `certs/b{W}x{H}.txt.xz` | Stabiliser classes and base masks of the slices of each box |
| `inputs/tset_E.txt` | The base template set the search starts from (3 742 templates) |
| `inputs/tset_G.txt` | The global template set the certificates index (11 029 templates) |
| `inputs/reps/e{W}.txt` | Canonical row tuples (slices) for boxes of width `W` |
| `src/` | The certificate search `slicehyb` (C; with `../lib/c/zzn.c`) |
| `tools/` | Certificates → Lean modules (Python), the Lean generators `WinGenU`, `FireGen`, `BaseGen`, and `export.py` |
| `regen.sh` | Certificates → `gen/` (Lean modules) → `proof/` |
| `../notes/gen_lookgen.py` | `proof/ZZN/LookGen/` (the lookup table of the construction) from the certificate modules in `proof/BoxKGen/`; not run by `regen.sh` |

## Regenerating the Lean modules

From the repository root, with the `proof/` library built (`lake build` in `proof/`):

```bash
certgen/regen.sh
```

Theorem A modules come from `certs/` with `tools/gen_box.py` and `tools/gen_cbox.py`. Theorem B
modules come from `tools/wincases.txt` through `tools/WinGenU.lean` and the post-processing
scripts. `tools/export.py` writes the modules into `proof/`, and `tools/palomar.py` regenerates the
Palomar files: `proof/Challenge{Decide,Construct}.lean`, `Solution{Decide,Construct}.lean` and
`comparator_{decide,construct}.json`. A challenge holds the library declarations its statements
depend on; `tools/Closure.lean` lists them (`tools/palomar_{decide,construct}_decls.txt`), and
`tools/HashDump.lean` checks that each challenge and its solution agree on them. `regen.sh` lists
every step. Its output was checked byte for byte against the committed `proof/` on 2026-11-02; the
step-count, construction and lookup modules added since then are written by hand (except
`proof/ZZN/LookGen/`, see the table above), and `regen.sh` has not been rerun on the current tree.

## Rerunning the certificate search

```bash
gcc -O2 -I lib/c -o slicehyb certgen/src/slicehyb.c lib/c/zzn.c lib/c/look.c -lz -lm
REDUCE=1 GPOOL=1 FOLD=1 SOLS=1 GSEED=pool.txt GDUMP=pool_out.txt TOUT=t11x11.txt \
  ./slicehyb 11 11 certgen/inputs/tset_E.txt certgen/inputs/reps/e11.txt 1 0 > c11x11.txt
```

`slicehyb` calls the library's `zzn_solve` for explicit solutions. For boxes 11–16 the current
library answers from the lookup table `lib/data/look.json.gz`, which was generated from these
certificates, so a search with the current library depends on the existing table. The released
certificates were found with the library's earlier solver (before commit `1c1cfa7`).

For each slice (a canonical tuple of the four endpoint rows), `slicehyb` lists the column tuples
that pass the catalogue and covers them with (template, symmetry) pairs. A template is a cut tree
that solves every instance it matches. Uncovered instances get explicit solutions (`SOL`), and
lanes where all four reflections fail the catalogue are listed as `FIRE`. The options:

- `GPOOL=1` adds every pair an earlier slice of the box chose to each slice's candidates, and the
  greedy cover runs over all of them.
- `REDUCE=1` drops chosen pairs whose instances other chosen pairs cover.
- `GSEED` / `GDUMP` read and write that pool, so one box can start from another's.

Together these cut the pairs from 380 333 to 255 545. The released certificates seeded each box
from the previous box in two chains.

The certificate then goes through four steps:

1. `tools/remap_templates.py` renumbers the template indices into `inputs/tset_G.txt`.
2. `tools/cert2c.py` converts the format.
3. `tools/FireGen.lean` adds a fire witness per reflection (`lake env lean --run`, from `proof/`).
4. `tools/BaseGen.lean` computes the base file from `inputs/reps/e{W}.txt`.

The result is what `certs/` holds.

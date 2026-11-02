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
| `regen.sh` | Certificates → `lean/gen/` (Lean modules) → `proof/` |

## Regenerating the Lean modules

From the repository root, with the library in `lean/` built:

```bash
certgen/regen.sh
```

Theorem A modules come from `certs/` with the Python tools in `lean/tools/` (`gen_box.py`,
`gen_cbox.py`). Theorem B modules come from `lean/tools/wincases.txt` through `WinGenU.lean` and
the post-processing scripts. `regen.sh` lists every step.

## Rerunning the certificate search

```bash
gcc -O2 -I lib/c -o slicehyb certgen/src/slicehyb.c lib/c/zzn.c -lm
REDUCE=1 GPOOL=1 FOLD=1 SOLS=1 GSEED=pool.txt GDUMP=pool_out.txt TOUT=t11x11.txt \
  ./slicehyb 11 11 certgen/inputs/tset_E.txt certgen/inputs/reps/e11.txt 1 0 > c11x11.txt
```

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

1. `lean/tools/remap_templates.py` renumbers the template indices into `inputs/tset_G.txt`.
2. `lean/tools/cert2c.py` converts the format.
3. `lean/tools/FireGen.lean` adds a fire witness per reflection (`lake env lean --run`).
4. `lean/tools/BaseGen.lean` computes the base file from `inputs/reps/e{W}.txt`.

The result is what `certs/` holds.

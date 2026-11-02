# Lean development: two-colour Zig-Zag Numberlink on rectangles

This is the development tree. The released proof is [`../proof/`](../proof/), exported from here by
`tools/make_proof.py`: there `passes_iff_solvable` comes from kernel-checked certificates
(`passes_iff_solvable_K`, generated into `gen/` by [`../certgen/regen.sh`](../certgen/regen.sh)),
so every result below holds with the standard axioms only. In this tree `ZZN/Main.lean` still
proves it from the 154 `native_decide` checks described below.

The definitions of the statements are in `ZZN/Statement.lean` (instances, paths, solutions, the
catalogue, the plug DP, `solvableB`, `solveZZN`). Everything else is checked by Lean against them.

## Main results

| Theorem | File | Statement | Axioms |
|---|---|---|---|
| `ZZN.passes_iff_solvable` | `ZZN/Main.lean` | both sides ≥ 11: `Passes I ↔ Solvable I` | standard + 154 `native_decide` |
| `ZZN.Thin.thinBF_iff` | `ZZN/Thin/Fast.lean` | the plug DP accepts ↔ solvable (any rectangle; fast when a side is ≤ 10) | standard |
| `ZZN.solvableB_iff` | `ZZN/Thin/Decide.lean` | every rectangle: `solvableB I = true ↔ Solvable I` | standard + 154 `native_decide` |

`Passes` is the forbidden-pattern catalogue test (`ZZN/Catalogue.lean`, `fires3`). The theorems do
not depend on the catalogue being transcribed faithfully: they state equivalence with whatever
`fires3` computes.

## Running time of the decision procedure

`ZZN/Timed/` rewrites the decision procedure `solvableB` with explicit step counts, in the monad
`TimeM` of `ZZN/Timed/TimeM.lean`.

| Theorem | File | Statement | Axioms |
|---|---|---|---|
| `ZZN.T.solvableBT_time` | `ZZN/Timed/Main.lean` | `(solvableBT I).time ≤ Cdec · (R C + R + C + 1)` | standard |
| `ZZN.T.solvableBT_main` | `ZZN/Timed/Main.lean` | well-formed `I`: answer `true` ↔ `Solvable I`, within that bound | standard + 154 `native_decide` |

- **What is trusted.** The cost table in `TimeM.lean`: one step per list element touched, a
  quadratic charge for removing duplicates, and constant time for arithmetic on numbers.
  `checks/timed_lint.py` checks that the counted definitions use only counted list operations.
- **What is proved.** `solvableBT_ret`: the counted procedure returns what `solvableB` returns.
  The catalogue test takes at most `300000 (R + C + 1)` steps (`fires3T_time`). The plug DP takes
  at most `(R C + 1) (Kst b + 2) + Nst b + 1` steps, where `b` is the short side (`thinBFT_time`).
- **The constant.** `Nst b` bounds the number of DP states on a strip of width `b`, by an injective
  encoding of states as numbers (`ThinCount.lean`). It is crude, and `Cdec` is about 10^756. It is
  a constant, so the bound is polynomial, but it says nothing about practical speed.

## The construction and its running time

`ZZN/Constr/` implements the construction (`solveZZN`). It recurses through reductions and band
extension and calls a witness-carrying plug DP on rectangles with a side at most 10 and on
irreducible rectangles (both sides at most 22). Every answer is checked by `solB`.
`ZZN/Timed/Band.lean`, `Lift.lean`, `Solve.lean`, `ThinWit.lean` and `Construct.lean` count its
steps in `TimeM`.

| Theorem | File | Statement | Axioms |
|---|---|---|---|
| `ZZN.solveZZN_sound` | `ZZN/Constr/Main.lean` | an answer `(p, q)` is a solution | standard |
| `ZZN.solveZZN_complete` | `ZZN/Constr/Main.lean` | well-formed and solvable: there is an answer | standard + 154 `native_decide` |
| `ZZN.T.solveZZNT_ret` | `ZZN/Timed/Construct.lean` | the counted construction returns what `solveZZN` returns | standard |
| `ZZN.T.solveZZNT_time` | `ZZN/Timed/Construct.lean` | at most `(w + h + 1) (1100 (M + 1)⁴ + (M² + 1)² Kw 22 + 10)` steps, `M = max w h` | standard |

- The bound is polynomial (degree 5 in `M`). The constant `Kw 22` (about 10^3500) comes from the
  same crude state count `Nst` as `Cdec`, so the bound says nothing about practical speed.
- In practice the plug DP is slow on irreducible rectangles with both sides between 11 and 22: a
  12 × 12 run did not finish.
- The cost table and the lint are those of the decision procedure. `stretchT` and `insBT` charge
  `++` by hand (`gap` has at most two cells; `X ++ _` is charged `|X| + 1`).

The `native_decide` results are 144 box checks (`ZZN/Box/*`, Theorem A's finite case,
`ZZN/Finite.lean`, `ZZN/Finite2.lean`) and 10 window certificates (`ZZN/Cert/*`, Theorem B,
`ZZN/Win*.lean`).

## Building

- `lake build` builds the library `ZZN` (all proofs except the `native_decide` checks).
- `lake build ZZN.Main` adds Theorem B's window certificates (`ZZN/Final.lean`, about 45 min on 4
  threads) and the 144 box checks (`ZZN/Boxes.lean`, about 17 CPU-hours).
- `lake build ZZN.Thin.Decide` builds the decision procedure for every rectangle (needs `ZZN.Main`).
- `lake build ZZN.Timed.Main ZZN.Timed.Construct` builds the step bounds and the construction (needs
  `ZZN.Main`).
- `lake env lean CheckAxioms.lean` prints the axioms of the main results (after the build).

`precompileModules` is set for `ZZN` and `GridHam` in the lakefile. Without it `native_decide` runs
our functions in the interpreter, about 400 times slower. Cap parallelism with
`LEAN_NUM_THREADS=4`; each Lean process needs about 2 GB of private memory.

## Tools (executables)

- `boxcheck`: run or sample a box check (`boxcheck w h [a]`, `boxcheck sample w h stride`).
- `thintime`: time the plug DP on random thin instances against the unverified solver.
- `movecheck`, `movetime`, `soltime`, `symcheck`, `catcheck`, `statecount`: cross-checks and timings
  used during development.

The proof in prose is in [`../PROOF.md`](../PROOF.md); the paper (`../paper/`) describes the
algorithm, the proof structure and the compromises of the formalization.

## License

CC0 1.0 Universal: to the extent possible under law, the author has waived all copyright and
related or neighboring rights to this work. See [`LICENSE`](../LICENSE).

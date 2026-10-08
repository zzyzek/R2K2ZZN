/* SPDX-License-Identifier: CC0-1.0 */
/* To the extent possible under law, the author has waived all copyright and related or
   neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal). */

/*
 * zzn: decide and solve two-colour Zig-Zag Numberlink on rectangles.
 *
 * An instance is an R x C grid of cells (row, col) with endpoints s0, t0 (colour A) and s1, t1
 * (colour B). A solution is two vertex-disjoint paths s0 -> t0 and s1 -> t1 covering every cell.
 * Same algorithm and same results as the Python and JavaScript libraries (docs/ALGORITHM.md).
 *
 *   #include "zzn.h"
 *   zzn_instance in = {12, 12, {0, 0}, {0, 11}, {11, 0}, {11, 11}};
 *   zzn_solution sol;
 *   if (zzn_solve(&in, &sol) == 1) { ... sol.a.cells[i], sol.b.len ...; zzn_solution_free(&sol); }
 */
#ifndef ZZN_H
#define ZZN_H

#ifdef __cplusplus
extern "C" {
#endif

typedef struct { int r, c; } zzn_cell;

typedef struct {
  int R, C;                    /* rows, columns */
  zzn_cell s0, t0, s1, t1;     /* endpoints of colour A (s0, t0) and B (s1, t1) */
} zzn_instance;

typedef struct { zzn_cell *cells; int len; } zzn_path;

typedef struct { zzn_path a, b; } zzn_solution;   /* a: s0 -> t0, b: s1 -> t1 */

/* Status codes. */
enum { ZZN_UNSOLVABLE = 0, ZZN_SOLVED = 1, ZZN_INVALID = -1, ZZN_INTERNAL = -2 };

/* 1 if the four endpoints are distinct cells of the grid (R, C >= 1). */
int zzn_well_formed(const zzn_instance *in);

/* 1 solvable, 0 unsolvable, ZZN_INVALID if the instance is not well formed. */
int zzn_decide(const zzn_instance *in);

/* ZZN_SOLVED (out filled; free with zzn_solution_free), ZZN_UNSOLVABLE, ZZN_INVALID, or
 * ZZN_INTERNAL. The solution is checked before it is returned. */
int zzn_solve(const zzn_instance *in, zzn_solution *out);

/* As zzn_solve; if trace is not NULL, *trace receives a malloc'd text listing the steps
 * (reductions, moves, thin solves), one per line. */
int zzn_solve_trace(const zzn_instance *in, zzn_solution *out, char **trace);

void zzn_solution_free(zzn_solution *sol);

/* Optimized versions for thin instances (a side <= 10): the instance is cut into pieces at guessed
 * splits, well away from the endpoints, and the plug DP runs only on pieces with a short side; if
 * the guesses fail, the plug DP decides. Same results as zzn_decide (exact); the paths can differ
 * from zzn_solve's. Instances with both sides >= 11 use zzn_decide / zzn_solve. */
int zzn_decide_optimized(const zzn_instance *in);
int zzn_solve_optimized(const zzn_instance *in, zzn_solution *out);
int zzn_solve_optimized_trace(const zzn_instance *in, zzn_solution *out, char **trace);

/* The catalogue: the name of an entry that fires ("P", "T1", ..., "R"), or NULL if it passes. */
const char *zzn_fires(int R, int C, zzn_cell s0, zzn_cell t0, zzn_cell s1, zzn_cell t1);

/* A short explanation: which entry fires, or "thin: decided by the plug DP". */
const char *zzn_explain(const zzn_instance *in);

/* 1 if sol solves in. */
int zzn_check_solution(const zzn_instance *in, const zzn_solution *sol);

/* Hamiltonian paths in rectangles (IPS): acceptable(R, C, s, t) is 1 iff an s-t Hamiltonian path
 * exists; hamiltonian_path fills *out (free out->cells) and returns 1, or returns 0. */
int zzn_acceptable(int R, int C, zzn_cell s, zzn_cell t);
int zzn_hamiltonian_path(int R, int C, zzn_cell s, zzn_cell t, zzn_path *out);

/* An ASCII picture (A/B endpoints, a/b path cells); malloc'd, free it. sol may be NULL. */
char *zzn_render(const zzn_instance *in, const zzn_solution *sol);

#ifdef __cplusplus
}
#endif
#endif

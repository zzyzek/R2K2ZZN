/* SPDX-License-Identifier: CC0-1.0 */
/* To the extent possible under law, the author has waived all copyright and related or
   neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal). */

/*
 * Exhaustive test of zzn_solve on one box: every passing instance of an R x C rectangle, one per
 * symmetry class, is solved, and its solution checked (zzn_solve checks it before returning).
 * Classes: unordered pairs {s0,t0}, {s1,t1}, colours interchangeable, and the rectangle's
 * geometric symmetries (4, or 8 if square). Prints how the top level was solved (same-colour
 * split, move, or the exact fallback) and every instance that fails.
 *
 * No reduction applies with both sides at most 12, so on 11x11, 11x12 and 12x12 every passing
 * instance reaches the same-colour split or the move search. These are the boxes where the proof
 * shows each instance solvable directly rather than by a move (docs/PROOF.md, section 5.1).
 *
 * build: cc -O2 -std=c11 -I../c -o boxes boxes.c ../c/zzn.c
 * usage: ./boxes R C [shard nshards]          (boxes.sh runs all three boxes)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "zzn.h"

static int R_, C_;

static int xf(int t, int x) {
  int r = x / C_, c = x % C_, nr, nc;
  switch (t) {
    case 0:  nr = r;          nc = c;          break;
    case 1:  nr = R_ - 1 - r; nc = c;          break;
    case 2:  nr = r;          nc = C_ - 1 - c; break;
    case 3:  nr = R_ - 1 - r; nc = C_ - 1 - c; break;
    case 4:  nr = c;          nc = r;          break;
    case 5:  nr = C_ - 1 - c; nc = r;          break;
    case 6:  nr = c;          nc = R_ - 1 - r; break;
    default: nr = C_ - 1 - c; nc = R_ - 1 - r; break;
  }
  return nr * C_ + nc;
}

/* sort each pair, then order the pairs, so equal classes get equal tuples */
static void norm(int *p) {
  int t;
  if (p[0] > p[1]) { t = p[0]; p[0] = p[1]; p[1] = t; }
  if (p[2] > p[3]) { t = p[2]; p[2] = p[3]; p[3] = t; }
  if ( (p[0] > p[2]) || ((p[0] == p[2]) && (p[1] > p[3])) ) {
    t = p[0]; p[0] = p[2]; p[2] = t;
    t = p[1]; p[1] = p[3]; p[3] = t;
  }
}

static int canonical(const int *p) {
  int ng = ( (R_ == C_) ? 8 : 4 );
  for (int t = 1; t < ng; t++) {
    int q[4];
    for (int i = 0; i < 4; i++) { q[i] = xf(t, p[i]); }
    norm(q);
    for (int i = 0; i < 4; i++) {
      if (q[i] < p[i]) { return 0; }
      if (q[i] > p[i]) { break; }
    }
  }
  return 1;
}

static zzn_cell cell(int x) { zzn_cell c = {x / C_, x % C_}; return c; }

int main(int argc, char **argv) {
  R_ = atoi(argv[1]); C_ = atoi(argv[2]);
  int shard = (argc > 4) ? atoi(argv[3]) : 0, nsh = (argc > 4) ? atoi(argv[4]) : 1;
  int N = R_ * C_;
  long ncanon = 0, nfire = 0, nsame = 0, nmove = 0, nexact = 0, nfail = 0, nother = 0;
  time_t t0 = time(NULL);

  /* a < b is the first pair, c < d the second, with a < c (pairs ordered by first cell) */
  for (int a = 0; a < N; a++) {
    if ((a % nsh) != shard) { continue; }
    for (int b = a + 1; b < N; b++) {
      for (int c = a + 1; c < N; c++) {
        if (c == b) { continue; }
        for (int d = c + 1; d < N; d++) {
          if ( (d == a) || (d == b) ) { continue; }
          int p[4] = {a, b, c, d};
          if (!canonical(p)) { continue; }
          ncanon++;
          zzn_cell s0 = cell(a), t0c = cell(b), s1 = cell(c), t1 = cell(d);
          if (zzn_fires(R_, C_, s0, t0c, s1, t1)) { nfire++; continue; }
          zzn_instance in = {R_, C_, s0, t0c, s1, t1};
          zzn_solution sol;
          char *tr = NULL;
          int st = zzn_solve_trace(&in, &sol, &tr);
          if (st == ZZN_SOLVED) {
            zzn_solution_free(&sol);
            if      (tr && strstr(tr, "  same ")) { nsame++; }
            else if (tr && strstr(tr, "  move ")) { nmove++; }
            else if (tr && strstr(tr, "  exact ")) { nexact++; }
            else                                  { nother++; }
          }
          else {
            nfail++;
            printf("FAIL st=%d %dx%d %d,%d %d,%d %d,%d %d,%d\n", st, R_, C_, s0.r, s0.c, t0c.r, t0c.c,
                   s1.r, s1.c, t1.r, t1.c);
            fflush(stdout);
          }
          free(tr);
        }
      }
    }
    fprintf(stderr, "%dx%d shard %d a=%d/%d canon %ld fails %ld %lds\n", R_, C_, shard, a, N,
            ncanon, nfail, (long)(time(NULL) - t0));
  }
  printf("DONE %dx%d shard %d canon %ld fired %ld passing %ld same %ld move %ld exact %ld other %ld fail %ld secs %ld\n",
         R_, C_, shard, ncanon, nfire, ncanon - nfire, nsame, nmove, nexact, nother, nfail, (long)(time(NULL) - t0));
  return 0;
}

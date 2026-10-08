/* SPDX-License-Identifier: CC0-1.0 */
/* To the extent possible under law, the author has waived all copyright and related or
   neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal). */

/*
 * Command line: decide or solve instances.
 *   zzn R C s0r s0c t0r t0c s1r s1c t1r t1c [--decide] [--grid] [--trace] [--json] [--optimized]
 *   zzn [options] < instances.txt        (one instance per line)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "zzn.h"

static int opt_decide, opt_grid, opt_trace, opt_json, opt_optimized;

static void print_path(const char *name, const zzn_path *p) {
  printf("%s:", name);
  for (int i = 0; i < p->len; i++) printf(" %d,%d", p->cells[i].r, p->cells[i].c);
  printf("\n");
}

static void print_json_path(const zzn_path *p) {
  printf("[");
  for (int i = 0; i < p->len; i++) printf("%s[%d,%d]", i ? "," : "", p->cells[i].r, p->cells[i].c);
  printf("]");
}

static int run(const int *v) {
  zzn_instance in = {v[0], v[1], {v[2], v[3]}, {v[4], v[5]}, {v[6], v[7]}, {v[8], v[9]}};
  if (!zzn_well_formed(&in)) { printf("error: endpoints must be four distinct cells inside the grid\n"); return 2; }
  if (opt_decide) {
    int d = opt_optimized ? zzn_decide_optimized(&in) : zzn_decide(&in);
    if (opt_json) printf("{\"solvable\": %s}\n", d ? "true" : "false");
    else if (d) printf("solvable\n");
    else printf("unsolvable: %s\n", zzn_explain(&in));
    return 0;
  }
  zzn_solution sol;
  char *trace = NULL;
  int r = (opt_optimized ? zzn_solve_optimized_trace : zzn_solve_trace)(&in, &sol, opt_trace ? &trace : NULL);
  if (r == ZZN_INTERNAL) { printf("error: internal\n"); free(trace); return 3; }
  if (opt_json) {
    if (r == ZZN_SOLVED) {
      printf("{\"solvable\": true, \"paths\": [");
      print_json_path(&sol.a); printf(", "); print_json_path(&sol.b); printf("]}\n");
    } else printf("{\"solvable\": false, \"paths\": null}\n");
  } else {
    if (r == ZZN_SOLVED) { printf("solvable\n"); print_path("A", &sol.a); print_path("B", &sol.b); }
    else printf("unsolvable: %s\n", zzn_explain(&in));
    if (trace) fputs(trace, stdout);
    if (opt_grid) {
      char *g = zzn_render(&in, r == ZZN_SOLVED ? &sol : NULL);
      printf("%s\n", g);
      free(g);
    }
  }
  free(trace);
  if (r == ZZN_SOLVED) zzn_solution_free(&sol);
  return 0;
}

int main(int argc, char **argv) {
  int v[10], nv = 0;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "--decide")) opt_decide = 1;
    else if (!strcmp(argv[i], "--grid")) opt_grid = 1;
    else if (!strcmp(argv[i], "--trace")) opt_trace = 1;
    else if (!strcmp(argv[i], "--json")) opt_json = 1;
    else if (!strcmp(argv[i], "--optimized")) opt_optimized = 1;
    else if (!strcmp(argv[i], "-h") || !strcmp(argv[i], "--help")) {
      printf("usage: zzn R C s0r s0c t0r t0c s1r s1c t1r t1c [--decide] [--grid] [--trace] [--json] [--optimized]\n"
             "   or: zzn [options] < instances.txt\n");
      return 0;
    } else if (nv < 10) v[nv++] = atoi(argv[i]);
    else { fprintf(stderr, "too many arguments\n"); return 2; }
  }
  if (nv == 10) return run(v);
  if (nv != 0) { fprintf(stderr, "expected 10 integers\n"); return 2; }
  char line[1024];
  int rc = 0;
  while (fgets(line, sizeof line, stdin)) {
    int n = sscanf(line, "%d %d %d %d %d %d %d %d %d %d", &v[0], &v[1], &v[2], &v[3], &v[4], &v[5], &v[6], &v[7], &v[8], &v[9]);
    if (n <= 0) continue;
    if (n != 10) { printf("error: expected 10 integers\n"); rc = 2; continue; }
    int r = run(v);
    if (r > rc) rc = r;
    fflush(stdout);
  }
  return rc;
}

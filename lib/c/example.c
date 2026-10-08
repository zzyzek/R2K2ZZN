/* SPDX-License-Identifier: CC0-1.0 */
/* To the extent possible under law, the author has waived all copyright and related or
   neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal). */

/* Minimal use of the library: solve one instance and print it. */
#include <stdio.h>
#include <stdlib.h>
#include "zzn.h"

int main(void) {
  zzn_instance in = {12, 12, {0, 0}, {0, 11}, {11, 0}, {11, 11}};
  zzn_solution sol;
  int r = zzn_solve(&in, &sol);
  if (r == ZZN_SOLVED) {
    char *pic = zzn_render(&in, &sol);
    printf("solved: path A has %d cells, path B %d\n%s\n", sol.a.len, sol.b.len, pic);
    free(pic);
    zzn_solution_free(&sol);
  } else if (r == ZZN_UNSOLVABLE) {
    printf("unsolvable: %s\n", zzn_explain(&in));
  }
  zzn_instance bad = {12, 12, {0, 0}, {11, 11}, {0, 11}, {11, 0}};
  printf("decide(bad) = %d (%s)\n", zzn_decide(&bad), zzn_explain(&bad));
  return 0;
}

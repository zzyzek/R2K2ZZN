// Peel + template test. Loads depth-2 templates (tmpl output) and asks, for
// each instance in a file, whether it is matched by a template (under any
// symmetry), or after k peels: one endpoint alone beyond a cut, its path
// covering that side as one IPS rectangle and crossing at any cell y.
//
// usage: peel R C K templates instances
//
#define NO_TMPL_MAIN
#include "tmpl.c"

static int parse(FILE *f, tmpl_t *t) {
  char line[1 << 14];
  if (!fgets(line, sizeof line, f)) { return 0; }
  memset(t, 0, sizeof *t);
  char *p = strchr(line, ':') + 1;
  static const char *AN = "abcdLH";
  while (*p) {
    while (*p == ' ' || *p == '\n') { p++; }
    if (!*p) { break; }
    tnode *nd = &t->nd[t->nn++];
    if (*p == 'I') { nd->leaf = 1; nd->n = 1; p++; continue; }
    nd->axis = ( (*p == 'V') ? 1 : 0 ); p++;
    nd->pa = strchr(AN, *p++) - AN;
    nd->po = strtol(p, &p, 10);
    p++;
    while (*p != ']') {
      int i = nd->n++;
      char k = *p++;
      nd->sa[i] = *p++ - '0';
      if (k == 's') { nd->kind[i] = 0; nd->sb[i] = nd->sa[i]; }
      else if (k == 'c') {
        nd->kind[i] = 1; nd->sb[i] = 1 - nd->sa[i];
        nd->ya[i] = strchr(AN, *p++) - AN; nd->yo[i] = strtol(p, &p, 10);
      }
      else {
        nd->kind[i] = 2; nd->sb[i] = nd->sa[i];
        nd->ya[i] = strchr(AN, *p++) - AN; nd->yo[i] = strtol(p, &p, 10);
        nd->za[i] = strchr(AN, *p++) - AN; nd->zo[i] = strtol(p, &p, 10);
      }
      if (*p == ',') { p++; }
    }
    p++;
  }
  return 1;
}

// Any template under any symmetry (transpose allowed for any box).
//
static int match_any(int R, int C, const cell *c) {
  for (int g = 0; g < 8; g++) {
    int R2 = ( (g & 4) ? C : R ), C2 = ( (g & 4) ? R : C );
    for (int l = 0; l < 8; l++) {
      cell q[4];
      apply_sym(R, C, g, l, c, q);
      piece_t P;
      P.R = R2; P.C = C2; P.n = 2;
      for (int i = 0; i < 4; i++) { P.e[i] = q[i]; }
      set_anchors(R2, C2, q);
      for (int k = 0; k < nT; k++) {
        if (ev(&T[k], 0, &P, 0, 0) == T[k].nn) { return 1; }
      }
    }
  }
  return 0;
}

static long npeel[8];

static int solved(int R, int C, const cell *c, int K) {
  if (match_any(R, C, c)) { return 1; }
  if (K == 0) { return 0; }
  for (int g = 0; g < 8; g++) {
    int R2 = ( (g & 4) ? C : R ), C2 = ( (g & 4) ? R : C );
    cell q[4];
    apply_sym(R, C, g, 0, c, q);
    // endpoint e alone in rows < p; its partner is e ^ 1
    //
    for (int e = 0; e < 4; e++) {
      for (int p = 1; p < R2; p++) {
        int ok = (q[e].r < p);
        for (int j = 0; j < 4; j++) { if ( (j != e) && (q[j].r < p) ) { ok = 0; } }
        if (!ok) { continue; }
        for (int y = 0; y < C2; y++) {
          cell x = { p - 1, y };
          if (!acceptable(p, C2, q[e], x)) { continue; }
          cell r[4];
          for (int j = 0; j < 4; j++) { r[j] = (cell){ q[j].r - p, q[j].c }; }
          r[e] = (cell){ 0, y };
          int dup = 0;
          for (int j = 0; j < 4; j++) { if ( (j != e) && ceq(r[j], r[e]) ) { dup = 1; } }
          if (dup) { continue; }
          if (solved(R2 - p, C2, r, K - 1)) { npeel[K]++; return 1; }
        }
      }
    }
  }
  return 0;
}

#ifndef NO_PEEL_MAIN
int main(int argc, char **argv) {
  int R = atoi(argv[1]), C = atoi(argv[2]), K = atoi(argv[3]);
  FILE *f = fopen(argv[4], "r");
  capT = 4096; T = calloc(capT, sizeof(tmpl_t));
  while (nT < capT && parse(f, &T[nT])) { nT++; }
  fclose(f);
  fprintf(stderr, "%d templates\n", nT);
  f = fopen(argv[5], "r");
  int a[8];
  long n = 0, ok[8] = {0};
  while (fscanf(f, "%d %d %d %d %d %d %d %d", &a[0], &a[1], &a[2], &a[3], &a[4], &a[5], &a[6], &a[7]) == 8) {
    cell c[4];
    for (int i = 0; i < 4; i++) { c[i].r = a[2 * i]; c[i].c = a[2 * i + 1]; }
    n++;
    int k;
    for (k = 0; k <= K; k++) {
      if (solved(R, C, c, k)) { ok[k]++; break; }
    }
    if (k > K) { printf("unsolved %d %d %d %d %d %d %d %d\n", a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7]); }
  }
  printf("%dx%d instances %ld; first solved at peel depth:", R, C, n);
  for (int k = 0; k <= K; k++) { printf(" %d:%ld", k, ok[k]); }
  printf("\n");
  return 0;
}
#endif

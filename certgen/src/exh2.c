// Exhaustive template+peel coverage over the irreducible instances of boxes
// R x C (R <= C), restricted to the symmetry fundamental domain. Irreducible:
// no RedX reduction on either axis (axB, proof/ZZN/Finite.lean). Peel results
// are memoised.
//
// usage: exh2 K templates R C [R C ...]
//
#define NO_PEEL_MAIN
#include "peel.c"

static int Fr(const int *xs, int k) { for (int i = 0; i < 4; i++) { if (xs[i] == k) { return 0; } } return 1; }
static int Bl(const int *xs, int k) { for (int i = 0; i < 4; i++) { if (xs[i] < k) { return 1; } } return 0; }
static int Ab(const int *xs, int k) { for (int i = 0; i < 4; i++) { if (xs[i] > k) { return 1; } } return 0; }

#ifndef FARK
#define FARK 5
#endif
static int redX(int n, const int *xs, int d) {
  if (n < 13) { return 0; }
  if (d == 0) { int ok = 1; for (int i = 0; i < 4; i++) { ok &= Fr(xs, i); } if (ok) { return 1; } }
  if (d + 2 == n) { int ok = 1; for (int i = 0; i < 4; i++) { ok &= Fr(xs, n - 4 + i); } if (ok) { return 1; } }
  for (int lo = 0; lo <= d; lo++) {
    if ( (d + 1 <= lo + 9) && (lo + 10 <= n) && Bl(xs, lo) && Ab(xs, lo + 9) ) {
      int ok = 1;
      for (int i = 0; i < 10; i++) { ok &= Fr(xs, lo + i); }
      if (ok) { return 1; }
    }
  }
  if ( (8 <= d) && (d + 10 <= n) && Fr(xs, d) && Fr(xs, d + 1) &&
       ( ((1 <= d) && Fr(xs, d - 1)) || Fr(xs, d + 2) ) && Bl(xs, d) && Ab(xs, d + 1) ) { return 1; }
  // band compression (RedB, bandGen in proof/ZZN/FiniteB.lean): 5 <= d, d + 7 <= n, every
  // endpoint at least 5 lines from the edge it approaches after deleting d, d+1.
  //
  if ( (5 <= d) && (d + 7 <= n) && Fr(xs, d) && Fr(xs, d + 1) &&
       ( ((1 <= d) && Fr(xs, d - 1)) || Fr(xs, d + 2) ) && Bl(xs, d) && Ab(xs, d + 1) ) {
    int ok = 1;
    for (int i = 0; i < 4; i++) {
      if ( (xs[i] < d) && (n < xs[i] + FARK + 3) ) { ok = 0; }
      if ( (d + 2 <= xs[i]) && (xs[i] < FARK + 2) ) { ok = 0; }
    }
    if (ok) { return 1; }
  }
  return 0;
}

static int axB(int n, const int *xs) {
  for (int d = 0; d < n; d++) { if (redX(n, xs, d)) { return 0; } }
  return 1;
}

static int tuples(int n, int (*out)[4]) {
  int m = 0;
  for (int a = 0; a < n; a++) for (int b = 0; b < n; b++) for (int c = 0; c < n; c++) for (int d = 0; d < n; d++) {
    int xs[4] = { a, b, c, d };
    if (axB(n, xs)) { memcpy(out[m++], xs, sizeof xs); }
  }
  return m;
}

// memo for solved(R, C, c, K)
//
#define MBITS 24
static uint64_t *mkeys;
static uint8_t *mvals;
static long mcount = 0;

static uint64_t mkey(int R, int C, const cell *c, int K) {
  uint64_t k = (uint64_t)R;
  k = k * 32 + C;
  for (int i = 0; i < 4; i++) { k = k * 32 + c[i].r; k = k * 32 + c[i].c; }
  return (k * 8 + K) + 1;
}

static int solved_m(int R, int C, const cell *c, int K);

static int solved2(int R, int C, const cell *c, int K) {
  if (match_any(R, C, c)) { return 1; }
  if (K == 0) { return 0; }
  for (int g = 0; g < 8; g++) {
    int R2 = ( (g & 4) ? C : R ), C2 = ( (g & 4) ? R : C );
    cell q[4];
    apply_sym(R, C, g, 0, c, q);
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
          if (solved_m(R2 - p, C2, r, K - 1)) { return 1; }
        }
      }
    }
  }
  return 0;
}

static int solved_m(int R, int C, const cell *c, int K) {
  uint64_t k = mkey(R, C, c, K), m = (1ull << MBITS) - 1;
  uint64_t i = (k * 0x9E3779B97F4A7C15ull) >> (64 - MBITS);
  while (mkeys[i] && mkeys[i] != k) { i = (i + 1) & m; }
  if (mkeys[i] == k) { return mvals[i]; }
  int v = solved2(R, C, c, K);
  if (mcount < (long)(0.7 * (double)(1ull << MBITS))) {
    i = (k * 0x9E3779B97F4A7C15ull) >> (64 - MBITS);
    while (mkeys[i]) { i = (i + 1) & m; }
    mkeys[i] = k; mvals[i] = (uint8_t)v; mcount++;
  }
  return v;
}

#ifndef NO_EXH2_MAIN
int main(int argc, char **argv) {
  int K = atoi(argv[1]);
  setvbuf(stdout, NULL, _IOLBF, 0);
  FILE *f = fopen(argv[2], "r");
  capT = 1 << 16; T = calloc(capT, sizeof(tmpl_t));
  while (nT < capT && parse(f, &T[nT])) { nT++; }
  fclose(f);
  mkeys = calloc(1ull << MBITS, 8); mvals = calloc(1ull << MBITS, 1);
  int (*X)[4] = malloc(234256 * sizeof *X), (*Y)[4] = malloc(234256 * sizeof *Y);
  for (int a = 3; a + 1 < argc; a += 2) {
    int R = atoi(argv[a]), C = atoi(argv[a + 1]);
    int nx = tuples(R, X), ny = tuples(C, Y);
    long npass = 0, ok[8] = {0}, nun = 0;
    for (int i = 0; i < nx; i++) {
      for (int j = 0; j < ny; j++) {
        cell c[4];
        for (int t = 0; t < 4; t++) { c[t] = (cell){ X[i][t], Y[j][t] }; }
        int dup = 0;
        for (int s = 0; s < 4; s++) for (int t = s + 1; t < 4; t++) { if (ceq(c[s], c[t])) { dup = 1; } }
        if (dup || !fund(R, C, c)) { continue; }
        zzn_cell z[4];
        for (int t = 0; t < 4; t++) { z[t].r = c[t].r; z[t].c = c[t].c; }
        if (zzn_fires(R, C, z[0], z[1], z[2], z[3]) != NULL) { continue; }
        npass++;
        int k;
        for (k = 0; k <= K; k++) { if (solved_m(R, C, c, k)) { ok[k]++; break; } }
        if (k > K) {
          nun++;
          printf("U %d %d %d %d %d %d %d %d %d %d\n", R, C, c[0].r, c[0].c, c[1].r, c[1].c, c[2].r, c[2].c, c[3].r, c[3].c);
        }
      }
    }
    printf("S %dx%d tuples %d x %d passing %ld by peel depth:", R, C, nx, ny, npass);
    for (int k = 0; k <= K; k++) { printf(" %d:%ld", k, ok[k]); }
    printf(" unsolved %ld memo %ld\n", nun, mcount);
  }
  return 0;
}
#endif

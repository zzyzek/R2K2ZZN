// IPS cut trees, generalised: pieces hold up to 3 path segments, and a
// segment may be a single cell (a path entering and leaving at once).
// Leaves: one segment, IPS-acceptable (or a 1x1 piece).
//
// usage: chain3 R C Dmax N seed REL [file]   (file: instances "r c r c r c r c" per line)
//
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "zzn.h"

typedef struct { int r, c; } cell;
typedef unsigned __int128 u128;

static int par(cell v) { return (v.r + v.c) & 1; }
static int ceq(cell a, cell b) { return (a.r == b.r) && (a.c == b.c); }

static int is_corner(int w, int h, cell v) {
  return ( (v.r == 0 || v.r == w - 1) && (v.c == 0 || v.c == h - 1) );
}

// IPS criterion, transcribed from lib/python/zzn/ips.py.
//
static int acceptable(int R, int C, cell s, cell t) {
  int w = R, h = C;
  if (ceq(s, t)) { return R * C == 1; }
  if ((R * C) % 2 == 1) {
    if (par(s) != 0 || par(t) != 0) { return 0; }
  }
  else if (par(s) == par(t)) { return 0; }
  if (w == 1 || h == 1) {
    int isw = (w == 1), bound = ( isw ? h : w );
    cell far = ( isw ? (cell){0, bound - 1} : (cell){bound - 1, 0} );
    cell o = {0, 0};
    return ( (ceq(s, o) && ceq(t, far)) || (ceq(s, far) && ceq(t, o)) );
  }
  if (w == 2 || h == 2) {
    int forb = ( !is_corner(w, h, s) && !is_corner(w, h, t) &&
                 ( ((w == 2) && (s.c == t.c)) || ((h == 2) && (s.r == t.r)) ) );
    return !forb;
  }
  if (w == 3 || h == 3) {
    int isw = (w == 3), opp = ( isw ? h : w );
    if (!( ((opp % 2) == 0) && (par(s) != par(t)) )) { return 1; }
    int c0 = ( isw ? s.c : s.r ), c1 = ( isw ? t.c : t.r ), oc = ( isw ? s.r : s.c );
    int greater = (c1 < c0);
    int dist = ( greater ? c0 - c1 : c1 - c0 );
    int dist_ok = ( (oc == 1) ? (dist > 0) : (dist > 1) );
    int forb = ( dist_ok && ( (greater && (par(s) != 1)) || ((!greater) && (par(s) != 0)) ) );
    return !forb;
  }
  return 1;
}

#define SEGMAX 3

typedef struct { int R, C, n; cell e[2 * SEGMAX + 6]; } piece_t;

// Memo on a 128-bit key; value = (ok depth or 0xff) << 8 | max failed depth.
//
#define HBITS 26
static u128 *hkey;
static uint16_t *hval;
static long nstates = 0, nfull = 0;

static u128 mkkey(const piece_t *P) {
  uint32_t s[SEGMAX];
  for (int i = 0; i < P->n; i++) {
    uint32_t x = P->e[2 * i].r * 32 + P->e[2 * i].c, y = P->e[2 * i + 1].r * 32 + P->e[2 * i + 1].c, t;
    if (x > y) { t = x; x = y; y = t; }
    s[i] = (x << 10) | y;
  }
  for (int i = 0; i < P->n; i++) {
    for (int j = i + 1; j < P->n; j++) {
      if (s[j] < s[i]) { uint32_t t = s[i]; s[i] = s[j]; s[j] = t; }
    }
  }
  u128 k = ((u128)P->R << 7) | ((u128)P->C << 2) | (u128)P->n;
  for (int i = 0; i < P->n; i++) { k = (k << 20) | s[i]; }
  return k + 1;
}

static uint16_t *hfind(u128 k) {
  uint64_t m = (1ull << HBITS) - 1;
  uint64_t h = (uint64_t)k ^ (uint64_t)(k >> 64) * 0xC2B2AE3D27D4EB4Full;
  uint64_t i = (h * 0x9E3779B97F4A7C15ull) >> (64 - HBITS);
  long probes = 0;
  while (hkey[i] && hkey[i] != k) { i = (i + 1) & m; probes++; }
  if (!hkey[i]) {
    if (nstates > (long)(0.7 * (double)(1ull << HBITS))) { nfull = 1; return NULL; }
    hkey[i] = k; hval[i] = 0xff00; nstates++;
  }
  return &hval[i];
}

// Validity: endpoints in range and pairwise distinct, a one-cell segment
// counting its cell once.
//
static int valid(const piece_t *P) {
  cell c[2 * SEGMAX];
  int m = 0;
  for (int i = 0; i < P->n; i++) {
    cell a = P->e[2 * i], b = P->e[2 * i + 1];
    c[m++] = a;
    if (!ceq(a, b)) { c[m++] = b; }
  }
  for (int i = 0; i < m; i++) {
    if (c[i].r < 0 || c[i].c < 0 || c[i].r >= P->R || c[i].c >= P->C) { return 0; }
    for (int j = i + 1; j < m; j++) { if (ceq(c[i], c[j])) { return 0; } }
  }
  return 1;
}

static int parity_ok(const piece_t *P) {
  int bal = ( ((P->R * P->C) % 2 == 1) ? 1 : 0 ), need = 0;
  for (int i = 0; i < P->n; i++) {
    cell a = P->e[2 * i], b = P->e[2 * i + 1];
    if (ceq(a, b))            { need += ( (par(a) == 0) ? 1 : -1 ); }
    else if (par(a) == par(b)) { need += ( (par(a) == 0) ? 1 : -1 ); }
  }
  return need == bal;
}

static int REL = 0;

static int near(int v, int n, const piece_t *P, int along) {
  if (!REL) { return 1; }
  if ( (v <= 1) || (v >= n - 2) ) { return 1; }
  for (int i = 0; i < 2 * P->n; i++) {
    int u = ( along ? P->e[i].r : P->e[i].c );
    if ( (v - u <= 1) && (u - v <= 1) ) { return 1; }
  }
  return 0;
}

static int solve(const piece_t *P, int depth);

static int side(cell v, int axis, int p) { return ( ((axis == 0 ? v.r : v.c) < p) ? 0 : 1 ); }

static cell tr(cell v, int axis, int p, int s) {
  if (s == 0) { return v; }
  return ( (axis == 0) ? (cell){v.r - p, v.c} : (cell){v.r, v.c - p} );
}

static cell cutc(int axis, int p, int s, int y) {
  if (axis == 0) { return ( (s == 0) ? (cell){p - 1, y} : (cell){0, y} ); }
  return ( (s == 0) ? (cell){y, p - 1} : (cell){y, 0} );
}

typedef struct { const piece_t *P; int axis, p, m, depth; piece_t S[2]; int kind[SEGMAX], yy[SEGMAX], zz[SEGMAX]; } cutctx;

static void push(piece_t *S, cell a, cell b) { S->e[2 * S->n] = a; S->e[2 * S->n + 1] = b; S->n++; }

// Choose an option for segment i, then recurse; at the end solve both sides.
//
static int opt(cutctx *X, int i) {
  const piece_t *P = X->P;
  if (i == P->n) {
    if (X->S[0].n == 0 || X->S[1].n == 0) { return 0; }
    if (!valid(&X->S[0]) || !valid(&X->S[1])) { return 0; }
    if (!parity_ok(&X->S[0]) || !parity_ok(&X->S[1])) { return 0; }
    int f = ( (X->S[0].n <= X->S[1].n) ? 0 : 1 );
    if (!solve(&X->S[f], X->depth - 1)) { return 0; }
    return solve(&X->S[1 - f], X->depth - 1);
  }
  cell a = P->e[2 * i], b = P->e[2 * i + 1];
  int sa = side(a, X->axis, X->p), sb = side(b, X->axis, X->p), ax = X->axis, p = X->p;
  piece_t save0 = X->S[0], save1 = X->S[1];
  if (sa != sb) {
    for (int y = 0; y < X->m; y++) {
      if (!near(y, X->m, P, ax)) { continue; }
      X->kind[i] = 1; X->yy[i] = y;
      push(&X->S[sa], tr(a, ax, p, sa), cutc(ax, p, sa, y));
      push(&X->S[sb], cutc(ax, p, sb, y), tr(b, ax, p, sb));
      if ( (X->S[0].n <= SEGMAX) && (X->S[1].n <= SEGMAX) && opt(X, i + 1) ) { return 1; }
      X->S[0] = save0; X->S[1] = save1;
    }
    return 0;
  }
  X->kind[i] = 0;
  push(&X->S[sa], tr(a, ax, p, sa), tr(b, ax, p, sa));
  if ( (X->S[sa].n <= SEGMAX) && opt(X, i + 1) ) { return 1; }
  X->S[0] = save0; X->S[1] = save1;
  int o = 1 - sa;
  for (int y = 0; y < X->m; y++) {
    if (!near(y, X->m, P, ax)) { continue; }
    for (int z = 0; z < X->m; z++) {
      if ( (z == y) || !near(z, X->m, P, ax) ) { continue; }
      X->kind[i] = 2; X->yy[i] = y; X->zz[i] = z;
      push(&X->S[sa], tr(a, ax, p, sa), cutc(ax, p, sa, y));
      push(&X->S[sa], cutc(ax, p, sa, z), tr(b, ax, p, sa));
      push(&X->S[o], cutc(ax, p, o, y), cutc(ax, p, o, z));
      if ( (X->S[0].n <= SEGMAX) && (X->S[1].n <= SEGMAX) && opt(X, i + 1) ) { return 1; }
      X->S[0] = save0; X->S[1] = save1;
    }
  }
  return 0;
}

static long BUDGET = 0, calls = 0;
static int aborted = 0;

static int solve(const piece_t *P, int depth) {
  if (BUDGET && (++calls > BUDGET)) { aborted = 1; return 0; }
  if (P->n == 1) {
    cell a = P->e[0], b = P->e[1];
    if (ceq(a, b)) { return P->R * P->C == 1; }
    return acceptable(P->R, P->C, a, b);
  }
  if (depth <= 0) { return 0; }
  u128 k = mkkey(P);
  uint16_t *v = hfind(k);
  if (v) {
    int okd = *v >> 8, fail = *v & 0xff;
    if (okd != 0xff && okd <= depth) { return 1; }
    if (fail >= depth) { return 0; }
  }
  int res = 0;
  for (int axis = 0; (axis < 2) && !res; axis++) {
    int n = ( (axis == 0) ? P->R : P->C );
    for (int p = 1; (p < n) && !res; p++) {
      if ( REL && !( near(p, n, P, axis == 0) || near(p - 1, n, P, axis == 0) ) ) { continue; }
      cutctx X;
      X.P = P; X.axis = axis; X.p = p; X.m = ( (axis == 0) ? P->C : P->R ); X.depth = depth;
      for (int s = 0; s < 2; s++) {
        X.S[s].n = 0;
        X.S[s].R = ( (axis == 0) ? ( s ? P->R - p : p ) : P->R );
        X.S[s].C = ( (axis == 0) ? P->C : ( s ? P->C - p : p ) );
      }
      res = opt(&X, 0);
    }
  }
  v = ( aborted ? NULL : hfind(k) );
  if (v) {
    if (res) { *v = (uint16_t)((depth << 8) | (*v & 0xff)); }
    else     { *v = (uint16_t)((*v & 0xff00) | depth); }
  }
  return res;
}

// Template text: a position v on a line of length n, relative to the first
// endpoint within 1 of it, else to the low or high boundary.
//
static char *rel(char *o, int v, int n, const piece_t *P, int along) {
  for (int i = 0; i < 2 * P->n; i++) {
    int u = ( along ? P->e[i].r : P->e[i].c );
    if ( (v - u <= 1) && (u - v <= 1) ) { return o + sprintf(o, "e%d%+d", i, v - u); }
  }
  if (v <= n - 1 - v) { return o + sprintf(o, "L%d", v); }
  return o + sprintf(o, "H%d", n - 1 - v);
}

// Write the cut tree found for P at depth into o (memo makes this fast).
//
static char *witness(char *o, const piece_t *P, int depth) {
  if (P->n == 1) { *o++ = 'I'; *o = 0; return o; }
  for (int axis = 0; axis < 2; axis++) {
    int n = ( (axis == 0) ? P->R : P->C );
    for (int p = 1; p < n; p++) {
      if ( REL && !( near(p, n, P, axis == 0) || near(p - 1, n, P, axis == 0) ) ) { continue; }
      cutctx X;
      X.P = P; X.axis = axis; X.p = p; X.m = ( (axis == 0) ? P->C : P->R ); X.depth = depth;
      for (int s = 0; s < 2; s++) {
        X.S[s].n = 0;
        X.S[s].R = ( (axis == 0) ? ( s ? P->R - p : p ) : P->R );
        X.S[s].C = ( (axis == 0) ? P->C : ( s ? P->C - p : p ) );
      }
      if (!opt(&X, 0)) { continue; }
      o += sprintf(o, "%c", ( axis ? 'V' : 'H' ));
      o = rel(o, p, n, P, axis == 0);
      for (int i = 0; i < P->n; i++) {
        if (X.kind[i] == 0) { *o++ = 's'; }
        else if (X.kind[i] == 1) { *o++ = 'c'; o = rel(o, X.yy[i], X.m, P, axis); }
        else { *o++ = 'x'; o = rel(o, X.yy[i], X.m, P, axis); o = rel(o, X.zz[i], X.m, P, axis); }
      }
      piece_t S0 = X.S[0], S1 = X.S[1];
      *o++ = '(';
      o = witness(o, &S0, depth - 1);
      *o++ = ')'; *o++ = '(';
      o = witness(o, &S1, depth - 1);
      *o++ = ')'; *o = 0;
      return o;
    }
  }
  *o++ = '?'; *o = 0;
  return o;
}

static int WIT = 0;

static int run(int R, int C, cell *c, int Dmax) {
  piece_t P;
  P.R = R; P.C = C; P.n = 2;
  for (int i = 0; i < 4; i++) { P.e[i] = c[i]; }
  int d;
  for (d = 1; d <= Dmax; d++) { if (solve(&P, d)) { break; } }
  if (WIT && d <= Dmax) {
    static char buf[1 << 16];
    witness(buf, &P, d);
    printf("T %d %s\n", d, buf);
  }
  return d;
}

int main(int argc, char **argv) {
  int R = atoi(argv[1]), C = atoi(argv[2]), Dmax = atoi(argv[3]);
  long N = atol(argv[4]);
  setvbuf(stdout, NULL, _IOLBF, 0);
  srand(atoi(argv[5]));
  REL = atoi(argv[6]);
  WIT = ( getenv("WIT") != NULL );
  hkey = calloc(1ull << HBITS, sizeof(u128)); hval = calloc(1ull << HBITS, 2);
  long hist[16] = {0}, npass = 0, nmiss = 0;
  if (argc > 7) {
    FILE *f = fopen(argv[7], "r");
    int a[8];
    while (fscanf(f, "%d %d %d %d %d %d %d %d", &a[0], &a[1], &a[2], &a[3], &a[4], &a[5], &a[6], &a[7]) == 8) {
      cell c[4];
      for (int i = 0; i < 4; i++) { c[i].r = a[2 * i]; c[i].c = a[2 * i + 1]; }
      int d = run(R, C, c, Dmax);
      printf("(%d,%d) (%d,%d) (%d,%d) (%d,%d): depth %s%d\n", a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7],
             ( (d > Dmax) ? ">" : "" ), ( (d > Dmax) ? Dmax : d ));
    }
    return 0;
  }
  int n = R * C;
  for (long it = 0; npass < N; it++) {
    int e[4];
    for (int i = 0; i < 4; i++) { e[i] = rand() % n; }
    if (!(e[0] != e[1] && e[0] != e[2] && e[0] != e[3] && e[1] != e[2] && e[1] != e[3] && e[2] != e[3])) { continue; }
    zzn_cell z[4];
    for (int i = 0; i < 4; i++) { z[i].r = e[i] / C; z[i].c = e[i] % C; }
    if (zzn_fires(R, C, z[0], z[1], z[2], z[3]) != NULL) { continue; }
    npass++;
    cell c[4];
    for (int i = 0; i < 4; i++) { c[i].r = z[i].r; c[i].c = z[i].c; }
    int d = run(R, C, c, Dmax);
    hist[d]++;
    if (d > Dmax) {
      nmiss++;
      if (nmiss <= 10) { printf("miss (%d,%d) (%d,%d) (%d,%d) (%d,%d)\n", c[0].r, c[0].c, c[1].r, c[1].c, c[2].r, c[2].c, c[3].r, c[3].c); }
    }
  }
  printf("%dx%d Dmax %d REL %d: passing %ld; min depth:", R, C, Dmax, REL, npass);
  for (int d = 1; d <= Dmax + 1; d++) { printf(" %d:%ld", d, hist[d]); }
  printf("  (%d = miss) states %ld%s\n", Dmax + 1, nstates, ( nfull ? " TABLE FULL" : "" ));
  return 0;
}

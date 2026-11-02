// Online template cover for IPS cut trees.
//
// A template is a cut tree whose cut lines and crossing cells are given as
// (anchor, offset): anchor 0..3 = a coordinate of original endpoint s0 t0 s1 t1
// on that axis, 4 = low boundary 0, 5 = high boundary (the side length).
// Instances are mapped to a symmetry fundamental domain first. Each new
// instance tries the known templates; if none applies, chain3's search finds
// a witness, which becomes a new template.
//
// usage: tmpl R C Dmax N seed [out]
//
#define main chain3_main
#include "chain3.c"
#undef main

typedef struct {
  int axis, pa, po, n, leaf;
  int kind[SEGMAX], sa[SEGMAX], sb[SEGMAX], ya[SEGMAX], yo[SEGMAX], za[SEGMAX], zo[SEGMAX];
} tnode;

#define TMAX 64
typedef struct { int nn; tnode nd[TMAX]; long hits; int depth; } tmpl_t;

static tmpl_t *T;
static int nT = 0, capT = 0;

// Absolute anchor values of the current instance, per axis.
//
static int ANC[2][6];

static void enc(int v, int ax, int *a, int *o) {
  int best = 0, bo = 1 << 20;
  for (int i = 0; i < 6; i++) {
    int d = v - ANC[ax][i];
    if (abs(d) < abs(bo)) { best = i; bo = d; }
  }
  *a = best; *o = bo;
}

static int dec(int a, int o, int ax) { return ANC[ax][a] + o; }

// Witness extraction with absolute coordinates. or_, oc: piece origin.
//
static void wit(tmpl_t *t, const piece_t *P, int depth, int or_, int oc) {
  tnode *nd = &t->nd[t->nn++];
  memset(nd, 0, sizeof *nd);
  nd->n = P->n;
  if (P->n == 1) { nd->leaf = 1; return; }
  for (int axis = 0; axis < 2; axis++) {
    int n = ( (axis == 0) ? P->R : P->C );
    for (int p = 1; p < n; p++) {
      if ( !( near(p, n, P, axis == 0) || near(p - 1, n, P, axis == 0) ) ) { continue; }
      cutctx X;
      X.P = P; X.axis = axis; X.p = p; X.m = ( (axis == 0) ? P->C : P->R ); X.depth = depth;
      for (int s = 0; s < 2; s++) {
        X.S[s].n = 0;
        X.S[s].R = ( (axis == 0) ? ( s ? P->R - p : p ) : P->R );
        X.S[s].C = ( (axis == 0) ? P->C : ( s ? P->C - p : p ) );
      }
      if (!opt(&X, 0)) { continue; }
      int o0 = ( (axis == 0) ? or_ : oc ), o1 = ( (axis == 0) ? oc : or_ );
      nd->axis = axis;
      enc(p + o0, axis, &nd->pa, &nd->po);
      for (int i = 0; i < P->n; i++) {
        nd->kind[i] = X.kind[i];
        nd->sa[i] = side(P->e[2 * i], axis, p);
        nd->sb[i] = side(P->e[2 * i + 1], axis, p);
        if (X.kind[i] >= 1) { enc(X.yy[i] + o1, 1 - axis, &nd->ya[i], &nd->yo[i]); }
        if (X.kind[i] == 2) { enc(X.zz[i] + o1, 1 - axis, &nd->za[i], &nd->zo[i]); }
      }
      piece_t S0 = X.S[0], S1 = X.S[1];
      wit(t, &S0, depth - 1, or_, oc);
      if (axis == 0) { wit(t, &S1, depth - 1, or_ + p, oc); }
      else           { wit(t, &S1, depth - 1, or_, oc + p); }
      return;
    }
  }
  fprintf(stderr, "witness failed\n");
  exit(1);
}

// Evaluate template node k on piece P (origin or_, oc); returns next node
// index, or -1 if the template does not apply.
//
static int CHEAP = 0;
static unsigned char *THIN = NULL;

static int ev(const tmpl_t *t, int k, const piece_t *P, int or_, int oc) {
  const tnode *nd = &t->nd[k];
  if (nd->n != P->n) { return -1; }
  if (nd->leaf) {
    cell a = P->e[0], b = P->e[1];
    // Cheap leaves only: both sides at least 4 (IPS forbidden cases cannot apply).
    //
    if ( CHEAP && ((P->R < 4) || (P->C < 4)) ) { return -1; }
    if ( THIN && ((P->R < 4) || (P->C < 4)) ) { THIN[k] = 1; }
    if (ceq(a, b)) { return ( (P->R * P->C == 1) ? k + 1 : -1 ); }
    return ( acceptable(P->R, P->C, a, b) ? k + 1 : -1 );
  }
  int axis = nd->axis, n = ( (axis == 0) ? P->R : P->C ), m = ( (axis == 0) ? P->C : P->R );
  int o0 = ( (axis == 0) ? or_ : oc ), o1 = ( (axis == 0) ? oc : or_ );
  int p = dec(nd->pa, nd->po, axis) - o0;
  if ( (p < 1) || (p > n - 1) ) { return -1; }
  piece_t S[2];
  for (int s = 0; s < 2; s++) {
    S[s].n = 0;
    S[s].R = ( (axis == 0) ? ( s ? P->R - p : p ) : P->R );
    S[s].C = ( (axis == 0) ? P->C : ( s ? P->C - p : p ) );
  }
  for (int i = 0; i < P->n; i++) {
    cell a = P->e[2 * i], b = P->e[2 * i + 1];
    int sa = side(a, axis, p), sb = side(b, axis, p);
    if ( (sa != nd->sa[i]) || (sb != nd->sb[i]) ) { return -1; }
    if (nd->kind[i] == 0) {
      if (sa != sb) { return -1; }
      push(&S[sa], tr(a, axis, p, sa), tr(b, axis, p, sa));
    }
    else if (nd->kind[i] == 1) {
      int y = dec(nd->ya[i], nd->yo[i], 1 - axis) - o1;
      if ( (sa == sb) || (y < 0) || (y >= m) ) { return -1; }
      push(&S[sa], tr(a, axis, p, sa), cutc(axis, p, sa, y));
      push(&S[sb], cutc(axis, p, sb, y), tr(b, axis, p, sb));
    }
    else {
      int y = dec(nd->ya[i], nd->yo[i], 1 - axis) - o1, z = dec(nd->za[i], nd->zo[i], 1 - axis) - o1;
      if ( (sa != sb) || (y < 0) || (y >= m) || (z < 0) || (z >= m) || (y == z) ) { return -1; }
      push(&S[sa], tr(a, axis, p, sa), cutc(axis, p, sa, y));
      push(&S[sa], cutc(axis, p, sa, z), tr(b, axis, p, sa));
      push(&S[1 - sa], cutc(axis, p, 1 - sa, y), cutc(axis, p, 1 - sa, z));
    }
    if ( (S[0].n > SEGMAX) || (S[1].n > SEGMAX) ) { return -1; }
  }
  for (int s = 0; s < 2; s++) {
    if ( (S[s].n == 0) || !valid(&S[s]) || !parity_ok(&S[s]) ) { return -1; }
  }
  int j = ev(t, k + 1, &S[0], or_, oc);
  if (j < 0) { return -1; }
  return ( (axis == 0) ? ev(t, j, &S[1], or_ + p, oc) : ev(t, j, &S[1], or_, oc + p) );
}

static void set_anchors(int R, int C, const cell *c) {
  for (int i = 0; i < 4; i++) { ANC[0][i] = c[i].r; ANC[1][i] = c[i].c; }
  ANC[0][4] = 0; ANC[0][5] = R;
  ANC[1][4] = 0; ANC[1][5] = C;
}

static int tsame(const tmpl_t *a, const tmpl_t *b) {
  return ( (a->nn == b->nn) && (memcmp(a->nd, b->nd, a->nn * sizeof(tnode)) == 0) );
}

// Symmetry: geometric g (bit0 flip rows, bit1 flip cols, bit2 transpose,
// square grids only) and relabel l (bit0 swap colours, bit1 swap s0/t0,
// bit2 swap s1/t1).
//
static void apply_sym(int R, int C, int g, int l, const cell *in, cell *out) {
  cell q[4];
  for (int i = 0; i < 4; i++) {
    cell v = in[i];
    if (g & 1) { v.r = R - 1 - v.r; }
    if (g & 2) { v.c = C - 1 - v.c; }
    if (g & 4) { int t = v.r; v.r = v.c; v.c = t; }
    q[i] = v;
  }
  if (l & 1) { cell t0 = q[0], t1 = q[1]; q[0] = q[2]; q[1] = q[3]; q[2] = t0; q[3] = t1; }
  if (l & 2) { cell t = q[0]; q[0] = q[1]; q[1] = t; }
  if (l & 4) { cell t = q[2]; q[2] = q[3]; q[3] = t; }
  for (int i = 0; i < 4; i++) { out[i] = q[i]; }
}

static int cdist(int R, int C, cell v) {
  int a = ( (v.r < R - 1 - v.r) ? v.r : R - 1 - v.r ), b = ( (v.c < C - 1 - v.c) ? v.c : C - 1 - v.c );
  return a + b;
}

// Fundamental domain: s0 has the least corner distance, lies in the top-left
// quarter (and on or above the diagonal when square), and s1 precedes t1.
//
static int fund(int R, int C, const cell *c) {
  for (int i = 1; i < 4; i++) { if (cdist(R, C, c[i]) < cdist(R, C, c[0])) { return 0; } }
  if ( (c[0].r > R - 1 - c[0].r) || (c[0].c > C - 1 - c[0].c) ) { return 0; }
  if ( (R == C) && (c[0].r > c[0].c) ) { return 0; }
  return ( (c[2].r * C + c[2].c) < (c[3].r * C + c[3].c) );
}

static int canon(int R, int C, const cell *in, cell *out) {
  int ng = ( (R == C) ? 8 : 4 );
  for (int g = 0; g < ng; g++) {
    for (int l = 0; l < 8; l++) {
      apply_sym(R, C, g, l, in, out);
      if (fund(R, C, out)) { return 1; }
    }
  }
  return 0;
}

static int try_templates(int R, int C, const cell *c) {
  piece_t P;
  P.R = R; P.C = C; P.n = 2;
  for (int i = 0; i < 4; i++) { P.e[i] = c[i]; }
  set_anchors(R, C, c);
  for (int k = 0; k < nT; k++) {
    if (ev(&T[k], 0, &P, 0, 0) == T[k].nn) { T[k].hits++; return k; }
  }
  return -1;
}

static void print_t(FILE *f, const tmpl_t *t) {
  static const char *AN = "abcdLH";
  fprintf(f, "d%d hits %ld :", t->depth, t->hits);
  for (int k = 0; k < t->nn; k++) {
    const tnode *nd = &t->nd[k];
    if (nd->leaf) { fprintf(f, " I"); continue; }
    fprintf(f, " %c%c%+d[", ( nd->axis ? 'V' : 'H' ), AN[nd->pa], nd->po);
    for (int i = 0; i < nd->n; i++) {
      if (i) { fprintf(f, ","); }
      if (nd->kind[i] == 0) { fprintf(f, "s%d", nd->sa[i]); }
      else if (nd->kind[i] == 1) { fprintf(f, "c%d%c%+d", nd->sa[i], AN[nd->ya[i]], nd->yo[i]); }
      else { fprintf(f, "x%d%c%+d%c%+d", nd->sa[i], AN[nd->ya[i]], nd->yo[i], AN[nd->za[i]], nd->zo[i]); }
    }
    fprintf(f, "]");
  }
  fprintf(f, "\n");
}

#ifndef NO_TMPL_MAIN
int main(int argc, char **argv) {
  int R = atoi(argv[1]), C = atoi(argv[2]), Dmax = atoi(argv[3]);
  long N = atol(argv[4]);
  setvbuf(stdout, NULL, _IOLBF, 0);
  srand(atoi(argv[5]));
  REL = 1;
  BUDGET = ( getenv("BUDGET") ? atol(getenv("BUDGET")) : 0 );
  hkey = calloc(1ull << HBITS, sizeof(u128)); hval = calloc(1ull << HBITS, 2);
  long npass = 0, nmiss = 0, nnew = 0;
  int n = R * C;
  for (long it = 0; npass < N; it++) {
    int e[4];
    for (int i = 0; i < 4; i++) { e[i] = rand() % n; }
    if (!(e[0] != e[1] && e[0] != e[2] && e[0] != e[3] && e[1] != e[2] && e[1] != e[3] && e[2] != e[3])) { continue; }
    zzn_cell z[4];
    for (int i = 0; i < 4; i++) { z[i].r = e[i] / C; z[i].c = e[i] % C; }
    if (zzn_fires(R, C, z[0], z[1], z[2], z[3]) != NULL) { continue; }
    cell c0[4], c[4];
    for (int i = 0; i < 4; i++) { c0[i].r = z[i].r; c0[i].c = z[i].c; }
    if (!canon(R, C, c0, c)) { fprintf(stderr, "no canon\n"); return 1; }
    npass++;
    if (try_templates(R, C, c) >= 0) { goto report; }
    {
      piece_t P;
      P.R = R; P.C = C; P.n = 2;
      for (int i = 0; i < 4; i++) { P.e[i] = c[i]; }
      int d;
      calls = 0; aborted = 0;
      for (d = 1; d <= Dmax; d++) { if (solve(&P, d) && !aborted) { break; } if (aborted) { d = Dmax + 1; break; } }
      if (d > Dmax) {
        nmiss++;
        printf("miss (%d,%d) (%d,%d) (%d,%d) (%d,%d)\n", c[0].r, c[0].c, c[1].r, c[1].c, c[2].r, c[2].c, c[3].r, c[3].c);
        goto report;
      }
      if (nT == capT) { capT = ( capT ? 2 * capT : 1024 ); T = realloc(T, capT * sizeof(tmpl_t)); }
      tmpl_t *t = &T[nT];
      memset(t, 0, sizeof *t);
      set_anchors(R, C, c);
      { long b = BUDGET; BUDGET = 0; wit(t, &P, d, 0, 0); BUDGET = b; }
      t->depth = d;
      if (ev(t, 0, &P, 0, 0) != t->nn) { fprintf(stderr, "template does not reproduce\n"); return 1; }
      t->hits = 1;
      nT++; nnew++;
    }
  report:
    if (npass % 50 == 0) {
      printf("passing %ld templates %d miss %ld states %ld%s\n", npass, nT, nmiss, nstates, ( nfull ? " FULL" : "" ));
    }
  }
  if (argc > 6) {
    FILE *f = fopen(argv[6], "w");
    for (int k = 0; k < nT; k++) { print_t(f, &T[k]); }
    fclose(f);
  }
  return 0;
}
#endif

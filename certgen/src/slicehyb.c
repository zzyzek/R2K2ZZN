// Hybrid slice certificates. Per slice (canonical row tuple), instances are the irreducible
// column tuples (band compressions included) that pass or have a passing reflection.
// First fit over (template, symmetry) pairs collects candidates; a greedy cover over the
// candidates orders them. Pairs covering >= THRESH instances become lane checks (PAIR k s);
// the other covered instances become single entries (INST lane k s); unmatched instances
// are solved by the chain search and emitted as their own template (ITREE lane text).
// Lanes that fire with no passing reflection: FIRE lane.
//
// usage: slicehyb R C templates repsfile thresh Dmax   (env BUDGET: search budget)
//
#define NO_EXH2_MAIN
#include "exh2.c"
#include <time.h>
static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static void lab(int l, const int *in, int *out) {
  int q[4] = { in[0], in[1], in[2], in[3] };
  if (l & 1) { int a = q[0], b = q[1]; q[0] = q[2]; q[1] = q[3]; q[2] = a; q[3] = b; }
  if (l & 2) { int t = q[0]; q[0] = q[1]; q[1] = t; }
  if (l & 4) { int t = q[2]; q[2] = q[3]; q[3] = t; }
  memcpy(out, q, sizeof q);
}
static void applyS(int R, int C, int s, const cell *in, cell *out) {
  int xs[4], ys[4], x2[4], y2[4];
  for (int i = 0; i < 4; i++) { xs[i] = ( (s & 1) ? R - 1 - in[i].r : in[i].r ); ys[i] = ( (s & 2) ? C - 1 - in[i].c : in[i].c ); }
  lab(s >> 2, xs, x2); lab(s >> 2, ys, y2);
  for (int i = 0; i < 4; i++) { out[i] = (cell){ x2[i], y2[i] }; }
}
static int matchTS(int R, int C, const cell *c, int k, int s) {
  cell q[4];
  applyS(R, C, s, c, q);
  piece_t P;
  P.R = R; P.C = C; P.n = 2;
  for (int i = 0; i < 4; i++) { P.e[i] = q[i]; }
  set_anchors(R, C, q);
  return ev(&T[k], 0, &P, 0, 0) == T[k].nn;
}
// Bit 5 of s: transpose first (as Lean's Sym.geo), then reflect in the transposed box.
// Used for single entries only; lane checks need no transpose.
//
static int matchTT(int R, int C, const cell *c, int k, int s) {
  cell t[4], q[4];
  for (int i = 0; i < 4; i++) { t[i] = (cell){ c[i].c, c[i].r }; }
  applyS(C, R, s & 31, t, q);
  piece_t P;
  P.R = C; P.C = R; P.n = 2;
  for (int i = 0; i < 4; i++) { P.e[i] = q[i]; }
  set_anchors(C, R, q);
  return ev(&T[k], 0, &P, 0, 0) == T[k].nn;
}
#include "tx.c"

// Candidates are (template << 6) | symmetry; bit 5 = transpose (square boxes only).
// With env FOLD the reflections and the transposition are folded into the template
// (tx.c) on output, so every emitted pair has a label-only symmetry and all pairs of a
// slice share the identity column lanes.
//
#define CK(x) ((x) >> 6)
#define CS(x) ((x) & 63)
#define CE(k, s) (((k) << 6) | (s))
static int NSYM = 32, FOLD = 0, nT0 = 0, MORE = 0, REDUCE = 0;
static long nred = 0;
static int GPOOL = 0, gpool[1 << 20], ngp = 0;
// Membership marks for gpool, indexed by candidate code (capT = 1 << 16 templates, 64 codes each).
//
static unsigned char *ingm(void) { static unsigned char *g = NULL; if (!g) { g = calloc((size_t)(1 << 16) * 64, 1); } return g; }
static int matchAny(int R, int C, const cell *c, int k, int s) {
  return ( (s & 32) ? matchTT(R, C, c, k, s & 31) : matchTS(R, C, c, k, s) );
}
#define FHB 20
static int *fh;
static unsigned long thash(const tmpl_t *t) {
  unsigned long h = 1469598103934665603ul;
  const unsigned char *b = (const unsigned char *)t->nd;
  for (size_t i = 0; i < t->nn * sizeof(tnode); i++) { h = (h ^ b[i]) * 1099511628211ul; }
  return h;
}
// Index of the folded template (k, s); new templates are appended to T.
//
static int foldid(int k, int s) {
  if ((s & 35) == 0) { return k; }
  tmpl_t *u = &T[nT];
  fold(&T[k], s, u);
  unsigned long h = thash(u) & ((1ul << FHB) - 1);
  while (fh[h] >= 0) {
    if (tsame(&T[fh[h]], u)) { return fh[h]; }
    h = (h + 1) & ((1ul << FHB) - 1);
  }
  fh[h] = nT;
  return nT++;
}
static int outsym(int s) { return ( FOLD ? (s & 28) : s ); }
static int outk(int k, int s) { return ( FOLD ? foldid(k, s) : k ); }
static long LEAVES = 0, CHEAPL = 0;
static int lexlt4(const int *a, const int *b) { for (int i = 0; i < 4; i++) { if (a[i] != b[i]) { return a[i] < b[i]; } } return 0; }

static int passImg(int R, int C, const cell *c) {
  for (int g = 0; g < 4; g++) {
    zzn_cell z[4];
    for (int u = 0; u < 4; u++) { z[u].r = (g & 1) ? R - 1 - c[u].r : c[u].r; z[u].c = (g & 2) ? C - 1 - c[u].c : c[u].c; }
    if (!zzn_fires(R, C, z[0], z[1], z[2], z[3])) { return 1; }
  }
  return 0;
}

#ifndef NO_HYB_MAIN
int main(int argc, char **argv) {
  int R = atoi(argv[1]), C = atoi(argv[2]), TH = atoi(argv[5]), Dmax = atoi(argv[6]);
  setvbuf(stdout, NULL, _IOLBF, 0);
  REL = 1;
  BUDGET = ( getenv("BUDGET") ? atol(getenv("BUDGET")) : 0 );
  CHEAP = ( getenv("CHEAP") ? atoi(getenv("CHEAP")) : 0 );
  hkey = calloc(1ull << HBITS, sizeof(u128)); hval = calloc(1ull << HBITS, 2);
  mkeys = calloc(1ull << MBITS, 8); mvals = calloc(1ull << MBITS, 1);
  FILE *f = fopen(argv[3], "r");
  capT = 1 << 16; T = calloc(capT + 1, sizeof(tmpl_t));
  while (nT < capT && parse(f, &T[nT])) { nT++; }
  fclose(f);
  nT0 = nT;
  FOLD = ( getenv("FOLD") ? 1 : 0 );
  MORE = ( getenv("MORE") ? atoi(getenv("MORE")) : 0 );
  REDUCE = ( getenv("REDUCE") ? 1 : 0 );
  GPOOL = ( getenv("GPOOL") ? 1 : 0 );
  // GSEED=file: start the pool from candidate codes CE(k, s) written by GDUMP (base templates
  // only, so codes mean the same in every box).
  //
  if (getenv("GSEED")) {
    FILE *gf = fopen(getenv("GSEED"), "r"); int v;
    while ( (ngp < (1 << 20)) && (fscanf(gf, "%d", &v) == 1) ) {
      if (!ingm()[v]) { ingm()[v] = 1; gpool[ngp++] = v; }
    }
    fclose(gf);
  }
  if (FOLD) { NSYM = 64; }
  fh = malloc(sizeof(int) << FHB); for (int i = 0; i < (1 << FHB); i++) { fh[i] = -1; }
  for (int k = 0; k < nT; k++) { unsigned long h = thash(&T[k]) & ((1ul << FHB) - 1); while (fh[h] >= 0) { h = (h + 1) & ((1ul << FHB) - 1); } fh[h] = k; }
  int (*Y)[4] = malloc(234256 * sizeof *Y);
  int ny = tuples(C, Y);
  static cell IC[240000][4]; static long IL[240000]; static int asg[240000];
  FILE *rf = fopen(argv[4], "r");
  int xs[4]; long ns = 0, sp = 0, si = 0, su = 0, sf = 0, sfail = 0;
  while (fscanf(rf, "%d,%d,%d,%d", &xs[0], &xs[1], &xs[2], &xs[3]) == 4) {
    printf("SLICE %d,%d,%d,%d\n", xs[0], xs[1], xs[2], xs[3]);
    // Row symmetries fixing xs (stabL in proof/ZZN/BoxK/Slice.lean); with the column reflection.
    //
    int stb[16][2], nstb = 0;
    for (int f = 0; f < 2; f++) for (int l = 0; l < 8; l++) {
      int y[4], z[4];
      for (int u = 0; u < 4; u++) { y[u] = ( f ? R - 1 - xs[u] : xs[u] ); }
      lab(l, y, z);
      if (memcmp(z, xs, sizeof z) == 0) { stb[nstb][0] = f; stb[nstb][1] = l; nstb++; }
    }
    int ni = 0;
    for (int jj = 0; jj < ny; jj++) {
      cell c[4];
      for (int u = 0; u < 4; u++) { c[u] = (cell){ xs[u], Y[jj][u] }; }
      int dup = 0;
      for (int a = 0; a < 4; a++) for (int b = a + 1; b < 4; b++) { if (ceq(c[a], c[b])) { dup = 1; } }
      if (dup) { continue; }
      // Column-canonical lanes only (ccV in proof/ZZN/BoxK/Slice.lean): key(y) <= key(C - 1 - y).
      //
      { int lt = 0, gt = 0;
        for (int u = 0; (u < 4) && !lt && !gt; u++) {
          int r = C - 1 - Y[jj][u];
          if      (r < Y[jj][u]) { lt = 1; }
          else if (r > Y[jj][u]) { gt = 1; }
        }
        if (lt) { continue; } }
      // Square box: lanes with key(y) >= key(x) only (trV in proof/ZZN/BoxK/Slice.lean).
      //
      if ( (R == C) && lexlt4(Y[jj], xs) ) { continue; }
      { int skip = 0;
        for (int k = 0; (k < nstb) && !skip; k++) for (int ry = 0; (ry < 2) && !skip; ry++) {
          int y[4], z[4];
          for (int u = 0; u < 4; u++) { y[u] = ( ry ? C - 1 - Y[jj][u] : Y[jj][u] ); }
          lab(stb[k][1], y, z);
          if (lexlt4(z, Y[jj])) { skip = 1; }
        }
        if (skip) { continue; } }
      zzn_cell z[4];
      for (int u = 0; u < 4; u++) { z[u].r = c[u].r; z[u].c = c[u].c; }
      const char *fi = zzn_fires(R, C, z[0], z[1], z[2], z[3]);
      if (fi && strcmp(fi, "P") == 0) { continue; }
      long lane = ((Y[jj][0] * C + Y[jj][1]) * C + Y[jj][2]) * C + Y[jj][3];
      if (fi && !passImg(R, C, c)) { printf("FIRE %ld\n", lane); sf++; continue; }
      memcpy(IC[ni], c, sizeof c); IL[ni] = lane; ni++;
    }
    double t0 = now();
    // first fit: candidate pairs
    static int cand[1 << 16]; int nc = 0;
    for (int a = 0; a < ni; a++) {
      int ok = 0;
      for (int b = 0; b < nc && !ok; b++) { if (matchAny(R, C, IC[a], CK(cand[b]), CS(cand[b]))) { ok = 1; } }
      for (int k = 0; k < nT0 && !ok; k++) for (int s = 0; s < NSYM && !ok; s++) {
        if (matchAny(R, C, IC[a], k, s)) { cand[nc++] = CE(k, s); ok = 1; }
      }
      // MORE=m: keep scanning for up to m further matching pairs, giving the greedy cover
      // more candidates than the first match of each instance.
      //
      if ( ok && (MORE > 0) ) {
        int got = 0;
        for (int k = 0; (k < nT0) && (got < MORE); k++) for (int s = 0; (s < NSYM) && (got < MORE); s++) {
          if (!matchAny(R, C, IC[a], k, s)) { continue; }
          int dup = 0;
          for (int b = 0; (b < nc) && !dup; b++) { if (cand[b] == CE(k, s)) { dup = 1; } }
          if (!dup) { cand[nc++] = CE(k, s); got++; }
        }
      }
      asg[a] = ( ok ? 0 : -1 );
    }
    // GPOOL=1: add every pair chosen by an earlier slice of this box to the candidates.
    // Neighbouring slices share most of their structure, so the box's pool contains pairs
    // that cover many instances at once; first fit alone finds one pair per instance.
    //
    if (GPOOL) {
      static unsigned char *inc = NULL;
      if (!inc) { inc = calloc((size_t)capT * 64, 1); }
      for (int b = 0; b < nc; b++) { inc[cand[b]] = 1; }
      for (int q = 0; q < ngp; q++) {
        if ( !inc[gpool[q]] && (nc < (1 << 16)) ) { inc[gpool[q]] = 1; cand[nc++] = gpool[q]; }
      }
      for (int b = 0; b < nc; b++) { inc[cand[b]] = 0; }
    }
    double t1 = now();
    // greedy over candidates
    unsigned char *cov = calloc((size_t)nc * ni, 1);
    long *cnt = calloc(nc, sizeof(long));
    for (int b = 0; b < nc; b++) for (int a = 0; a < ni; a++) {
      if (asg[a] >= 0 && matchAny(R, C, IC[a], CK(cand[b]), CS(cand[b]))) { cov[(size_t)b * ni + a] = 1; cnt[b]++; }
    }
    for (int a = 0; a < ni; a++) { if (asg[a] >= 0) { asg[a] = -2; } }
    static int rk[1 << 16]; int nrank = 0;
    static int chosen[1 << 16]; int nch = 0;
    for (int b = 0; b < nc; b++) { rk[b] = 1 << 20; }
    for (;;) {
      int best = -1; long bc = 0;
      for (int b = 0; b < nc; b++) { if (cnt[b] > bc) { bc = cnt[b]; best = b; } }
      if (best < 0) { break; }
      rk[best] = nrank++;
      int heavy = ( bc >= TH );
      if ( heavy && !REDUCE ) { printf("PAIR %d %d\n", outk(CK(cand[best]), CS(cand[best])), outsym(CS(cand[best]))); sp++; }
      if (heavy) { chosen[nch++] = best; }
      if (getenv("PAIRCNT")) { fprintf(stderr, "PC %ld\n", bc); }
      if (getenv("LEAFSTAT")) {
        static unsigned char th[256];
        memset(th, 0, sizeof th); THIN = th;
        for (int a = 0; a < ni; a++) {
          if (asg[a] == -2 && cov[(size_t)best * ni + a]) { matchAny(R, C, IC[a], CK(cand[best]), CS(cand[best])); }
        }
        THIN = NULL;
        const tmpl_t *tt = &T[cand[best] >> 5];
        for (int q = 0; q < tt->nn; q++) { if (tt->nd[q].leaf) { LEAVES++; if (!th[q]) { CHEAPL++; } } }
      }
      for (int a = 0; a < ni; a++) {
        if (asg[a] == -2 && cov[(size_t)best * ni + a]) {
          asg[a] = best;
          if (!heavy) { printf("INST %ld %d %d\n", IL[a], outk(CK(cand[best]), CS(cand[best])), outsym(CS(cand[best]))); si++; }
          for (int b = 0; b < nc; b++) { if (cov[(size_t)b * ni + a]) { cnt[b]--; } }
        }
      }
    }
    // REDUCE=1 (with thresh 1): reverse delete. Walk the chosen pairs from the last greedy
    // pick to the first and drop a pair when every instance it covers is covered by another
    // chosen pair. Each emitted pair costs one kernel lane check regardless of how much it covers.
    //
    if (REDUCE) {
      int *cc = calloc(ni, sizeof(int));
      for (int q = 0; q < nch; q++) for (int a = 0; a < ni; a++) {
        if ( (asg[a] >= 0) && cov[(size_t)chosen[q] * ni + a] ) { cc[a]++; }
      }
      for (int q = nch - 1; q >= 0; q--) {
        int b = chosen[q], need = 0;
        for (int a = 0; (a < ni) && !need; a++) {
          if ( (asg[a] >= 0) && cov[(size_t)b * ni + a] && (cc[a] < 2) ) { need = 1; }
        }
        if (need) { continue; }
        for (int a = 0; a < ni; a++) { if ( (asg[a] >= 0) && cov[(size_t)b * ni + a] ) { cc[a]--; } }
        chosen[q] = -1; nred++;
      }
      for (int q = 0; q < nch; q++) {
        if (chosen[q] < 0) { continue; }
        if (GPOOL) {
          if (!ingm()[cand[chosen[q]]]) { ingm()[cand[chosen[q]]] = 1; gpool[ngp++] = cand[chosen[q]]; }
        }
        printf("PAIR %d %d\n", outk(CK(cand[chosen[q]]), CS(cand[chosen[q]])), outsym(CS(cand[chosen[q]]))); sp++;
      }
      free(cc);
    }
    if (getenv("TAILSTAT")) {
      // Instances not covered by the first TAILK greedy pairs: corner/edge structure.
      //
      int K = atoi(getenv("TAILSTAT"));
      static long hist[5][5]; static long tot = 0;
      for (int a = 0; a < ni; a++) {
        if (asg[a] < 0) { continue; }
        int rank = rk[asg[a]];
        if (rank < K) { continue; }
        int nc4 = 0, ne4 = 0;
        for (int u = 0; u < 4; u++) {
          int dr = ( (IC[a][u].r < R - 1 - IC[a][u].r) ? IC[a][u].r : R - 1 - IC[a][u].r );
          int dc = ( (IC[a][u].c < C - 1 - IC[a][u].c) ? IC[a][u].c : C - 1 - IC[a][u].c );
          if ( (dr <= 3) && (dc <= 3) ) { nc4++; }
          if ( (dr <= 0) || (dc <= 0) ) { ne4++; }
        }
        hist[nc4][ne4]++; tot++;
        if (getenv("CFGOUT")) {
          // window configuration: for each corner, endpoints within the k x k window (k = 5)
          //
          int kw = 5, ncor = 0, single = -1;
          for (int cr = 0; cr < 4; cr++) {
            int in = 0;
            for (int u = 0; u < 4; u++) {
              int r = ( (cr & 1) ? R - 1 - IC[a][u].r : IC[a][u].r ), c = ( (cr & 2) ? C - 1 - IC[a][u].c : IC[a][u].c );
              if ( (r < kw) && (c < kw) ) { in++; }
            }
            if (in > 0) { ncor++; single = cr; }
          }
          printf("CFG %d", ncor);
          if (ncor == 1) {
            int far = 1;
            for (int u = 0; u < 4; u++) {
              int r = ( (single & 1) ? R - 1 - IC[a][u].r : IC[a][u].r ), c = ( (single & 2) ? C - 1 - IC[a][u].c : IC[a][u].c );
              if ( (r < kw) && (c < kw) ) { printf(" %d:%d,%d", u, r, c); }
              else if ( (r < kw + 2) && (c < kw + 2) ) { far = 0; }
            }
            printf(" far=%d", far);
          }
          printf("\n");
        }
      }
      if (getenv("TAILLAST")) {
        fprintf(stderr, "tail %ld; rows = endpoints within 3 of a corner (0..4), cols = endpoints on an edge\n", tot);
        for (int i = 0; i < 5; i++) { fprintf(stderr, "  %d: %ld %ld %ld %ld %ld\n", i, hist[i][0], hist[i][1], hist[i][2], hist[i][3], hist[i][4]); }
      }
    }
    free(cov); free(cnt);
    double t2 = now(); int nun = 0, nst = 0;
    // unmatched: solve each
    for (int a = 0; a < ni; a++) {
      if (asg[a] != -1) { continue; }
      cell *c = IC[a];
      int tk = -1, ts = 0;
      for (int k = 0; k < nT0 && tk < 0; k++) for (int s = 0; s < 32 && tk < 0; s++) {
        if (matchTT(R, C, c, k, s)) { tk = k; ts = s; }
      }
      if (tk >= 0) { printf("INST %ld %d %d\n", IL[a], outk(tk, 32 | ts), outsym(32 | ts)); si++; nst++; continue; }
      nun++;
      // With env SOLS: an explicit solution from the library solver (SOL lane P Q, checked in
      // Lean by solF) in place of a cut-tree search.
      //
      if (getenv("SOLS")) {
        zzn_instance zi;
        zi.R = R; zi.C = C;
        zi.s0 = (zzn_cell){ c[0].r, c[0].c }; zi.t0 = (zzn_cell){ c[1].r, c[1].c };
        zi.s1 = (zzn_cell){ c[2].r, c[2].c }; zi.t1 = (zzn_cell){ c[3].r, c[3].c };
        zzn_solution zs;
        if ( (zzn_solve(&zi, &zs) == ZZN_SOLVED) && zzn_check_solution(&zi, &zs) ) {
          printf("SOL %ld [", IL[a]);
          for (int i = 0; i < zs.a.len; i++) { printf("%s(%d, %d)", (i ? ", " : ""), zs.a.cells[i].r, zs.a.cells[i].c); }
          printf("] [");
          for (int i = 0; i < zs.b.len; i++) { printf("%s(%d, %d)", (i ? ", " : ""), zs.b.cells[i].r, zs.b.cells[i].c); }
          printf("]\n");
          zzn_solution_free(&zs); su++; continue;
        }
        printf("UNSOLVED %ld %d %d %d %d %d %d %d %d\n", IL[a], c[0].r, c[0].c, c[1].r, c[1].c, c[2].r, c[2].c, c[3].r, c[3].c);
        sfail++; continue;
      }
      piece_t P;
      P.R = R; P.C = C; P.n = 2;
      for (int i = 0; i < 4; i++) { P.e[i] = c[i]; }
      int d;
      calls = 0; aborted = 0;
      for (d = 1; d <= Dmax; d++) { if (solve(&P, d) && !aborted) { break; } if (aborted) { d = Dmax + 1; break; } }
      if (d > Dmax) {
        printf("UNSOLVED %ld %d %d %d %d %d %d %d %d\n", IL[a], c[0].r, c[0].c, c[1].r, c[1].c, c[2].r, c[2].c, c[3].r, c[3].c);
        sfail++; continue;
      }
      tmpl_t *t = &T[capT];
      memset(t, 0, sizeof *t);
      set_anchors(R, C, c);
      { long b = BUDGET; BUDGET = 0; wit(t, &P, d, 0, 0); BUDGET = b; }
      t->depth = d;
      printf("ITREE %ld ", IL[a]); print_t(stdout, t);
      su++;
    }
    fprintf(stderr, "slice %d,%d,%d,%d: inst %d cand %d tr %d unm %d  firstfit %.1fs greedy %.1fs solve %.1fs\n",
      xs[0], xs[1], xs[2], xs[3], ni, nc, nst, nun, t1 - t0, t2 - t1, now() - t2);
    ns++;
  }
  if (getenv("LEAFSTAT")) { fprintf(stderr, "leaves %ld cheap %ld\n", LEAVES, CHEAPL); }
  if (getenv("TOUT")) { FILE *to = fopen(getenv("TOUT"), "w"); for (int k = 0; k < nT; k++) { print_t(to, &T[k]); } fclose(to); fprintf(stderr, "templates written %d (folded new %d)\n", nT, nT - nT0); }
  if (REDUCE) { fprintf(stderr, "reverse delete removed %ld pairs\n", nred); }
  if (getenv("GDUMP")) { FILE *gf = fopen(getenv("GDUMP"), "w"); for (int q = 0; q < ngp; q++) { fprintf(gf, "%d\n", gpool[q]); } fclose(gf); }
  fprintf(stderr, "slices %ld pairs %ld (%.1f/slice) inst %ld itree %ld fires %ld unsolved %ld\n",
    ns, sp, (double)sp / ns, si, su, sf, sfail);
  return 0;
}
#endif

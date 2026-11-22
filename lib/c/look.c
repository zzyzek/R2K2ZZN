/* SPDX-License-Identifier: CC0-1.0 */
/* To the extent possible under law, the author has waived all copyright and related or
   neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal). */

/*
 * look.c: implementation of look.h, a port of lib/python/zzn/look.py (the Lean leaf solver
 * `lookJ tabAll`). Every function mirrors the one of the same name there, with the same iteration
 * orders and first-match choices, so the C and Python libraries return identical paths. Lean's
 * cell (x, y) is the library's (r, c). Subtraction of naturals truncates at 0 (ns).
 *
 * The table (lib/data/look.json.gz, format in lib/tools/export_look.py) is parsed once by a small
 * reader for the JSON it uses (arrays, objects, integers, strings) into flat arrays below.
 */
#include "look.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <threads.h>
#include <zlib.h>

#ifndef ZZN_LOOK_DATA_DEFAULT
#define ZZN_LOOK_DATA_DEFAULT "look.json.gz"
#endif

/* ------------------------------------------------------------------ basics ---------- */

static void *xrealloc(void *p, size_t n) {
  p = realloc(p, n ? n : 1);
  if (!p) { fprintf(stderr, "zzn: out of memory\n"); exit(1); }
  return p;
}
static int ns(int a, int b) { return a > b ? a - b : 0; }   /* natural-number subtraction, as in Lean */
static int iabs(int a) { return a < 0 ? -a : a; }
static zzn_cell C2(int r, int c) { zzn_cell x; x.r = r; x.c = c; return x; }
static int ceq(zzn_cell a, zzn_cell b) { return a.r == b.r && a.c == b.c; }
static zzn_cell swc(zzn_cell v) { return C2(v.c, v.r); }

#define GROW(arr, n, cap, need) do { if ((need) > (cap)) { (cap) = (need) > 2 * (cap) + 8 ? (need) : 2 * (cap) + 8; \
  (arr) = xrealloc((arr), sizeof(*(arr)) * (size_t)(cap)); } } while (0)

typedef struct { zzn_cell *v; int n, cap; } lp_t;   /* a path */
static void lp_init(lp_t *p) { p->v = NULL; p->n = p->cap = 0; }
static void lp_free(lp_t *p) { free(p->v); lp_init(p); }
static void lp_push(lp_t *p, zzn_cell x) { GROW(p->v, p->n, p->cap, p->n + 1); p->v[p->n++] = x; }
static void lp_append(lp_t *d, const lp_t *s) {
  GROW(d->v, d->n, d->cap, d->n + s->n);
  if (s->n) memcpy(d->v + d->n, s->v, sizeof(zzn_cell) * s->n);
  d->n += s->n;
}
static void lp_rev(lp_t *p) {
  for (int i = 0, j = p->n - 1; i < j; i++, j--) { zzn_cell t = p->v[i]; p->v[i] = p->v[j]; p->v[j] = t; }
}
static void lp_swap(lp_t *p) { for (int i = 0; i < p->n; i++) p->v[i] = swc(p->v[i]); }

/* ------------------------------------------------------------------ the table ------- */

typedef struct { int vert, a, o, k0, nk, left, right; } tnode_t;   /* left/right: node index, -1 leaf */
typedef struct { int len, s, a, o, a2, o2; } tkind_t;               /* len 1 stay, 3 cross, 5 exc */
typedef struct { int rows[4], p0, np, q0, nq; } slice_t;            /* pairs [p0, p0+2np), sols [q0, q0+nq) */
typedef struct { int64_t lane; int n0, n1; size_t off; } sol_t;     /* n0 + n1 path bytes at off */
typedef struct { int sl0, nsl, present; int32_t *first; } box_t;  /* first[16^4]: first slice of a row tuple */
typedef struct { zzn_cell s, t; int c0, nc; } pent_t;
typedef struct { int w, h, e0, ne; } pshape_t;

static struct {
  tnode_t *node; int nnode, cnode;
  tkind_t *kind; int nkind, ckind;
  int *troot; int ntpl, ctpl;
  slice_t *sl; int nsl, csl;
  int64_t *pair; int npair, cpair;
  sol_t *sol; int nsol, csol;
  uint8_t *byte; size_t nbyte, cbyte;
  box_t box[17][17];
  pshape_t *ps; int nps, cps;
  pent_t *pe; int npe, cpe;
  zzn_cell *pc; int npc, cpc;
} D;

static once_flag g_once = ONCE_FLAG_INIT;
static int g_loaded;   /* 1 loaded, -1 failed; written once inside call_once */

/* A reader for the JSON subset of the table. */
typedef struct { const char *s; size_t i, n; int err; } js_t;

static int jpeek(js_t *J) {
  while (J->i < J->n && (J->s[J->i] == ' ' || J->s[J->i] == '\n' || J->s[J->i] == '\r' || J->s[J->i] == '\t')) J->i++;
  return J->i < J->n ? (unsigned char)J->s[J->i] : -1;
}
static void jeat(js_t *J, int c) { if (jpeek(J) != c) J->err = 1; else J->i++; }
static int isdig(int c) { return c >= '0' && c <= '9'; }

/* Elements of an array or object: jeat(J, '['); for (k = 0; jmore(J, ']', &k); ) { ... }. */
static int jmore(js_t *J, int close, int *k) {
  if (J->err) return 0;
  int c = jpeek(J);
  if (c == close) { J->i++; return 0; }
  if (*k > 0) { if (c != ',') { J->err = 1; return 0; } J->i++; }
  (*k)++;
  return 1;
}

static int64_t jint(js_t *J) {
  int neg = 0;
  if (jpeek(J) == '-') { neg = 1; J->i++; }
  if (J->i >= J->n || !isdig((unsigned char)J->s[J->i])) { J->err = 1; return 0; }
  int64_t v = 0;
  while (J->i < J->n && isdig((unsigned char)J->s[J->i])) {
    if (v > 100000000000000000LL) { J->err = 1; return 0; }
    v = 10 * v + (J->s[J->i++] - '0');
  }
  if (J->i < J->n && (J->s[J->i] == '.' || J->s[J->i] == 'e' || J->s[J->i] == 'E')) { J->err = 1; return 0; }
  return neg ? -v : v;
}

/* An int that must fit in an int. */
static int jint32(js_t *J) {
  int64_t v = jint(J);
  if (v < -1000000000 || v > 1000000000) { J->err = 1; return 0; }
  return (int)v;
}

/* A non-negative decimal integer of any size: its bytes 0 .. n-1, least significant first
 * (zero beyond its length), as `decPath` reads them. */
static void jbig(js_t *J, uint8_t *out, int n) {
  jpeek(J);
  size_t d0 = J->i;
  while (J->i < J->n && isdig((unsigned char)J->s[J->i])) J->i++;
  size_t nd = J->i - d0;
  if (nd == 0) { J->err = 1; return; }
  int cap = (int)(nd / 9 + 2), nl = 0;
  uint32_t *l = calloc((size_t)cap, sizeof(uint32_t));
  if (!l) { fprintf(stderr, "zzn: out of memory\n"); exit(1); }
  for (size_t p = d0; p < J->i; ) {
    size_t q = p + 9 < J->i ? p + 9 : J->i;
    uint64_t chunk = 0, mul = 1;
    for (; p < q; p++) { chunk = 10 * chunk + (uint64_t)(J->s[p] - '0'); mul *= 10; }
    uint64_t carry = chunk;
    for (int k = 0; k < nl; k++) { uint64_t t = (uint64_t)l[k] * mul + carry; l[k] = (uint32_t)t; carry = t >> 32; }
    if (carry) l[nl++] = (uint32_t)carry;
  }
  for (int k = 0; k < n; k++) out[k] = k / 4 < nl ? (uint8_t)(l[k / 4] >> (8 * (k % 4))) : 0;
  free(l);
}

static void jstr(js_t *J, char *buf, size_t cap) {
  jeat(J, '"');
  size_t k = 0;
  while (!J->err && J->i < J->n && J->s[J->i] != '"') {
    if (J->s[J->i] == '\\' || k + 1 >= cap) { J->err = 1; return; }
    buf[k++] = J->s[J->i++];
  }
  buf[k] = 0;
  jeat(J, '"');
}

static void jskip(js_t *J) {
  int c = jpeek(J), k = 0;
  char tmp[256];
  if (c == '[') { J->i++; while (jmore(J, ']', &k)) jskip(J); }
  else if (c == '{') { J->i++; while (jmore(J, '}', &k)) { jstr(J, tmp, sizeof tmp); jeat(J, ':'); jskip(J); } }
  else if (c == '"') { J->i++; while (J->i < J->n && J->s[J->i] != '"') J->i += J->s[J->i] == '\\' ? 2 : 1; jeat(J, '"'); }
  else if (c == 't' && J->n - J->i >= 4 && !memcmp(J->s + J->i, "true", 4)) J->i += 4;
  else if (c == 'f' && J->n - J->i >= 5 && !memcmp(J->s + J->i, "false", 5)) J->i += 5;
  else if (c == 'n' && J->n - J->i >= 4 && !memcmp(J->s + J->i, "null", 4)) J->i += 4;
  else { jpeek(J); while (J->i < J->n && J->s[J->i] && strchr("+-.eE0123456789", J->s[J->i])) J->i++; }
}

/* An anchor of `anchors`: 0-3 an endpoint (Python's e[a], negative indices counted from the end),
 * 4 zero, otherwise n. */
static int anchor_of(js_t *J) {
  int a = jint32(J);
  if (a < -4) { J->err = 1; return 0; }
  return a < 0 ? a + 4 : a;
}

static void read_kind(js_t *J) {
  tkind_t K = {0, 0, 0, 0, 0, 0};
  int k = 0;
  jeat(J, '[');
  while (jmore(J, ']', &k)) {
    if (k == 1) K.s = jint(J) != 0;
    else if (k == 2) K.a = anchor_of(J);
    else if (k == 3) K.o = jint32(J);
    else if (k == 4) K.a2 = anchor_of(J);
    else if (k == 5) K.o2 = jint32(J);
    else { J->err = 1; return; }
  }
  K.len = k;
  if (k != 1 && k != 3 && k != 5) J->err = 1;
  GROW(D.kind, D.nkind, D.ckind, D.nkind + 1);
  D.kind[D.nkind++] = K;
}

/* A template: 0 (`CTree.leaf`, -1) or [vert, a, o, kinds, L, R] (a node index, preorder). */
static int read_tree(js_t *J) {
  if (jpeek(J) != '[') { if (jint(J) != 0) J->err = 1; return -1; }
  J->i++;
  GROW(D.node, D.nnode, D.cnode, D.nnode + 1);
  int me = D.nnode++;
  tnode_t T = {0, 0, 0, 0, 0, -1, -1};
  T.vert = jint(J) != 0; jeat(J, ',');
  T.a = anchor_of(J); jeat(J, ',');
  T.o = jint32(J); jeat(J, ',');
  T.k0 = D.nkind;
  int k = 0;
  jeat(J, '[');
  while (jmore(J, ']', &k)) read_kind(J);
  T.nk = D.nkind - T.k0;
  jeat(J, ',');
  T.left = read_tree(J); jeat(J, ',');
  T.right = read_tree(J); jeat(J, ']');
  D.node[me] = T;
  return me;
}

static void read_slice(js_t *J) {
  slice_t S = {{0, 0, 0, 0}, D.npair, 0, D.nsol, 0};
  int m;
  jeat(J, '[');
  m = 0; jeat(J, '[');
  while (jmore(J, ']', &m)) { int v = jint32(J); if (m > 4) J->err = 1; else S.rows[m - 1] = v; }
  if (m != 4) J->err = 1;
  jeat(J, ',');
  m = 0; jeat(J, '[');
  while (jmore(J, ']', &m)) { GROW(D.pair, D.npair, D.cpair, D.npair + 1); D.pair[D.npair++] = jint(J); }
  if (m % 2) J->err = 1;
  S.np = m / 2;
  jeat(J, ',');
  m = 0; jeat(J, '[');
  while (jmore(J, ']', &m)) {
    sol_t E;
    jeat(J, '[');
    E.lane = jint(J); jeat(J, ',');
    int n0 = jint32(J); jeat(J, ',');
    E.n0 = n0 < 0 ? 0 : n0;
    if (E.n0 > (1 << 20)) { J->err = 1; return; }
    E.off = D.nbyte;
    GROW(D.byte, D.nbyte, D.cbyte, D.nbyte + (size_t)E.n0);
    jbig(J, D.byte + D.nbyte, E.n0); D.nbyte += (size_t)E.n0; jeat(J, ',');
    int n1 = jint32(J); jeat(J, ',');
    E.n1 = n1 < 0 ? 0 : n1;
    if (E.n1 > (1 << 20)) { J->err = 1; return; }
    GROW(D.byte, D.nbyte, D.cbyte, D.nbyte + (size_t)E.n1);
    jbig(J, D.byte + D.nbyte, E.n1); D.nbyte += (size_t)E.n1;
    jeat(J, ']');
    GROW(D.sol, D.nsol, D.csol, D.nsol + 1);
    D.sol[D.nsol++] = E;
  }
  S.nq = D.nsol - S.q0;
  jeat(J, ']');
  GROW(D.sl, D.nsl, D.csl, D.nsl + 1);
  D.sl[D.nsl++] = S;
}

static void read_boxes(js_t *J) {
  int k = 0;
  char key[64];
  jeat(J, '{');
  while (jmore(J, '}', &k)) {
    int w, h, m = 0;
    char tail;
    jstr(J, key, sizeof key);
    jeat(J, ':');
    if (J->err) return;
    if (sscanf(key, "%dx%d%c", &w, &h, &tail) != 2 || !(11 <= w && w <= h && h <= 16)) { jskip(J); continue; }
    box_t *B = &D.box[w][h];
    B->sl0 = D.nsl; B->present = 1;
    jeat(J, '[');
    while (jmore(J, ']', &m)) read_slice(J);
    B->nsl = D.nsl - B->sl0;
  }
}

static void read_prime(js_t *J) {
  int k = 0;
  jeat(J, '[');
  while (jmore(J, ']', &k)) {
    pshape_t P;
    int m = 0;
    jeat(J, '[');
    P.w = jint32(J); jeat(J, ',');
    P.h = jint32(J); jeat(J, ',');
    P.e0 = D.npe;
    jeat(J, '[');
    while (jmore(J, ']', &m)) {
      pent_t E;
      int v[4], q = 0;
      jeat(J, '[');
      for (int i = 0; i < 4; i++) { v[i] = jint32(J); jeat(J, ','); }
      E.s = C2(v[0], v[1]); E.t = C2(v[2], v[3]);
      E.c0 = D.npc;
      jeat(J, '[');
      while (jmore(J, ']', &q)) {
        int x = jint32(J);
        if (q % 2) { GROW(D.pc, D.npc, D.cpc, D.npc + 1); D.pc[D.npc].r = x; }
        else { D.pc[D.npc].c = x; D.npc++; }
      }
      if (q % 2) J->err = 1;
      E.nc = D.npc - E.c0;
      jeat(J, ']');
      GROW(D.pe, D.npe, D.cpe, D.npe + 1);
      D.pe[D.npe++] = E;
    }
    P.ne = D.npe - P.e0;
    jeat(J, ']');
    GROW(D.ps, D.nps, D.cps, D.nps + 1);
    D.ps[D.nps++] = P;
  }
}

/* Parse the whole document; NULL on success, else what is wrong. */
static const char *parse_all(js_t *J) {
  int k = 0, have_fmt = 0, have_t = 0, have_b = 0, have_p = 0;
  char key[64], fmt[64];
  jeat(J, '{');
  while (jmore(J, '}', &k)) {
    jstr(J, key, sizeof key);
    jeat(J, ':');
    if (J->err) break;
    if (!strcmp(key, "format")) { jstr(J, fmt, sizeof fmt); have_fmt = 1; }
    else if (!strcmp(key, "templates")) {
      int m = 0;
      D.ntpl = 0;
      jeat(J, '[');
      while (jmore(J, ']', &m)) { int r = read_tree(J); GROW(D.troot, D.ntpl, D.ctpl, D.ntpl + 1); D.troot[D.ntpl++] = r; }
      have_t = 1;
    }
    else if (!strcmp(key, "boxes")) { read_boxes(J); have_b = 1; }
    else if (!strcmp(key, "prime")) { D.nps = 0; read_prime(J); have_p = 1; }
    else jskip(J);
  }
  if (J->err) return "malformed JSON";
  if (!have_fmt || strcmp(fmt, "zzn-look-1")) return "unknown look data format";
  if (!have_t || !have_b || !have_p) return "missing fields";
  for (int w = 11; w <= 16; w++)
    for (int h = w; h <= 16; h++) if (!D.box[w][h].present) return "missing box";
  for (int w = 11; w <= 16; w++)
    for (int h = w; h <= 16; h++)
      for (int i = 0; i < D.box[w][h].nsl; i++) {
        const slice_t *S = &D.sl[D.box[w][h].sl0 + i];
        for (int j = 0; j < S->np; j++) {
          int64_t t = D.pair[S->p0 + 2 * j];
          if (t < 0 || t >= D.ntpl) return "template id out of range";
        }
      }
  return NULL;
}

static void build_index(void) {
  for (int w = 11; w <= 16; w++)
    for (int h = w; h <= 16; h++) {
      box_t *B = &D.box[w][h];
      B->first = xrealloc(NULL, sizeof(int32_t) * 65536);
      for (int i = 0; i < 65536; i++) B->first[i] = -1;
      for (int i = 0; i < B->nsl; i++) {
        const int *x = D.sl[B->sl0 + i].rows;
        int ok = 1;

        /* Rows outside 0..15 never equal the rows of an instance with sides <= 16. */
        for (int j = 0; j < 4; j++) if (x[j] < 0 || x[j] > 15) ok = 0;
        if (!ok) continue;
        int key = ((x[0] * 16 + x[1]) * 16 + x[2]) * 16 + x[3];
        if (B->first[key] < 0) B->first[key] = i;
      }
    }
}

static void load_once(void) {
  const char *path = getenv("ZZN_LOOK_DATA");
  if (!path || !*path) path = ZZN_LOOK_DATA_DEFAULT;
  gzFile f = gzopen(path, "rb");
  if (!f) { fprintf(stderr, "zzn: cannot open the lookup table %s (set ZZN_LOOK_DATA)\n", path); g_loaded = -1; return; }
  char *buf = NULL;
  size_t n = 0, cap = 0;
  for (;;) {
    GROW(buf, n, cap, n + (1 << 20));
    int r = gzread(f, buf + n, (unsigned)(cap - n));
    if (r < 0) { fprintf(stderr, "zzn: cannot read the lookup table %s\n", path); gzclose(f); free(buf); g_loaded = -1; return; }
    if (r == 0) break;
    n += (size_t)r;
  }
  gzclose(f);
  js_t J = {buf, 0, n, 0};
  const char *e = parse_all(&J);
  free(buf);
  if (e) { fprintf(stderr, "zzn: bad lookup table %s: %s\n", path, e); g_loaded = -1; return; }
  build_index();
  g_loaded = 1;
}

int zzn_look_load(void) {
  call_once(&g_once, load_once);
  return g_loaded == 1 ? 0 : -1;
}

/* ------------------------------------------------------------------ symmetries ------ */

typedef zzn_instance inst_t;

#define S_TR(k) (((k) >> 5) & 1)
#define S_RX(k) (((k) >> 4) & 1)
#define S_RY(k) (((k) >> 3) & 1)
#define S_R0(k) (((k) >> 2) & 1)
#define S_R1(k) (((k) >> 1) & 1)
#define S_SW(k) ((k) & 1)

static inst_t transpose(inst_t I) {
  inst_t J = {I.C, I.R, swc(I.s0), swc(I.t0), swc(I.s1), swc(I.t1)};
  return J;
}
static zzn_cell refl_x(int w, zzn_cell v) { return C2(ns(ns(w, 1), v.r), v.c); }
static inst_t reflect_x(inst_t I) {
  inst_t J = {I.R, I.C, refl_x(I.R, I.s0), refl_x(I.R, I.t0), refl_x(I.R, I.s1), refl_x(I.R, I.t1)};
  return J;
}
static inst_t reflect_y(inst_t I) { return transpose(reflect_x(transpose(I))); }
static inst_t rev0(inst_t I) { inst_t J = {I.R, I.C, I.t0, I.s0, I.s1, I.t1}; return J; }
static inst_t rev1(inst_t I) { inst_t J = {I.R, I.C, I.s0, I.t0, I.t1, I.s1}; return J; }
static inst_t swap_colors(inst_t I) { inst_t J = {I.R, I.C, I.s1, I.t1, I.s0, I.t0}; return J; }

static inst_t sym_geo(int k, inst_t I) {
  inst_t I1 = S_TR(k) ? transpose(I) : I;
  inst_t I2 = S_RX(k) ? reflect_x(I1) : I1;
  return S_RY(k) ? reflect_y(I2) : I2;
}
static inst_t sym_lab(int k, inst_t I) {
  inst_t I3 = S_R0(k) ? rev0(I) : I;
  inst_t I4 = S_R1(k) ? rev1(I3) : I3;
  return S_SW(k) ? swap_colors(I4) : I4;
}
static inst_t apply_sym(int k, inst_t I) { return sym_lab(k, sym_geo(k, I)); }

static void un_lab(int k, lp_t s[2]) {
  if (S_SW(k)) { lp_t t = s[0]; s[0] = s[1]; s[1] = t; }
  if (S_R1(k)) lp_rev(&s[1]);
  if (S_R0(k)) lp_rev(&s[0]);
}

/* `unRy`: swap, reflX hh, swap, i.e. y -> hh - 1 - y. */
static void un_ry(int hh, lp_t *p) {
  for (int i = 0; i < p->n; i++) {
    zzn_cell u = refl_x(hh, swc(p->v[i]));
    p->v[i] = swc(u);
  }
}

static void un_geo(int k, inst_t J, lp_t s[2]) {
  inst_t I1 = S_TR(k) ? transpose(J) : J;
  inst_t I2 = S_RX(k) ? reflect_x(I1) : I1;
  if (S_RY(k)) { un_ry(I2.C, &s[0]); un_ry(I2.C, &s[1]); }
  if (S_RX(k))
    for (int j = 0; j < 2; j++) for (int i = 0; i < s[j].n; i++) s[j].v[i] = refl_x(I1.R, s[j].v[i]);
  if (S_TR(k)) { lp_swap(&s[0]); lp_swap(&s[1]); }
}

/* `unSym σ J s = unGeo σ J (unLab σ s)`: from a solution of `σ.apply J`, one of J (in place). */
static void un_sym(int k, inst_t J, lp_t s[2]) { un_lab(k, s); un_geo(k, J, s); }

/* ------------------------------------------------------------------ canonical form -- */

static void rows_of(const inst_t *I, int x[4]) { x[0] = I->s0.r; x[1] = I->t0.r; x[2] = I->s1.r; x[3] = I->t1.r; }
static void cols_of(const inst_t *I, int x[4]) { x[0] = I->s0.c; x[1] = I->t0.c; x[2] = I->s1.c; x[3] = I->t1.c; }
static uint64_t key_r(const int x[4]) {
  return (((uint64_t)x[0] * 32 + (uint64_t)x[1]) * 32 + (uint64_t)x[2]) * 32 + (uint64_t)x[3];
}
static uint64_t key2(const inst_t *K) {
  int r[4], c[4];
  rows_of(K, r); cols_of(K, c);
  return key_r(r) * ((uint64_t)1 << 20) + key_r(c);
}
static int64_t idx(int w, const int x[4]) {
  return (((int64_t)x[0] * w + x[1]) * w + x[2]) * w + x[3];
}

/* `argminS (fun σ => key2 (σ.apply J)) (Gbox J.w J.h)`: the first symmetry of least key; Gbox is
 * `allSym` (indices 0..63) on a square box, else `G32` (no transposition: 0..31). */
static int canon_sym(inst_t J) {
  int n = J.R == J.C ? 64 : 32, b = 0;
  inst_t K = apply_sym(0, J);
  uint64_t fb = key2(&K);
  for (int c = 1; c < n; c++) {
    K = apply_sym(c, J);
    uint64_t fc = key2(&K);
    if (fc < fb) { b = c; fb = fc; }
  }
  return b;
}

/* ------------------------------------------------------------------ templates ------- */

/* The endpoint coordinates and sides that instantiate a template (`inst_of`): positions are
 * computed on demand from the template node, which is the same as instantiating the tree first. */
typedef struct { int er[4], ec[4], R, C; } ictx_t;

static int off_n(int a, int o) { return o >= 0 ? a + o : ns(a, -o); }
static int anchors(const int *e, int n, int a) { return a <= 3 ? e[a] : (a == 4 ? 0 : n); }
static int pos_n(const int *e, int n, int a, int o) { return off_n(anchors(e, n, a), o); }
static int fR(const ictx_t *X, int a, int o) { return pos_n(X->er, X->R, a, o); }
static int fC(const ictx_t *X, int a, int o) { return pos_n(X->ec, X->C, a, o); }

static int node_pos(const ictx_t *X, const tnode_t *T) { return T->vert ? fC(X, T->a, T->o) : fR(X, T->a, T->o); }

/* `instK`: the crossings of a kind, on the axis other than the cut's. */
static void kind_yz(const ictx_t *X, int vert, const tkind_t *k, int *y, int *z) {
  *y = *z = 0;
  if (k->len >= 3) *y = vert ? fR(X, k->a, k->o) : fC(X, k->a, k->o);
  if (k->len == 5) *z = vert ? fR(X, k->a2, k->o2) : fC(X, k->a2, k->o2);
}

static void ictx_of(const inst_t *I, ictx_t *X) { rows_of(I, X->er); cols_of(I, X->ec); X->R = I->R; X->C = I->C; }

/* `cutc`: the crossing cell at y along the cut, on side s. */
static zzn_cell cutc(int vert, int pos, int s, int y) {
  int x = s ? pos : ns(pos, 1);
  return vert ? C2(y, x) : C2(x, y);
}

typedef struct { zzn_cell a, b; } pr_t;
typedef struct { pr_t *v; int n, cap; } prs_t;
static void prs_free(prs_t *p) { free(p->v); p->v = NULL; p->n = p->cap = 0; }

/* `put`: append (a, b) to side s. */
static void put(int s, zzn_cell a, zzn_cell b, prs_t *L, prs_t *R) {
  prs_t *d = s ? R : L;
  GROW(d->v, d->n, d->cap, d->n + 1);
  d->v[d->n].a = a; d->v[d->n].b = b; d->n++;
}

/* `split`: 0 (None) if the kinds and segments differ in number, else 1 with L, R filled. */
static int split(const ictx_t *X, const tnode_t *T, int pos, const prs_t *ss, prs_t *L, prs_t *R) {
  L->v = R->v = NULL; L->n = L->cap = R->n = R->cap = 0;
  if (T->nk != ss->n) return 0;
  for (int i = 0; i < T->nk; i++) {
    const tkind_t *k = &D.kind[T->k0 + i];
    zzn_cell a = ss->v[i].a, b = ss->v[i].b;
    int s = k->s, y, z;
    kind_yz(X, T->vert, k, &y, &z);
    if (k->len == 1) put(s, a, b, L, R);
    else if (k->len == 3) {
      put(s, a, cutc(T->vert, pos, s, y), L, R);
      put(!s, cutc(T->vert, pos, !s, y), b, L, R);
    } else {
      put(s, a, cutc(T->vert, pos, s, y), L, R);
      put(s, cutc(T->vert, pos, s, z), b, L, R);
      put(!s, cutc(T->vert, pos, !s, y), cutc(T->vert, pos, !s, z), L, R);
    }
  }
  return 1;
}

typedef struct { int ox, oy, pw, ph; prs_t segs; } piece_t;   /* segs borrowed */

static piece_t piece_lo(const piece_t *P, int vert, int pos, prs_t L) {
  piece_t Q = *P;
  if (vert) Q.ph = ns(pos, P->oy); else Q.pw = ns(pos, P->ox);
  Q.segs = L;
  return Q;
}
static piece_t piece_hi(const piece_t *P, int vert, int pos, prs_t R) {
  piece_t Q = *P;
  if (vert) { Q.oy = pos; Q.ph = ns(P->oy + P->ph, pos); }
  else { Q.ox = pos; Q.pw = ns(P->ox + P->pw, pos); }
  Q.segs = R;
  return Q;
}
static int inside(int vert, int pos, const piece_t *P) {
  return vert ? (P->oy < pos && pos < P->oy + P->ph) : (P->ox < pos && pos < P->ox + P->pw);
}
static int region_b(const piece_t *P, zzn_cell v) {
  return P->ox <= v.r && v.r < P->ox + P->pw && P->oy <= v.c && v.c < P->oy + P->ph;
}

/* `Lane.accB`: IPS acceptability, as written there. */
static int acc_b(int w, int h, zzn_cell s, zzn_cell t) {
  int ps = (s.r + s.c) % 2 == 1, pt = (t.r + t.c) % 2 == 1;
  int ow = w % 2 == 1, oh = h % 2 == 1;
  int cc = (ow && oh) ? (!ps && !pt) : (ps != pt);
  int w1 = ns(w, 1), h1 = ns(h, 1);
#define CORNER(v) (((v).r == 0 || (v).r == w1) && ((v).c == 0 || (v).c == h1))
  int isW1 = w == 1;
  int fx = isW1 ? 0 : w1, fy = isW1 ? h1 : 0;
  int f1 = !((s.r == 0 && s.c == 0 && t.r == fx && t.c == fy) || (s.r == fx && s.c == fy && t.r == 0 && t.c == 0));
  int f2 = !CORNER(s) && !CORNER(t) && ((w == 2 && s.c == t.c) || (h == 2 && s.r == t.r));
#undef CORNER
  int isW3 = w == 3;
  int opp_odd = isW3 ? oh : ow;
  int c0 = isW3 ? s.c : s.r, c1 = isW3 ? t.c : t.r, oc = isW3 ? s.r : s.c;
  int gr = c1 < c0;
  int dist = gr ? ns(c0, c1) : ns(c1, c0);
  int dsat = oc == 1 ? 0 < dist : 1 < dist;
  int f3 = !opp_odd && (ps != pt) && dsat && ((gr && !ps) || (!gr && ps));
  int forb;
  if (w == 1 || h == 1) forb = f1;
  else if (w == 2 || h == 2) forb = f2;
  else if (w == 3 || h == 3) forb = f3;
  else forb = 0;
  return cc && !forb;
}

/* `leafOK`: one pair, a single cell or an IPS-acceptable rectangle. */
static int leaf_ok(const piece_t *P) {
  if (P->segs.n != 1) return 0;
  zzn_cell a = P->segs.v[0].a, b = P->segs.v[0].b;
  if (ceq(a, b)) return P->pw == 1 && P->ph == 1 && ceq(a, C2(P->ox, P->oy));
  return region_b(P, a) && region_b(P, b) &&
         acc_b(P->pw, P->ph, C2(ns(a.r, P->ox), ns(a.c, P->oy)), C2(ns(b.r, P->ox), ns(b.c, P->oy)));
}

/* `check`, on the template node t (-1: leaf) instantiated by X. */
static int check(const ictx_t *X, int t, const piece_t *P) {
  if (t < 0) return leaf_ok(P);
  const tnode_t *T = &D.node[t];
  int pos = node_pos(X, T);
  if (!inside(T->vert, pos, P)) return 0;
  prs_t L, R;
  if (!split(X, T, pos, &P->segs, &L, &R)) { prs_free(&L); prs_free(&R); return 0; }
  piece_t lo = piece_lo(P, T->vert, pos, L), hi = piece_hi(P, T->vert, pos, R);
  int ok = check(X, T->left, &lo) && check(X, T->right, &hi);
  prs_free(&L); prs_free(&R);
  return ok;
}

static piece_t root_piece(const inst_t *I, pr_t two[2]) {
  piece_t P;
  P.ox = 0; P.oy = 0; P.pw = I->R; P.ph = I->C;
  two[0].a = I->s0; two[0].b = I->t0; two[1].a = I->s1; two[1].b = I->t1;
  P.segs.v = two; P.segs.n = P.segs.cap = 2;
  return P;
}

/* `tcheck`: the instantiated template t checks on I. */
static int tcheck(int t, const inst_t *I) {
  ictx_t X;
  pr_t two[2];
  ictx_of(I, &X);
  piece_t P = root_piece(I, two);
  return check(&X, t, &P);
}

/* ------------------------------------------------------------------ the constructive IPS path */

static void ips_p(int n, int w, int h, zzn_cell s, zzn_cell t, lp_t *out);

/* `colSeg`: (c, lo + k), ..., (c, lo), appended. */
static void col_seg(int c, int lo, int k, lp_t *out) { for (int j = k; j >= 0; j--) lp_push(out, C2(c, lo + j)); }

/* `rightDetour`, appended (reversed if rev). */
static void right_detour(int w, int h, int y, int rev, lp_t *out) {
  lp_t d, m;
  lp_init(&d); lp_init(&m);
  col_seg(w, 0, y, &d);
  col_seg(w + 1, 0, ns(h, 1), &m); lp_rev(&m); lp_append(&d, &m);
  col_seg(w, y + 1, ns(ns(h, 1), y + 1), &d);
  if (rev) lp_rev(&d);
  lp_append(out, &d);
  lp_free(&d); lp_free(&m);
}

/* `stripRightP`, in place. */
static void strip_right_p(int width, int height, lp_t *p) {
  int X = ns(width, 3), i;
  for (i = 0; i + 1 < p->n; i++) if (p->v[i].r == X && p->v[i + 1].r == X) break;
  if (i + 1 >= p->n) return;
  zzn_cell a = p->v[i], b = p->v[i + 1];
  lp_t q;
  lp_init(&q);
  for (int j = 0; j <= i; j++) lp_push(&q, p->v[j]);
  if (b.c == a.c + 1) right_detour(ns(width, 2), height, a.c, 0, &q);

  /* reverse(reverse l2 + [b] + rightDetour(.., b.y) + [a] + reverse l1) = l1 + [a] + reverse(rightDetour) + [b] + l2 */
  else right_detour(ns(width, 2), height, b.c, 1, &q);
  for (int j = i + 1; j < p->n; j++) lp_push(&q, p->v[j]);
  lp_free(p);
  *p = q;
}

/* `stripLeftP`: reflect, strip on the right, reflect back. */
static void strip_left_p(int width, int height, lp_t *p) {
  for (int i = 0; i < p->n; i++) p->v[i] = refl_x(ns(width, 2), p->v[i]);
  strip_right_p(width, height, p);
  for (int i = 0; i < p->n; i++) p->v[i] = refl_x(width, p->v[i]);
}

static int not_prime(int w, int h) {
  return !((w <= 3 && h <= 3) || (w == 4 && h == 4) || (w == 4 && h == 5) || (w == 5 && h == 4));
}

static int r_choice(int sx, int sy, int h) {
  if ((sx + sy) % 2 == 0) return 0;
  if (sx == 0 && sy == 1 && 1 < ns(h, 1)) return 3;
  return 1;
}

/* `primeLookup`: the stored path, appended (nothing if none). */
static void prime_lookup(int w, int h, zzn_cell s, zzn_cell t, lp_t *out) {
  for (int i = 0; i < D.nps; i++) {
    if (D.ps[i].w != w || D.ps[i].h != h) continue;
    for (int j = 0; j < D.ps[i].ne; j++) {
      const pent_t *E = &D.pe[D.ps[i].e0 + j];
      if (ceq(E->s, s) && ceq(E->t, t)) { for (int c = 0; c < E->nc; c++) lp_push(out, D.pc[E->c0 + c]); return; }
    }
    return;
  }
}

/* `normP`: one step for h <= w, s.x <= t.x, with f = ipsP (n - 1); the path in *out (empty on entry). */
static void norm_p(int n, int w, int h, zzn_cell s, zzn_cell t, lp_t *out) {
  if (!not_prime(w, h)) { prime_lookup(w, h, s, t, out); return; }
  if (2 <= s.r) {
    ips_p(n - 1, ns(w, 2), h, C2(ns(s.r, 2), s.c), C2(ns(t.r, 2), t.c), out);
    strip_left_p(w, h, out);
    return;
  }
  if (t.r + 2 < w) {
    ips_p(n - 1, ns(w, 2), h, s, t, out);
    strip_right_p(w, h, out);
    return;
  }
  int r = r_choice(s.r, s.c, h);
  lp_t q;
  lp_init(&q);
  ips_p(n - 1, 2, h, s, C2(1, r), out);
  ips_p(n - 1, ns(w, 2), h, C2(0, r), C2(ns(t.r, 2), t.c), &q);
  for (int i = 0; i < q.n; i++) q.v[i].r += 2;
  lp_append(out, &q);
  lp_free(&q);
}

/* `stepP`. */
static void step_p(int n, int w, int h, zzn_cell s, zzn_cell t, lp_t *out) {
  if (h <= w) {
    if (s.r <= t.r) norm_p(n, w, h, s, t, out);
    else { norm_p(n, w, h, t, s, out); lp_rev(out); }
    return;
  }
  if (s.c <= t.c) norm_p(n, h, w, swc(s), swc(t), out);
  else { norm_p(n, h, w, swc(t), swc(s), out); lp_rev(out); }
  lp_swap(out);
}

/* `ipsP`: the IPS path with fuel n, into *out (which must be empty). */
static void ips_p(int n, int w, int h, zzn_cell s, zzn_cell t, lp_t *out) {
  if (n == 0) return;
  step_p(n, w, h, s, t, out);
}

/* ------------------------------------------------------------------ building -------- */

typedef struct { zzn_cell a, b; lp_t p; } seg_t;
typedef struct { seg_t *v; int n, cap; } segs_t;
static void segs_free(segs_t *S) { for (int i = 0; i < S->n; i++) lp_free(&S->v[i].p); free(S->v); S->v = NULL; S->n = S->cap = 0; }
static void segs_push(segs_t *S, zzn_cell a, zzn_cell b, lp_t p) {
  GROW(S->v, S->n, S->cap, S->n + 1);
  S->v[S->n].a = a; S->v[S->n].b = b; S->v[S->n].p = p; S->n++;
}

/* `joinL`: join the segments a -> u and v -> b (the first ones with these ends); the joined
 * segment goes first. Unchanged if either is missing. */
static void join_l(zzn_cell a, zzn_cell u, zzn_cell v, zzn_cell b, segs_t *ps) {
  int i, j;
  for (i = 0; i < ps->n; i++) if (ceq(ps->v[i].a, a) && ceq(ps->v[i].b, u)) break;
  if (i == ps->n) return;
  for (j = 0; j < ps->n; j++) if (j != i && ceq(ps->v[j].a, v) && ceq(ps->v[j].b, b)) break;
  if (j == ps->n) return;
  segs_t q = {NULL, 0, 0};
  lp_t p = ps->v[i].p;
  lp_append(&p, &ps->v[j].p);
  lp_free(&ps->v[j].p);
  segs_push(&q, a, b, p);
  for (int k = 0; k < ps->n; k++) if (k != i && k != j) segs_push(&q, ps->v[k].a, ps->v[k].b, ps->v[k].p);
  free(ps->v);
  *ps = q;
}

/* `unsplit`: join the segments across a cut, the last pair first (its accumulator is never read). */
static void unsplit(const ictx_t *X, const tnode_t *T, int pos, const prs_t *ss, segs_t *ps) {
  int m = T->nk < ss->n ? T->nk : ss->n, vt = T->vert;
  for (int i = m - 1; i >= 0; i--) {
    const tkind_t *k = &D.kind[T->k0 + i];
    zzn_cell a = ss->v[i].a, b = ss->v[i].b;
    int s = k->s, y, z;
    kind_yz(X, vt, k, &y, &z);
    if (k->len == 1) continue;
    if (k->len == 3) { join_l(a, cutc(vt, pos, s, y), cutc(vt, pos, !s, y), b, ps); continue; }
    join_l(a, cutc(vt, pos, s, y), cutc(vt, pos, !s, y), cutc(vt, pos, !s, z), ps);
    join_l(a, cutc(vt, pos, !s, z), cutc(vt, pos, s, z), b, ps);
  }
}

/* `leafP`: the IPS path of a leaf, or its single cell (appended to out). */
static void leaf_p(const piece_t *P, segs_t *out) {
  if (P->segs.n != 1) return;
  zzn_cell a = P->segs.v[0].a, b = P->segs.v[0].b;
  lp_t p;
  lp_init(&p);
  if (ceq(a, b)) { lp_push(&p, a); segs_push(out, a, a, p); return; }
  ips_p(P->pw + P->ph, P->pw, P->ph, C2(ns(a.r, P->ox), ns(a.c, P->oy)), C2(ns(b.r, P->ox), ns(b.c, P->oy)), &p);
  for (int i = 0; i < p.n; i++) { p.v[i].r += P->ox; p.v[i].c += P->oy; }
  segs_push(out, a, b, p);
}

/* `buildT`, on the template node t (-1: leaf) instantiated by X; the segments into *out (empty). */
static void build_t(const ictx_t *X, int t, const piece_t *P, segs_t *out) {
  if (t < 0) { leaf_p(P, out); return; }
  const tnode_t *T = &D.node[t];
  int pos = node_pos(X, T);
  prs_t L, R;
  if (!split(X, T, pos, &P->segs, &L, &R)) { prs_free(&L); prs_free(&R); return; }
  piece_t lo = piece_lo(P, T->vert, pos, L), hi = piece_hi(P, T->vert, pos, R);
  segs_t B = {NULL, 0, 0};
  build_t(X, T->left, &lo, out);
  build_t(X, T->right, &hi, &B);
  for (int i = 0; i < B.n; i++) segs_push(out, B.v[i].a, B.v[i].b, B.v[i].p);
  free(B.v);
  prs_free(&L); prs_free(&R);
  unsplit(X, T, pos, &P->segs, out);
}

/* `tsol`: the solution built from template t on I (`solOf`: the first segments s0 -> t0 and
 * s1 -> t1, empty if missing), into s[0], s[1]. */
static void tsol(int t, const inst_t *I, lp_t s[2]) {
  ictx_t X;
  pr_t two[2];
  segs_t ps = {NULL, 0, 0};
  ictx_of(I, &X);
  piece_t P = root_piece(I, two);
  build_t(&X, t, &P, &ps);
  lp_init(&s[0]); lp_init(&s[1]);
  for (int j = 0; j < 2; j++) {
    zzn_cell a = j ? I->s1 : I->s0, b = j ? I->t1 : I->t0;
    for (int i = 0; i < ps.n; i++)
      if (ceq(ps.v[i].a, a) && ceq(ps.v[i].b, b)) { lp_append(&s[j], &ps.v[i].p); break; }
  }
  segs_free(&ps);
}

/* ------------------------------------------------------------------ stored paths ---- */

/* `decPath`: byte k is the cell 16 x + y. */
static void dec_path(int n, const uint8_t *code, lp_t *out) {
  lp_init(out);
  for (int k = 0; k < n; k++) lp_push(out, C2(code[k] / 16, code[k] % 16));
}

static int chain_adjacent(const lp_t *p) {
  for (int i = 0; i + 1 < p->n; i++)
    if (iabs(p->v[i].r - p->v[i + 1].r) + iabs(p->v[i].c - p->v[i + 1].c) != 1) return 0;
  return 1;
}

/* `maskOK w h 0` on p ++ q: in bounds, no cell twice. */
static int mask_ok(int w, int h, const lp_t *p, const lp_t *q) {
  uint8_t small[256], *seen = small;
  size_t n = (size_t)(w > 0 ? w : 0) * (size_t)(h > 0 ? h : 0);
  if (n > sizeof small) seen = xrealloc(NULL, n);
  memset(seen, 0, n);
  int ok = 1;
  for (int j = 0; j < 2 && ok; j++) {
    const lp_t *s = j ? q : p;
    for (int i = 0; i < s->n; i++) {
      zzn_cell v = s->v[i];
      if (!(v.r < w && v.c < h)) { ok = 0; break; }
      size_t k = (size_t)v.r * (size_t)h + (size_t)v.c;
      if (seen[k]) { ok = 0; break; }
      seen[k] = 1;
    }
  }
  if (seen != small) free(seen);
  return ok;
}

/* `solF`: p, q solve I. */
static int sol_f(const inst_t *I, const lp_t *p, const lp_t *q) {
  return p->n > 0 && ceq(p->v[0], I->s0) && ceq(p->v[p->n - 1], I->t0) && chain_adjacent(p) &&
         q->n > 0 && ceq(q->v[0], I->s1) && ceq(q->v[q->n - 1], I->t1) && chain_adjacent(q) &&
         mask_ok(I->R, I->C, p, q) && p->n + q->n == I->R * I->C;
}

/* ------------------------------------------------------------------ the lookup ------ */

/* `entryP`: solve K from the slice d; 1 with s filled and *kind, *index set, else 0. */
static int entry_p(const inst_t *K, const slice_t *d, lp_t s[2], int *kind, int *index) {
  for (int i = 0; i < d->np; i++) {
    int t = (int)D.pair[d->p0 + 2 * i], sigma = (int)(D.pair[d->p0 + 2 * i + 1] & 63);
    inst_t J = apply_sym(sigma, *K);
    if (tcheck(D.troot[t], &J)) {
      tsol(D.troot[t], &J, s);
      un_sym(sigma, *K, s);
      *kind = 0; *index = i;
      return 1;
    }
  }
  int c[4];
  cols_of(K, c);
  int64_t lane = idx(K->C, c);
  for (int i = 0; i < d->nq; i++) {
    const sol_t *e = &D.sol[d->q0 + i];
    if (e->lane != lane) continue;
    dec_path(e->n0, D.byte + e->off, &s[0]);
    dec_path(e->n1, D.byte + e->off + e->n0, &s[1]);
    if (sol_f(K, &s[0], &s[1])) { *kind = 1; *index = i; return 1; }
    lp_free(&s[0]); lp_free(&s[1]);
  }
  return 0;
}

/* `lookK tabAll`: the first slice with K's rows (`sameX`). */
static int look_k(const inst_t *K, lp_t s[2], zzn_look_info *info) {
  if (!(11 <= K->R && K->R <= K->C && K->C <= 16)) return 0;
  const box_t *B = &D.box[K->R][K->C];
  int x[4];
  rows_of(K, x);
  for (int j = 0; j < 4; j++) if (x[j] < 0 || x[j] > 15) return 0;
  int i = B->first[((x[0] * 16 + x[1]) * 16 + x[2]) * 16 + x[3]];
  if (i < 0) return 0;
  int kind, index;
  if (!entry_p(K, &D.sl[B->sl0 + i], s, &kind, &index)) return 0;
  info->slice = i; info->kind = kind; info->index = index;
  return 1;
}

/* `lookLe tabAll`: canonical form, table, pull back. */
static int look_le(inst_t J, lp_t s[2], zzn_look_info *info) {
  int sigma = canon_sym(J);
  info->sym = sigma;
  inst_t K = apply_sym(sigma, J);
  if (!look_k(&K, s, info)) return 0;
  un_sym(sigma, J, s);
  return 1;
}

int zzn_look_j(const zzn_instance *in, zzn_path *a, zzn_path *b, zzn_look_info *info) {
  zzn_look_info dummy;
  if (!info) info = &dummy;
  info->sym = 0; info->slice = info->kind = info->index = -1;
  a->cells = b->cells = NULL; a->len = b->len = 0;
  if (zzn_look_load() < 0) return ZZN_INTERNAL;
  lp_t s[2];
  inst_t I = *in;
  int r;
  if (I.R <= I.C) r = look_le(I, s, info);
  else {
    r = look_le(transpose(I), s, info);
    if (r) { lp_swap(&s[0]); lp_swap(&s[1]); }
  }
  if (!r) { info->slice = info->kind = info->index = -1; return 0; }
  a->cells = s[0].v; a->len = s[0].n;
  b->cells = s[1].v; b->len = s[1].n;
  return 1;
}

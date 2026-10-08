/* SPDX-License-Identifier: CC0-1.0 */
/* To the extent possible under law, the author has waived all copyright and related or
   neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal). */

/*
 * zzn.c: implementation of zzn.h. A port of the Python reference library (lib/python/zzn);
 * every function below mirrors the one of the same name there, in the same iteration order,
 * so the three implementations return identical paths.
 */
#include "zzn.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define THIN 10
#define SMALL 6

static _Thread_local int g_err;   /* set on an internal error (never expected) */

/* ------------------------------------------------------------------ basics ---------- */

typedef struct { zzn_cell *v; int n, cap; } path_t;

static zzn_cell C2(int r, int c) { zzn_cell x; x.r = r; x.c = c; return x; }
static int ceq(zzn_cell a, zzn_cell b) { return a.r == b.r && a.c == b.c; }
static int imin(int a, int b) { return a < b ? a : b; }
static int imax(int a, int b) { return a > b ? a : b; }
static int iabs(int a) { return a < 0 ? -a : a; }

static void *xmalloc(size_t n) {
  void *p = malloc(n ? n : 1);
  if (!p) { fprintf(stderr, "zzn: out of memory\n"); exit(1); }
  return p;
}
static void *xrealloc(void *p, size_t n) {
  p = realloc(p, n ? n : 1);
  if (!p) { fprintf(stderr, "zzn: out of memory\n"); exit(1); }
  return p;
}

static void pinit(path_t *p) { p->v = NULL; p->n = p->cap = 0; }
static void pfree(path_t *p) { free(p->v); pinit(p); }
static void pres(path_t *p, int n) {
  if (n > p->cap) { p->cap = imax(n, 2 * p->cap + 8); p->v = xrealloc(p->v, sizeof(zzn_cell) * p->cap); }
}
static void ppush(path_t *p, zzn_cell x) { pres(p, p->n + 1); p->v[p->n++] = x; }
static void pcopy(path_t *d, const path_t *s) { pinit(d); pres(d, s->n); memcpy(d->v, s->v, sizeof(zzn_cell) * s->n); d->n = s->n; }
static void prev_(path_t *p) {
  for (int i = 0, j = p->n - 1; i < j; i++, j--) { zzn_cell t = p->v[i]; p->v[i] = p->v[j]; p->v[j] = t; }
}
static void pappend(path_t *d, const path_t *s) { pres(d, d->n + s->n); memcpy(d->v + d->n, s->v, sizeof(zzn_cell) * s->n); d->n += s->n; }
/* insert m[0..k) after index i */
static void pinsert(path_t *p, int i, const zzn_cell *m, int k) {
  pres(p, p->n + k);
  memmove(p->v + i + 1 + k, p->v + i + 1, sizeof(zzn_cell) * (p->n - i - 1));
  memcpy(p->v + i + 1, m, sizeof(zzn_cell) * k);
  p->n += k;
}

typedef struct { int R, C; zzn_cell s0, t0, s1, t1; } inst_t;   /* same layout as zzn_instance */

static inst_t mk(int R, int C, zzn_cell s0, zzn_cell t0, zzn_cell s1, zzn_cell t1) {
  inst_t I; I.R = R; I.C = C; I.s0 = s0; I.t0 = t0; I.s1 = s1; I.t1 = t1; return I;
}
static void ends4(const inst_t *I, zzn_cell e[4]) { e[0] = I->s0; e[1] = I->t0; e[2] = I->s1; e[3] = I->t1; }

static int well_formed(const inst_t *I) {
  if (I->R < 1 || I->C < 1) return 0;
  zzn_cell e[4]; ends4(I, e);
  for (int i = 0; i < 4; i++) {
    if (e[i].r < 0 || e[i].r >= I->R || e[i].c < 0 || e[i].c >= I->C) return 0;
    for (int j = 0; j < i; j++) if (ceq(e[i], e[j])) return 0;
  }
  return 1;
}

static int check_path(int R, int C, zzn_cell s, zzn_cell t, const path_t *p, char *seen) {
  if (p->n == 0 || !ceq(p->v[0], s) || !ceq(p->v[p->n - 1], t)) return 0;
  for (int i = 0; i < p->n; i++) {
    zzn_cell x = p->v[i];
    if (x.r < 0 || x.r >= R || x.c < 0 || x.c >= C) return 0;
    if (seen[x.r * C + x.c]) return 0;
    seen[x.r * C + x.c] = 1;
    if (i > 0 && iabs(x.r - p->v[i - 1].r) + iabs(x.c - p->v[i - 1].c) != 1) return 0;
  }
  return 1;
}

static int check_sol(const inst_t *I, const path_t *a, const path_t *b) {
  char *seen = xmalloc((size_t)I->R * I->C);
  memset(seen, 0, (size_t)I->R * I->C);
  int ok = check_path(I->R, I->C, I->s0, I->t0, a, seen) && check_path(I->R, I->C, I->s1, I->t1, b, seen) &&
           a->n + b->n == I->R * I->C;
  free(seen);
  return ok;
}

/* geometric symmetry g = (tr, fr, fc): transpose, then flip rows, then flip columns */
typedef struct { int tr, fr, fc; } geo_t;
static const geo_t GEOS[8] = {{0,0,0},{0,0,1},{0,1,0},{0,1,1},{1,0,0},{1,0,1},{1,1,0},{1,1,1}};

static zzn_cell geo_cell(geo_t g, int R, int C, zzn_cell x) {
  int r = x.r, c = x.c;
  if (g.tr) { int t = r; r = c; c = t; t = R; R = C; C = t; }
  if (g.fr) r = R - 1 - r;
  if (g.fc) c = C - 1 - c;
  return C2(r, c);
}
static zzn_cell geo_inv(geo_t g, int R, int C, zzn_cell x) {
  int R2 = g.tr ? C : R, C2_ = g.tr ? R : C, r = x.r, c = x.c;
  if (g.fc) c = C2_ - 1 - c;
  if (g.fr) r = R2 - 1 - r;
  if (g.tr) { int t = r; r = c; c = t; }
  return C2(r, c);
}
static inst_t apply_geo(geo_t g, const inst_t *I) {
  return mk(g.tr ? I->C : I->R, g.tr ? I->R : I->C, geo_cell(g, I->R, I->C, I->s0), geo_cell(g, I->R, I->C, I->t0),
            geo_cell(g, I->R, I->C, I->s1), geo_cell(g, I->R, I->C, I->t1));
}
typedef struct { int r0, r1, sw; } lab_t;
static inst_t relabel(lab_t l, const inst_t *I) {
  zzn_cell s0 = I->s0, t0 = I->t0, s1 = I->s1, t1 = I->t1, t;
  if (l.r0) { t = s0; s0 = t0; t0 = t; }
  if (l.r1) { t = s1; s1 = t1; t1 = t; }
  if (l.sw) { t = s0; s0 = s1; s1 = t; t = t0; t0 = t1; t1 = t; }
  return mk(I->R, I->C, s0, t0, s1, t1);
}

/* orient: two paths joining the endpoint pairs in some order/direction -> (s0..t0, s1..t1); the
 * inputs are consumed */
static int orient(const inst_t *I, path_t in[2], path_t out[2]) {
  path_t o[2]; pinit(&o[0]); pinit(&o[1]);
  int got[2] = {0, 0};
  for (int k = 0; k < 2; k++) {
    path_t *p = &in[k];
    zzn_cell f = p->v[0], l = p->v[p->n - 1];
    for (int col = 0; col < 2; col++) {
      zzn_cell s = col ? I->s1 : I->s0, t = col ? I->t1 : I->t0;
      if (ceq(f, s) && ceq(l, t)) { pfree(&o[col]); pcopy(&o[col], p); got[col] = 1; }
      else if (ceq(f, t) && ceq(l, s)) { pfree(&o[col]); pcopy(&o[col], p); prev_(&o[col]); got[col] = 1; }
    }
  }
  pfree(&in[0]); pfree(&in[1]);
  if (!got[0] || !got[1]) { g_err = 1; pfree(&o[0]); pfree(&o[1]); return 0; }
  out[0] = o[0]; out[1] = o[1];
  return 1;
}

static int map_back(geo_t g, const inst_t *I, path_t img[2], path_t out[2]) {
  for (int k = 0; k < 2; k++) for (int i = 0; i < img[k].n; i++) img[k].v[i] = geo_inv(g, I->R, I->C, img[k].v[i]);
  return orient(I, img, out);
}

/* --------------------------------------------------------------- catalogue ---------- */

typedef struct { zzn_cell x; int col; } pt_t;
typedef struct { int fr, fc, tr; } frame_t;
static const frame_t FRAMES[8] = {{0,0,0},{0,0,1},{0,1,0},{0,1,1},{1,0,0},{1,0,1},{1,1,0},{1,1,1}};

static const int CORNER4[36][8] = {
  {0,1,0,3,1,1,1,3},{0,1,0,6,0,7,1,1},{0,1,0,6,1,1,7,0},{0,1,0,6,1,2,6,0},{0,1,0,7,1,1,6,0},{0,1,1,3,1,1,1,2},
  {0,1,1,3,1,2,2,2},{0,1,1,3,1,2,3,1},{0,1,2,2,1,1,1,2},{0,1,2,2,1,2,3,1},{0,1,2,2,1,3,3,0},{0,1,7,0,1,1,6,0},
  {0,2,1,1,2,1,3,0},{0,2,2,0,1,2,2,1},{0,3,2,1,3,1,4,0},{0,6,2,1,1,2,6,0},{1,2,2,2,1,3,2,1},{1,2,3,1,1,3,2,1},
  {0,1,1,2,0,4,2,2},{0,1,1,2,0,4,3,1},{0,1,1,2,1,3,2,0},{0,1,1,2,1,3,4,0},{0,1,1,2,2,0,2,2},{0,1,1,2,2,2,4,0},
  {0,1,1,2,3,1,4,0},{0,1,1,3,0,3,0,4},{0,1,1,3,0,3,2,0},{0,1,1,3,0,3,4,0},{0,1,2,1,0,2,2,2},{0,1,2,1,0,2,3,1},
  {0,1,2,1,0,4,1,3},{0,1,2,1,0,4,2,2},{0,1,2,1,0,4,3,1},{0,1,2,1,1,3,4,0},{0,1,2,1,2,2,4,0},{0,1,2,1,3,1,4,0}};
static const int CORNER4_ODD[3][8] = {{0,0,0,1,1,1,2,0},{0,0,1,4,0,2,1,3},{0,0,2,3,0,2,1,3}};
static const int B3_EVEN[21][6] = {
  {0,0,1,1,1,2},{0,1,0,2,1,1},{0,1,0,2,1,2},{0,1,0,3,1,1},{0,1,0,4,1,1},{0,1,0,4,1,2},{0,1,0,5,1,1},
  {0,1,1,2,1,1},{0,1,1,2,1,3},{0,1,1,2,2,2},{0,1,1,2,3,1},{0,1,1,3,0,3},{0,1,2,1,1,3},{0,1,2,1,2,2},
  {0,1,2,1,3,1},{0,2,2,1,1,0},{0,3,1,1,1,0},{0,4,1,1,1,0},{0,4,2,1,1,0},{0,4,2,1,1,2},{0,5,1,1,1,0}};
static const int B3_ODD[5][6] = {{0,0,1,1,1,2},{0,0,1,1,2,2},{0,1,0,2,1,1},{0,1,0,4,1,1},{0,4,1,1,1,0}};

static int ns(int a, int b) { return a > b ? a - b : 0; }   /* natural-number subtraction, as in Lean */
static int sgn(zzn_cell p) { return (p.r + p.c) % 2 == 0 ? 1 : -1; }

static int parity_ok(int R, int C, const pt_t *pts) {
  int s = 0;
  for (int i = 0; i < 4; i++) s += sgn(pts[i].x);
  return s == 2 * ((R * C) % 2);
}

static int perim_index(int R, int C, zzn_cell p) {
  if (p.r == 0) return p.c;
  if (p.c == C - 1) return C - 1 + p.r;
  if (p.r == R - 1) return C - 1 + (R - 1) + (C - 1 - p.c);
  if (p.c == 0) return 2 * (C - 1) + (R - 1) + (R - 1 - p.r);
  return -1;
}

static int alternating(const int *cols, int n) {
  return n == 4 && cols[0] != cols[1] && cols[1] != cols[2] && cols[2] != cols[3];
}

/* stable sort of (key, colour) pairs by key; returns the colours */
static void sort_cols(int *keys, int *cols, int n) {
  for (int i = 1; i < n; i++)
    for (int j = i; j > 0 && keys[j - 1] > keys[j]; j--) {
      int t = keys[j]; keys[j] = keys[j - 1]; keys[j - 1] = t;
      t = cols[j]; cols[j] = cols[j - 1]; cols[j - 1] = t;
    }
}

static int t1_fires(int R, int C, const pt_t *pts) {
  int k[4], c[4];
  for (int i = 0; i < 4; i++) { k[i] = perim_index(R, C, pts[i].x); c[i] = pts[i].col; if (k[i] < 0) return 0; }
  sort_cols(k, c, 4);
  return alternating(c, 4);
}

static int t2_fires(const pt_t *pts) {
  int rmin = 1 << 30, rmax = -1, cmin = 1 << 30, cmax = -1;
  for (int i = 0; i < 4; i++) {
    rmin = imin(rmin, pts[i].x.r); rmax = imax(rmax, pts[i].x.r);
    cmin = imin(cmin, pts[i].x.c); cmax = imax(cmax, pts[i].x.c);
  }
  return rmax - rmin == 1 && cmax - cmin == 1 && pts[0].x.r != pts[1].x.r && pts[0].x.c != pts[1].x.c;
}

static int l1_fires(int R, int C, const pt_t *pts) {
  static const int D[4][2] = {{-1,0},{1,0},{0,-1},{0,1}};
  for (int i = 0; i < 4; i++) {
    int all = 1;
    for (int d = 0; d < 4 && all; d++) {
      zzn_cell q = C2(pts[i].x.r + D[d][0], pts[i].x.c + D[d][1]);
      if (q.r < 0 || q.r >= R || q.c < 0 || q.c >= C) continue;
      int found = 0;
      for (int j = 0; j < 4; j++) if (ceq(pts[j].x, q) && pts[j].col != pts[i].col) found = 1;
      if (!found) all = 0;
    }
    if (all) return 1;
  }
  return 0;
}

static int find_pt(const pt_t *pts, int n, zzn_cell x) {
  for (int i = 0; i < n; i++) if (ceq(pts[i].x, x)) return i;
  return -1;
}

static int l6_fires(int R, int C, const pt_t *pts) {
  int corners[4][4] = {{0,0,1,1},{0,C-1,1,-1},{R-1,0,-1,1},{R-1,C-1,-1,-1}};
  int has0 = 0, has1 = 0;
  for (int k = 0; k < 4; k++) {
    int cr = corners[k][0], cc = corners[k][1], dr = corners[k][2], dc = corners[k][3];
    int e1 = find_pt(pts, 4, C2(cr, imax(cc + dc, 0))), e2 = find_pt(pts, 4, C2(imax(cr + dr, 0), cc));
    if (e1 >= 0 && e2 >= 0 && pts[e1].col == pts[e2].col && find_pt(pts, 4, C2(cr, cc)) < 0) {
      if (pts[e1].col == 0) has0 = 1; else has1 = 1;
    }
  }
  return has0 && has1 && R * C > 6;
}

static zzn_cell frame_to(int R, int C, frame_t f, zzn_cell p) {
  int a = f.fr ? ns(ns(R, 1), p.r) : p.r, b = f.fc ? ns(ns(C, 1), p.c) : p.c;
  return f.tr ? C2(b, a) : C2(a, b);
}
static zzn_cell frame_back(int R, int C, frame_t f, zzn_cell q) {
  int r = f.tr ? q.c : q.r, c = f.tr ? q.r : q.c;
  return C2(f.fr ? ns(ns(R, 1), r) : r, f.fc ? ns(ns(C, 1), c) : c);
}

typedef struct { int H, W; pt_t p[4]; } view_t;
static view_t make_view(int R, int C, frame_t f, const pt_t *pts) {
  view_t v; v.H = f.tr ? C : R; v.W = f.tr ? R : C;
  for (int i = 0; i < 4; i++) { v.p[i].x = frame_to(R, C, f, pts[i].x); v.p[i].col = pts[i].col; }
  return v;
}
static int vat(const view_t *v, int r, int c) {
  for (int i = 0; i < 4; i++) if (v->p[i].x.r == r && v->p[i].x.c == c) return v->p[i].col;
  return -1;
}
static int vempty(const view_t *v, const int (*cells)[2], int n) {
  for (int i = 0; i < n; i++) if (vat(v, cells[i][0], cells[i][1]) >= 0) return 0;
  return 1;
}

static int test_l2(const view_t *v) {
  static const int e[1][2] = {{0,0}};
  int a = vat(v, 0, 1), b = vat(v, 1, 0);
  return a >= 0 && b >= 0 && a != b && vempty(v, e, 1);
}
static int test_l3(const view_t *v) {
  static const int e[2][2] = {{0,0},{0,1}};
  int a = vat(v, 0, 2);
  return a >= 0 && vat(v, 1, 1) == a && vat(v, 1, 0) == 1 - a && vempty(v, e, 2);
}
static int test_l4(const view_t *v) {
  static const int e[2][2] = {{0,1},{1,0}};
  int a = vat(v, 0, 0);
  return a >= 0 && vat(v, 1, 1) == a && vat(v, 0, 2) == 1 - a && v->H >= 3 && vempty(v, e, 2);
}
static int test_l5(const view_t *v) {
  static const int e[3][2] = {{0,1},{1,0},{1,1}};
  int b = vat(v, 0, 0);
  return b >= 0 && vat(v, 0, 2) == 1 - b && vat(v, 2, 0) == 1 - b && vempty(v, e, 3);
}
static int edge_closure(const view_t *v) {
  for (int k = 0; k + 3 < v->W; k++) {
    int a = vat(v, 0, k);
    if (a >= 0 && vat(v, 1, k + 1) == a && vat(v, 0, k + 3) == 1 - a && vat(v, 1, k + 2) == 1 - a) return 1;
  }
  return 0;
}

static int boundary_only(int R, int C, frame_t f, const pt_t *pts) {
  int odd = (R % 2 == 1 && C % 2 == 1), n = odd ? 5 : 21;
  view_t v = make_view(R, C, f, pts);
  for (int k = 0; k < n; k++) {
    const int *t = odd ? B3_ODD[k] : B3_EVEN[k];
    zzn_cell a1 = C2(t[0], t[1]), a2 = C2(t[2], t[3]), b = C2(t[4], t[5]);
    for (int A = 0; A <= 1; A++) {
      int hb = 0, h1 = 0, h2 = 0, fourth = -1;
      for (int i = 0; i < 4; i++) {
        if (v.p[i].col == 1 - A && ceq(v.p[i].x, b)) hb = 1;
        if (v.p[i].col == A && ceq(v.p[i].x, a1)) h1 = 1;
        if (v.p[i].col == A && ceq(v.p[i].x, a2)) h2 = 1;
      }
      if (!hb || !h1 || !h2) continue;
      for (int i = 0; i < 4; i++) if (v.p[i].col == 1 - A && !ceq(v.p[i].x, b)) { fourth = i; break; }
      if (fourth < 0) continue;
      zzn_cell x = v.p[fourth].x;
      int on = x.r == 0 || x.c == 0 || x.r == v.H - 1 || x.c == v.W - 1;
      if (on && !(x.r < 6 && x.c < 6)) return 1;
    }
  }
  return 0;
}

static int same_set2(const zzn_cell *a, const zzn_cell *b, int nb) {
  if (nb != 2) return 0;
  for (int i = 0; i < 2; i++) {
    int f = 0;
    for (int j = 0; j < nb; j++) if (ceq(a[i], b[j])) f = 1;
    if (!f) return 0;
  }
  return 1;
}

static int corner4(int R, int C, frame_t f, const pt_t *pts) {
  zzn_cell A0[4], A1[4];
  int n0 = 0, n1 = 0;
  for (int i = 0; i < 4; i++) {
    if (pts[i].col == 0) A0[n0++] = frame_to(R, C, f, pts[i].x);
    if (pts[i].col == 1) A1[n1++] = frame_to(R, C, f, pts[i].x);
  }
  int even = (R * C) % 2 == 0, n = even ? 36 : 3;
  for (int k = 0; k < n; k++) {
    const int *t = even ? CORNER4[k] : CORNER4_ODD[k];
    zzn_cell A[2] = {C2(t[0], t[1]), C2(t[2], t[3])}, B[2] = {C2(t[4], t[5]), C2(t[6], t[7])};
    if ((same_set2(A, A0, n0) && same_set2(B, A1, n1)) || (same_set2(A, A1, n1) && same_set2(B, A0, n0))) return 1;
  }
  return 0;
}

static const char *frame_fires(int R, int C, const pt_t *pts, frame_t f) {
  view_t v = make_view(R, C, f, pts);
  if (test_l2(&v)) return "L2";
  if (test_l3(&v)) return "L3";
  if (test_l4(&v)) return "L4";
  if (test_l5(&v)) return "L5";
  if (edge_closure(&v)) return "E1";
  if (boundary_only(R, C, f, pts)) return "B";
  if (R >= 10 && C >= 10 && corner4(R, C, f, pts)) return "C4";
  return NULL;
}

/* R: forced corner rewrites, then alternation along the outer walk */
typedef struct { int nrem, nmov; zzn_cell rem[8]; zzn_cell mov[2][2]; } rw_t;

static int rewrites_at(const view_t *v, rw_t *rw) {
  static const int e3[8][2] = {{0,0},{0,1},{0,2},{0,3},{1,0},{1,1},{2,0},{3,0}};
  static const int e2[4][2] = {{0,1},{1,0},{0,2},{2,0}};
  static const int e1[2][2] = {{0,0},{1,0}};
  int x = vat(v, 1, 2), y = vat(v, 2, 1);
  if (x >= 0 && y >= 0 && x != y && v->H >= 4 && v->W >= 4 && vempty(v, e3, 8)) {
    static const int rm[8][2] = {{0,0},{0,1},{0,2},{1,0},{1,1},{2,0},{1,2},{2,1}};
    rw->nrem = 8; for (int i = 0; i < 8; i++) rw->rem[i] = C2(rm[i][0], rm[i][1]);
    rw->nmov = 2; rw->mov[0][0] = C2(1, 2); rw->mov[0][1] = C2(0, 3); rw->mov[1][0] = C2(2, 1); rw->mov[1][1] = C2(3, 0);
    return 1;
  }
  int a = vat(v, 0, 0);
  if (a >= 0 && vat(v, 1, 1) == a && v->H >= 3 && v->W >= 3 && vempty(v, e2, 4)) {
    static const int rm[4][2] = {{0,0},{0,1},{1,0},{1,1}};
    rw->nrem = 4; for (int i = 0; i < 4; i++) rw->rem[i] = C2(rm[i][0], rm[i][1]);
    rw->nmov = 2; rw->mov[0][0] = C2(0, 0); rw->mov[0][1] = C2(0, 2); rw->mov[1][0] = C2(1, 1); rw->mov[1][1] = C2(2, 0);
    return 1;
  }
  if (vat(v, 0, 1) >= 0 && vempty(v, e1, 2) && v->H >= 2) {
    rw->nrem = 2; rw->rem[0] = C2(0, 0); rw->rem[1] = C2(0, 1);
    rw->nmov = 1; rw->mov[0][0] = C2(0, 1); rw->mov[0][1] = C2(1, 0);
    return 1;
  }
  return 0;
}

static int in_list(const zzn_cell *l, int n, zzn_cell x) {
  for (int i = 0; i < n; i++) if (ceq(l[i], x)) return 1;
  return 0;
}

static const frame_t FTL = {0,0,0}, FTR = {0,1,0}, FBR = {1,1,0}, FBL = {1,0,0};

static int notch_len(int R, int C, frame_t f, const zzn_cell *rem, int nrem, int i) {
  int n = 0;
  for (int j = 0; j < 4; j++) if (in_list(rem, nrem, frame_back(R, C, f, C2(i, j)))) n++;
  return n;
}

static void stair_of(int R, int C, frame_t f, const zzn_cell *rem, int nrem, path_t *out) {
  int lam[5];
  for (int i = 0; i < 5; i++) lam[i] = notch_len(R, C, f, rem, nrem, i);
  int k = 0;
  for (int i = 0; i < 4; i++) if (lam[i] > 0) k++;
  pinit(out);
  ppush(out, frame_back(R, C, f, C2(k, 0)));
  for (int i = k - 1; i >= 0; i--) {
    int n = ns(lam[i], lam[i + 1]);
    for (int j = 0; j < n; j++) ppush(out, frame_back(R, C, f, C2(i + 1, lam[i + 1] + 1 + j)));
    ppush(out, frame_back(R, C, f, C2(i, lam[i])));
  }
}

static void walk3(int R, int C, const zzn_cell *rem, int nrem, path_t *w) {
  path_t tl, trr, br, bl;
  stair_of(R, C, FTL, rem, nrem, &tl);
  stair_of(R, C, FTR, rem, nrem, &trr); prev_(&trr);
  stair_of(R, C, FBR, rem, nrem, &br);
  stair_of(R, C, FBL, rem, nrem, &bl); prev_(&bl);
  int lTL = notch_len(R, C, FTL, rem, nrem, 0), lTR = notch_len(R, C, FTR, rem, nrem, 0);
  int lBR = notch_len(R, C, FBR, rem, nrem, 0), lBL = notch_len(R, C, FBL, rem, nrem, 0);
  int kTL = 0, kTR = 0, kBR = 0, kBL = 0;
  for (int i = 0; i < 4; i++) {
    kTL += notch_len(R, C, FTL, rem, nrem, i) > 0; kTR += notch_len(R, C, FTR, rem, nrem, i) > 0;
    kBR += notch_len(R, C, FBR, rem, nrem, i) > 0; kBL += notch_len(R, C, FBL, rem, nrem, i) > 0;
  }
  pinit(w);
  pappend(w, &tl);
  for (int y = 0; y < C; y++) if (lTL < y && y + 1 + lTR < C) ppush(w, C2(0, y));
  pappend(w, &trr);
  for (int x = 0; x < R; x++) if (kTR < x && x + 1 + kBR < R) ppush(w, C2(x, C - 1));
  pappend(w, &br);
  for (int y = C - 1; y >= 0; y--) if (lBL < y && y + 1 + lBR < C) ppush(w, C2(R - 1, y));
  pappend(w, &bl);
  for (int x = R - 1; x >= 0; x--) if (kTL < x && x + 1 + kBL < R) ppush(w, C2(x, 0));
  pfree(&tl); pfree(&trr); pfree(&br); pfree(&bl);
}

static int eff_alt(int R, int C, const pt_t *pts) {
  pt_t eff[4];
  memcpy(eff, pts, sizeof(eff));
  zzn_cell rem[64];
  int nrem = 0, any = 0;
  for (int fi = 0; fi < 8; fi++) {
    frame_t f = FRAMES[fi];
    view_t v = make_view(R, C, f, eff);
    rw_t rw;
    if (!rewrites_at(&v, &rw)) continue;
    zzn_cell cells[8], mov[2][2];
    int clash = 0;
    for (int i = 0; i < rw.nrem; i++) { cells[i] = frame_back(R, C, f, rw.rem[i]); if (in_list(rem, nrem, cells[i])) clash = 1; }
    for (int i = 0; i < rw.nmov; i++) {
      mov[i][0] = frame_back(R, C, f, rw.mov[i][0]); mov[i][1] = frame_back(R, C, f, rw.mov[i][1]);
      if (in_list(rem, nrem, mov[i][1])) clash = 1;
    }
    if (clash) continue;
    for (int i = 0; i < rw.nmov; i++) {
      int k = find_pt(eff, 4, mov[i][0]);
      if (k >= 0) eff[k].x = mov[i][1];
    }
    for (int i = 0; i < rw.nrem; i++) rem[nrem++] = cells[i];
    any = 1;
  }
  if (!any) return 0;
  for (int i = 0; i < 4; i++) if (in_list(rem, nrem, eff[i].x)) return 0;
  for (int i = 0; i < 4; i++) for (int j = 0; j < i; j++) if (ceq(eff[i].x, eff[j].x)) return 0;
  path_t w;
  walk3(R, C, rem, nrem, &w);
  int keys[4], cols[4], ok = 1;
  for (int i = 0; i < 4 && ok; i++) {
    int cnt = 0, pos = -1;
    for (int j = 0; j < w.n; j++) if (ceq(w.v[j], eff[i].x)) { cnt++; pos = j; }
    if (cnt != 1) ok = 0;
    keys[i] = pos; cols[i] = eff[i].col;
  }
  pfree(&w);
  if (!ok) return 0;
  sort_cols(keys, cols, 4);
  return alternating(cols, 4);
}

const char *zzn_fires(int R, int C, zzn_cell s0, zzn_cell t0, zzn_cell s1, zzn_cell t1) {
  pt_t pts[4] = {{s0, 0}, {t0, 0}, {s1, 1}, {t1, 1}};
  if (!parity_ok(R, C, pts)) return "P";
  if (t1_fires(R, C, pts)) return "T1";
  if (t2_fires(pts)) return "T2";
  if (l1_fires(R, C, pts)) return "L1";
  if (l6_fires(R, C, pts)) return "L6";
  for (int i = 0; i < 8; i++) { const char *n = frame_fires(R, C, pts, FRAMES[i]); if (n) return n; }
  if (eff_alt(R, C, pts)) return "R";
  return NULL;
}
static const char *fires_i(const inst_t *I) { return zzn_fires(I->R, I->C, I->s0, I->t0, I->s1, I->t1); }

/* ----------------------------------------------------------------- plug DP ---------- */

enum { EM = 0, A0 = 1, A1 = 2, O0 = 3, C0 = 4, O1 = 5, C1 = 6 };
static int gv(uint64_t s, int i) { return (int)((s >> (3 * i)) & 7); }
static uint64_t svv(uint64_t s, int i, int v) { return (s & ~((uint64_t)7 << (3 * i))) | ((uint64_t)v << (3 * i)); }
static int is_anchor(int v) { return v == A0 || v == A1; }
static int is_open(int v) { return v == O0 || v == O1; }
static int is_close(int v) { return v == C0 || v == C1; }
static int color_of(int v) { return is_anchor(v) ? v - 1 : (v - 3) >> 1; }

static int partner(uint64_t s, int i, int n) {
  int v = gv(s, i), depth = 0;
  if (is_open(v)) {
    for (int j = i + 1; j < n; j++) {
      int w = gv(s, j);
      if (is_open(w)) depth++;
      else if (is_close(w)) { if (depth == 0) return j; depth--; }
    }
  } else {
    for (int j = i - 1; j >= 0; j--) {
      int w = gv(s, j);
      if (is_close(w)) depth++;
      else if (is_open(w)) { if (depth == 0) return j; depth--; }
    }
  }
  return -1;
}

static int step_cell(uint64_t s, int r, int n, int tc, int can_r, int can_d, int ncol, uint64_t *out) {
  int k = 0, budget = tc >= 0 ? 1 : 2, navail = can_r + can_d;
  int up = gv(s, r), lf = gv(s, r + 1), have = (up != EM) + (lf != EM);
  if (have > budget) return 0;
  int need = budget - have;
  if (need > navail) return 0;
  uint64_t base = svv(svv(s, r, EM), r + 1, EM);
  if (have == 0) {
    if (tc >= 0) {
      if (can_r) out[k++] = svv(base, r, 1 + tc);
      if (can_d) out[k++] = svv(base, r + 1, 1 + tc);
    } else {
      for (int col = 0; col < ncol; col++) out[k++] = svv(svv(base, r, 3 + 2 * col), r + 1, 4 + 2 * col);
    }
  } else if (have == 1) {
    int p = up != EM ? up : lf, pos = up != EM ? r : r + 1, pc = color_of(p);
    if (need == 0) {
      if (pc != tc) return 0;
      if (is_anchor(p)) out[k++] = base;
      else out[k++] = svv(base, partner(s, pos, n), 1 + pc);
    } else {
      if (can_r) out[k++] = svv(base, r, p);
      if (can_d) out[k++] = svv(base, r + 1, p);
    }
  } else {
    int col = color_of(up);
    if (col != color_of(lf)) return 0;
    if (is_anchor(up) && is_anchor(lf)) out[k++] = base;
    else if (is_anchor(up) || is_anchor(lf)) out[k++] = svv(base, partner(s, is_anchor(up) ? r + 1 : r, n), 1 + col);
    else if (is_open(up) && is_close(lf)) return 0;
    else if (is_close(up) && is_open(lf)) out[k++] = base;
    else if (is_open(up)) out[k++] = svv(base, partner(s, r + 1, n), 3 + 2 * col);
    else out[k++] = svv(base, partner(s, r, n), 4 + 2 * col);
  }
  return k;
}

/* a hash set of states with insertion order (dense arrays) and optional predecessor indices */
typedef struct {
  uint64_t *hk; int32_t *hv; size_t cap;
  uint64_t *keys; int32_t *pred; size_t cnt, dcap;
} layer_t;
#define SENT (~(uint64_t)0)

static size_t hidx(uint64_t k, size_t cap) { k ^= k >> 31; k *= 0x9E3779B97F4A7C15ULL; k ^= k >> 29; return (size_t)k & (cap - 1); }
static void layer_init(layer_t *L, size_t cap) {
  L->cap = cap; L->hk = xmalloc(cap * sizeof(uint64_t)); L->hv = xmalloc(cap * sizeof(int32_t));
  memset(L->hk, 0xff, cap * sizeof(uint64_t));
  L->dcap = cap / 2 + 1; L->keys = xmalloc(L->dcap * sizeof(uint64_t)); L->pred = xmalloc(L->dcap * sizeof(int32_t));
  L->cnt = 0;
}
static void layer_free(layer_t *L) { free(L->hk); free(L->hv); free(L->keys); free(L->pred); }
static void layer_grow(layer_t *L) {
  free(L->hk); free(L->hv);
  L->cap *= 2; L->hk = xmalloc(L->cap * sizeof(uint64_t)); L->hv = xmalloc(L->cap * sizeof(int32_t));
  memset(L->hk, 0xff, L->cap * sizeof(uint64_t));
  for (size_t d = 0; d < L->cnt; d++) {
    size_t i = hidx(L->keys[d], L->cap);
    while (L->hk[i] != SENT) i = (i + 1) & (L->cap - 1);
    L->hk[i] = L->keys[d]; L->hv[i] = (int32_t)d;
  }
  L->dcap = L->cap / 2 + 1;
  L->keys = xrealloc(L->keys, L->dcap * sizeof(uint64_t)); L->pred = xrealloc(L->pred, L->dcap * sizeof(int32_t));
}
static int layer_find(const layer_t *L, uint64_t k) {
  size_t i = hidx(k, L->cap);
  while (L->hk[i] != SENT) { if (L->hk[i] == k) return L->hv[i]; i = (i + 1) & (L->cap - 1); }
  return -1;
}
static void layer_add(layer_t *L, uint64_t k, int32_t pred) {
  if ((L->cnt + 1) * 2 > L->cap) layer_grow(L);
  size_t i = hidx(k, L->cap);
  while (L->hk[i] != SENT) { if (L->hk[i] == k) return; i = (i + 1) & (L->cap - 1); }
  L->hk[i] = k; L->hv[i] = (int32_t)L->cnt; L->keys[L->cnt] = k; L->pred[L->cnt] = pred; L->cnt++;
}
static int cmp_u64(const void *a, const void *b) {
  uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
  return x < y ? -1 : x > y;
}

typedef struct { zzn_cell x; int col; } term_t;

/* Necessary for any covering by paths: the endpoint signs (+1 on cells with r + c even, -1
 * otherwise) sum to 2 (R C mod 2). Each path's cells alternate in sign, so a path's sign sum is
 * half its two endpoints' signs; the whole grid sums to R C mod 2. */
static int terms_parity_ok(int R, int C, const term_t *terms, int nt) {
  int s = 0;
  for (int i = 0; i < nt; i++) s += ((terms[i].x.r + terms[i].x.c) % 2 == 0) ? 1 : -1;
  return s == 2 * ((R * C) % 2);
}

/* The plug DP: paths for each colour among the terms (2 or 4 terms; colours 0 and/or 1).
 * Returns 1 and fills out[colour] (for the colours present), 0 if no covering, -1 on error.
 * If feas_only, only decides. */
static int plug_dp(int R, int C, const term_t *terms0, int nt, int feas_only, path_t out[2]) {
  term_t terms[4];
  int ncol = 0, present[2] = {0, 0};
  for (int i = 0; i < nt; i++) { terms[i] = terms0[i]; present[terms[i].col] = 1; ncol = imax(ncol, terms[i].col + 1); }
  int transposed = R > C;
  if (transposed) {
    int t = R; R = C; C = t;
    for (int i = 0; i < nt; i++) { int x = terms[i].x.r; terms[i].x.r = terms[i].x.c; terms[i].x.c = x; }
  }
  if (R + 1 > 21) { g_err = 1; return -1; }
  if (!terms_parity_ok(R, C, terms, nt)) return 0;
  int *term = xmalloc(sizeof(int) * R * C);
  for (int i = 0; i < R * C; i++) term[i] = -1;
  for (int i = 0; i < nt; i++) term[terms[i].x.r * C + terms[i].x.c] = terms[i].col;
  int n = R + 1;
  uint64_t mask = n >= 21 ? ~(uint64_t)0 : (((uint64_t)1 << (3 * n)) - 1);
  uint64_t outb[4];
  uint64_t **ckpt = feas_only ? NULL : xmalloc(sizeof(uint64_t *) * C);
  size_t *ckn = feas_only ? NULL : xmalloc(sizeof(size_t) * C);
  layer_t cur, nxt;
  layer_init(&cur, 1024); layer_init(&nxt, 1024);
  layer_add(&cur, 0, -1);
  int alive = 1, c;
  for (c = 0; c < C && alive; c++) {
    if (c > 0) {
      layer_free(&nxt); layer_init(&nxt, 1024);
      for (size_t d = 0; d < cur.cnt; d++) layer_add(&nxt, (cur.keys[d] << 3) & mask, -1);
      layer_t t = cur; cur = nxt; nxt = t;
    }
    if (!feas_only) {
      ckn[c] = cur.cnt; ckpt[c] = xmalloc(sizeof(uint64_t) * (cur.cnt + 1));
      memcpy(ckpt[c], cur.keys, sizeof(uint64_t) * cur.cnt);
      qsort(ckpt[c], cur.cnt, sizeof(uint64_t), cmp_u64);
    }
    for (int r = 0; r < R; r++) {
      layer_free(&nxt); layer_init(&nxt, 1024);
      for (size_t d = 0; d < cur.cnt; d++) {
        int k = step_cell(cur.keys[d], r, n, term[r * C + c], c < C - 1, r < R - 1, ncol, outb);
        for (int q = 0; q < k; q++) layer_add(&nxt, outb[q], -1);
      }
      layer_t t = cur; cur = nxt; nxt = t;
      if (cur.cnt == 0) { alive = 0; break; }
    }
  }
  int ok = alive && layer_find(&cur, 0) >= 0;
  layer_free(&cur); layer_free(&nxt);
  if (feas_only || !ok) {
    if (!feas_only) { for (int k = 0; k < c; k++) free(ckpt[k]); free(ckpt); free(ckn); }
    free(term);
    return ok;
  }
  signed char *right = xmalloc(R * C), *down = xmalloc(R * C);
  memset(right, -1, R * C); memset(down, -1, R * C);
  uint64_t target = 0;
  layer_t *lay = xmalloc(sizeof(layer_t) * (R + 1));
  for (c = C - 1; c >= 0; c--) {
    layer_init(&lay[0], 1024);
    for (size_t d = 0; d < ckn[c]; d++) layer_add(&lay[0], ckpt[c][d], -1);
    for (int r = 0; r < R; r++) {
      layer_init(&lay[r + 1], 1024);
      for (size_t d = 0; d < lay[r].cnt; d++) {
        int k = step_cell(lay[r].keys[d], r, n, term[r * C + c], c < C - 1, r < R - 1, ncol, outb);
        for (int q = 0; q < k; q++) {
          uint64_t t = outb[q];
          if (layer_find(&lay[r + 1], t) >= 0) continue;
          int match = 1;
          for (int j = 0; j <= r && match; j++) {
            int a = gv(t, j), b = gv(target, j);
            int sa = a == EM ? 0 : 1 + color_of(a), sb = b == EM ? 0 : 1 + color_of(b);
            if (sa != sb) match = 0;
          }
          if (match) layer_add(&lay[r + 1], t, (int32_t)d);
        }
      }
    }
    int idx = layer_find(&lay[R], target);
    if (idx < 0) { g_err = 1; ok = -1; }
    for (int r = R; r >= 1 && idx >= 0; r--) {
      uint64_t s = lay[r].keys[idx];
      int ru = gv(s, r - 1), dn = gv(s, r);
      if (ru != EM) right[(r - 1) * C + c] = (signed char)color_of(ru);
      if (dn != EM) down[(r - 1) * C + c] = (signed char)color_of(dn);
      idx = lay[r].pred[idx];
    }
    if (idx >= 0) target = lay[0].keys[idx] >> 3;
    for (int r = 0; r <= R; r++) layer_free(&lay[r]);
    free(ckpt[c]);
    if (ok < 0) { for (int k = 0; k < c; k++) free(ckpt[k]); break; }
  }
  free(lay); free(ckpt); free(ckn);
  if (ok == 1) {
    for (int col = 0; col < 2; col++) {
      if (!present[col]) continue;
      zzn_cell a = C2(-1, -1), b = C2(-1, -1);
      for (int i = 0; i < nt; i++) if (terms[i].col == col) { if (a.r < 0) a = terms[i].x; else b = terms[i].x; }
      path_t *p = &out[col];
      pinit(p); ppush(p, a);
      zzn_cell prv = C2(-1, -1), x = a;
      while (!ceq(x, b)) {
        int r = x.r, cc = x.c, nc = 0;
        zzn_cell cand[4];
        if (right[r * C + cc] == col) cand[nc++] = C2(r, cc + 1);
        if (down[r * C + cc] == col) cand[nc++] = C2(r + 1, cc);
        if (cc > 0 && right[r * C + cc - 1] == col) cand[nc++] = C2(r, cc - 1);
        if (r > 0 && down[(r - 1) * C + cc] == col) cand[nc++] = C2(r - 1, cc);
        zzn_cell nx = C2(-1, -1);
        for (int i = 0; i < nc; i++) if (!ceq(cand[i], prv)) { nx = cand[i]; break; }
        if (nx.r < 0) { g_err = 1; ok = -1; break; }
        prv = x; x = nx; ppush(p, x);
      }
      if (transposed) for (int i = 0; i < p->n; i++) { int t = p->v[i].r; p->v[i].r = p->v[i].c; p->v[i].c = t; }
    }
  }
  free(right); free(down); free(term);
  return ok;
}

static int dp_feasible(const inst_t *I) {
  term_t t[4] = {{I->s0, 0}, {I->t0, 0}, {I->s1, 1}, {I->t1, 1}};
  return plug_dp(I->R, I->C, t, 4, 1, NULL) == 1;
}
static int dp_solve(const inst_t *I, path_t out[2]) {
  term_t t[4] = {{I->s0, 0}, {I->t0, 0}, {I->s1, 1}, {I->t1, 1}};
  return plug_dp(I->R, I->C, t, 4, 0, out);
}

/* -------------------------------------------------------------------- lift ---------- */

static int splice(path_t *ps, int np, zzn_cell u, zzn_cell v, const zzn_cell *mid, int k) {
  for (int q = 0; q < np; q++) {
    path_t *p = &ps[q];
    for (int i = 0; i + 1 < p->n; i++) {
      if (ceq(p->v[i], u) && ceq(p->v[i + 1], v)) { pinsert(p, i, mid, k); return 1; }
      if (ceq(p->v[i], v) && ceq(p->v[i + 1], u)) {
        zzn_cell *rv = xmalloc(sizeof(zzn_cell) * (k + 1));
        for (int j = 0; j < k; j++) rv[j] = mid[k - 1 - j];
        pinsert(p, i, rv, k); free(rv); return 1;
      }
    }
  }
  g_err = 1;
  return 0;
}

static void block_cycle(int w, int L, path_t *cyc) {
  pinit(cyc);
  for (int j = 0; j < L; j++) ppush(cyc, C2(0, j));
  if (w % 2 == 0) {
    for (int i = 1; i < w; i++) {
      if (i % 2 == 1) for (int j = L - 1; j >= 1; j--) ppush(cyc, C2(i, j));
      else for (int j = 1; j < L; j++) ppush(cyc, C2(i, j));
    }
    for (int i = w - 1; i >= 1; i--) ppush(cyc, C2(i, 0));
  } else {
    for (int j = L - 1; j >= 0; j--) {
      if ((L - 1 - j) % 2 == 0) for (int i = 1; i < w; i++) ppush(cyc, C2(i, j));
      else for (int i = w - 1; i >= 1; i--) ppush(cyc, C2(i, j));
    }
  }
}

/* the cycle minus its edge (0,a)-(0,a+1), from (0,a) to (0,a+1), excluding nothing */
static void flip_path(const path_t *cyc, int a, path_t *out) {
  pinit(out);
  for (int i = a; i >= 0; i--) ppush(out, cyc->v[i]);
  for (int i = cyc->n - 1; i > a; i--) ppush(out, cyc->v[i]);
}

static void band_rows(int R, int C, path_t *ps, int np, int r) {
  (void)R;
  for (int q = 0; q < np; q++) for (int i = 0; i < ps[q].n; i++) if (ps[q].v[i].r > r) ps[q].v[i].r += 2;
  int n1 = r + 1, n2 = r + 2;
  int *xs = xmalloc(sizeof(int) * (C + 1)), m = 0;
  for (int q = 0; q < np; q++)
    for (int i = 0; i + 1 < ps[q].n; i++) {
      zzn_cell a = ps[q].v[i], b = ps[q].v[i + 1];
      if (a.c == b.c && ((a.r == r && b.r == r + 3) || (a.r == r + 3 && b.r == r))) xs[m++] = a.c;
    }
  for (int i = 1; i < m; i++) for (int j = i; j > 0 && xs[j - 1] > xs[j]; j--) { int t = xs[j]; xs[j] = xs[j - 1]; xs[j - 1] = t; }
  for (int i = 0; i < m; i++) { zzn_cell mid[2] = {C2(n1, xs[i]), C2(n2, xs[i])}; splice(ps, np, C2(r, xs[i]), C2(r + 3, xs[i]), mid, 2); }
  int nr = m + 1, *lo = xmalloc(sizeof(int) * nr), *hi = xmalloc(sizeof(int) * nr);
  for (int i = 0; i < nr; i++) { lo[i] = (i == 0 ? -1 : xs[i - 1]) + 1; hi[i] = (i == m ? C : xs[i]) - 1; }
  char *horiz = xmalloc(C + 1);
  memset(horiz, 0, C + 1);
  for (int q = 0; q < np; q++)
    for (int i = 0; i + 1 < ps[q].n; i++) {
      zzn_cell a = ps[q].v[i], b = ps[q].v[i + 1];
      if (a.r == r && b.r == r && iabs(a.c - b.c) == 1) horiz[imin(a.c, b.c)] = 1;
    }
  int j = -1;
  for (int i = 0; i < nr && j < 0; i++) if (lo[i] > hi[i]) j = i;
  for (int i = 0; i < nr && j < 0; i++) for (int a = lo[i]; a < hi[i]; a++) if (horiz[a]) { j = i; break; }
  if (j < 0) { g_err = 1; j = 0; }
  path_t mid; pinit(&mid);
  for (int k = 1; k <= m; k++) {
    int c = xs[k - 1], L_ = k <= j ? lo[k - 1] : lo[k], H_ = k <= j ? hi[k - 1] : hi[k];
    if (L_ > H_) continue;
    mid.n = 0;
    if (k <= j) {
      for (int y = c - 1; y >= L_; y--) ppush(&mid, C2(n1, y));
      for (int y = L_; y < c; y++) ppush(&mid, C2(n2, y));
    } else {
      for (int y = c + 1; y <= H_; y++) ppush(&mid, C2(n1, y));
      for (int y = H_; y > c; y--) ppush(&mid, C2(n2, y));
    }
    splice(ps, np, C2(n1, c), C2(n2, c), mid.v, mid.n);
  }
  pfree(&mid);
  if (lo[j] <= hi[j]) {
    int a = -1;
    for (int x = lo[j]; x < hi[j]; x++) if (horiz[x]) { a = x; break; }
    if (a < 0) g_err = 1;
    else {
      path_t cyc, fp;
      block_cycle(2, hi[j] - lo[j] + 1, &cyc);
      for (int i = 0; i < cyc.n; i++) { cyc.v[i].r += n1; cyc.v[i].c += lo[j]; }
      flip_path(&cyc, a - lo[j], &fp);
      splice(ps, np, C2(r, a), C2(r, a + 1), fp.v, fp.n);
      pfree(&cyc); pfree(&fp);
    }
  }
  free(xs); free(lo); free(hi); free(horiz);
}

static void rows_extend(int R, int C, path_t *ps, int np, int k) {
  int free_km1 = k >= 1, free_k = k < R;
  for (int q = 0; q < np; q++) {
    zzn_cell e[2] = {ps[q].v[0], ps[q].v[ps[q].n - 1]};
    for (int i = 0; i < 2; i++) { if (e[i].r == k - 1) free_km1 = 0; if (e[i].r == k) free_k = 0; }
  }
  if (free_km1) { band_rows(R, C, ps, np, k - 1); return; }
  if (free_k) {
    for (int q = 0; q < np; q++) for (int i = 0; i < ps[q].n; i++) ps[q].v[i].r = R - 1 - ps[q].v[i].r;
    band_rows(R, C, ps, np, R - 1 - k);
    for (int q = 0; q < np; q++) for (int i = 0; i < ps[q].n; i++) ps[q].v[i].r = R + 1 - ps[q].v[i].r;
    return;
  }
  g_err = 1;
}

static void tp_paths(path_t *ps, int np) {
  for (int q = 0; q < np; q++) for (int i = 0; i < ps[q].n; i++) { int t = ps[q].v[i].r; ps[q].v[i].r = ps[q].v[i].c; ps[q].v[i].c = t; }
}

/* insert two empty lines at position k on the axis (in place) */
static void extend(int R, int C, path_t *ps, int np, int axis, int k) {
  if (axis == 0) { rows_extend(R, C, ps, np, k); return; }
  tp_paths(ps, np);
  rows_extend(C, R, ps, np, k);
  tp_paths(ps, np);
}

static void add_block(int R, int C, path_t *ps, int np, int w) {
  int a = -1;
  for (int q = 0; q < np && a < 0; q++)
    for (int i = 0; i + 1 < ps[q].n; i++) {
      zzn_cell x = ps[q].v[i], y = ps[q].v[i + 1];
      if (x.r == R - 1 && y.r == R - 1 && iabs(x.c - y.c) == 1) { a = imin(x.c, y.c); break; }
    }
  if (a < 0) { g_err = 1; return; }
  path_t cyc, fp;
  block_cycle(w, C, &cyc);
  for (int i = 0; i < cyc.n; i++) cyc.v[i].r += R;
  flip_path(&cyc, a, &fp);
  splice(ps, np, C2(R - 1, a), C2(R - 1, a + 1), fp.v, fp.n);
  pfree(&cyc); pfree(&fp);
}

/* --------------------------------------------------------------------- IPS ---------- */

static int par(zzn_cell v) { return (v.r + v.c) % 2; }
static int color_compatible(int R, int C, zzn_cell s, zzn_cell t) {
  if ((R * C) % 2 == 1) return par(s) == 0 && par(t) == 0;
  return par(s) != par(t);
}
static int is_corner(int w, int h, zzn_cell v) {
  return ceq(v, C2(0, 0)) || ceq(v, C2(w - 1, 0)) || ceq(v, C2(0, h - 1)) || ceq(v, C2(w - 1, h - 1));
}
static int forbidden(int w, int h, zzn_cell s, zzn_cell t) {
  if (w == 1 || h == 1) {
    int isw = w == 1, bound = isw ? h : w;
    zzn_cell far = isw ? C2(0, bound - 1) : C2(bound - 1, 0);
    return !((ceq(s, C2(0, 0)) && ceq(t, far)) || (ceq(s, far) && ceq(t, C2(0, 0))));
  }
  if (w == 2 || h == 2)
    return !is_corner(w, h, s) && !is_corner(w, h, t) && ((w == 2 && s.c == t.c) || (h == 2 && s.r == t.r));
  if (w == 3 || h == 3) {
    int isw = w == 3, opp = isw ? h : w;
    if (!(opp % 2 == 0 && par(s) != par(t))) return 0;
    int c0 = isw ? s.c : s.r, c1 = isw ? t.c : t.r, oc = isw ? s.r : s.c;
    int greater = c1 < c0, dist = greater ? c0 - c1 : c1 - c0;
    int dist_ok = oc == 1 ? dist > 0 : dist > 1;
    return dist_ok && ((greater && par(s) != 1) || (!greater && par(s) != 0));
  }
  return 0;
}

int zzn_acceptable(int R, int C, zzn_cell s, zzn_cell t) {
  if (ceq(s, t)) return R * C == 1;
  if (!(s.r >= 0 && s.r < R && s.c >= 0 && s.c < C && t.r >= 0 && t.r < R && t.c >= 0 && t.c < C)) return 0;
  return color_compatible(R, C, s, t) && !forbidden(R, C, s, t);
}

static zzn_cell sh(zzn_cell v, int dr, int dc) { return C2(v.r + dr, v.c + dc); }

static int ham(int R, int C, zzn_cell s, zzn_cell t, path_t *out);

static int ham_extend(int R, int C, zzn_cell s, zzn_cell t, int axis, int k, path_t *out) {
  if (!ham(R, C, s, t, out)) return 0;
  extend(R, C, out, 1, axis, k);
  return 1;
}

static int ham(int R, int C, zzn_cell s, zzn_cell t, path_t *out) {
  pinit(out);
  if (!zzn_acceptable(R, C, s, t)) return 0;
  if (ceq(s, t)) { ppush(out, s); return 1; }
  if (imin(R, C) <= SMALL) {
    term_t tt[2] = {{s, 0}, {t, 0}};
    path_t o[2];
    if (plug_dp(R, C, tt, 2, 0, o) != 1) { g_err = 1; return 0; }
    *out = o[0];
    return 1;
  }
  if (s.r >= 3 && t.r >= 3 && zzn_acceptable(R - 2, C, sh(s, -2, 0), sh(t, -2, 0)))
    return ham_extend(R - 2, C, sh(s, -2, 0), sh(t, -2, 0), 0, 0, out);
  if (s.r < R - 3 && t.r < R - 3 && zzn_acceptable(R - 2, C, s, t)) return ham_extend(R - 2, C, s, t, 0, R - 2, out);
  if (s.c >= 3 && t.c >= 3 && zzn_acceptable(R, C - 2, sh(s, 0, -2), sh(t, 0, -2)))
    return ham_extend(R, C - 2, sh(s, 0, -2), sh(t, 0, -2), 1, 0, out);
  if (s.c < C - 3 && t.c < C - 3 && zzn_acceptable(R, C - 2, s, t)) return ham_extend(R, C - 2, s, t, 1, C - 2, out);
  zzn_cell a = s.r <= t.r ? s : t, b = s.r <= t.r ? t : s;
  for (int p = a.r + 1; p <= b.r; p++)
    for (int y = 0; y < C; y++) {
      zzn_cell u = C2(p - 1, y);
      if (zzn_acceptable(p, C, a, u) && zzn_acceptable(R - p, C, C2(0, y), C2(b.r - p, b.c))) {
        path_t top, bot;
        ham(p, C, a, u, &top);
        ham(R - p, C, C2(0, y), C2(b.r - p, b.c), &bot);
        for (int i = 0; i < bot.n; i++) bot.v[i].r += p;
        pappend(&top, &bot); pfree(&bot);
        if (!ceq(top.v[0], s)) prev_(&top);
        *out = top;
        return 1;
      }
    }
  a = s.c <= t.c ? s : t; b = s.c <= t.c ? t : s;
  for (int p = a.c + 1; p <= b.c; p++)
    for (int x = 0; x < R; x++) {
      zzn_cell u = C2(x, p - 1);
      if (zzn_acceptable(R, p, a, u) && zzn_acceptable(R, C - p, C2(x, 0), C2(b.r, b.c - p))) {
        path_t left, rgt;
        ham(R, p, a, u, &left);
        ham(R, C - p, C2(x, 0), C2(b.r, b.c - p), &rgt);
        for (int i = 0; i < rgt.n; i++) rgt.v[i].c += p;
        pappend(&left, &rgt); pfree(&rgt);
        if (!ceq(left.v[0], s)) prev_(&left);
        *out = left;
        return 1;
      }
    }
  term_t tt[2] = {{s, 0}, {t, 0}};
  path_t o[2];
  if (plug_dp(R, C, tt, 2, 0, o) != 1) return 0;
  *out = o[0];
  return 1;
}

int zzn_hamiltonian_path(int R, int C, zzn_cell s, zzn_cell t, zzn_path *out) {
  path_t p;
  g_err = 0;
  if (!ham(R, C, s, t, &p)) { pfree(&p); out->cells = NULL; out->len = 0; return 0; }
  out->cells = p.v; out->len = p.n;
  return 1;
}

/* ------------------------------------------------------------------ solver ---------- */

typedef struct { char *buf; size_t n, cap; } sbuf_t;
static void sb_add(sbuf_t *b, const char *s) {
  size_t k = strlen(s);
  if (b->n + k + 1 > b->cap) { b->cap = (b->n + k + 1) * 2; b->buf = xrealloc(b->buf, b->cap); }
  memcpy(b->buf + b->n, s, k + 1); b->n += k;
}

typedef struct { int key[10]; int val; } fe_t;
typedef struct {
  fe_t *tab; size_t cap, cnt;      /* feasibility cache for thin pieces */
  sbuf_t *trace; int nested;       /* trace lines; moves are inserted before their pieces */
} solver_t;

static size_t fe_hash(const int *k) {
  uint64_t h = 1469598103934665603ULL;
  for (int i = 0; i < 10; i++) { h ^= (uint64_t)(unsigned)k[i]; h *= 1099511628211ULL; }
  return (size_t)h;
}
static void inst_key(const inst_t *J, int *k) {
  k[0] = J->R; k[1] = J->C; k[2] = J->s0.r; k[3] = J->s0.c; k[4] = J->t0.r; k[5] = J->t0.c;
  k[6] = J->s1.r; k[7] = J->s1.c; k[8] = J->t1.r; k[9] = J->t1.c;
}
static int fe_get(solver_t *S, const inst_t *J, int *val) {
  if (!S->tab) return 0;
  int k[10]; inst_key(J, k);
  for (size_t i = fe_hash(k) & (S->cap - 1);; i = (i + 1) & (S->cap - 1)) {
    if (S->tab[i].val < 0) return 0;
    if (!memcmp(S->tab[i].key, k, sizeof(k))) { *val = S->tab[i].val; return 1; }
  }
}
static void fe_put(solver_t *S, const inst_t *J, int val) {
  if (!S->tab || (S->cnt + 1) * 2 > S->cap) {
    size_t oc = S->cap; fe_t *old = S->tab;
    S->cap = oc ? oc * 2 : 1024; S->tab = xmalloc(sizeof(fe_t) * S->cap);
    for (size_t i = 0; i < S->cap; i++) S->tab[i].val = -1;
    S->cnt = 0;
    for (size_t i = 0; i < oc; i++) if (old[i].val >= 0) {
      size_t j = fe_hash(old[i].key) & (S->cap - 1);
      while (S->tab[j].val >= 0) j = (j + 1) & (S->cap - 1);
      S->tab[j] = old[i]; S->cnt++;
    }
    free(old);
  }
  int k[10]; inst_key(J, k);
  size_t i = fe_hash(k) & (S->cap - 1);
  while (S->tab[i].val >= 0) i = (i + 1) & (S->cap - 1);
  memcpy(S->tab[i].key, k, sizeof(k)); S->tab[i].val = val; S->cnt++;
}

static void tlog(solver_t *S, const char *line) { if (S->trace) { sb_add(S->trace, line); sb_add(S->trace, "\n"); } }

static int tw(int w, int h) { return (w <= THIN || h <= THIN) ? imin(w, h) : 0; }
static int parity_ok_i(const inst_t *J) {
  zzn_cell e[4]; ends4(J, e);
  int s = 0;
  for (int i = 0; i < 4; i++) s += ((e[i].r + e[i].c) % 2 == 0) ? 1 : -1;
  return s == 2 * ((J->R * J->C) % 2);
}

static int find_reduction(const inst_t *I, int *axis_out, int *d_out) {
  zzn_cell e[4]; ends4(I, e);
  for (int axis = 0; axis < 2; axis++) {
    int n = axis == 0 ? I->R : I->C, lines[4];
    if (n < 13) continue;
    for (int i = 0; i < 4; i++) lines[i] = axis == 0 ? e[i].r : e[i].c;
#define FREE(k) (lines[0] != (k) && lines[1] != (k) && lines[2] != (k) && lines[3] != (k))
#define BELOW(k) (lines[0] < (k) || lines[1] < (k) || lines[2] < (k) || lines[3] < (k))
#define ABOVE(k) (lines[0] > (k) || lines[1] > (k) || lines[2] > (k) || lines[3] > (k))
    if (FREE(0) && FREE(1) && FREE(2) && FREE(3)) { *axis_out = axis; *d_out = 0; return 1; }
    if (FREE(n - 4) && FREE(n - 3) && FREE(n - 2) && FREE(n - 1)) { *axis_out = axis; *d_out = n - 2; return 1; }
    for (int lo = 0; lo < n - 9; lo++) {
      int all = 1;
      for (int k = lo; k < lo + 10; k++) if (!FREE(k)) all = 0;
      if (all && BELOW(lo) && ABOVE(lo + 9)) { *axis_out = axis; *d_out = lo + 4; return 1; }
    }
    for (int d = 8; d < n - 9; d++)
      if (FREE(d) && FREE(d + 1) && ((d >= 1 && FREE(d - 1)) || FREE(d + 2)) && BELOW(d) && ABOVE(d + 1)) {
        *axis_out = axis; *d_out = d; return 1;
      }
#undef FREE
#undef BELOW
#undef ABOVE
  }
  return 0;
}

static inst_t delete_lines(const inst_t *I, int axis, int d) {
  zzn_cell e[4]; ends4(I, e);
  for (int i = 0; i < 4; i++) {
    int *v = axis == 0 ? &e[i].r : &e[i].c;
    if (*v > d + 1) *v -= 2;
  }
  return mk(axis == 0 ? I->R - 2 : I->R, axis == 0 ? I->C : I->C - 2, e[0], e[1], e[2], e[3]);
}

static int solve_rec(solver_t *S, const inst_t *I, path_t out[2]);

static int piece_ok(solver_t *S, const inst_t *J) {
  if (!well_formed(J)) return 0;
  if (J->R <= THIN || J->C <= THIN) {
    if (!parity_ok_i(J)) return 0;
    int v;
    if (!fe_get(S, J, &v)) { v = dp_feasible(J); fe_put(S, J, v); }
    return v;
  }
  return fires_i(J) == NULL;
}

static int piece_solve(solver_t *S, const inst_t *J, path_t out[2]) {
  if (solve_rec(S, J, out) != 1) { g_err = 1; return 0; }
  return 1;
}

static const lab_t LABS0[1] = {{0,0,0}}, LABS1[2] = {{0,0,0},{0,0,1}}, LABS2[4] = {{0,0,0},{1,0,0},{0,0,1},{0,1,1}},
                   LABS3[4] = {{0,0,0},{1,0,0},{0,1,0},{1,1,0}}, LABS4[2] = {{0,0,0},{0,0,1}};
static const lab_t *LABS[5] = {LABS0, LABS1, LABS2, LABS3, LABS4};
static const int NLABS[5] = {1, 2, 4, 4, 2};
static const char *MOVE_NAMES[5] = {"strip", "2/2 same", "1/3", "2/2 cross", "excursion"};

static zzn_cell shr(zzn_cell x, int p) { return C2(x.r - p, x.c); }
static void up_shift(path_t *p, int k) { for (int i = 0; i < p->n; i++) p->v[i].r += k; }

/* canonical move of type t (cut between rows p-1 and p) with widest thin piece of width m;
 * returns 1 with sol (labelling of J) and *pcut, or 0 */
static int canon(solver_t *S, int t, int m, const inst_t *J, path_t sol[2], int *pcut) {
  int R = J->R, C = J->C;
  zzn_cell s0 = J->s0, t0 = J->t0, s1 = J->s1, t1 = J->t1;
  for (int p = 1; p < R; p++) {
    *pcut = p;
    if (t == 0) {
      if (imax(imax(s0.r, t0.r), imax(s1.r, t1.r)) < p && R - p >= 2 && ((R - p) * C) % 2 == 0 && C >= 5 && tw(p, C) == m) {
        inst_t L = mk(p, C, s0, t0, s1, t1);
        if (piece_ok(S, &L)) {
          if (!piece_solve(S, &L, sol)) return 0;
          add_block(p, C, sol, 2, R - p);
          return 1;
        }
      }
    } else if (t == 1) {
      if (m == 0 && s0.r < p && t0.r < p && s1.r >= p && t1.r >= p && zzn_acceptable(p, C, s0, t0) &&
          zzn_acceptable(R - p, C, shr(s1, p), shr(t1, p))) {
        ham(p, C, s0, t0, &sol[0]);
        ham(R - p, C, shr(s1, p), shr(t1, p), &sol[1]);
        up_shift(&sol[1], p);
        return 1;
      }
    } else if (t == 2) {
      if (s0.r < p && t0.r >= p && s1.r >= p && t1.r >= p && tw(R - p, C) == m) {
        for (int y = 0; y < C; y++) {
          if (!zzn_acceptable(p, C, s0, C2(p - 1, y))) continue;
          inst_t Rr = mk(R - p, C, C2(0, y), shr(t0, p), shr(s1, p), shr(t1, p));
          if (piece_ok(S, &Rr)) {
            path_t r2[2];
            ham(p, C, s0, C2(p - 1, y), &sol[0]);
            if (!piece_solve(S, &Rr, r2)) return 0;
            up_shift(&r2[0], p); up_shift(&r2[1], p);
            pappend(&sol[0], &r2[0]); pfree(&r2[0]);
            sol[1] = r2[1];
            return 1;
          }
        }
      }
    } else if (t == 3) {
      if (s0.r < p && s1.r < p && t0.r >= p && t1.r >= p && imax(tw(p, C), tw(R - p, C)) == m) {
        for (int y0 = 0; y0 < C; y0++)
          for (int y1 = 0; y1 < C; y1++) {
            inst_t L = mk(p, C, s0, C2(p - 1, y0), s1, C2(p - 1, y1));
            inst_t Rr = mk(R - p, C, C2(0, y0), shr(t0, p), C2(0, y1), shr(t1, p));
            const inst_t *first = p <= R - p ? &L : &Rr, *second = p <= R - p ? &Rr : &L;
            if (piece_ok(S, first) && piece_ok(S, second)) {
              path_t r2[2];
              if (!piece_solve(S, &L, sol)) return 0;
              if (!piece_solve(S, &Rr, r2)) return 0;
              up_shift(&r2[0], p); up_shift(&r2[1], p);
              pappend(&sol[0], &r2[0]); pappend(&sol[1], &r2[1]);
              pfree(&r2[0]); pfree(&r2[1]);
              return 1;
            }
          }
      }
    } else {
      if (s0.r < p && t0.r < p && s1.r >= p && t1.r >= p && imax(tw(p, C), tw(R - p, C)) == m) {
        for (int ya = 0; ya < C; ya++)
          for (int yb = 0; yb < C; yb++) {
            inst_t N = mk(p, C, s0, C2(p - 1, ya), C2(p - 1, yb), t0);
            inst_t F = mk(R - p, C, shr(s1, p), shr(t1, p), C2(0, ya), C2(0, yb));
            const inst_t *first = p <= R - p ? &N : &F, *second = p <= R - p ? &F : &N;
            if (piece_ok(S, first) && piece_ok(S, second)) {
              path_t nn[2], ff[2];
              if (!piece_solve(S, &N, nn)) return 0;
              if (!piece_solve(S, &F, ff)) return 0;
              up_shift(&ff[0], p); up_shift(&ff[1], p);
              pinit(&sol[0]);
              pappend(&sol[0], &nn[0]); pappend(&sol[0], &ff[1]); pappend(&sol[0], &nn[1]);
              pfree(&nn[0]); pfree(&nn[1]); pfree(&ff[1]);
              sol[1] = ff[0];
              return 1;
            }
          }
      }
    }
  }
  return 0;
}

static void cut_back(geo_t g, const inst_t *I, int p, int *axis, int *k) {
  int R2 = g.tr ? I->C : I->R;
  *k = g.fr ? R2 - p : p;
  *axis = g.tr ? 1 : 0;
}

static int solve_rec(solver_t *S, const inst_t *I, path_t out[2]) {
  char line[160];
  if (imin(I->R, I->C) <= THIN) {
    snprintf(line, sizeof line, "  thin %dx%d", I->R, I->C); tlog(S, line);
    int r = dp_solve(I, out);
    return r == 1 ? 1 : (r == 0 ? 0 : -1);
  }
  const char *f = fires_i(I);
  if (f) { snprintf(line, sizeof line, "  fires %dx%d: %s", I->R, I->C, f); tlog(S, line); return 0; }
  int axis, d;
  if (find_reduction(I, &axis, &d)) {
    snprintf(line, sizeof line, "  reduce %dx%d: delete %s %d,%d", I->R, I->C, axis == 0 ? "rows" : "columns", d, d + 1);
    tlog(S, line);
    inst_t Ir = delete_lines(I, axis, d);
    path_t s[2];
    if (solve_rec(S, &Ir, s) != 1) { g_err = 1; return -1; }
    extend(Ir.R, Ir.C, s, 2, axis, d);
    return orient(I, s, out) ? 1 : -1;
  }
  /* same-colour split */
  geo_t gs[2] = {{0,0,0},{1,0,0}};
  for (int gi = 0; gi < 2; gi++) {
    inst_t J0 = apply_geo(gs[gi], I);
    lab_t sw = {0, 0, 1};
    inst_t Js[2] = {J0, relabel(sw, &J0)};
    for (int ji = 0; ji < 2; ji++) {
      inst_t *J = &Js[ji];
      for (int p = 1; p < J->R; p++) {
        if (J->s0.r < p && J->t0.r < p && J->s1.r >= p && J->t1.r >= p && zzn_acceptable(p, J->C, J->s0, J->t0) &&
            zzn_acceptable(J->R - p, J->C, shr(J->s1, p), shr(J->t1, p))) {
          snprintf(line, sizeof line, "  same %dx%d: cut between %s %d and %d", I->R, I->C, gs[gi].tr ? "columns" : "rows", p - 1, p);
          tlog(S, line);
          path_t s[2];
          ham(p, J->C, J->s0, J->t0, &s[0]);
          ham(J->R - p, J->C, shr(J->s1, p), shr(J->t1, p), &s[1]);
          up_shift(&s[1], p);
          return map_back(gs[gi], I, s, out) ? 1 : -1;
        }
      }
    }
  }
  /* moves */
  for (int m = 0; m <= THIN; m++)
    for (int t = 0; t < 5; t++)
      for (int gi = 0; gi < 8; gi++)
        for (int li = 0; li < NLABS[t]; li++) {
          inst_t G = apply_geo(GEOS[gi], I);
          inst_t J = relabel(LABS[t][li], &G);
          size_t mark = S->trace ? S->trace->n : 0;
          path_t s[2];
          int p;
          if (canon(S, t, m, &J, s, &p)) {
            if (S->trace) {
              int ax, k;
              cut_back(GEOS[gi], I, p, &ax, &k);
              snprintf(line, sizeof line, "  move %dx%d: %s, cut between %s %d and %d\n", I->R, I->C, MOVE_NAMES[t],
                       ax == 0 ? "rows" : "columns", k - 1, k);
              size_t k2 = strlen(line), tail = S->trace->n - mark;
              if (S->trace->n + k2 + 1 > S->trace->cap) { S->trace->cap = (S->trace->n + k2 + 1) * 2; S->trace->buf = xrealloc(S->trace->buf, S->trace->cap); }
              memmove(S->trace->buf + mark + k2, S->trace->buf + mark, tail + 1);
              memcpy(S->trace->buf + mark, line, k2);
              S->trace->n += k2;
            }
            return map_back(GEOS[gi], I, s, out) ? 1 : -1;
          }
          if (g_err) return -1;
        }
  g_err = 1;
  return -1;
}

/* ------------------------------------------------------------------- public ---------- */

/* --------------------------------------------------------------- optimized ---------- */
/* Optimized solving for thin instances: guess splits, fall back to the plug DP. Same algorithm,
 * parameters and candidate order as lib/python/zzn/optimized.py (see its docstring), so the paths
 * are the same. The plug DP's cost grows exponentially with the shorter side; cutting a thin grid
 * into pieces with a short side makes it cheap. A piece is reported unsolvable only after an exact
 * test (parity, IPS, or the plug DP), so the answers are exact. */

#define OPT_MARGIN 3
#define OPT_NARROW 6
#define OPT_AREA 60
#define OPT_SMALL 7
#define OPT_TRIES 4
#define OPT_CUTS 2
#define OPT_BUDGET 1
#define OPT_NOGUESS 2   /* opt_guess: no guess passes the cheap exact tests */

/* the trace, and the work done so far in estimated plug DP steps (opt_est) */
typedef struct { sbuf_t *trace; long long work; } opt_t;

/* estimated plug DP cost of an R x C piece: cells times a bound on the states per cell */
static long long opt_est(int R, int C) {
  long long e = (long long)R * C;
  for (int i = imin(R, C); i > 0; i--) e *= 3;
  return e;
}

static void opt_log(opt_t *O, const char *kind, int R, int C, const char *detail) {
  char line[160];
  if (!O->trace) return;
  if (detail) snprintf(line, sizeof line, "  %s %dx%d: %s", kind, R, C, detail);
  else snprintf(line, sizeof line, "  %s %dx%d", kind, R, C);
  sb_add(O->trace, line); sb_add(O->trace, "\n");
}

static int opt_colours(const term_t *t, int nt, int present[2]) {
  present[0] = present[1] = 0;
  for (int i = 0; i < nt; i++) present[t[i].col] = 1;
  return present[0] + present[1];
}
static void opt_transpose(const term_t *t, int nt, term_t *o) {
  for (int i = 0; i < nt; i++) { o[i].x = C2(t[i].x.c, t[i].x.r); o[i].col = t[i].col; }
}
static void opt_shift(const term_t *t, int nt, int dc, term_t *o) {
  for (int i = 0; i < nt; i++) { o[i].x = C2(t[i].x.r, t[i].x.c + dc); o[i].col = t[i].col; }
}
static void path_shift(path_t *p, int dc) { for (int i = 0; i < p->n; i++) p->v[i].c += dc; }
static void path_transpose(path_t *p) { for (int i = 0; i < p->n; i++) { int x = p->v[i].r; p->v[i].r = p->v[i].c; p->v[i].c = x; } }
static void paths_free(path_t out[2], const int present[2]) { for (int k = 0; k < 2; k++) if (present[k]) pfree(&out[k]); }

/* each colour's path starts at that colour's first term */
static void opt_orient(path_t out[2], const term_t *t, int nt) {
  for (int k = 0; k < 2; k++)
    for (int i = 0; i < nt; i++)
      if (t[i].col == k) { if (out[k].n && !ceq(out[k].v[0], t[i].x)) prev_(&out[k]); break; }
}

static int floordiv(int a, int b) {
  int q = a / b;
  if (a % b != 0 && ((a < 0) != (b < 0))) q--;
  return q;
}

static int cmp_int3(const void *a, const void *b) {
  const int *x = a, *y = b;
  for (int i = 0; i < 3; i++) if (x[i] != y[i]) return x[i] < y[i] ? -1 : 1;
  return 0;
}
static int cmp_int4(const void *a, const void *b) {
  const int *x = a, *y = b;
  for (int i = 0; i < 4; i++) if (x[i] != y[i]) return x[i] < y[i] ? -1 : 1;
  return 0;
}

/* Cuts between columns m-1 and m with at least `margin` endpoint-free columns on each side and both
 * pieces at least 2 wide, best first: strips (the empty block of even area, largest first), then
 * cuts in the gaps between endpoint columns, farthest from the endpoints first, ties nearest the
 * middle. Returns the number of cuts written to ms. */
static int opt_cuts(int R, int C, const term_t *t, int nt, int margin, int *ms) {
  int xs[4], nx = 0, n = 0;
  for (int i = 0; i < nt; i++) {
    int x = t[i].x.c, j = 0;
    while (j < nx && xs[j] < x) j++;
    if (j < nx && xs[j] == x) continue;
    for (int q = nx; q > j; q--) xs[q] = xs[q - 1];
    xs[j] = x; nx++;
  }
  int sw[2], sm[2], ns = 0;
  int m = xs[0] - margin;
  if (m >= 2 && (m * R) % 2 == 1) m--;
  if (m >= 2) { sw[ns] = m; sm[ns] = m; ns++; }
  m = xs[nx - 1] + 1 + margin;
  if (C - m >= 2 && ((C - m) * R) % 2 == 1) m++;
  if (C - m >= 2) { sw[ns] = C - m; sm[ns] = m; ns++; }
  if (ns == 2 && (sw[1] > sw[0] || (sw[1] == sw[0] && sm[1] < sm[0]))) {
    int a = sw[0], b = sm[0]; sw[0] = sw[1]; sm[0] = sm[1]; sw[1] = a; sm[1] = b;
  }
  for (int i = 0; i < ns; i++) ms[n++] = sm[i];
  int (*inner)[3] = xmalloc(sizeof(int[3]) * (C + 1)), ni = 0;
  for (int i = 0; i + 1 < nx; i++) {
    int a = xs[i], b = xs[i + 1];
    for (int mm = a + 1 + margin; mm <= b - margin; mm++) {
      inner[ni][0] = -imin(mm - 1 - a, b - mm); inner[ni][1] = iabs(2 * mm - C); inner[ni][2] = mm; ni++;
    }
  }
  qsort(inner, ni, sizeof(int[3]), cmp_int3);
  for (int i = 0; i < ni; i++) ms[n++] = inner[i][2];
  free(inner);
  return n;
}

/* Cuts to try, as (transposed, m): across the longer side first, then the shorter; with MARGIN
 * free lines next to the cut, then with 1. Returns the count; trs and ms are malloc'd. */
static int opt_options(int R, int C, const term_t *t, int nt, int **trs, int **ms) {
  int axes[2] = {C >= R ? 0 : 1, C >= R ? 1 : 0}, margins[2] = {OPT_MARGIN, 1}, n = 0;
  int cap = 4 * (R + C) + 8;
  int *ot = xmalloc(sizeof(int) * cap), *om = xmalloc(sizeof(int) * cap), *buf = xmalloc(sizeof(int) * (R + C + 4));
  for (int a = 0; a < 2; a++)
    for (int b = 0; b < 2; b++) {
      int tr = axes[b];
      term_t tt[4];
      if (tr) opt_transpose(t, nt, tt); else memcpy(tt, t, sizeof(term_t) * nt);
      int k = opt_cuts(tr ? C : R, tr ? R : C, tt, nt, margins[a], buf);
      for (int i = 0; i < k; i++) {
        int seen = 0;
        for (int j = 0; j < n && !seen; j++) if (ot[j] == tr && om[j] == buf[i]) seen = 1;
        if (!seen) { ot[n] = tr; om[n] = buf[i]; n++; }
      }
    }
  free(buf);
  *trs = ot; *ms = om;
  return n;
}

static int opt_viable(int R, int C, const term_t *t, int nt) {
  int present[2];
  if (!terms_parity_ok(R, C, t, nt)) return 0;
  if (opt_colours(t, nt, present) == 1) return zzn_acceptable(R, C, t[0].x, t[1].x);
  return 1;
}

static int opt_piece(opt_t *O, int R, int C, const term_t *t, int nt, path_t out[2]);

/* both pieces of a guess: the one-path piece first, else the smaller one first */
static int opt_pair(opt_t *O, int R, int C, int m, const term_t *lt, int nlt, const term_t *rt, int nrt,
                    path_t A[2], path_t B[2]) {
  int pl[2], pr[2];
  int nl = opt_colours(lt, nlt, pl), nr = opt_colours(rt, nrt, pr);
  int left_first = nl < nr || (nl == nr && m <= C - m), r;
  if (left_first) {
    if ((r = opt_piece(O, R, m, lt, nlt, A)) != 1) return r;
    if ((r = opt_piece(O, R, C - m, rt, nrt, B)) != 1) { paths_free(A, pl); return r; }
  } else {
    if ((r = opt_piece(O, R, C - m, rt, nrt, B)) != 1) return r;
    if ((r = opt_piece(O, R, m, lt, nlt, A)) != 1) { paths_free(B, pr); return r; }
  }
  return 1;
}

/* All endpoints on one side of the cut: solve that side, then splice the empty block into a path
 * running along the cut. */
static int opt_strip(opt_t *O, int R, int C, const term_t *t, int nt, int m, int left, path_t out[2]) {
  char d[64];
  int present[2], r, edge, w;
  snprintf(d, sizeof d, "strip, column %d", m);
  opt_log(O, "split", R, C, d);
  opt_colours(t, nt, present);
  if (left) {
    r = opt_piece(O, R, m, t, nt, out);
    edge = m - 1; w = C - m;
  } else {
    term_t s[4];
    opt_shift(t, nt, -m, s);
    r = opt_piece(O, R, C - m, s, nt, out);
    if (r == 1) for (int k = 0; k < 2; k++) if (present[k]) path_shift(&out[k], m);
    edge = m; w = m;
  }
  if (r != 1) return r;
  char *used = calloc((size_t)R, 1);
  for (int k = 0; k < 2; k++) {
    if (!present[k]) continue;
    for (int i = 0; i + 1 < out[k].n; i++) {
      zzn_cell u = out[k].v[i], v = out[k].v[i + 1];
      if (u.c == edge && v.c == edge && iabs(u.r - v.r) == 1) used[imin(u.r, v.r)] = 1;
    }
  }
  for (int a = 0; a + 1 < R; a++) {
    if (!used[a]) continue;
    path_t cyc, fp, ps[2];
    int ks[2], np = 0;
    block_cycle(w, R, &cyc);
    flip_path(&cyc, a, &fp);
    for (int i = 0; i < fp.n; i++) {
      int bi = fp.v[i].r, bj = fp.v[i].c;
      fp.v[i] = left ? C2(bj, m + bi) : C2(bj, m - 1 - bi);
    }
    for (int k = 0; k < 2; k++) if (present[k]) { ks[np] = k; ps[np++] = out[k]; }
    int ok = splice(ps, np, C2(a, edge), C2(a + 1, edge), fp.v, fp.n);
    for (int i = 0; i < np; i++) out[ks[i]] = ps[i];
    pfree(&cyc); pfree(&fp); free(used);
    if (!ok) { paths_free(out, present); return -1; }
    return 1;
  }
  free(used);
  paths_free(out, present);
  return 0;
}

/* Paths for the piece by one of the guesses at cut m: 1, 0 if they all fail, OPT_NOGUESS if no
 * guess passes the cheap exact tests, -1 on error. */
static int opt_guess(opt_t *O, int R, int C, const term_t *t, int nt, int m, int tries, long long limit, path_t out[2]) {
  term_t L[4], Rt[4], Rs[4];
  int nl = 0, nr = 0, present[2], split[2], nsplit = 0;
  char d[96];
  for (int i = 0; i < nt; i++) { if (t[i].x.c < m) L[nl++] = t[i]; else Rt[nr++] = t[i]; }
  if (!nl || !nr) return opt_strip(O, R, C, t, nt, m, nl > 0, out);
  opt_colours(t, nt, present);
  for (int k = 0; k < 2; k++) {
    if (!present[k]) continue;
    int c = 0;
    for (int i = 0; i < nl; i++) if (L[i].col == k) c++;
    if (c == 1) split[nsplit++] = k;
  }
  opt_shift(Rt, nr, -m, Rs);
  if (!nsplit) {
    if (!(opt_viable(R, m, L, nl) && opt_viable(R, C - m, Rs, nr))) return OPT_NOGUESS;
    snprintf(d, sizeof d, "same, column %d", m);
    opt_log(O, "split", R, C, d);
    path_t pl[2], pr[2];
    int ql[2], qr[2], r;
    opt_colours(L, nl, ql); opt_colours(Rs, nr, qr);
    if ((r = opt_piece(O, R, m, L, nl, pl)) != 1) return r;
    if ((r = opt_piece(O, R, C - m, Rs, nr, pr)) != 1) { paths_free(pl, ql); return r; }
    for (int k = 0; k < 2; k++) {
      if (ql[k]) out[k] = pl[k];
      if (qr[k]) { path_shift(&pr[k], m); out[k] = pr[k]; }
    }
    return 1;
  }

  /* Crossings on the border rows or next to each other come last; then the distance from the
   * straight line between that colour's two endpoints; ties by row. */
  int tgt[2];
  for (int i = 0; i < nsplit; i++) {
    zzn_cell lo = C2(0, 0), hi = C2(0, 0);
    int k = split[i], fl = 0, fh = 0;
    for (int j = 0; j < nl; j++) if (!fl && L[j].col == k) { lo = L[j].x; fl = 1; }
    for (int j = 0; j < nr; j++) if (!fh && Rt[j].col == k) { hi = Rt[j].x; fh = 1; }
    tgt[i] = lo.r + floordiv((hi.r - lo.r) * (2 * (m - lo.c) - 1), 2 * (hi.c - lo.c));
  }
  int (*cand)[4] = xmalloc(sizeof(int[4]) * (R * R + 1)), nc = 0;
  for (int a = 0; a < R; a++)
    for (int b = 0; b < (nsplit == 2 ? R : 1); b++) {
      if (nsplit == 2 && a == b) continue;
      int rows[2] = {a, b}, pen = 0, dist = 0;
      for (int i = 0; i < nsplit; i++) {
        if (rows[i] == 0 || rows[i] == R - 1) pen++;
        dist += iabs(rows[i] - tgt[i]);
      }
      if (nsplit == 2 && iabs(a - b) == 1) pen++;
      cand[nc][0] = pen; cand[nc][1] = dist; cand[nc][2] = a; cand[nc][3] = b; nc++;
    }
  qsort(cand, nc, sizeof(int[4]), cmp_int4);
  int tried = 0, res = 0;
  for (int ci = 0; ci < nc; ci++) {
    int rows[2] = {cand[ci][2], cand[ci][3]};
    term_t lt[4], rt[4];
    int nlt = nl, nrt = nr;
    memcpy(lt, L, sizeof(term_t) * nl); memcpy(rt, Rs, sizeof(term_t) * nr);
    for (int i = 0; i < nsplit; i++) {
      lt[nlt].x = C2(rows[i], m - 1); lt[nlt++].col = split[i];
      rt[nrt].x = C2(rows[i], 0); rt[nrt++].col = split[i];
    }
    if (!(opt_viable(R, m, lt, nlt) && opt_viable(R, C - m, rt, nrt))) continue;
    if (tried == tries || O->work >= limit) break;
    tried++;
    if (nsplit == 2) snprintf(d, sizeof d, "2/2 cross, column %d, rows %d,%d", m, rows[0], rows[1]);
    else snprintf(d, sizeof d, "1/3, column %d, rows %d", m, rows[0]);
    opt_log(O, "split", R, C, d);
    path_t A[2], B[2];
    int pa[2], pb[2];
    opt_colours(lt, nlt, pa); opt_colours(rt, nrt, pb);
    int r = opt_pair(O, R, C, m, lt, nlt, rt, nrt, A, B);
    if (r < 0) { res = -1; break; }
    if (r == 0) continue;
    for (int k = 0; k < 2; k++) {
      int si = -1;
      for (int i = 0; i < nsplit; i++) if (split[i] == k) si = i;
      if (si >= 0) {
        path_t lp = A[k], rp = B[k];
        if (!ceq(lp.v[lp.n - 1], C2(rows[si], m - 1))) prev_(&lp);
        path_shift(&rp, m);
        if (!ceq(rp.v[0], C2(rows[si], m))) prev_(&rp);
        pappend(&lp, &rp); pfree(&rp);
        out[k] = lp;
      } else if (pb[k]) { path_shift(&B[k], m); out[k] = B[k]; }
      else if (pa[k]) out[k] = A[k];
    }
    res = 1;
    break;
  }
  free(cand);
  if (res) return res;
  return tried ? 0 : OPT_NOGUESS;
}

/* Paths covering the R x C piece (1), none (0), or an error (-1). Exact. */
static int opt_piece(opt_t *O, int R, int C, const term_t *t, int nt, path_t out[2]) {
  int present[2];
  pinit(&out[0]); pinit(&out[1]);
  if (!terms_parity_ok(R, C, t, nt)) return 0;
  if (opt_colours(t, nt, present) == 1) {
    opt_log(O, "ips", R, C, NULL);
    O->work += (long long)R * C;
    int k = t[0].col;
    if (!ham(R, C, t[0].x, t[1].x, &out[k])) { pfree(&out[k]); return 0; }
    return 1;
  }
  if (imin(R, C) > OPT_NARROW && R * C > OPT_AREA) {
    /* guessing here, including the pieces below, may cost at most OPT_BUDGET times this piece's
     * own plug DP; then the plug DP decides */
    long long limit = O->work + OPT_BUDGET * opt_est(R, C);
    int small = imin(R, C) <= OPT_SMALL;
    int cuts = small ? 1 : OPT_CUTS, tries = small ? 1 : OPT_TRIES, tried = 0;
    int *trs, *ms, no = opt_options(R, C, t, nt, &trs, &ms);
    for (int i = 0; i < no && tried < cuts && O->work < limit; i++) {
      term_t tt[4];
      int tr = trs[i];
      if (tr) opt_transpose(t, nt, tt); else memcpy(tt, t, sizeof(term_t) * nt);
      int r = opt_guess(O, tr ? C : R, tr ? R : C, tt, nt, ms[i], tries, limit, out);
      if (r == OPT_NOGUESS) continue;
      if (r < 0) { free(trs); free(ms); return -1; }
      tried++;
      if (r == 1) {
        if (tr) for (int k = 0; k < 2; k++) if (present[k]) path_transpose(&out[k]);
        opt_orient(out, t, nt);
        free(trs); free(ms);
        return 1;
      }
    }
    free(trs); free(ms);
    if (tried) opt_log(O, "fallback", R, C, NULL);
  }
  opt_log(O, "dp", R, C, NULL);
  O->work += opt_est(R, C);
  int r = plug_dp(R, C, t, nt, 0, out);
  if (r == 1) opt_orient(out, t, nt);
  return r;
}

static int opt_solve(const inst_t *I, sbuf_t *trace, path_t s[2]) {
  int R = I->R, C = I->C, tr = R > C;
  term_t t[4] = {{I->s0, 0}, {I->t0, 0}, {I->s1, 1}, {I->t1, 1}};
  if (tr) { term_t u[4]; opt_transpose(t, 4, u); memcpy(t, u, sizeof t); R = I->C; C = I->R; }
  opt_t O = {trace, 0};
  int r = opt_piece(&O, R, C, t, 4, s);
  if (r == 1 && tr) { path_transpose(&s[0]); path_transpose(&s[1]); }
  return r;
}

static inst_t from_pub(const zzn_instance *in) { return mk(in->R, in->C, in->s0, in->t0, in->s1, in->t1); }

int zzn_well_formed(const zzn_instance *in) { inst_t I = from_pub(in); return well_formed(&I); }

int zzn_decide(const zzn_instance *in) {
  inst_t I = from_pub(in);
  if (!well_formed(&I)) return ZZN_INVALID;
  if (imin(I.R, I.C) <= THIN) return dp_feasible(&I);
  return fires_i(&I) == NULL;
}

const char *zzn_explain(const zzn_instance *in) {
  static _Thread_local char buf[64];
  inst_t I = from_pub(in);
  if (imin(I.R, I.C) <= THIN) return "thin: decided by the plug DP";
  const char *f = fires_i(&I);
  if (!f) return "passes the catalogue";
  snprintf(buf, sizeof buf, "catalogue entry %s fires", f);
  return buf;
}

int zzn_solve_trace(const zzn_instance *in, zzn_solution *out, char **trace) {
  inst_t I = from_pub(in);
  out->a.cells = out->b.cells = NULL; out->a.len = out->b.len = 0;
  if (trace) *trace = NULL;
  if (!well_formed(&I)) return ZZN_INVALID;
  g_err = 0;
  sbuf_t tb = {NULL, 0, 0};
  solver_t S = {NULL, 0, 0, trace ? &tb : NULL, 0};
  if (trace) sb_add(&tb, "");
  path_t s[2];
  int r = solve_rec(&S, &I, s);
  free(S.tab);
  if (trace) *trace = tb.buf; else free(tb.buf);
  if (g_err || r < 0) { if (r == 1) { pfree(&s[0]); pfree(&s[1]); } return ZZN_INTERNAL; }
  if (r == 0) return ZZN_UNSOLVABLE;
  if (!check_sol(&I, &s[0], &s[1])) { pfree(&s[0]); pfree(&s[1]); return ZZN_INTERNAL; }
  out->a.cells = s[0].v; out->a.len = s[0].n; out->b.cells = s[1].v; out->b.len = s[1].n;
  return ZZN_SOLVED;
}

int zzn_solve(const zzn_instance *in, zzn_solution *out) { return zzn_solve_trace(in, out, NULL); }

int zzn_solve_optimized_trace(const zzn_instance *in, zzn_solution *out, char **trace) {
  inst_t I = from_pub(in);
  if (imin(I.R, I.C) > THIN) return zzn_solve_trace(in, out, trace);
  out->a.cells = out->b.cells = NULL; out->a.len = out->b.len = 0;
  if (trace) *trace = NULL;
  if (!well_formed(&I)) return ZZN_INVALID;
  g_err = 0;
  sbuf_t tb = {NULL, 0, 0};
  if (trace) sb_add(&tb, "");
  path_t s[2];
  int r = opt_solve(&I, trace ? &tb : NULL, s);
  if (trace) *trace = tb.buf; else free(tb.buf);
  if (g_err || r < 0) { if (r == 1) { pfree(&s[0]); pfree(&s[1]); } return ZZN_INTERNAL; }
  if (r == 0) return ZZN_UNSOLVABLE;
  if (!check_sol(&I, &s[0], &s[1])) { pfree(&s[0]); pfree(&s[1]); return ZZN_INTERNAL; }
  out->a.cells = s[0].v; out->a.len = s[0].n; out->b.cells = s[1].v; out->b.len = s[1].n;
  return ZZN_SOLVED;
}

int zzn_solve_optimized(const zzn_instance *in, zzn_solution *out) { return zzn_solve_optimized_trace(in, out, NULL); }

int zzn_decide_optimized(const zzn_instance *in) {
  inst_t I = from_pub(in);
  if (!well_formed(&I)) return ZZN_INVALID;
  if (imin(I.R, I.C) > THIN) return zzn_decide(in);
  zzn_solution sol;
  int r = zzn_solve_optimized(in, &sol);
  if (r == ZZN_SOLVED) { zzn_solution_free(&sol); return 1; }
  return r == ZZN_UNSOLVABLE ? 0 : r;
}

void zzn_solution_free(zzn_solution *sol) {
  free(sol->a.cells); free(sol->b.cells);
  sol->a.cells = sol->b.cells = NULL; sol->a.len = sol->b.len = 0;
}

int zzn_check_solution(const zzn_instance *in, const zzn_solution *sol) {
  inst_t I = from_pub(in);
  path_t a = {sol->a.cells, sol->a.len, sol->a.len}, b = {sol->b.cells, sol->b.len, sol->b.len};
  if (!well_formed(&I)) return 0;
  return check_sol(&I, &a, &b);
}

char *zzn_render(const zzn_instance *in, const zzn_solution *sol) {
  int R = in->R, C = in->C;
  char *s = xmalloc((size_t)R * (C + 1) + 1);
  for (int r = 0; r < R; r++) { for (int c = 0; c < C; c++) s[r * (C + 1) + c] = '.'; s[r * (C + 1) + C] = '\n'; }
  s[R * (C + 1)] = 0;
  if (sol) {
    for (int i = 0; i < sol->a.len; i++) s[sol->a.cells[i].r * (C + 1) + sol->a.cells[i].c] = 'a';
    for (int i = 0; i < sol->b.len; i++) s[sol->b.cells[i].r * (C + 1) + sol->b.cells[i].c] = 'b';
  }
  s[in->s0.r * (C + 1) + in->s0.c] = 'A'; s[in->t0.r * (C + 1) + in->t0.c] = 'A';
  s[in->s1.r * (C + 1) + in->s1.c] = 'B'; s[in->t1.r * (C + 1) + in->t1.c] = 'B';
  if (R > 0) s[R * (C + 1) - 1] = 0;
  return s;
}

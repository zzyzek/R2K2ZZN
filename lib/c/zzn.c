/* SPDX-License-Identifier: CC0-1.0 */
/* To the extent possible under law, the author has waived all copyright and related or
   neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal). */

/*
 * zzn.c: implementation of zzn.h. A port of the Python reference library (lib/python/zzn);
 * every function below mirrors the one of the same name there, in the same iteration order,
 * so the three implementations return identical paths.
 */
#include "zzn.h"
#include "look.h"

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

typedef struct {
  sbuf_t *trace;                   /* trace lines */
} solver_t;

static void tlog(solver_t *S, const char *line) { if (S->trace) { sb_add(S->trace, line); sb_add(S->trace, "\n"); } }

/* thin instances (a side <= 10): the plug DP algorithm */
static int solve_thin(solver_t *S, const inst_t *I, path_t out[2]) {
  char line[160];
  snprintf(line, sizeof line, "  thin %dx%d", I->R, I->C); tlog(S, line);
  int r = dp_solve(I, out);
  return r == 1 ? 1 : (r == 0 ? 0 : -1);
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

/* ------------------------------------------------------------------ blocks ---------- */
/* Block deletion: the outer layer of the Lean construction `solveR`. Same definitions and
 * choices as lib/python/zzn/blocks.py (see its docstring): Lean's cell (x, y) on a w x h grid is
 * (r, c) on an R x C grid, x = r, w = R, y = c, h = C. */

typedef struct { int kind, r, k; } blk_t;   /* kind 0 left (k), 1 right (k), 2 inner (r, k) */
typedef struct { blk_t b; inst_t J; int tr; } bstep_t;

static void xs_of(const inst_t *I, int xs[4]) { xs[0] = I->s0.r; xs[1] = I->t0.r; xs[2] = I->s1.r; xs[3] = I->t1.r; }
static int left_k(const inst_t *I) {
  int xs[4]; xs_of(I, xs);
  return imin(ns(imin(imin(xs[0], xs[1]), imin(xs[2], xs[3])), 2) / 2, ns(I->R, 11) / 2);
}
static int right_k(const inst_t *I) {
  int xs[4]; xs_of(I, xs);
  return imin(ns(ns(I->R, 3), imax(imax(xs[0], xs[1]), imax(xs[2], xs[3]))) / 2, ns(I->R, 11) / 2);
}
static int inner_k(const inst_t *I, int a, int b) { return imin(ns(ns(b, a), 9) / 2, ns(I->R, 11) / 2); }

static int blk_x(const inst_t *I, blk_t *b) {
  int k = left_k(I);
  if (k >= 1) { b->kind = 0; b->r = 0; b->k = k; return 1; }
  k = right_k(I);
  if (k >= 1) { b->kind = 1; b->r = 0; b->k = k; return 1; }
  int xs[4]; xs_of(I, xs);
  for (int i = 0; i < 4; i++)
    for (int j = 0; j < 4; j++) {
      int a = xs[i], c = xs[j], ok = a < c;
      for (int m = 0; m < 4 && ok; m++) if (a < xs[m] && xs[m] < c) ok = 0;
      if (ok && inner_k(I, a, c) >= 1) { b->kind = 2; b->r = a + 1; b->k = inner_k(I, a, c); return 1; }
    }
  return 0;
}

static zzn_cell blk_del_cell(const blk_t *b, zzn_cell v) {
  if (b->kind == 0) return C2(v.r - 2 * b->k, v.c);
  if (b->kind == 1) return v;
  return v.r <= b->r ? v : C2(v.r - 2 * b->k, v.c);
}
static inst_t blk_delete(const blk_t *b, const inst_t *I) {
  return mk(I->R - 2 * b->k, I->C, blk_del_cell(b, I->s0), blk_del_cell(b, I->t0), blk_del_cell(b, I->s1),
            blk_del_cell(b, I->t1));
}
static zzn_cell swc(zzn_cell v) { return C2(v.c, v.r); }
static inst_t transpose_i(const inst_t *I) { return mk(I->C, I->R, swc(I->s0), swc(I->t0), swc(I->s1), swc(I->t1)); }

/* colSnake(x, A, k), appended to out */
static void col_snake(path_t *out, int x, const int *A, int n, int k) {
  for (int i = 0; i < k; i++) {
    for (int j = 0; j < n; j++) ppush(out, C2(x + 2 * i, A[j]));
    for (int j = n - 1; j >= 0; j--) ppush(out, C2(x + 2 * i + 1, A[j]));
  }
}

/* edgeBlock(w, h, y, k), appended to out */
static void edge_block(path_t *out, int w, int h, int y, int k) {
  int *A = xmalloc(sizeof(int) * (h + 1)), n = 0;
  for (int z = y; z >= 0; z--) A[n++] = z;
  col_snake(out, w, A, n, k);
  n = 0;
  for (int z = y + 1; z < h; z++) A[n++] = z;
  path_t t; pinit(&t);
  col_snake(&t, w, A, n, k);
  prev_(&t); pappend(out, &t); pfree(&t); free(A);
}

static int find_v(int x, const path_t *L) {
  for (int i = 0; i + 1 < L->n; i++) {
    zzn_cell u = L->v[i], v = L->v[i + 1];
    if (u.r == x && v.r == x && iabs(u.c - v.c) == 1) return i;
  }
  return -1;
}

static void edge_lift(int w, int h, int k, path_t ps[2]) {
  for (int which = 0; which < 2; which++) {
    path_t *p = &ps[which];
    int i = find_v(w - 1, p);
    if (i < 0) continue;
    zzn_cell a = p->v[i], b = p->v[i + 1];
    path_t X; pinit(&X);
    if (a.c < b.c) edge_block(&X, w, h, a.c, k);
    else { edge_block(&X, w, h, b.c, k); prev_(&X); }
    pinsert(p, i, X.v, X.n);
    pfree(&X);
    return;
  }
}

static void refl_paths(path_t ps[2], int W) {
  for (int j = 0; j < 2; j++) for (int i = 0; i < ps[j].n; i++) ps[j].v[i].r = W - 1 - ps[j].v[i].r;
}
static void edge_lift_l(int w, int h, int k, path_t ps[2]) {
  refl_paths(ps, w);
  edge_lift(w, h, k, ps);
  refl_paths(ps, w + 2 * k);
}

typedef struct { int r, k, h, R, flip; const char *cross; int *buf; } wide_t;

static int wide_cv(const wide_t *W, int y) { return W->cross[y] || (W->flip && (y + 1 == W->R || y == W->R)); }

/* snW(a), appended to out (reversed when rev) */
static void wide_sn(const wide_t *W, int a, int rev, path_t *out) {
  int n = 0;
  W->buf[n++] = a;
  if (a < W->R) { for (int y = a - 1; y >= 0 && !wide_cv(W, y); y--) W->buf[n++] = y; }
  else { for (int y = a + 1; y < W->h && !wide_cv(W, y); y++) W->buf[n++] = y; }
  if (!rev) { col_snake(out, W->r + 1, W->buf, n, W->k); return; }
  path_t t; pinit(&t);
  col_snake(&t, W->r + 1, W->buf, n, W->k);
  prev_(&t); pappend(out, &t); pfree(&t);
}

static void inner_lift(const inst_t *J, int r, int k, path_t ps[2]) {
  int h = J->C;

  /* seedW: crossings between lines r and r + 1, and steps (r, y - 1) - (r, y) */
  char *cross = calloc(h + 1, 1), *vert = calloc(h + 1, 1);
  if (!cross || !vert) { fprintf(stderr, "zzn: out of memory\n"); abort(); }
  for (int j = 0; j < 2; j++)
    for (int i = 0; i + 1 < ps[j].n; i++) {
      zzn_cell u = ps[j].v[i], v = ps[j].v[i + 1];
      if (u.c == v.c && ((u.r == r && v.r == r + 1) || (u.r == r + 1 && v.r == r))) cross[u.c] = 1;
      else if (u.r == r && v.r == r && iabs(u.c - v.c) == 1) vert[imax(u.c, v.c)] = 1;
    }
  int R = 0, flip = 0;
  for (int R0 = 0; R0 <= h; R0++) {
    int a = (R0 == 0 || cross[R0 - 1]) && (R0 == h || cross[R0]);
    int b = R0 >= 1 && R0 < h && !cross[R0 - 1] && !cross[R0] && vert[R0];
    if (a || b) { R = R0; flip = !a; break; }
  }
  wide_t W = {r, k, h, R, flip, cross, xmalloc(sizeof(int) * (h + 1))};
  int Wd = 2 * k;
  path_t fw; pinit(&fw);
  if (flip) { wide_sn(&W, R - 1, 0, &fw); wide_sn(&W, R, 1, &fw); }
  for (int j = 0; j < 2; j++) {
    path_t *L = &ps[j], out; pinit(&out);
    for (int i = 0; i < L->n; i++) if (L->v[i].r > r) L->v[i].r += Wd;
    for (int i = 0; i < L->n; i++) {
      zzn_cell u = L->v[i];
      ppush(&out, u);
      if (i + 1 == L->n) break;
      zzn_cell v = L->v[i + 1];
      if (u.r == r && v.r == r + Wd + 1 && u.c == v.c) wide_sn(&W, u.c, 0, &out);
      else if (u.r == r + Wd + 1 && v.r == r && u.c == v.c) wide_sn(&W, u.c, 1, &out);
      else if (flip && u.r == r && u.c == R - 1 && v.r == r && v.c == R) pappend(&out, &fw);
      else if (flip && u.r == r && u.c == R && v.r == r && v.c == R - 1) {
        path_t t; pcopy(&t, &fw); prev_(&t); pappend(&out, &t); pfree(&t);
      }
    }
    pfree(L);
    *L = out;
  }
  pfree(&fw); free(W.buf); free(cross); free(vert);
}

static void blk_lift(const blk_t *b, const inst_t *J, path_t ps[2]) {
  if (b->kind == 0) edge_lift_l(J->R, J->C, b->k, ps);
  else if (b->kind == 1) edge_lift(J->R, J->C, b->k, ps);
  else inner_lift(J, b->r, b->k, ps);
}

/* ----------------------------------------------------------------- reduce2 ---------- */
/* Two-line reductions: the inner layer of the Lean construction, `solveZ2`. Same definitions and
 * choices as lib/python/zzn/reduce2.py (see its docstring). */

static int free_line2(const inst_t *I, int k) { return I->s0.r != k && I->t0.r != k && I->s1.r != k && I->t1.r != k; }
static int end_below2(const inst_t *I, int k) { return I->s0.r < k || I->t0.r < k || I->s1.r < k || I->t1.r < k; }
static int end_above2(const inst_t *I, int k) { return k < I->s0.r || k < I->t0.r || k < I->s1.r || k < I->t1.r; }

static int red_x2(const inst_t *I, int d) {
  int w = I->R;
  if (!(13 <= w)) return 0;
  if (d == 0) { int ok = 1; for (int k = 0; k < 4; k++) if (!free_line2(I, k)) ok = 0; if (ok) return 1; }
  if (d + 2 == w) { int ok = 1; for (int k = 0; k < w; k++) if (w <= k + 4 && !free_line2(I, k)) ok = 0; if (ok) return 1; }
  for (int lo = 0; lo <= d; lo++) {
    if (d + 1 <= lo + 9 && lo + 10 <= w && end_below2(I, lo) && end_above2(I, lo + 9)) {
      int ok = 1;
      for (int j = 0; j < 10; j++) if (!free_line2(I, lo + j)) ok = 0;
      if (ok) return 1;
    }
  }
  return 8 <= d && d + 10 <= w && free_line2(I, d) && free_line2(I, d + 1) &&
         ((1 <= d && free_line2(I, d - 1)) || free_line2(I, d + 2)) && end_below2(I, d) && end_above2(I, d + 1);
}

static int red_b2(const inst_t *I, int d) {
  return 13 <= I->R && 5 <= d && d + 7 <= I->R && free_line2(I, d) && free_line2(I, d + 1) &&
         ((1 <= d && free_line2(I, d - 1)) || free_line2(I, d + 2)) && end_below2(I, d) && end_above2(I, d + 1);
}

static int find_red2(const inst_t *I) {
  for (int d = 0; d < I->R; d++) if (red_x2(I, d) || red_b2(I, d)) return d;
  return -1;
}

static zzn_cell del_at2(int d, zzn_cell v) { return v.r < d ? v : C2(v.r - 2, v.c); }
static inst_t delete_at2(const inst_t *I, int d) {
  return mk(I->R - 2, I->C, del_at2(d, I->s0), del_at2(d, I->t0), del_at2(d, I->s1), del_at2(d, I->t1));
}

static void stretch2(int r, const path_t *L, path_t *out) {
  pinit(out);
  for (int i = 0; i < L->n; i++) {
    zzn_cell a = L->v[i];
    ppush(out, a.r <= r ? a : C2(a.r + 2, a.c));
    if (i + 1 < L->n) {
      zzn_cell b = L->v[i + 1];
      if (a.r == r && b.r == r + 1 && a.c == b.c) { ppush(out, C2(r + 1, a.c)); ppush(out, C2(r + 2, a.c)); }
      else if (a.r == r + 1 && b.r == r && a.c == b.c) { ppush(out, C2(r + 2, a.c)); ppush(out, C2(r + 1, a.c)); }
    }
  }
}

static int edge_at2(const path_t *L, zzn_cell a, zzn_cell b) {
  for (int i = 0; i + 1 < L->n; i++) if (ceq(L->v[i], a) && ceq(L->v[i + 1], b)) return i;
  return -1;
}

/* spliceE: insert X after the first a, b in P if P has that edge, else in Q (if it has it) */
static void splice2(path_t ps[2], zzn_cell a, zzn_cell b, const zzn_cell *X, int k) {
  int i = edge_at2(&ps[0], a, b);
  if (i >= 0) { pinsert(&ps[0], i, X, k); return; }
  i = edge_at2(&ps[1], a, b);
  if (i >= 0) pinsert(&ps[1], i, X, k);
}

static void absorb2(int r, int y, int y2, path_t ps[2]) {
  zzn_cell u = C2(r + 1, y2), v = C2(r + 2, y2);
  if (edge_at2(&ps[0], u, v) >= 0 || edge_at2(&ps[1], u, v) >= 0) {
    zzn_cell X[2] = {C2(r + 1, y), C2(r + 2, y)}; splice2(ps, u, v, X, 2);
  } else {
    zzn_cell X[2] = {C2(r + 2, y), C2(r + 1, y)}; splice2(ps, v, u, X, 2);
  }
}

static void flip2(int r, int y, path_t ps[2]) {
  zzn_cell u = C2(r, y), v = C2(r, y + 1);
  if (edge_at2(&ps[0], u, v) >= 0 || edge_at2(&ps[1], u, v) >= 0) {
    zzn_cell X[4] = {C2(r + 1, y), C2(r + 2, y), C2(r + 2, y + 1), C2(r + 1, y + 1)}; splice2(ps, u, v, X, 4);
  } else {
    zzn_cell X[4] = {C2(r + 1, y + 1), C2(r + 2, y + 1), C2(r + 2, y), C2(r + 1, y)}; splice2(ps, v, u, X, 4);
  }
}

/* sweepLeftE r n U; U is a 0/1 array over columns (copied, not changed) */
static void sweep_left2(int r, int n, const char *U0, int h, path_t ps[2]) {
  char *U = xmalloc(h + 2); memcpy(U, U0, h + 2);
  while (n > 0) {
    int L = n - 1;
    if (U[L]) { absorb2(r, L, L + 1, ps); U[L] = 0; }
    n = L;
  }
  free(U);
}

static void sweep_right2(int r, int h, int n, int R, const char *U0, path_t ps[2]) {
  char *U = xmalloc(h + 2); memcpy(U, U0, h + 2);
  while (n > 0) {
    if (R + 1 <= h && U[R + 1]) { absorb2(r, R + 1, R, ps); U[R + 1] = 0; }
    else if (!(R + 1 < h)) break;
    n--; R++;
  }
  free(U);
}

/* bandExtE I r: ps (a solution of I) is replaced by the extended paths */
static void band_ext2(const inst_t *I, int r, path_t ps[2]) {
  int h = I->C;
  char *cross = calloc(h + 2, 1), *vert = calloc(h + 2, 1), *U0 = calloc(h + 2, 1), *U1 = calloc(h + 2, 1);
  if (!cross || !vert || !U0 || !U1) { fprintf(stderr, "zzn: out of memory\n"); abort(); }
  for (int j = 0; j < 2; j++)
    for (int i = 0; i + 1 < ps[j].n; i++) {
      zzn_cell a = ps[j].v[i], b = ps[j].v[i + 1];
      if (a.c == b.c && ((a.r == r && b.r == r + 1) || (a.r == r + 1 && b.r == r))) cross[a.c] = 1;
      else if (a.r == r && b.r == r && iabs(a.c - b.c) == 1) vert[imax(a.c, b.c)] = 1;
    }
  for (int y = 0; y < h; y++) U0[y] = !cross[y];
  path_t out[2];
  stretch2(r, &ps[0], &out[0]); stretch2(r, &ps[1], &out[1]);
  pfree(&ps[0]); pfree(&ps[1]); ps[0] = out[0]; ps[1] = out[1];
  int R = -1, A = 0;
  for (int R0 = 0; R0 <= h; R0++) {
    int a = (R0 == 0 || cross[R0 - 1]) && (R0 == h || cross[R0]);
    int b = R0 >= 1 && R0 < h && !cross[R0 - 1] && !cross[R0] && vert[R0];
    if (a || b) { R = R0; A = a; break; }
  }
  if (R >= 0) {
    if (A) {
      if (R == 0) sweep_right2(r, h, h, 0, U0, ps);
      else if (R == h) sweep_left2(r, R - 1, U0, h, ps);
      else {
        sweep_left2(r, R - 1, U0, h, ps);
        for (int y = 0; y <= h; y++) U1[y] = U0[y] && R - 1 < y;
        sweep_right2(r, h, h - R, R, U1, ps);
      }
    } else {
      memcpy(U1, U0, h + 2); U1[R - 1] = 0; U1[R] = 0;
      flip2(r, R - 1, ps);
      sweep_left2(r, R - 1, U1, h, ps);
      for (int y = 0; y <= h; y++) if (!(R - 1 < y)) U1[y] = 0;
      sweep_right2(r, h, h - R, R, U1, ps);
    }
  }
  free(cross); free(vert); free(U0); free(U1);
}

static void lift_e2(const inst_t *I, int d, path_t ps[2]) {
  inst_t J = delete_at2(I, d);
  if (d + 3 <= I->R && free_line2(I, d + 2)) band_ext2(&J, d, ps);
  else band_ext2(&J, d - 1, ps);
}

typedef struct { inst_t P; int d, tr; } rstep_t;

/* Both sides >= 11 (see solver.py): the Lean construction solveZ3 (leafL thinSolveW2 tabAll): block
 * deletion, two-line reductions by RedX or RedB, the leaf lookup, then the lifts back. */
static int solve_top(solver_t *S, const inst_t *I, path_t out[2]) {
  if (imin(I->R, I->C) <= THIN) return solve_thin(S, I, out);
  char line[160];
  const char *f = fires_i(I);
  if (f) { snprintf(line, sizeof line, "  fires %dx%d: %s", I->R, I->C, f); tlog(S, line); return 0; }
  bstep_t *st = xmalloc(sizeof(bstep_t) * (I->R + I->C + 1));
  int ns_ = 0;
  inst_t cur = *I;
  while (cur.R > 10 && cur.C > 10) {
    blk_t b;
    if (blk_x(&cur, &b)) { st[ns_].b = b; st[ns_].J = blk_delete(&b, &cur); st[ns_].tr = 0; cur = st[ns_++].J; continue; }
    inst_t T = transpose_i(&cur);
    if (blk_x(&T, &b)) { st[ns_].b = b; st[ns_].J = blk_delete(&b, &T); st[ns_].tr = 1; cur = st[ns_++].J; continue; }
    break;
  }
  int tr = 0;
  inst_t fr = *I;
  for (int i = 0; i < ns_; i++) {
    tr ^= st[i].tr;
    const blk_t *b = &st[i].b;
    const char *lines = tr ? "columns" : "rows";
    int n = tr ? fr.C : fr.R, lo, hi;
    if (b->kind == 0) { lo = 0; hi = 2 * b->k - 1; }
    else if (b->kind == 1) { lo = n - 2 * b->k; hi = n - 1; }
    else { lo = b->r + 1; hi = b->r + 2 * b->k; }
    snprintf(line, sizeof line, "  block %dx%d: delete %s %d..%d", fr.R, fr.C, lines, lo, hi);
    tlog(S, line);
    fr = tr ? transpose_i(&st[i].J) : st[i].J;
  }
  /* two-line reductions (solveRec2) on what is left */
  rstep_t *rs = xmalloc(sizeof(rstep_t) * (cur.R + cur.C + 1));
  int nr = 0;
  while (cur.R > 10 && cur.C > 10) {
    int d = find_red2(&cur);
    if (d >= 0) { rs[nr].P = cur; rs[nr].d = d; rs[nr].tr = 0; nr++; cur = delete_at2(&cur, d); continue; }
    inst_t T = transpose_i(&cur);
    d = find_red2(&T);
    if (d >= 0) { rs[nr].P = T; rs[nr].d = d; rs[nr].tr = 1; nr++; cur = delete_at2(&T, d); continue; }
    break;
  }
  for (int i = 0; i < nr; i++) {
    tr ^= rs[i].tr;
    snprintf(line, sizeof line, "  reduce %dx%d: delete %s %d,%d", fr.R, fr.C, tr ? "columns" : "rows", rs[i].d, rs[i].d + 1);
    tlog(S, line);
    inst_t J = delete_at2(&rs[i].P, rs[i].d);
    fr = tr ? transpose_i(&J) : J;
  }
  int r;
  if (imin(cur.R, cur.C) <= THIN) r = solve_thin(S, &cur, out);
  else {
    snprintf(line, sizeof line, "  leaf %dx%d", cur.R, cur.C); tlog(S, line);

    /* The certificate lookup `lookJ tabAll` (look.c), as solver.py's leaf: no answer on a leaf
       of a passing instance, or a table that cannot be loaded, is an internal error. */
    zzn_instance L = {cur.R, cur.C, cur.s0, cur.t0, cur.s1, cur.t1};
    zzn_path pa, pb;
    r = zzn_look_j(&L, &pa, &pb, NULL);
    if (r == 1) {
      out[0].v = pa.cells; out[0].n = out[0].cap = pa.len;
      out[1].v = pb.cells; out[1].n = out[1].cap = pb.len;
    }
  }
  if (r != 1) { free(st); free(rs); g_err = 1; return -1; }
  for (int i = nr - 1; i >= 0; i--) {
    lift_e2(&rs[i].P, rs[i].d, out);
    if (rs[i].tr) { path_transpose(&out[0]); path_transpose(&out[1]); }
  }
  free(rs);
  for (int i = ns_ - 1; i >= 0; i--) {
    blk_lift(&st[i].b, &st[i].J, out);
    if (st[i].tr) { path_transpose(&out[0]); path_transpose(&out[1]); }
  }
  free(st);
  return 1;
}

int zzn_solve_trace(const zzn_instance *in, zzn_solution *out, char **trace) {
  inst_t I = from_pub(in);
  out->a.cells = out->b.cells = NULL; out->a.len = out->b.len = 0;
  if (trace) *trace = NULL;
  if (!well_formed(&I)) return ZZN_INVALID;
  g_err = 0;
  sbuf_t tb = {NULL, 0, 0};
  solver_t S = {trace ? &tb : NULL};
  if (trace) sb_add(&tb, "");
  path_t s[2];
  int r = solve_top(&S, &I, s);
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

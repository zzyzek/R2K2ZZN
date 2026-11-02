// Fold the reflections of a symmetry into a template: xform(t, g) is a template t' with
// ev(t', c) = ev(t, refl_g(c)) for g bit0 = flip rows, bit1 = flip columns. A cut line on a
// flipped axis maps (a, o) to (a, 1 - o) for endpoint anchors and swaps the boundary anchors;
// a cell maps (a, o) to (a, -o). At a cut on a flipped axis the two children swap and the side
// flags flip.
//
static void tx_line(int a, int o, int *a2, int *o2) {
  if      (a < 4)  { *a2 = a; *o2 = 1 - o; }
  else if (a == 4) { *a2 = 5; *o2 = -o; }
  else             { *a2 = 4; *o2 = -o; }
}
static void tx_cell(int a, int o, int *a2, int *o2) {
  if      (a < 4)  { *a2 = a; *o2 = -o; }
  else if (a == 4) { *a2 = 5; *o2 = -1 - o; }
  else             { *a2 = 4; *o2 = -1 - o; }
}
// Copy the subtree at node k of t into out (appending), transformed; returns the next node of t.
//
static int tx_rec(const tmpl_t *t, int k, int g, tmpl_t *out) {
  const tnode *nd = &t->nd[k];
  tnode *o = &out->nd[out->nn++];
  *o = *nd;
  if (nd->leaf) { return k + 1; }
  int fl = ( g >> nd->axis ) & 1, fc = ( g >> (1 - nd->axis) ) & 1;
  if (fl) {
    tx_line(nd->pa, nd->po, &o->pa, &o->po);
    for (int i = 0; i < nd->n; i++) { o->sa[i] = 1 - nd->sa[i]; o->sb[i] = 1 - nd->sb[i]; }
  }
  if (fc) {
    for (int i = 0; i < nd->n; i++) {
      if (nd->kind[i] >= 1) { tx_cell(nd->ya[i], nd->yo[i], &o->ya[i], &o->yo[i]); }
      if (nd->kind[i] == 2) { tx_cell(nd->za[i], nd->zo[i], &o->za[i], &o->zo[i]); }
    }
  }
  int k0 = k + 1;
  int k1 = tx_rec(t, k0, g, &(tmpl_t){ 0 });
  if (!fl) {
    tx_rec(t, k0, g, out);
    return tx_rec(t, k1, g, out);
  }
  int k2 = tx_rec(t, k1, g, out);
  tx_rec(t, k0, g, out);
  return k2;
}
static void xform(const tmpl_t *t, int g, tmpl_t *out) {
  memset(out, 0, sizeof *out);
  out->depth = t->depth;
  tx_rec(t, 0, g, out);
}
// Fold a whole symmetry s (bit0 flip rows, bit1 flip columns, bit 5 transpose first as in
// matchTT; labels untouched): ev(fold(t, s), p) = ev(t, (s geometric part)(p)).
//
static void fold(const tmpl_t *t, int s, tmpl_t *out) {
  xform(t, s & 3, out);
  if (s & 32) {
    for (int k = 0; k < out->nn; k++) { if (!out->nd[k].leaf) { out->nd[k].axis = 1 - out->nd[k].axis; } }
  }
}

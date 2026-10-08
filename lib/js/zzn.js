// SPDX-License-Identifier: CC0-1.0
// To the extent possible under law, the author has waived all copyright and related or
// neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

/*
 * zzn.js: decide and solve two-colour Zig-Zag Numberlink on rectangles.
 *
 * A port of the Python reference library (lib/python/zzn); same algorithm, same results.
 * Cells are [row, col]; an instance is {R, C, s0, t0, s1, t1}. See README.md and
 * docs/ALGORITHM.md.
 *
 *   const zzn = require("./zzn.js");
 *   zzn.solve({R: 12, C: 12, s0: [0, 0], t0: [0, 11], s1: [11, 0], t1: [11, 11]});
 *     // -> [pathA, pathB] or null
 */
(function (root, factory) {
  if (typeof module === "object" && module.exports) module.exports = factory();
  else root.zzn = factory();
})(typeof self !== "undefined" ? self : this, function () {
  "use strict";

  const THIN = 10;

  // ---------------------------------------------------------------- grid ----------
  const eq = (a, b) => a[0] === b[0] && a[1] === b[1];
  const key = (x) => x[0] * 65536 + x[1];
  const ends = (I) => [I.s0, I.t0, I.s1, I.t1];
  const inst = (R, C, s0, t0, s1, t1) => ({ R, C, s0, t0, s1, t1 });

  function wellFormed(I) {
    if (!(I.R >= 1 && I.C >= 1)) return false;
    const e = ends(I);
    for (const [r, c] of e) if (!(r >= 0 && r < I.R && c >= 0 && c < I.C)) return false;
    return new Set(e.map(key)).size === 4;
  }

  const adjacent = (u, v) => Math.abs(u[0] - v[0]) + Math.abs(u[1] - v[1]) === 1;

  function checkPath(R, C, s, t, p) {
    if (!p || p.length === 0 || !eq(p[0], s) || !eq(p[p.length - 1], t)) return false;
    if (new Set(p.map(key)).size !== p.length) return false;
    for (const [r, c] of p) if (!(r >= 0 && r < R && c >= 0 && c < C)) return false;
    for (let i = 0; i + 1 < p.length; i++) if (!adjacent(p[i], p[i + 1])) return false;
    return true;
  }

  function checkSolution(I, sol) {
    if (!sol) return false;
    const [p, q] = sol;
    if (!checkPath(I.R, I.C, I.s0, I.t0, p) || !checkPath(I.R, I.C, I.s1, I.t1, q)) return false;
    const cells = new Set(p.map(key).concat(q.map(key)));
    return cells.size === p.length + q.length && cells.size === I.R * I.C;
  }

  // geometric symmetry g = [tr, fr, fc]: transpose, then flip rows, then flip columns
  function geoCell(g, R, C, x) {
    let [r, c] = x;
    if (g[0]) { [r, c] = [c, r]; [R, C] = [C, R]; }
    if (g[1]) r = R - 1 - r;
    if (g[2]) c = C - 1 - c;
    return [r, c];
  }
  const geoDims = (g, R, C) => (g[0] ? [C, R] : [R, C]);
  function geoInverseCell(g, R, C, x) {
    const [R2, C2] = geoDims(g, R, C);
    let [r, c] = x;
    if (g[2]) c = C2 - 1 - c;
    if (g[1]) r = R2 - 1 - r;
    if (g[0]) [r, c] = [c, r];
    return [r, c];
  }
  const GEOS = [];
  for (const tr of [false, true]) for (const fr of [false, true]) for (const fc of [false, true]) GEOS.push([tr, fr, fc]);

  function applyGeo(g, I) {
    const [R2, C2] = geoDims(g, I.R, I.C);
    const f = (x) => geoCell(g, I.R, I.C, x);
    return inst(R2, C2, f(I.s0), f(I.t0), f(I.s1), f(I.t1));
  }

  function relabel(lab, I) {
    let [s0, t0, s1, t1] = [I.s0, I.t0, I.s1, I.t1];
    if (lab[0]) [s0, t0] = [t0, s0];
    if (lab[1]) [s1, t1] = [t1, s1];
    if (lab[2]) [s0, t0, s1, t1] = [s1, t1, s0, t0];
    return inst(I.R, I.C, s0, t0, s1, t1);
  }

  function orient(I, paths) {
    const out = [null, null];
    for (const p of paths) {
      [[I.s0, I.t0], [I.s1, I.t1]].forEach(([s, t], col) => {
        if (eq(p[0], s) && eq(p[p.length - 1], t)) out[col] = p.slice();
        else if (eq(p[0], t) && eq(p[p.length - 1], s)) out[col] = p.slice().reverse();
      });
    }
    if (!out[0] || !out[1]) throw new Error("paths do not match the endpoints");
    return out;
  }

  function mapBack(g, I, solImage) {
    return orient(I, solImage.map((p) => p.map((x) => geoInverseCell(g, I.R, I.C, x))));
  }

  function render(I, sol) {
    const g = [];
    for (let r = 0; r < I.R; r++) g.push(new Array(I.C).fill("."));
    if (sol) {
      for (const [r, c] of sol[0]) g[r][c] = "a";
      for (const [r, c] of sol[1]) g[r][c] = "b";
    }
    for (const [r, c] of [I.s0, I.t0]) g[r][c] = "A";
    for (const [r, c] of [I.s1, I.t1]) g[r][c] = "B";
    return g.map((row) => row.join("")).join("\n");
  }

  // ----------------------------------------------------------- catalogue ----------
  const CORNER4 = [
    [[[0, 1], [0, 3]], [[1, 1], [1, 3]]], [[[0, 1], [0, 6]], [[0, 7], [1, 1]]],
    [[[0, 1], [0, 6]], [[1, 1], [7, 0]]], [[[0, 1], [0, 6]], [[1, 2], [6, 0]]],
    [[[0, 1], [0, 7]], [[1, 1], [6, 0]]], [[[0, 1], [1, 3]], [[1, 1], [1, 2]]],
    [[[0, 1], [1, 3]], [[1, 2], [2, 2]]], [[[0, 1], [1, 3]], [[1, 2], [3, 1]]],
    [[[0, 1], [2, 2]], [[1, 1], [1, 2]]], [[[0, 1], [2, 2]], [[1, 2], [3, 1]]],
    [[[0, 1], [2, 2]], [[1, 3], [3, 0]]], [[[0, 1], [7, 0]], [[1, 1], [6, 0]]],
    [[[0, 2], [1, 1]], [[2, 1], [3, 0]]], [[[0, 2], [2, 0]], [[1, 2], [2, 1]]],
    [[[0, 3], [2, 1]], [[3, 1], [4, 0]]], [[[0, 6], [2, 1]], [[1, 2], [6, 0]]],
    [[[1, 2], [2, 2]], [[1, 3], [2, 1]]], [[[1, 2], [3, 1]], [[1, 3], [2, 1]]],
    [[[0, 1], [1, 2]], [[0, 4], [2, 2]]], [[[0, 1], [1, 2]], [[0, 4], [3, 1]]],
    [[[0, 1], [1, 2]], [[1, 3], [2, 0]]], [[[0, 1], [1, 2]], [[1, 3], [4, 0]]],
    [[[0, 1], [1, 2]], [[2, 0], [2, 2]]], [[[0, 1], [1, 2]], [[2, 2], [4, 0]]],
    [[[0, 1], [1, 2]], [[3, 1], [4, 0]]], [[[0, 1], [1, 3]], [[0, 3], [0, 4]]],
    [[[0, 1], [1, 3]], [[0, 3], [2, 0]]], [[[0, 1], [1, 3]], [[0, 3], [4, 0]]],
    [[[0, 1], [2, 1]], [[0, 2], [2, 2]]], [[[0, 1], [2, 1]], [[0, 2], [3, 1]]],
    [[[0, 1], [2, 1]], [[0, 4], [1, 3]]], [[[0, 1], [2, 1]], [[0, 4], [2, 2]]],
    [[[0, 1], [2, 1]], [[0, 4], [3, 1]]], [[[0, 1], [2, 1]], [[1, 3], [4, 0]]],
    [[[0, 1], [2, 1]], [[2, 2], [4, 0]]], [[[0, 1], [2, 1]], [[3, 1], [4, 0]]]];
  const CORNER4_ODD = [
    [[[0, 0], [0, 1]], [[1, 1], [2, 0]]], [[[0, 0], [1, 4]], [[0, 2], [1, 3]]],
    [[[0, 0], [2, 3]], [[0, 2], [1, 3]]]];
  const BOUNDARY3_EVEN = [
    [[0, 0], [1, 1], [1, 2]], [[0, 1], [0, 2], [1, 1]], [[0, 1], [0, 2], [1, 2]],
    [[0, 1], [0, 3], [1, 1]], [[0, 1], [0, 4], [1, 1]], [[0, 1], [0, 4], [1, 2]],
    [[0, 1], [0, 5], [1, 1]], [[0, 1], [1, 2], [1, 1]], [[0, 1], [1, 2], [1, 3]],
    [[0, 1], [1, 2], [2, 2]], [[0, 1], [1, 2], [3, 1]], [[0, 1], [1, 3], [0, 3]],
    [[0, 1], [2, 1], [1, 3]], [[0, 1], [2, 1], [2, 2]], [[0, 1], [2, 1], [3, 1]],
    [[0, 2], [2, 1], [1, 0]], [[0, 3], [1, 1], [1, 0]], [[0, 4], [1, 1], [1, 0]],
    [[0, 4], [2, 1], [1, 0]], [[0, 4], [2, 1], [1, 2]], [[0, 5], [1, 1], [1, 0]]];
  const BOUNDARY3_ODD = [
    [[0, 0], [1, 1], [1, 2]], [[0, 0], [1, 1], [2, 2]], [[0, 1], [0, 2], [1, 1]],
    [[0, 1], [0, 4], [1, 1]], [[0, 4], [1, 1], [1, 0]]];

  const ns = (a, b) => (a > b ? a - b : 0); // natural-number subtraction, as in Lean
  const FRAMES = [];
  for (const fr of [false, true]) for (const fc of [false, true]) for (const tr of [false, true]) FRAMES.push([fr, fc, tr]);

  const sgn = (p) => ((p[0] + p[1]) % 2 === 0 ? 1 : -1);
  const parityOk = (R, C, pts) => pts.reduce((a, q) => a + sgn(q[0]), 0) === 2 * ((R * C) % 2);

  function perimIndex(R, C, p) {
    const [r, c] = p;
    if (r === 0) return c;
    if (c === C - 1) return C - 1 + r;
    if (r === R - 1) return C - 1 + (R - 1) + (C - 1 - c);
    if (c === 0) return 2 * (C - 1) + (R - 1) + (R - 1 - r);
    return null;
  }

  const alternating = (cols) => cols.length === 4 && cols[0] !== cols[1] && cols[1] !== cols[2] && cols[2] !== cols[3];
  const sortByKey = (l) => l.map((x, i) => [x, i]).sort((a, b) => a[0][0] - b[0][0] || a[1] - b[1]).map((x) => x[0]);

  function t1Fires(R, C, pts) {
    const idx = pts.map((q) => perimIndex(R, C, q[0]));
    if (idx.some((i) => i === null)) return false;
    return alternating(sortByKey(idx.map((i, k) => [i, pts[k][1]])).map((x) => x[1]));
  }

  function t2Fires(cells) {
    const rs = cells.map((x) => x[0]), cs = cells.map((x) => x[1]);
    return Math.max(...rs) - Math.min(...rs) === 1 && Math.max(...cs) - Math.min(...cs) === 1 &&
      rs[0] !== rs[1] && cs[0] !== cs[1];
  }

  function l1Fires(R, C, pts) {
    for (const [p, col] of pts) {
      const nb = [[-1, 0], [1, 0], [0, -1], [0, 1]].map(([dr, dc]) => [p[0] + dr, p[1] + dc])
        .filter((q) => q[0] >= 0 && q[0] < R && q[1] >= 0 && q[1] < C);
      if (nb.every((q) => pts.some(([e, ec]) => eq(e, q) && ec !== col))) return true;
    }
    return false;
  }

  const findPt = (pts, x) => pts.find((q) => eq(q[0], x)) || null;

  function l6Fires(R, C, pts) {
    const closures = [];
    for (const [cr, cc, dr, dc] of [[0, 0, 1, 1], [0, C - 1, 1, -1], [R - 1, 0, -1, 1], [R - 1, C - 1, -1, -1]]) {
      const n1 = [cr, Math.max(cc + dc, 0)], n2 = [Math.max(cr + dr, 0), cc];
      const e1 = findPt(pts, n1), e2 = findPt(pts, n2);
      if (e1 && e2 && e1[1] === e2[1] && findPt(pts, [cr, cc]) === null) closures.push(e1[1]);
    }
    return closures.includes(0) && closures.includes(1) && R * C > 6;
  }

  function frameTo(R, C, f, p) {
    const a = f[0] ? ns(ns(R, 1), p[0]) : p[0];
    const b = f[1] ? ns(ns(C, 1), p[1]) : p[1];
    return f[2] ? [b, a] : [a, b];
  }
  function frameBack(R, C, f, q) {
    const r = f[2] ? q[1] : q[0], c = f[2] ? q[0] : q[1];
    return [f[0] ? ns(ns(R, 1), r) : r, f[1] ? ns(ns(C, 1), c) : c];
  }

  function makeView(R, C, f, pts) {
    const vp = pts.map((q) => [frameTo(R, C, f, q[0]), q[1]]);
    const at = (r, c) => { const q = vp.find((x) => x[0][0] === r && x[0][1] === c); return q ? q[1] : null; };
    return { H: f[2] ? C : R, W: f[2] ? R : C, at, empty: (cells) => cells.every(([r, c]) => at(r, c) === null) };
  }

  const testL2 = (v) => { const a = v.at(0, 1), b = v.at(1, 0); return a !== null && b !== null && a !== b && v.empty([[0, 0]]); };
  const testL3 = (v) => { const a = v.at(0, 2); return a !== null && v.at(1, 1) === a && v.at(1, 0) === 1 - a && v.empty([[0, 0], [0, 1]]); };
  const testL4 = (v) => { const a = v.at(0, 0); return a !== null && v.at(1, 1) === a && v.at(0, 2) === 1 - a && v.H >= 3 && v.empty([[0, 1], [1, 0]]); };
  const testL5 = (v) => { const b = v.at(0, 0); return b !== null && v.at(0, 2) === 1 - b && v.at(2, 0) === 1 - b && v.empty([[0, 1], [1, 0], [1, 1]]); };
  function edgeClosure(v) {
    for (let k = 0; k + 3 < v.W; k++) {
      const a = v.at(0, k);
      if (a !== null && v.at(1, k + 1) === a && v.at(0, k + 3) === 1 - a && v.at(1, k + 2) === 1 - a) return true;
    }
    return false;
  }

  function boundaryOnly(R, C, f, pts) {
    const lst = R % 2 === 1 && C % 2 === 1 ? BOUNDARY3_ODD : BOUNDARY3_EVEN;
    const fp = pts.map((q) => [frameTo(R, C, f, q[0]), q[1]]);
    const H = f[2] ? C : R, W = f[2] ? R : C;
    for (const [a1, a2, b] of lst) {
      for (const A of [0, 1]) {
        if (!fp.some(([x, col]) => col === 1 - A && eq(x, b))) continue;
        if (!(fp.some(([x, col]) => col === A && eq(x, a1)) && fp.some(([x, col]) => col === A && eq(x, a2)))) continue;
        const fourth = fp.find(([x, col]) => col === 1 - A && !eq(x, b));
        if (!fourth) continue;
        const x = fourth[0];
        const onPerim = x[0] === 0 || x[1] === 0 || x[0] === H - 1 || x[1] === W - 1;
        if (onPerim && !(x[0] < 6 && x[1] < 6)) return true;
      }
    }
    return false;
  }

  const sameSet = (a, b) => a.length === b.length && a.every((x) => b.some((y) => eq(x, y)));

  function corner4(R, C, f, pts) {
    const A0 = pts.filter((q) => q[1] === 0).map((q) => frameTo(R, C, f, q[0]));
    const A1 = pts.filter((q) => q[1] === 1).map((q) => frameTo(R, C, f, q[0]));
    const lst = (R * C) % 2 === 0 ? CORNER4 : CORNER4_ODD;
    return lst.some(([A, B]) => (sameSet(A, A0) && sameSet(B, A1)) || (sameSet(A, A1) && sameSet(B, A0)));
  }

  function frameFires(R, C, pts, f) {
    const v = makeView(R, C, f, pts);
    if (testL2(v)) return "L2";
    if (testL3(v)) return "L3";
    if (testL4(v)) return "L4";
    if (testL5(v)) return "L5";
    if (edgeClosure(v)) return "E1";
    if (boundaryOnly(R, C, f, pts)) return "B";
    if (R >= 10 && C >= 10 && corner4(R, C, f, pts)) return "C4";
    return null;
  }

  function rewritesAt(v) {
    const x = v.at(1, 2), y = v.at(2, 1);
    if (x !== null && y !== null && x !== y && v.H >= 4 && v.W >= 4 &&
        v.empty([[0, 0], [0, 1], [0, 2], [0, 3], [1, 0], [1, 1], [2, 0], [3, 0]]))
      return [[[0, 0], [0, 1], [0, 2], [1, 0], [1, 1], [2, 0], [1, 2], [2, 1]], [[[1, 2], [0, 3]], [[2, 1], [3, 0]]]];
    const a = v.at(0, 0);
    if (a !== null && v.at(1, 1) === a && v.H >= 3 && v.W >= 3 && v.empty([[0, 1], [1, 0], [0, 2], [2, 0]]))
      return [[[0, 0], [0, 1], [1, 0], [1, 1]], [[[0, 0], [0, 2]], [[1, 1], [2, 0]]]];
    if (v.at(0, 1) !== null && v.empty([[0, 0], [1, 0]]) && v.H >= 2) return [[[0, 0], [0, 1]], [[[0, 1], [1, 0]]]];
    return null;
  }

  const inList = (l, x) => l.some((y) => eq(x, y));

  function rewriteAll(R, C, pts) {
    let eff = pts.map((q) => [q[0], q[1]]), removed = [], any = false;
    for (const f of FRAMES) {
      const rw = rewritesAt(makeView(R, C, f, eff));
      if (!rw) continue;
      const cells = rw[0].map((x) => frameBack(R, C, f, x));
      const moves = rw[1].map(([a, b]) => [frameBack(R, C, f, a), frameBack(R, C, f, b)]);
      if (cells.some((x) => inList(removed, x)) || moves.some((m) => inList(removed, m[1]))) continue;
      for (const [a, b] of moves) {
        const i = eff.findIndex((q) => eq(q[0], a));
        if (i >= 0) eff[i] = [b, eff[i][1]];
      }
      removed = removed.concat(cells);
      any = true;
    }
    return [eff, removed, any];
  }

  const FTL = [false, false, false], FTR = [false, true, false], FBR = [true, true, false], FBL = [true, false, false];
  const notchLen = (R, C, f, removed, i) => [0, 1, 2, 3].filter((j) => inList(removed, frameBack(R, C, f, [i, j]))).length;

  function staircase(lam) {
    const k = [0, 1, 2, 3].filter((i) => lam(i) > 0).length;
    const out = [[k, 0]];
    for (let i = k - 1; i >= 0; i--) {
      const n = ns(lam(i), lam(i + 1));
      for (let j = 0; j < n; j++) out.push([i + 1, lam(i + 1) + 1 + j]);
      out.push([i, lam(i)]);
    }
    return out;
  }
  const stairOf = (R, C, f, removed) => staircase((i) => notchLen(R, C, f, removed, i)).map((x) => frameBack(R, C, f, x));

  function walk3(R, C, removed) {
    const tl = stairOf(R, C, FTL, removed), trr = stairOf(R, C, FTR, removed).reverse();
    const br = stairOf(R, C, FBR, removed), bl = stairOf(R, C, FBL, removed).reverse();
    const lam = (f) => notchLen(R, C, f, removed, 0);
    const kk = (f) => [0, 1, 2, 3].filter((i) => notchLen(R, C, f, removed, i) > 0).length;
    const [lTL, lTR, lBR, lBL] = [lam(FTL), lam(FTR), lam(FBR), lam(FBL)];
    const [kTL, kTR, kBR, kBL] = [kk(FTL), kk(FTR), kk(FBR), kk(FBL)];
    const top = [], right = [], bottom = [], left = [];
    for (let y = 0; y < C; y++) if (lTL < y && y + 1 + lTR < C) top.push([0, y]);
    for (let x = 0; x < R; x++) if (kTR < x && x + 1 + kBR < R) right.push([x, C - 1]);
    for (let y = 0; y < C; y++) if (lBL < y && y + 1 + lBR < C) bottom.push([R - 1, y]);
    for (let x = 0; x < R; x++) if (kTL < x && x + 1 + kBL < R) left.push([x, 0]);
    return tl.concat(top, trr, right, br, bottom.reverse(), bl, left.reverse());
  }

  function effAlt(R, C, pts) {
    const [eff, removed, any] = rewriteAll(R, C, pts);
    if (!any) return false;
    if (eff.some((q) => inList(removed, q[0]))) return false;
    if (new Set(eff.map((q) => key(q[0]))).size !== 4) return false;
    const walk = walk3(R, C, removed);
    const places = [];
    for (const q of eff) {
      const pos = [];
      walk.forEach((x, i) => { if (eq(x, q[0])) pos.push(i); });
      if (pos.length !== 1) return false;
      places.push([pos[0], q[1]]);
    }
    return alternating(sortByKey(places).map((x) => x[1]));
  }

  /** Name of a catalogue entry that fires, or null if the instance passes. */
  function fires(R, C, s0, t0, s1, t1) {
    const pts = [[s0, 0], [t0, 0], [s1, 1], [t1, 1]];
    if (!parityOk(R, C, pts)) return "P";
    if (t1Fires(R, C, pts)) return "T1";
    if (t2Fires([s0, t0, s1, t1])) return "T2";
    if (l1Fires(R, C, pts)) return "L1";
    if (l6Fires(R, C, pts)) return "L6";
    for (const f of FRAMES) { const n = frameFires(R, C, pts, f); if (n) return n; }
    if (effAlt(R, C, pts)) return "R";
    return null;
  }
  const firesI = (I) => fires(I.R, I.C, I.s0, I.t0, I.s1, I.t1);

  // -------------------------------------------------------------- plug DP ----------
  const EM = 0;
  const POW = []; for (let i = 0, p = 1; i < 18; i++, p *= 8) POW.push(p);
  // A state needs 3 (R + 1) bits, 33 for R = 10: more than JavaScript's 32-bit bitwise operators.
  // Slots 0-9 lie in the low 32 bits (`s >>> 0` is s mod 2^32, exact for s < 2^53), so they are
  // read with shifts; higher slots by division.
  //
  const gv = (s, i) => (i < 10 ? ((s >>> 0) >>> (3 * i)) & 7 : Math.floor(s / POW[i]) % 8);
  const sv = (s, i, v) => s + (v - gv(s, i)) * POW[i];

  // A set of states: open addressing on a Float64Array (-1 marks an empty slot), with the states
  // also kept in insertion order in `list` for iteration. Faster than Set for non-integer-tagged
  // numbers such as 33-bit states.
  //
  const hashS = (k) => {
    const h = Math.imul(k >>> 0, 0x9e3779b1) ^ Math.imul(((k / 4294967296) | 0) + 0x7f4a7c15, 0x85ebca6b);
    return h ^ (h >>> 15);
  };
  const capFor = (n) => { let c = 1024; while (c < 4 * n) c *= 2; return c; };
  class StateSet {
    constructor(cap = 1024) {
      this.cap = cap; this.size = 0;
      this.keys = new Float64Array(cap).fill(-1);
      this.list = new Float64Array(cap >> 1);
    }
    add(k) {
      if ((this.size + 1) * 2 > this.cap) this.grow();
      const m = this.cap - 1;
      let i = hashS(k) & m;
      for (;;) {
        const v = this.keys[i];
        if (v === -1) break;
        if (v === k) return;
        i = (i + 1) & m;
      }
      this.keys[i] = k;
      this.list[this.size++] = k;
    }
    has(k) {
      const m = this.cap - 1;
      for (let i = hashS(k) & m; ; i = (i + 1) & m) {
        const v = this.keys[i];
        if (v === -1) return false;
        if (v === k) return true;
      }
    }
    grow() {
      const old = this.list, n = this.size;
      this.cap *= 2; this.size = 0;
      this.keys = new Float64Array(this.cap).fill(-1);
      this.list = new Float64Array(this.cap >> 1);
      for (let j = 0; j < n; j++) this.add(old[j]);
    }
  }
  const isAnchor = (v) => v === 1 || v === 2, isOpen = (v) => v === 3 || v === 5, isClose = (v) => v === 4 || v === 6;
  const colorOf = (v) => (isAnchor(v) ? v - 1 : (v - 3) >> 1);

  function partner(s, i, n) {
    const v = gv(s, i);
    let depth = 0;
    if (isOpen(v)) {
      for (let j = i + 1; j < n; j++) {
        const w = gv(s, j);
        if (isOpen(w)) depth++;
        else if (isClose(w)) { if (depth === 0) return j; depth--; }
      }
    } else {
      for (let j = i - 1; j >= 0; j--) {
        const w = gv(s, j);
        if (isClose(w)) depth++;
        else if (isOpen(w)) { if (depth === 0) return j; depth--; }
      }
    }
    return -1;
  }

  function step(s, r, n, tc, canR, canD, ncol, out) {
    out.length = 0;
    const budget = tc >= 0 ? 1 : 2;
    const navail = (canR ? 1 : 0) + (canD ? 1 : 0);
    const up = gv(s, r), lf = gv(s, r + 1);
    const have = (up !== EM ? 1 : 0) + (lf !== EM ? 1 : 0);
    if (have > budget) return out;
    const need = budget - have;
    if (need > navail) return out;
    const base = sv(sv(s, r, EM), r + 1, EM);
    if (have === 0) {
      if (tc >= 0) {
        if (canR) out.push(sv(base, r, 1 + tc));
        if (canD) out.push(sv(base, r + 1, 1 + tc));
      } else {
        for (let col = 0; col < ncol; col++) out.push(sv(sv(base, r, 3 + 2 * col), r + 1, 4 + 2 * col));
      }
    } else if (have === 1) {
      const p = up !== EM ? up : lf, pos = up !== EM ? r : r + 1, pc = colorOf(p);
      if (need === 0) {
        if (pc !== tc) return out;
        if (isAnchor(p)) out.push(base);
        else out.push(sv(base, partner(s, pos, n), 1 + pc));
      } else {
        if (canR) out.push(sv(base, r, p));
        if (canD) out.push(sv(base, r + 1, p));
      }
    } else {
      const col = colorOf(up);
      if (col !== colorOf(lf)) return out;
      if (isAnchor(up) && isAnchor(lf)) out.push(base);
      else if (isAnchor(up) || isAnchor(lf)) out.push(sv(base, partner(s, isAnchor(up) ? r + 1 : r, n), 1 + col));
      else if (isOpen(up) && isClose(lf)) return out;
      else if (isClose(up) && isOpen(lf)) out.push(base);
      else if (isOpen(up)) out.push(sv(base, partner(s, r + 1, n), 3 + 2 * col));
      else out.push(sv(base, partner(s, r, n), 4 + 2 * col));
    }
    return out;
  }

  // Necessary for any covering by paths: the endpoint signs (+1 on cells with r + c even, -1
  // otherwise) sum to 2 (R C mod 2). Each path's cells alternate in sign, so a path's sign sum is
  // half its two endpoints' signs; the whole grid sums to R C mod 2.
  function termsParityOk(R, C, terms) {
    let s = 0;
    for (const [[r, c]] of terms) s += (r + c) % 2 === 0 ? 1 : -1;
    return s === 2 * ((R * C) % 2);
  }

  function prepare(R, C, terms) {
    const cols = [...new Set(terms.map((t) => t[1]))].sort();
    for (const col of cols) if (terms.filter((t) => t[1] === col).length !== 2) throw new Error("each colour needs exactly two endpoints");
    const transposed = R > C;
    if (transposed) { [R, C] = [C, R]; terms = terms.map(([[r, c], col]) => [[c, r], col]); }
    const term = new Map();
    for (const [x, col] of terms) term.set(key(x), col);
    return { R, C, terms, term, transposed, cols, ncol: Math.max(...cols) + 1 };
  }

  /** The plug DP: {colour: path} for the endpoints in terms ([[r, c], colour] pairs), or null. */
  function solvePaths(R0, C0, terms0) {
    const { R, C, terms, term, transposed, cols, ncol } = prepare(R0, C0, terms0);
    if (!termsParityOk(R, C, terms)) return null;
    const n = R + 1, MOD = POW[n];
    const tcAt = (r, c) => (term.has(key([r, c])) ? term.get(key([r, c])) : -1);
    const ckpt = [], buf = [];
    let cur = new StateSet();
    cur.add(0);
    for (let c = 0; c < C; c++) {
      if (c > 0) {
        const nx = new StateSet(capFor(cur.size));
        for (let j = 0; j < cur.size; j++) nx.add((cur.list[j] * 8) % MOD);
        cur = nx;
      }
      ckpt.push(Array.from(cur.list.slice(0, cur.size).sort()));
      for (let r = 0; r < R; r++) {
        const tc = tcAt(r, c), nx = new StateSet(capFor(cur.size));
        for (let j = 0; j < cur.size; j++) {
          step(cur.list[j], r, n, tc, c < C - 1, r < R - 1, ncol, buf);
          for (let q = 0; q < buf.length; q++) nx.add(buf[q]);
        }
        cur = nx;
        if (cur.size === 0) return null;
      }
    }
    if (!cur.has(0)) return null;
    const sig = (v) => (v === EM ? 0 : 1 + colorOf(v));
    const right = new Map(), down = new Map();
    let target = 0;
    for (let c = C - 1; c >= 0; c--) {
      const layers = [new Map(ckpt[c].map((s) => [s, null]))];
      for (let r = 0; r < R; r++) {
        const tc = tcAt(r, c), nx = new Map();
        for (const s of layers[r].keys()) {
          for (const t of step(s, r, n, tc, c < C - 1, r < R - 1, ncol, buf)) {
            if (nx.has(t)) continue;
            let ok = true;
            for (let j = 0; j <= r && ok; j++) if (sig(gv(t, j)) !== sig(gv(target, j))) ok = false;
            if (ok) nx.set(t, s);
          }
        }
        layers.push(nx);
      }
      let s = target;
      if (!layers[R].has(s)) throw new Error("plug DP: backward pass lost the target");
      for (let r = R; r >= 1; r--) {
        const ru = gv(s, r - 1), dn = gv(s, r);
        if (ru !== EM) right.set(key([r - 1, c]), colorOf(ru));
        if (dn !== EM) down.set(key([r - 1, c]), colorOf(dn));
        s = layers[r].get(s);
      }
      target = Math.floor(s / 8);
    }
    const out = {};
    for (const col of cols) {
      const [a, b] = terms.filter((t) => t[1] === col).map((t) => t[0]);
      const path = [a];
      let prev = null, x = a;
      while (!eq(x, b)) {
        const [r, c] = x, cand = [];
        if (right.get(key([r, c])) === col) cand.push([r, c + 1]);
        if (down.get(key([r, c])) === col) cand.push([r + 1, c]);
        if (c > 0 && right.get(key([r, c - 1])) === col) cand.push([r, c - 1]);
        if (r > 0 && down.get(key([r - 1, c])) === col) cand.push([r - 1, c]);
        const nx = cand.filter((y) => !(prev && eq(y, prev)));
        if (nx.length === 0) throw new Error("plug DP: broken path");
        prev = x; x = nx[0]; path.push(x);
      }
      out[col] = transposed ? path.map(([r, c]) => [c, r]) : path;
    }
    return out;
  }

  function solvablePaths(R0, C0, terms0) {
    const { R, C, terms, term, ncol } = prepare(R0, C0, terms0);
    if (!termsParityOk(R, C, terms)) return false;
    const n = R + 1, MOD = POW[n];
    const buf = [];
    let cur = new StateSet();
    cur.add(0);
    for (let c = 0; c < C; c++) {
      if (c > 0) {
        const nx = new StateSet(capFor(cur.size));
        for (let j = 0; j < cur.size; j++) nx.add((cur.list[j] * 8) % MOD);
        cur = nx;
      }
      for (let r = 0; r < R; r++) {
        const tc = term.has(key([r, c])) ? term.get(key([r, c])) : -1, nx = new StateSet(capFor(cur.size));
        for (let j = 0; j < cur.size; j++) {
          step(cur.list[j], r, n, tc, c < C - 1, r < R - 1, ncol, buf);
          for (let q = 0; q < buf.length; q++) nx.add(buf[q]);
        }
        cur = nx;
        if (cur.size === 0) return false;
      }
    }
    return cur.has(0);
  }

  const termsOf = (I) => [[I.s0, 0], [I.t0, 0], [I.s1, 1], [I.t1, 1]];
  function solveInstanceDP(I) {
    const res = solvePaths(I.R, I.C, termsOf(I));
    return res ? [res[0], res[1]] : null;
  }

  // ------------------------------------------------------------------ lift ----------
  function splice(paths, u, v, mid) {
    for (const p of paths) {
      for (let i = 0; i + 1 < p.length; i++) {
        if (eq(p[i], u) && eq(p[i + 1], v)) { p.splice(i + 1, 0, ...mid); return; }
        if (eq(p[i], v) && eq(p[i + 1], u)) { p.splice(i + 1, 0, ...mid.slice().reverse()); return; }
      }
    }
    throw new Error("edge not in any path");
  }

  function blockCycle(w, L) {
    const cyc = [];
    for (let j = 0; j < L; j++) cyc.push([0, j]);
    if (w % 2 === 0) {
      for (let i = 1; i < w; i++) {
        if (i % 2 === 1) for (let j = L - 1; j >= 1; j--) cyc.push([i, j]);
        else for (let j = 1; j < L; j++) cyc.push([i, j]);
      }
      for (let i = w - 1; i >= 1; i--) cyc.push([i, 0]);
    } else {
      for (let j = L - 1; j >= 0; j--) {
        if ((L - 1 - j) % 2 === 0) for (let i = 1; i < w; i++) cyc.push([i, j]);
        else for (let i = w - 1; i >= 1; i--) cyc.push([i, j]);
      }
    }
    return cyc;
  }
  const flipPath = (cyc, a) => cyc.slice(0, a + 1).reverse().concat(cyc.slice(a + 1).reverse());

  function bandRows(R, C, paths, r) {
    paths = paths.map((p) => p.map((x) => (x[0] <= r ? x : [x[0] + 2, x[1]])));
    const n1 = r + 1, n2 = r + 2;
    const xs = [];
    for (const p of paths) {
      for (let i = 0; i + 1 < p.length; i++) {
        const a = p[i], b = p[i + 1];
        if (a[1] === b[1] && ((a[0] === r && b[0] === r + 3) || (a[0] === r + 3 && b[0] === r))) xs.push(a[1]);
      }
    }
    xs.sort((a, b) => a - b);
    for (const c of xs) splice(paths, [r, c], [r + 3, c], [[n1, c], [n2, c]]);
    const bounds = [-1].concat(xs, [C]);
    const runs = [];
    for (let i = 0; i + 1 < bounds.length; i++) runs.push([bounds[i] + 1, bounds[i + 1] - 1]);
    const horiz = new Set();
    for (const p of paths) {
      for (let i = 0; i + 1 < p.length; i++) {
        const a = p[i], b = p[i + 1];
        if (a[0] === r && b[0] === r && Math.abs(a[1] - b[1]) === 1) horiz.add(Math.min(a[1], b[1]));
      }
    }
    const hs = [...horiz].sort((a, b) => a - b);
    let j = runs.findIndex(([lo, hi]) => lo > hi);
    if (j < 0) j = runs.findIndex(([lo, hi]) => hs.some((a) => lo <= a && a < hi));
    xs.forEach((c, k) => {
      const i = k + 1;
      const [lo, hi] = i <= j ? runs[i - 1] : runs[i];
      if (lo > hi) return;
      const mid = [];
      if (i <= j) {
        for (let y = c - 1; y >= lo; y--) mid.push([n1, y]);
        for (let y = lo; y < c; y++) mid.push([n2, y]);
      } else {
        for (let y = c + 1; y <= hi; y++) mid.push([n1, y]);
        for (let y = hi; y > c; y--) mid.push([n2, y]);
      }
      splice(paths, [n1, c], [n2, c], mid);
    });
    const [lo, hi] = runs[j];
    if (lo <= hi) {
      const a = hs.find((a) => lo <= a && a < hi);
      const cyc = blockCycle(2, hi - lo + 1).map(([i, y]) => [n1 + i, lo + y]);
      splice(paths, [r, a], [r, a + 1], flipPath(cyc, a - lo));
    }
    return paths;
  }

  function rowsExtend(R, C, paths, k) {
    const ends_ = paths.flatMap((p) => [p[0], p[p.length - 1]]);
    if (k >= 1 && !ends_.some((x) => x[0] === k - 1)) return bandRows(R, C, paths, k - 1);
    if (k < R && !ends_.some((x) => x[0] === k)) {
      const refl = (x, n) => [n - 1 - x[0], x[1]];
      const out = bandRows(R, C, paths.map((p) => p.map((x) => refl(x, R))), R - 1 - k);
      return out.map((p) => p.map((x) => refl(x, R + 2)));
    }
    throw new Error("no endpoint-free line next to the insertion point");
  }

  /** Insert two empty lines at position k on the axis (0 rows, 1 columns). */
  function extend(R, C, paths, axis, k) {
    paths = paths.map((p) => p.slice());
    if (axis === 0) return rowsExtend(R, C, paths, k);
    const tp = (ps) => ps.map((p) => p.map(([r, c]) => [c, r]));
    return tp(rowsExtend(C, R, tp(paths), k));
  }

  function addBlock(R, C, paths, w) {
    paths = paths.map((p) => p.slice());
    let a = null;
    outer: for (const p of paths) {
      for (let i = 0; i + 1 < p.length; i++) {
        const x = p[i], y = p[i + 1];
        if (x[0] === R - 1 && y[0] === R - 1 && Math.abs(x[1] - y[1]) === 1) { a = Math.min(x[1], y[1]); break outer; }
      }
    }
    if (a === null) throw new Error("no edge along the last row");
    const cyc = blockCycle(w, C).map(([i, y]) => [R + i, y]);
    splice(paths, [R - 1, a], [R - 1, a + 1], flipPath(cyc, a));
    return paths;
  }

  // ------------------------------------------------------------------- IPS ----------
  const par = (v) => (v[0] + v[1]) % 2;
  const colorCompatible = (R, C, s, t) => ((R * C) % 2 === 1 ? par(s) === 0 && par(t) === 0 : par(s) !== par(t));
  const isCorner = (w, h, v) => [[0, 0], [w - 1, 0], [0, h - 1], [w - 1, h - 1]].some((x) => eq(x, v));

  function forbidden(w, h, s, t) {
    if (w === 1 || h === 1) {
      const isw = w === 1, bound = isw ? h : w, far = isw ? [0, bound - 1] : [bound - 1, 0];
      return !((eq(s, [0, 0]) && eq(t, far)) || (eq(s, far) && eq(t, [0, 0])));
    }
    if (w === 2 || h === 2) {
      return !isCorner(w, h, s) && !isCorner(w, h, t) && ((w === 2 && s[1] === t[1]) || (h === 2 && s[0] === t[0]));
    }
    if (w === 3 || h === 3) {
      const isw = w === 3, opp = isw ? h : w;
      if (!(opp % 2 === 0 && par(s) !== par(t))) return false;
      const c0 = isw ? s[1] : s[0], c1 = isw ? t[1] : t[0], oc = isw ? s[0] : s[1];
      const greater = c1 < c0, dist = greater ? c0 - c1 : c1 - c0;
      const distOk = oc === 1 ? dist > 0 : dist > 1;
      return distOk && ((greater && par(s) !== 1) || (!greater && par(s) !== 0));
    }
    return false;
  }

  function acceptable(R, C, s, t) {
    if (eq(s, t)) return R * C === 1;
    if (!(s[0] >= 0 && s[0] < R && s[1] >= 0 && s[1] < C && t[0] >= 0 && t[0] < R && t[1] >= 0 && t[1] < C)) return false;
    return colorCompatible(R, C, s, t) && !forbidden(R, C, s, t);
  }

  const SMALL = 6;
  const sh = (v, dr, dc) => [v[0] + dr, v[1] + dc];

  /** A Hamiltonian path s -> t of the R x C grid, or null. */
  function hamiltonianPath(R, C, s, t) {
    if (!acceptable(R, C, s, t)) return null;
    if (eq(s, t)) return [s];
    if (Math.min(R, C) <= SMALL) return solvePaths(R, C, [[s, 0], [t, 0]])[0];
    for (const side of ["top", "bottom", "left", "right"]) {
      if (side === "top" && s[0] >= 3 && t[0] >= 3 && acceptable(R - 2, C, sh(s, -2, 0), sh(t, -2, 0)))
        return insertTwoLines(R - 2, C, [hamiltonianPath(R - 2, C, sh(s, -2, 0), sh(t, -2, 0))], 0, -1)[0];
      if (side === "bottom" && s[0] < R - 3 && t[0] < R - 3 && acceptable(R - 2, C, s, t))
        return insertTwoLines(R - 2, C, [hamiltonianPath(R - 2, C, s, t)], 0, R - 3)[0];
      if (side === "left" && s[1] >= 3 && t[1] >= 3 && acceptable(R, C - 2, sh(s, 0, -2), sh(t, 0, -2)))
        return insertTwoLines(R, C - 2, [hamiltonianPath(R, C - 2, sh(s, 0, -2), sh(t, 0, -2))], 1, -1)[0];
      if (side === "right" && s[1] < C - 3 && t[1] < C - 3 && acceptable(R, C - 2, s, t))
        return insertTwoLines(R, C - 2, [hamiltonianPath(R, C - 2, s, t)], 1, C - 3)[0];
    }
    let [a, b] = s[0] <= t[0] ? [s, t] : [t, s];
    for (let p = a[0] + 1; p <= b[0]; p++) {
      for (let y = 0; y < C; y++) {
        const u = [p - 1, y];
        if (acceptable(p, C, a, u) && acceptable(R - p, C, [0, y], [b[0] - p, b[1]])) {
          const top = hamiltonianPath(p, C, a, u), bot = hamiltonianPath(R - p, C, [0, y], [b[0] - p, b[1]]);
          const path = top.concat(bot.map(([r, c]) => [r + p, c]));
          return eq(path[0], s) ? path : path.reverse();
        }
      }
    }
    [a, b] = s[1] <= t[1] ? [s, t] : [t, s];
    for (let p = a[1] + 1; p <= b[1]; p++) {
      for (let x = 0; x < R; x++) {
        const u = [x, p - 1];
        if (acceptable(R, p, a, u) && acceptable(R, C - p, [x, 0], [b[0], b[1] - p])) {
          const left = hamiltonianPath(R, p, a, u), rgt = hamiltonianPath(R, C - p, [x, 0], [b[0], b[1] - p]);
          const path = left.concat(rgt.map(([r, c]) => [r, c + p]));
          return eq(path[0], s) ? path : path.reverse();
        }
      }
    }
    const res = solvePaths(R, C, [[s, 0], [t, 0]]);
    return res ? res[0] : null;
  }
  const insertTwoLines = (R, C, paths, axis, after) => extend(R, C, paths, axis, after + 1);

  // ---------------------------------------------------------------- solver ----------
  function checkInst(I) {
    if (Array.isArray(I)) I = inst(I[0], I[1], [I[2], I[3]], [I[4], I[5]], [I[6], I[7]], [I[8], I[9]]);
    if (!wellFormed(I)) throw new Error("instance must have four distinct endpoints inside the grid");
    return I;
  }

  /** Is the instance solvable? */
  function decide(I) {
    I = checkInst(I);
    if (Math.min(I.R, I.C) <= THIN) return solvablePaths(I.R, I.C, termsOf(I));
    return firesI(I) === null;
  }

  function explain(I) {
    I = checkInst(I);
    if (Math.min(I.R, I.C) <= THIN) return "thin: decided by the plug DP";
    const f = firesI(I);
    return f ? `catalogue entry ${f} fires` : "passes the catalogue";
  }

  function findReduction(I) {
    for (const axis of [0, 1]) {
      const n = axis === 0 ? I.R : I.C;
      if (n < 13) continue;
      const lines = ends(I).map((x) => x[axis]);
      const free = (k) => !lines.includes(k), below = (k) => lines.some((v) => v < k), above = (k) => lines.some((v) => v > k);
      let ok = true;
      for (let k = 0; k < 4; k++) ok = ok && free(k);
      if (ok) return [axis, 0];
      ok = true;
      for (let k = n - 4; k < n; k++) ok = ok && free(k);
      if (ok) return [axis, n - 2];
      for (let lo = 0; lo < n - 9; lo++) {
        let all = true;
        for (let k = lo; k < lo + 10; k++) all = all && free(k);
        if (all && below(lo) && above(lo + 9)) return [axis, lo + 4];
      }
      for (let d = 8; d < n - 9; d++) {
        if (free(d) && free(d + 1) && ((d >= 1 && free(d - 1)) || free(d + 2)) && below(d) && above(d + 1)) return [axis, d];
      }
    }
    return null;
  }

  function deleteLines(I, axis, d) {
    const f = (x) => { let v = x[axis]; if (v > d + 1) v -= 2; return axis === 0 ? [v, x[1]] : [x[0], v]; };
    const [R, C] = axis === 0 ? [I.R - 2, I.C] : [I.R, I.C - 2];
    return inst(R, C, f(I.s0), f(I.t0), f(I.s1), f(I.t1));
  }

  const tw = (w, h) => (w <= THIN || h <= THIN ? Math.min(w, h) : 0);
  const F = false, T = true;
  const LABS = {
    0: [[F, F, F]], 1: [[F, F, F], [F, F, T]],
    2: [[F, F, F], [T, F, F], [F, F, T], [F, T, T]],
    3: [[F, F, F], [T, F, F], [F, T, F], [T, T, F]], 4: [[F, F, F], [F, F, T]],
  };
  const TYPE_SYMS = [];
  for (let t = 0; t < 5; t++) for (const g of GEOS) for (const lab of LABS[t]) TYPE_SYMS.push([t, g, lab]);
  const MOVE_NAMES = ["strip", "2/2 same", "1/3", "2/2 cross", "excursion"];
  const instKey = (J) => [J.R, J.C, ...J.s0, ...J.t0, ...J.s1, ...J.t1].join(",");
  const parityOkI = (J) => ends(J).reduce((a, x) => a + ((x[0] + x[1]) % 2 === 0 ? 1 : -1), 0) === 2 * ((J.R * J.C) % 2);
  const shr = (x, p) => [x[0] - p, x[1]];

  function cutBack(g, I, p) {
    const R2 = g[0] ? I.C : I.R;
    const k = g[1] ? R2 - p : p;
    return g[0] ? [1, k] : [0, k];
  }

  class Solver {
    constructor(trace) { this.feas = new Map(); this.trace = trace; }
    log(...stepArgs) { if (this.trace) this.trace.push(stepArgs); }

    pieceOk(J) {
      if (!wellFormed(J)) return false;
      if (J.R <= THIN || J.C <= THIN) {
        if (!parityOkI(J)) return false;
        const k = instKey(J);
        if (!this.feas.has(k)) this.feas.set(k, solvablePaths(J.R, J.C, termsOf(J)));
        return this.feas.get(k);
      }
      return firesI(J) === null;
    }

    pieceSolve(J) {
      const sol = this.solve(J);
      if (!sol) throw new Error("internal error: piece unsolvable");
      return sol;
    }

    solve(I) {
      if (Math.min(I.R, I.C) <= THIN) { this.log("thin", I); return solveInstanceDP(I); }
      const f = firesI(I);
      if (f) { this.log("fires", I, f); return null; }
      const red = findReduction(I);
      if (red) {
        const [axis, d] = red;
        this.log("reduce", I, axis, d);
        const Ir = deleteLines(I, axis, d);
        const sol = this.solve(Ir);
        if (!sol) throw new Error("internal error: reduced instance unsolvable");
        return orient(I, extend(Ir.R, Ir.C, sol, axis, d));
      }
      let sol = this.sameSplit(I);
      if (sol) return sol;
      sol = this.move(I);
      if (!sol) throw new Error("no valid move found (contradicts Theorem A)");
      return sol;
    }

    sameSplit(I) {
      for (const g of [[F, F, F], [T, F, F]]) {
        const J0 = applyGeo(g, I);
        for (const J of [J0, relabel([F, F, T], J0)]) {
          for (let p = 1; p < J.R; p++) {
            if (J.s0[0] < p && J.t0[0] < p && J.s1[0] >= p && J.t1[0] >= p &&
                acceptable(p, J.C, J.s0, J.t0) && acceptable(J.R - p, J.C, shr(J.s1, p), shr(J.t1, p))) {
              this.log("same", I, [g[0] ? 1 : 0, p]);
              const a = hamiltonianPath(p, J.C, J.s0, J.t0);
              const b = hamiltonianPath(J.R - p, J.C, shr(J.s1, p), shr(J.t1, p));
              return mapBack(g, I, [a, b.map(([r, c]) => [r + p, c])]);
            }
          }
        }
      }
      return null;
    }

    move(I) {
      for (let m = 0; m <= THIN; m++) {
        for (const [t, g, lab] of TYPE_SYMS) {
          const J = relabel(lab, applyGeo(g, I));
          const mark = this.trace ? this.trace.length : 0;
          const res = this.canon(t, m, J);
          if (res) {
            const [sol, p] = res;
            if (this.trace) this.trace.splice(mark, 0, ["move", I, MOVE_NAMES[t], cutBack(g, I, p)]);
            return mapBack(g, I, sol);
          }
        }
      }
      return null;
    }

    canon(t, m, J) {
      const { R, C, s0, t0, s1, t1 } = J;
      const up = (p) => (path) => path.map(([r, c]) => [r + p, c]);
      for (let p = 1; p < R; p++) {
        if (t === 0) {
          if (Math.max(s0[0], t0[0], s1[0], t1[0]) < p && R - p >= 2 && ((R - p) * C) % 2 === 0 && C >= 5 && tw(p, C) === m) {
            const L = inst(p, C, s0, t0, s1, t1);
            if (this.pieceOk(L)) { const [a, b] = this.pieceSolve(L); return [addBlock(p, C, [a, b], R - p), p]; }
          }
        } else if (t === 1) {
          if (m === 0 && s0[0] < p && t0[0] < p && s1[0] >= p && t1[0] >= p &&
              acceptable(p, C, s0, t0) && acceptable(R - p, C, shr(s1, p), shr(t1, p))) {
            const a = hamiltonianPath(p, C, s0, t0), b = hamiltonianPath(R - p, C, shr(s1, p), shr(t1, p));
            return [[a, up(p)(b)], p];
          }
        } else if (t === 2) {
          if (s0[0] < p && t0[0] >= p && s1[0] >= p && t1[0] >= p && tw(R - p, C) === m) {
            for (let y = 0; y < C; y++) {
              if (!acceptable(p, C, s0, [p - 1, y])) continue;
              const Rr = inst(R - p, C, [0, y], shr(t0, p), shr(s1, p), shr(t1, p));
              if (this.pieceOk(Rr)) {
                const a = hamiltonianPath(p, C, s0, [p - 1, y]);
                const [r0, r1] = this.pieceSolve(Rr);
                return [[a.concat(up(p)(r0)), up(p)(r1)], p];
              }
            }
          }
        } else if (t === 3) {
          if (s0[0] < p && s1[0] < p && t0[0] >= p && t1[0] >= p && Math.max(tw(p, C), tw(R - p, C)) === m) {
            for (let y0 = 0; y0 < C; y0++) {
              for (let y1 = 0; y1 < C; y1++) {
                const L = inst(p, C, s0, [p - 1, y0], s1, [p - 1, y1]);
                const Rr = inst(R - p, C, [0, y0], shr(t0, p), [0, y1], shr(t1, p));
                const [first, second] = p <= R - p ? [L, Rr] : [Rr, L];
                if (this.pieceOk(first) && this.pieceOk(second)) {
                  const [l0, l1] = this.pieceSolve(L), [r0, r1] = this.pieceSolve(Rr);
                  return [[l0.concat(up(p)(r0)), l1.concat(up(p)(r1))], p];
                }
              }
            }
          }
        } else {
          if (s0[0] < p && t0[0] < p && s1[0] >= p && t1[0] >= p && Math.max(tw(p, C), tw(R - p, C)) === m) {
            for (let ya = 0; ya < C; ya++) {
              for (let yb = 0; yb < C; yb++) {
                const N = inst(p, C, s0, [p - 1, ya], [p - 1, yb], t0);
                const Fp = inst(R - p, C, shr(s1, p), shr(t1, p), [0, ya], [0, yb]);
                const [first, second] = p <= R - p ? [N, Fp] : [Fp, N];
                if (this.pieceOk(first) && this.pieceOk(second)) {
                  const [n0, n1] = this.pieceSolve(N), [f0, f1] = this.pieceSolve(Fp);
                  return [[n0.concat(up(p)(f1), n1), up(p)(f0)], p];
                }
              }
            }
          }
        }
      }
      return null;
    }
  }

  /** A solution [pathA, pathB], or null if unsolvable. `trace` (an array) collects the steps. */
  function solve(I, trace) {
    I = checkInst(I);
    const sol = new Solver(trace || null).solve(I);
    if (sol && !checkSolution(I, sol)) throw new Error("internal error: produced an invalid solution");
    return sol;
  }

  // ------------------------------------------------------------ optimized ----------
  // Optimized solving for thin instances: guess splits, fall back to the plug DP. Same algorithm,
  // parameters and candidate order as lib/python/zzn/optimized.py (see its docstring), so the
  // paths are the same. The plug DP's cost grows exponentially with the shorter side; cutting a
  // thin grid into pieces with a short side makes it cheap. A piece is reported unsolvable only
  // after an exact test (parity, IPS, or the plug DP), so the answers are exact.
  const OPT = { MARGIN: 3, NARROW: 6, AREA: 60, SMALL: 7, TRIES: 4, CUTS: 2, BUDGET: 1 };

  // Estimated plug DP cost of an R x C piece: cells times a bound on the states per cell. The
  // context `ctx` carries the trace function and the work done so far in these units.
  //
  const optEst = (R, C) => R * C * 3 ** Math.min(R, C);
  const NOGUESS = Symbol("no viable guess");
  const optTranspose = (terms) => terms.map(([[r, c], k]) => [[c, r], k]);
  const optShift = (terms, dc) => terms.map(([[r, c], k]) => [[r, c + dc], k]);
  const optColours = (terms) => [...new Set(terms.map((t) => t[1]))].sort((a, b) => a - b);
  const mapPaths = (paths, f) => {
    const out = {};
    for (const k of Object.keys(paths)) out[k] = paths[k].map(f);
    return out;
  };
  const cmpArr = (x, y) => {
    for (let i = 0; i < x.length; i++) if (x[i] !== y[i]) return x[i] - y[i];
    return 0;
  };

  // Each colour's path starts at that colour's first term.
  //
  function optOrient(paths, terms) {
    const out = {};
    for (const k of Object.keys(paths)) {
      const first = terms.find((t) => t[1] === +k)[0], p = paths[k];
      out[k] = eq(p[0], first) ? p : p.slice().reverse();
    }
    return out;
  }

  function optPiece(R, C, terms, ctx) {
    if (!termsParityOk(R, C, terms)) return null;
    const cols = optColours(terms);
    if (cols.length === 1) {
      ctx.log("ips", { R, C });
      ctx.work += R * C;
      const p = hamiltonianPath(R, C, terms[0][0], terms[1][0]);
      return p ? { [cols[0]]: p } : null;
    }
    if (Math.min(R, C) > OPT.NARROW && R * C > OPT.AREA) {
      // Guessing here, including the pieces below, may cost at most BUDGET times this piece's own
      // plug DP; then the plug DP decides.
      //
      const limit = ctx.work + OPT.BUDGET * optEst(R, C);
      const small = Math.min(R, C) <= OPT.SMALL;
      const cuts = small ? 1 : OPT.CUTS, tries = small ? 1 : OPT.TRIES;
      let tried = 0;
      for (const [tr, m] of optOptions(R, C, terms)) {
        if (tried === cuts || ctx.work >= limit) break;
        const [RR, CC, tt] = tr ? [C, R, optTranspose(terms)] : [R, C, terms];
        let res = optGuess(RR, CC, tt, m, tries, limit, ctx);
        if (res === NOGUESS) continue;
        tried++;
        if (res !== null) {
          if (tr) res = mapPaths(res, ([r, c]) => [c, r]);
          return optOrient(res, terms);
        }
      }
      if (tried) ctx.log("fallback", { R, C });
    }
    ctx.log("dp", { R, C });
    ctx.work += optEst(R, C);
    const res = solvePaths(R, C, terms);
    return res ? optOrient(res, terms) : null;
  }

  // Cuts to try, as [transposed, m]: across the longer side first, then the shorter; with MARGIN
  // free lines next to the cut, then with 1.
  //
  function optOptions(R, C, terms) {
    const axes = C >= R ? [false, true] : [true, false];
    const out = [], seen = new Set();
    for (const margin of [OPT.MARGIN, 1]) {
      for (const tr of axes) {
        const [RR, CC, tt] = tr ? [C, R, optTranspose(terms)] : [R, C, terms];
        for (const m of optCuts(RR, CC, tt, margin)) {
          const k = (tr ? "t" : "n") + m;
          if (!seen.has(k)) { seen.add(k); out.push([tr, m]); }
        }
      }
    }
    return out;
  }

  // Cuts between columns m-1 and m with at least `margin` endpoint-free columns on each side and
  // both pieces at least 2 wide, best first: strips (the empty block of even area, largest first),
  // then cuts in the gaps between endpoint columns, farthest from the endpoints first, ties nearest
  // the middle.
  //
  function optCuts(R, C, terms, margin) {
    const xs = [...new Set(terms.map((t) => t[0][1]))].sort((a, b) => a - b);
    const strips = [];
    let m = xs[0] - margin;
    if (m >= 2 && (m * R) % 2 === 1) m--;
    if (m >= 2) strips.push([m, m]);
    m = xs[xs.length - 1] + 1 + margin;
    if (C - m >= 2 && ((C - m) * R) % 2 === 1) m++;
    if (C - m >= 2) strips.push([C - m, m]);
    strips.sort((a, b) => b[0] - a[0] || a[1] - b[1]);
    const inner = [];
    for (let i = 0; i + 1 < xs.length; i++) {
      const a = xs[i], b = xs[i + 1];
      for (let mm = a + 1 + margin; mm <= b - margin; mm++) inner.push([-Math.min(mm - 1 - a, b - mm), Math.abs(2 * mm - C), mm]);
    }
    inner.sort(cmpArr);
    return strips.map((s) => s[1]).concat(inner.map((s) => s[2]));
  }

  // The row where the straight line from lo (left of the cut) to hi meets the cut, rounded down.
  //
  const optTarget = ([r1, c1], [r2, c2], m) => r1 + Math.floor(((r2 - r1) * (2 * (m - c1) - 1)) / (2 * (c2 - c1)));

  function optViable(R, C, terms) {
    if (!termsParityOk(R, C, terms)) return false;
    if (optColours(terms).length === 1) return acceptable(R, C, terms[0][0], terms[1][0]);
    return true;
  }

  // Paths for the piece by one of the guesses at cut m, null if they all fail, or NOGUESS if no
  // guess passes the cheap exact tests.
  //
  function optGuess(R, C, terms, m, tries, limit, ctx) {
    const L = terms.filter((t) => t[0][1] < m), Rt = terms.filter((t) => t[0][1] >= m);
    if (!L.length || !Rt.length) return optStrip(R, C, terms, m, L.length > 0, ctx);
    const split = optColours(terms).filter((k) => L.filter((t) => t[1] === k).length === 1);
    if (!split.length) {
      const Rs = optShift(Rt, -m);
      if (!(optViable(R, m, L) && optViable(R, C - m, Rs))) return NOGUESS;
      ctx.log("split", { R, C }, `same, column ${m}`);
      const pl = optPiece(R, m, L, ctx);
      if (!pl) return null;
      const pr = optPiece(R, C - m, Rs, ctx);
      if (!pr) return null;
      return Object.assign({}, pl, mapPaths(pr, ([r, c]) => [r, c + m]));
    }

    // Crossings on the border rows or next to each other come last; then the distance from the
    // straight line between that colour's two endpoints; ties by row.
    //
    const tgt = split.map((k) => optTarget(L.find((t) => t[1] === k)[0], Rt.find((t) => t[1] === k)[0], m));
    const score = (rows) => {
      let pen = rows.filter((a) => a === 0 || a === R - 1).length;
      if (rows.length === 2 && Math.abs(rows[0] - rows[1]) === 1) pen++;
      return [pen, rows.reduce((s, a, i) => s + Math.abs(a - tgt[i]), 0), ...rows];
    };
    const cands = [];
    if (split.length === 1) for (let a = 0; a < R; a++) cands.push([a]);
    else for (let a = 0; a < R; a++) for (let b = 0; b < R; b++) if (a !== b) cands.push([a, b]);
    const keyed = cands.map((c) => [score(c), c]).sort((x, y) => cmpArr(x[0], y[0]));
    let tried = 0;
    for (const [, rows] of keyed) {
      const lt = L.concat(rows.map((a, i) => [[a, m - 1], split[i]]));
      const rt = optShift(Rt, -m).concat(rows.map((a, i) => [[a, 0], split[i]]));
      if (!(optViable(R, m, lt) && optViable(R, C - m, rt))) continue;
      if (tried === tries || ctx.work >= limit) break;
      tried++;
      ctx.log("split", { R, C }, `${split.length === 2 ? "2/2 cross" : "1/3"}, column ${m}, rows ${rows.join(",")}`);
      const res = optPair(R, C, m, lt, rt, ctx);
      if (!res) continue;
      const [A, B] = res;
      rows.forEach((a, i) => {
        const k = split[i], lp = eq(A[k][A[k].length - 1], [a, m - 1]) ? A[k] : A[k].slice().reverse();
        const rp = B[k].map(([r, c]) => [r, c + m]);
        if (!eq(rp[0], [a, m])) rp.reverse();
        A[k] = lp.concat(rp);
      });
      for (const k of Object.keys(B)) if (!split.includes(+k)) A[k] = B[k].map(([r, c]) => [r, c + m]);
      return A;
    }
    return tried ? null : NOGUESS;
  }

  // Both pieces of a guess: the one-path piece first, else the smaller one first.
  //
  function optPair(R, C, m, lt, rt, ctx) {
    const nl = optColours(lt).length, nr = optColours(rt).length;
    const leftFirst = nl < nr || (nl === nr && m <= C - m);
    const [first, second] = leftFirst ? [[m, lt], [C - m, rt]] : [[C - m, rt], [m, lt]];
    const a = optPiece(R, first[0], first[1], ctx);
    if (!a) return null;
    const b = optPiece(R, second[0], second[1], ctx);
    if (!b) return null;
    return leftFirst ? [a, b] : [b, a];
  }

  // All endpoints on one side of the cut: solve that side, then splice the empty block into a path
  // running along the cut.
  //
  function optStrip(R, C, terms, m, left, ctx) {
    ctx.log("split", { R, C }, `strip, column ${m}`);
    let res, edge, w, cell;
    if (left) {
      res = optPiece(R, m, terms, ctx);
      edge = m - 1; w = C - m; cell = (i, j) => [j, m + i];
    } else {
      res = optPiece(R, C - m, optShift(terms, -m), ctx);
      if (res) res = mapPaths(res, ([r, c]) => [r, c + m]);
      edge = m; w = m; cell = (i, j) => [j, m - 1 - i];
    }
    if (!res) return null;
    const used = new Set();
    for (const k of Object.keys(res)) {
      const p = res[k];
      for (let i = 0; i + 1 < p.length; i++) {
        used.add(key(p[i]) + "|" + key(p[i + 1]));
        used.add(key(p[i + 1]) + "|" + key(p[i]));
      }
    }
    for (let a = 0; a + 1 < R; a++) {
      if (used.has(key([a, edge]) + "|" + key([a + 1, edge]))) {
        const mid = flipPath(blockCycle(w, R), a).map(([i, j]) => cell(i, j));
        const ks = Object.keys(res).map(Number).sort((x, y) => x - y);
        const paths = ks.map((k) => res[k].slice());
        splice(paths, [a, edge], [a + 1, edge], mid);
        const out = {};
        ks.forEach((k, i) => { out[k] = paths[i]; });
        return out;
      }
    }
    return null;
  }

  /** As solve; thin instances are solved by guessed splits with the plug DP as the fallback. */
  function solveOptimized(I, trace) {
    I = checkInst(I);
    if (Math.min(I.R, I.C) > THIN) return solve(I, trace);
    let terms = termsOf(I), R = I.R, C = I.C;
    const tr = R > C;
    if (tr) { [R, C] = [C, R]; terms = optTranspose(terms); }
    const ctx = { log: trace ? (...s) => trace.push(s) : () => {}, work: 0 };
    const res = optPiece(R, C, terms, ctx);
    if (!res) return null;
    let sol = [res[0], res[1]];
    if (tr) sol = sol.map((p) => p.map(([r, c]) => [c, r]));
    if (!checkSolution(I, sol)) throw new Error("internal error: produced an invalid solution");
    return sol;
  }

  function decideOptimized(I) {
    I = checkInst(I);
    if (Math.min(I.R, I.C) > THIN) return decide(I);
    return solveOptimized(I) !== null;
  }

  /** As solvePaths, by guessed splits. */
  function solvePathsOptimized(R, C, terms) {
    const tr = R > C;
    if (tr) { [R, C] = [C, R]; terms = optTranspose(terms); }
    const res = optPiece(R, C, terms, { log: () => {}, work: 0 });
    if (!res || !tr) return res;
    return mapPaths(res, ([r, c]) => [c, r]);
  }

  return {
    Instance: inst, decide, solve, explain, fires, acceptable, hamiltonianPath, solvePaths,
    checkSolution, render, wellFormed, version: "1.0.0",
    optimized: { decide: decideOptimized, solve: solveOptimized, solvePaths: solvePathsOptimized },
  };
});

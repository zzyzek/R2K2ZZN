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

  /** The steps: ["thin", I], ["fires", I, entry], ["block", I, axis, blk], ["reduce", I, axis, d],
   * ["leaf", L]; as in lib/python/zzn/solver.py. */
  class Solver {
    constructor(trace) { this.trace = trace; }
    log(...stepArgs) { if (this.trace) this.trace.push(stepArgs); }
    thin(I) { this.log("thin", I); return solveInstanceDP(I); }
  }

  // --------------------------------------------------------------- blocks ----------
  // Block deletion: the outer layer of the Lean construction `solveR`. Same definitions and
  // choices as lib/python/zzn/blocks.py (see its docstring): Lean's cell (x, y) on a w x h grid
  // is [r, c] on an R x C grid, x = r, w = R, y = c, h = C.
  const nsub = (a, b) => (a > b ? a - b : 0);
  const xsOf = (I) => ends(I).map((e) => e[0]);
  const leftK = (I) => Math.min(Math.floor(nsub(Math.min(...xsOf(I)), 2) / 2), Math.floor(nsub(I.R, 11) / 2));
  const rightK = (I) =>
    Math.min(Math.floor(nsub(nsub(I.R, 3), Math.max(...xsOf(I))) / 2), Math.floor(nsub(I.R, 11) / 2));
  const innerK = (I, a, b) => Math.min(Math.floor(nsub(nsub(b, a), 9) / 2), Math.floor(nsub(I.R, 11) / 2));

  function innerPair(I) {
    const xs = xsOf(I);
    for (const a of xs) {
      for (const b of xs) {
        if (a < b && xs.every((x) => !(a < x && x < b)) && innerK(I, a, b) >= 1) return [a, b];
      }
    }
    return null;
  }

  function blkX(I) {
    let k = leftK(I);
    if (k >= 1) return ["left", k];
    k = rightK(I);
    if (k >= 1) return ["right", k];
    const ab = innerPair(I);
    if (ab) return ["inner", ab[0] + 1, innerK(I, ab[0], ab[1])];
    return null;
  }

  const mapEnds = (I, R, f) => inst(R, I.C, f(I.s0), f(I.t0), f(I.s1), f(I.t1));

  function blkDelete(b, I) {
    if (b[0] === "left") { const m = 2 * b[1]; return mapEnds(I, I.R - m, (v) => [v[0] - m, v[1]]); }
    if (b[0] === "right") return mapEnds(I, I.R - 2 * b[1], (v) => v);
    const r = b[1], m = 2 * b[2];
    return mapEnds(I, I.R - m, (v) => (v[0] <= r ? v : [v[0] - m, v[1]]));
  }

  const transposeI = (I) => inst(I.C, I.R, ...ends(I).map((v) => [v[1], v[0]]));
  const swapPath = (L) => L.map((v) => [v[1], v[0]]);

  function colSnake(x, A, k) {
    const out = [], Ar = A.slice().reverse();
    for (let i = 0; i < k; i++) {
      for (const y of A) out.push([x + 2 * i, y]);
      for (const y of Ar) out.push([x + 2 * i + 1, y]);
    }
    return out;
  }

  function edgeBlock(w, h, y, k) {
    const down = [], up = [];
    for (let z = y; z >= 0; z--) down.push(z);
    for (let z = y + 1; z < h; z++) up.push(z);
    return colSnake(w, down, k).concat(colSnake(w, up, k).reverse());
  }

  function findV(x, L) {
    for (let i = 0; i + 1 < L.length; i++) {
      const u = L[i], v = L[i + 1];
      if (u[0] === x && v[0] === x && Math.abs(u[1] - v[1]) === 1) return i;
    }
    return -1;
  }

  const blkE = (w, h, k, a, b) => (a[1] < b[1] ? edgeBlock(w, h, a[1], k) : edgeBlock(w, h, b[1], k).reverse());

  function edgeLift(w, h, k, p, q) {
    let i = findV(w - 1, p);
    if (i >= 0) return [p.slice(0, i + 1).concat(blkE(w, h, k, p[i], p[i + 1]), p.slice(i + 1)), q];
    i = findV(w - 1, q);
    if (i >= 0) return [p, q.slice(0, i + 1).concat(blkE(w, h, k, q[i], q[i + 1]), q.slice(i + 1))];
    return [p, q];
  }

  function edgeLiftL(w, h, k, p, q) {
    const rf = (W) => (v) => [W - 1 - v[0], v[1]];
    const f = rf(w), g = rf(w + 2 * k);
    const [p2, q2] = edgeLift(w, h, k, p.map(f), q.map(f));
    return [p2.map(g), q2.map(g)];
  }

  /** `seedW`: [R, flip, cross], cross[y] = 1 when a path steps between lines r and r + 1 at y. */
  function seedW(h, p, q, r) {
    const cross = new Uint8Array(h + 1), vert = new Uint8Array(h + 1);
    for (const L of [p, q]) {
      for (let i = 0; i + 1 < L.length; i++) {
        const u = L[i], v = L[i + 1];
        if (u[1] === v[1] && ((u[0] === r && v[0] === r + 1) || (u[0] === r + 1 && v[0] === r))) cross[u[1]] = 1;
        else if (u[0] === r && v[0] === r && Math.abs(u[1] - v[1]) === 1) vert[Math.max(u[1], v[1])] = 1;
      }
    }
    for (let R = 0; R <= h; R++) {
      const a = (R === 0 || cross[R - 1] === 1) && (R === h || cross[R] === 1);
      const b = R >= 1 && R < h && !cross[R - 1] && !cross[R] && vert[R] === 1;
      if (a || b) return [R, !a, cross];
    }
    return [0, false, cross];
  }

  function innerLift(J, r, k, p, q) {
    const h = J.C;
    const [R, flip, cross] = seedW(h, p, q, r);
    const cv = (y) => cross[y] === 1 || (flip && (y + 1 === R || y === R));
    const grp = (a) => {
      const out = [a];
      if (a < R) { for (let y = a - 1; y >= 0 && !cv(y); y--) out.push(y); }
      else { for (let y = a + 1; y < h && !cv(y); y++) out.push(y); }
      return out;
    };
    const W = 2 * k;
    const sn = (a) => colSnake(r + 1, grp(a), k);
    const flipW = flip ? sn(R - 1).concat(sn(R).reverse()) : null;
    const gw = (u, v) => {
      if (u[0] === r && v[0] === r + W + 1 && u[1] === v[1]) return sn(u[1]);
      if (u[0] === r + W + 1 && v[0] === r && u[1] === v[1]) return sn(u[1]).reverse();
      if (flip && u[0] === r && u[1] === R - 1 && v[0] === r && v[1] === R) return flipW;
      if (flip && u[0] === r && u[1] === R && v[0] === r && v[1] === R - 1) return flipW.slice().reverse();
      return null;
    };
    const wideExt = (L) => {
      const S = L.map((v) => (v[0] <= r ? v : [v[0] + W, v[1]]));
      const out = [];
      for (let i = 0; i + 1 < S.length; i++) {
        out.push(S[i]);
        const g = gw(S[i], S[i + 1]);
        if (g) for (const x of g) out.push(x);
      }
      if (S.length) out.push(S[S.length - 1]);
      return out;
    };
    return [wideExt(p), wideExt(q)];
  }

  function blkLift(b, J, p, q) {
    if (b[0] === "left") return edgeLiftL(J.R, J.C, b[1], p, q);
    if (b[0] === "right") return edgeLift(J.R, J.C, b[1], p, q);
    return innerLift(J, b[1], b[2], p, q);
  }

  /** Delete blocks as `solveR` does: [leaf, steps], steps [blk, J, tr] as in blocks.py `plan`. */
  function blkPlan(I) {
    const steps = [];
    while (I.R > 10 && I.C > 10) {
      let b = blkX(I);
      if (b) { const J = blkDelete(b, I); steps.push([b, J, false]); I = J; continue; }
      const T = transposeI(I);
      b = blkX(T);
      if (b) { const J = blkDelete(b, T); steps.push([b, J, true]); I = J; continue; }
      break;
    }
    return [I, steps];
  }

  function blkLiftAll(steps, p, q) {
    for (let i = steps.length - 1; i >= 0; i--) {
      const [b, J, tr] = steps[i];
      [p, q] = blkLift(b, J, p, q);
      if (tr) { p = swapPath(p); q = swapPath(q); }
    }
    return [p, q];
  }


  // ------------------------------------------------------------ reduce2 ----------
  // Two-line reductions: the inner layer of the Lean construction, `solveZ2`. Same definitions
  // and choices as lib/python/zzn/reduce2.py (see its docstring).
  const freeLine = (I, k) => ends(I).every((e) => e[0] !== k);
  const endBelow = (I, k) => ends(I).some((e) => e[0] < k);
  const endAbove = (I, k) => ends(I).some((e) => k < e[0]);

  function redX(I, d) {
    const w = I.R;
    if (!(13 <= w)) return false;
    if (d === 0) { let ok = true; for (let k = 0; k < 4; k++) if (!freeLine(I, k)) ok = false; if (ok) return true; }
    if (d + 2 === w) { let ok = true; for (let k = 0; k < w; k++) if (w <= k + 4 && !freeLine(I, k)) ok = false; if (ok) return true; }
    for (let lo = 0; lo <= d; lo++) {
      if (d + 1 <= lo + 9 && lo + 10 <= w && endBelow(I, lo) && endAbove(I, lo + 9)) {
        let ok = true;
        for (let j = 0; j < 10; j++) if (!freeLine(I, lo + j)) ok = false;
        if (ok) return true;
      }
    }
    return 8 <= d && d + 10 <= w && freeLine(I, d) && freeLine(I, d + 1) &&
      ((1 <= d && freeLine(I, d - 1)) || freeLine(I, d + 2)) && endBelow(I, d) && endAbove(I, d + 1);
  }

  const redB = (I, d) => 13 <= I.R && 5 <= d && d + 7 <= I.R && freeLine(I, d) && freeLine(I, d + 1) &&
    ((1 <= d && freeLine(I, d - 1)) || freeLine(I, d + 2)) && endBelow(I, d) && endAbove(I, d + 1);

  function findRed2(I) {
    for (let d = 0; d < I.R; d++) if (redX(I, d) || redB(I, d)) return d;
    return -1;
  }

  function deleteAt(I, d) {
    const f = (v) => (v[0] < d ? v : [v[0] - 2, v[1]]);
    return inst(I.R - 2, I.C, f(I.s0), f(I.t0), f(I.s1), f(I.t1));
  }

  function stretch2(r, L) {
    const out = [];
    for (let i = 0; i < L.length; i++) {
      const a = L[i];
      out.push(a[0] <= r ? a : [a[0] + 2, a[1]]);
      if (i + 1 < L.length) {
        const b = L[i + 1];
        if (a[0] === r && b[0] === r + 1 && a[1] === b[1]) out.push([r + 1, a[1]], [r + 2, a[1]]);
        else if (a[0] === r + 1 && b[0] === r && a[1] === b[1]) out.push([r + 2, a[1]], [r + 1, a[1]]);
      }
    }
    return out;
  }

  function edgeAt(L, a, b) {
    for (let i = 0; i + 1 < L.length; i++) if (eq(L[i], a) && eq(L[i + 1], b)) return i;
    return -1;
  }

  function splice2(P, Q, a, b, X) {
    let i = edgeAt(P, a, b);
    if (i >= 0) return [P.slice(0, i + 1).concat(X, P.slice(i + 1)), Q];
    i = edgeAt(Q, a, b);
    if (i >= 0) return [P, Q.slice(0, i + 1).concat(X, Q.slice(i + 1))];
    return [P, Q];
  }

  function absorb2(r, y, y2, P, Q) {
    const u = [r + 1, y2], v = [r + 2, y2];
    if (edgeAt(P, u, v) >= 0 || edgeAt(Q, u, v) >= 0) return splice2(P, Q, u, v, [[r + 1, y], [r + 2, y]]);
    return splice2(P, Q, v, u, [[r + 2, y], [r + 1, y]]);
  }

  function flip2(r, y, P, Q) {
    const u = [r, y], v = [r, y + 1];
    if (edgeAt(P, u, v) >= 0 || edgeAt(Q, u, v) >= 0)
      return splice2(P, Q, u, v, [[r + 1, y], [r + 2, y], [r + 2, y + 1], [r + 1, y + 1]]);
    return splice2(P, Q, v, u, [[r + 1, y + 1], [r + 2, y + 1], [r + 2, y], [r + 1, y]]);
  }

  function sweepLeft2(r, n, U, P, Q) {
    U = new Set(U);
    while (n > 0) {
      const L = n - 1;
      if (U.has(L)) { [P, Q] = absorb2(r, L, L + 1, P, Q); U.delete(L); }
      n = L;
    }
    return [P, Q];
  }

  function sweepRight2(r, h, n, R, U, P, Q) {
    U = new Set(U);
    while (n > 0) {
      if (U.has(R + 1)) { [P, Q] = absorb2(r, R + 1, R, P, Q); U.delete(R + 1); }
      else if (!(R + 1 < h)) return [P, Q];
      n--; R++;
    }
    return [P, Q];
  }

  function bandExt2(I, r, p, q) {
    const h = I.C;
    const cross = new Uint8Array(h + 1), vert = new Uint8Array(h + 1);
    for (const L of [p, q]) {
      for (let i = 0; i + 1 < L.length; i++) {
        const a = L[i], b = L[i + 1];
        if (a[1] === b[1] && ((a[0] === r && b[0] === r + 1) || (a[0] === r + 1 && b[0] === r))) cross[a[1]] = 1;
        else if (a[0] === r && b[0] === r && Math.abs(a[1] - b[1]) === 1) vert[Math.max(a[1], b[1])] = 1;
      }
    }
    const U0 = [];
    for (let y = 0; y < h; y++) if (!cross[y]) U0.push(y);
    const P0 = stretch2(r, p), Q0 = stretch2(r, q);
    let R = -1, A = false;
    for (let R0 = 0; R0 <= h; R0++) {
      const a = (R0 === 0 || cross[R0 - 1] === 1) && (R0 === h || cross[R0] === 1);
      const b = R0 >= 1 && R0 < h && !cross[R0 - 1] && !cross[R0] && vert[R0] === 1;
      if (a || b) { R = R0; A = a; break; }
    }
    if (R < 0) return [P0, Q0];
    if (A) {
      if (R === 0) return sweepRight2(r, h, h, 0, U0, P0, Q0);
      if (R === h) return sweepLeft2(r, R - 1, U0, P0, Q0);
      const [P1, Q1] = sweepLeft2(r, R - 1, U0, P0, Q0);
      return sweepRight2(r, h, h - R, R, U0.filter((y) => R - 1 < y), P1, Q1);
    }
    const U1 = U0.filter((y) => y !== R - 1 && y !== R);
    const [P1, Q1] = flip2(r, R - 1, P0, Q0);
    const [P2, Q2] = sweepLeft2(r, R - 1, U1, P1, Q1);
    return sweepRight2(r, h, h - R, R, U1.filter((y) => R - 1 < y), P2, Q2);
  }

  function liftE2(I, d, p, q) {
    const J = deleteAt(I, d);
    if (d + 3 <= I.R && freeLine(I, d + 2)) return bandExt2(J, d, p, q);
    return bandExt2(J, d - 1, p, q);
  }

  /** Two-line reductions as `solveRec2`: [leaf, steps], steps [P, d, tr] as in reduce2.py `plan2`. */
  function plan2(I) {
    const steps = [];
    while (I.R > 10 && I.C > 10) {
      let d = findRed2(I);
      if (d >= 0) { steps.push([I, d, false]); I = deleteAt(I, d); continue; }
      const T = transposeI(I);
      d = findRed2(T);
      if (d >= 0) { steps.push([T, d, true]); I = deleteAt(T, d); continue; }
      break;
    }
    return [I, steps];
  }

  function liftAll2(steps, p, q) {
    for (let i = steps.length - 1; i >= 0; i--) {
      const [P, d, tr] = steps[i];
      [p, q] = liftE2(P, d, p, q);
      if (tr) { p = swapPath(p); q = swapPath(q); }
    }
    return [p, q];
  }

  // ----------------------------------------------------------------- look ----------
  // Irreducible leaves by certificate lookup: the Lean leaf solver `lookJ tabAll`. Same
  // definitions, iteration orders and choices as lib/python/zzn/look.py (see its docstring for
  // the Lean sources of each function). Lean's cell (x, y) on a w x h grid is [r, c] on an R x C
  // grid: x = r, w = R, y = c, h = C. A symmetry is an array of six bools [tr, rx, ry, r0, r1, sw].
  // A template is in the exported form: 0 for a leaf, [vert, a, o, kinds, L, R] for a cut. An
  // instantiated tree is null for a leaf and [vert, pos, kinds, L, R] for a cut, with kinds
  // ["stay", s], ["cross", s, y], ["exc", s, y, z]. A piece is [ox, oy, pw, ph, segs]; a path
  // segment is [a, b, path].
  //
  // The table (lib/data/look.json.gz, format in lib/tools/export_look.py) is read on first use in
  // Node; in a browser the page supplies it with setLookData. Stored path codes have up to 1352
  // bits, so the JSON text is parsed with the long integers kept as strings, decoded with BigInt.
  // All other values are small: keyR < 2^20 while coordinates are < 32 (sides 11-16), and key2 <
  // 2^53 while coordinates are < 2^17.
  const look = (() => {
    const sub = (a, b) => (a > b ? a - b : 0);
    const rev = (l) => l.slice().reverse();
    let DATA = null;

    // Quote the integers of 16 or more digits (the stored path codes), then parse.
    //
    function parseText(text) {
      return JSON.parse(text.replace(/([[,:]\s*)(-?\d{16,})(?=\s*[\],}])/g, '$1"$2"'));
    }

    function prepare(d) {
      if (typeof d === "string") d = parseText(d);
      if (!d || d.format !== "zzn-look-1") throw new Error("zzn: unknown look data format");
      const boxes = new Map(), rows = new Map();
      for (const k of Object.keys(d.boxes)) {
        const sl = d.boxes[k];
        const first = new Map();
        sl.forEach((s, i) => {
          const rk = s[0].join(",");
          if (!first.has(rk)) first.set(rk, i);
          for (const e of s[2]) {
            for (const c of [e[2], e[4]]) {
              if (typeof c === "number" && !Number.isSafeInteger(c)) {
                throw new Error("zzn: look data has a stored path code above 2^53 parsed as a number " +
                  "(precision lost); pass the JSON text to setLookData instead");
              }
            }
          }
        });
        boxes.set(k, sl);
        rows.set(k, first);
      }
      const prime = d.prime.map(([w, h, es]) => [w, h, es.map((e) => {
        const p = [];
        for (let i = 0; i < e[4].length; i += 2) p.push([e[4][i], e[4][i + 1]]);
        return [[e[0], e[1]], [e[2], e[3]], p];
      })]);
      return { templates: d.templates, boxes, prime, rows };
    }

    function setLookData(d) { DATA = prepare(d); }

    function data() {
      if (DATA) return DATA;
      if (typeof require !== "function" || typeof process === "undefined") {
        throw new Error("zzn: the lookup table is not loaded; call zzn.setLookData(text or object) " +
          "with the contents of lib/data/look.json.gz (gunzipped) first");
      }
      const env = process.env && process.env.ZZN_LOOK_DATA;
      const file = env || require("path").join(__dirname, "..", "data", "look.json.gz");
      const buf = require("zlib").gunzipSync(require("fs").readFileSync(file));
      DATA = prepare(buf.toString("utf8"));
      return DATA;
    }

    // --- symmetries ---
    const swp = (v) => [v[1], v[0]];
    const transpose = (I) => inst(I.C, I.R, swp(I.s0), swp(I.t0), swp(I.s1), swp(I.t1));
    const reflX = (w, v) => [sub(sub(w, 1), v[0]), v[1]];
    function reflectX(I) {
      const f = (v) => reflX(I.R, v);
      return inst(I.R, I.C, f(I.s0), f(I.t0), f(I.s1), f(I.t1));
    }
    const reflectY = (I) => transpose(reflectX(transpose(I)));
    const rev0 = (I) => inst(I.R, I.C, I.t0, I.s0, I.s1, I.t1);
    const rev1 = (I) => inst(I.R, I.C, I.s0, I.t0, I.t1, I.s1);
    const swapColors = (I) => inst(I.R, I.C, I.s1, I.t1, I.s0, I.t0);

    // `allSym` order: bits 32 tr, 16 rx, 8 ry, 4 r0, 2 r1, 1 sw.
    //
    const symOfInt = (k) => [0, 1, 2, 3, 4, 5].map((i) => ((k >> (5 - i)) & 1) === 1);
    const SYM_ID = symOfInt(0);
    const ALL_SYM = [];
    for (let k = 0; k < 64; k++) ALL_SYM.push(symOfInt(k));
    const G32 = ALL_SYM.filter((s) => !s[0]);
    const gbox = (w, h) => (w === h ? ALL_SYM : G32);

    function symGeo(sigma, I) {
      const I1 = sigma[0] ? transpose(I) : I;
      const I2 = sigma[1] ? reflectX(I1) : I1;
      return sigma[2] ? reflectY(I2) : I2;
    }
    function symLab(sigma, I) {
      const I3 = sigma[3] ? rev0(I) : I;
      const I4 = sigma[4] ? rev1(I3) : I3;
      return sigma[5] ? swapColors(I4) : I4;
    }
    const applySym = (sigma, I) => symLab(sigma, symGeo(sigma, I));

    function unLab(sigma, s) {
      const s1 = sigma[5] ? [s[1], s[0]] : s;
      const s2 = sigma[4] ? [s1[0], rev(s1[1])] : s1;
      return sigma[3] ? [rev(s2[0]), s2[1]] : s2;
    }
    const unRy = (hh, p) => p.map((v) => swp(reflX(hh, swp(v))));
    function unGeo(sigma, J, s) {
      const I1 = sigma[0] ? transpose(J) : J;
      const I2 = sigma[1] ? reflectX(I1) : I1;
      const s4 = sigma[2] ? [unRy(I2.C, s[0]), unRy(I2.C, s[1])] : s;
      const s5 = sigma[1] ? [s4[0].map((v) => reflX(I1.R, v)), s4[1].map((v) => reflX(I1.R, v))] : s4;
      return sigma[0] ? [s5[0].map(swp), s5[1].map(swp)] : s5;
    }
    const unSym = (sigma, J, s) => unGeo(sigma, J, unLab(sigma, s));

    // --- canonical form ---
    const rowsOf = (I) => [I.s0[0], I.t0[0], I.s1[0], I.t1[0]];
    const colsOf = (I) => [I.s0[1], I.t0[1], I.s1[1], I.t1[1]];
    const keyR = (x) => ((x[0] * 32 + x[1]) * 32 + x[2]) * 32 + x[3];
    const key2 = (K) => keyR(rowsOf(K)) * 1048576 + keyR(colsOf(K));
    const idx = (w, x) => ((x[0] * w + x[1]) * w + x[2]) * w + x[3];

    // `argminS`: the first element of least f; the identity on [].
    //
    function argminS(f, syms) {
      if (syms.length === 0) return SYM_ID;
      let b = syms[0], fb = f(b);
      for (let i = 1; i < syms.length; i++) {
        const fc = f(syms[i]);
        if (fc < fb) { b = syms[i]; fb = fc; }
      }
      return b;
    }
    const canonSym = (J) => argminS((s) => key2(applySym(s, J)), gbox(J.R, J.C));

    // --- templates and the cut-tree checker ---
    const offN = (a, o) => (o >= 0 ? a + o : sub(a, -o));
    const anchors = (e, n, a) => (a <= 3 ? e[a] : a === 4 ? 0 : n);
    const posN = (e, n, p) => offN(anchors(e, n, p[0]), p[1]);
    function instK(f, k) {
      if (k.length === 1) return ["stay", !!k[0]];
      if (k.length === 3) return ["cross", !!k[0], f([k[1], k[2]])];
      return ["exc", !!k[0], f([k[1], k[2]]), f([k[3], k[4]])];
    }
    function instT(fR, fC, T) {
      if (T === 0) return null;
      const vert = !!T[0], a = T[1], o = T[2], ks = T[3];
      const pos = vert ? fC([a, o]) : fR([a, o]);
      const g = vert ? fR : fC;
      return [vert, pos, ks.map((k) => instK(g, k)), instT(fR, fC, T[4]), instT(fR, fC, T[5])];
    }
    function instOf(T, I) {
      const er = rowsOf(I), ec = colsOf(I);
      return instT((p) => posN(er, I.R, p), (p) => posN(ec, I.C, p), T);
    }

    function cutc(vert, pos, s, y) {
      const x = s ? pos : sub(pos, 1);
      return vert ? [y, x] : [x, y];
    }
    const put = (s, e, LR) => (s ? [LR[0], LR[1].concat([e])] : [LR[0].concat([e]), LR[1]]);

    function split(vert, pos, ks, ss, acc) {
      if (ks.length !== ss.length) return null;
      for (let i = 0; i < ks.length; i++) {
        const k = ks[i], a = ss[i][0], b = ss[i][1], s = k[1];
        if (k[0] === "stay") acc = put(s, [a, b], acc);
        else if (k[0] === "cross") {
          const y = k[2];
          acc = put(!s, [cutc(vert, pos, !s, y), b], put(s, [a, cutc(vert, pos, s, y)], acc));
        } else {
          const y = k[2], z = k[3];
          acc = put(!s, [cutc(vert, pos, !s, y), cutc(vert, pos, !s, z)],
            put(s, [cutc(vert, pos, s, z), b], put(s, [a, cutc(vert, pos, s, y)], acc)));
        }
      }
      return acc;
    }

    function pieceLo(P, vert, pos, L) {
      const [ox, oy, pw, ph] = P;
      return vert ? [ox, oy, pw, sub(pos, oy), L] : [ox, oy, sub(pos, ox), ph, L];
    }
    function pieceHi(P, vert, pos, R) {
      const [ox, oy, pw, ph] = P;
      return vert ? [ox, pos, pw, sub(oy + ph, pos), R] : [pos, oy, sub(ox + pw, pos), ph, R];
    }
    function inside(vert, pos, P) {
      const [ox, oy, pw, ph] = P;
      return vert ? oy < pos && pos < oy + ph : ox < pos && pos < ox + pw;
    }
    function regionB(P, v) {
      const [ox, oy, pw, ph] = P;
      return ox <= v[0] && v[0] < ox + pw && oy <= v[1] && v[1] < oy + ph;
    }

    // `Lane.accB`: IPS acceptability, as written in Lean.
    //
    function accB(w, h, s, t) {
      const ps = (s[0] + s[1]) % 2 === 1, pt = (t[0] + t[1]) % 2 === 1;
      const ow = w % 2 === 1, oh = h % 2 === 1;
      const cc = ow && oh ? !ps && !pt : ps !== pt;
      const w1 = sub(w, 1), h1 = sub(h, 1);
      const corner = (v) => (v[0] === 0 || v[0] === w1) && (v[1] === 0 || v[1] === h1);
      const isW1 = w === 1;
      const fx = isW1 ? 0 : w1, fy = isW1 ? h1 : 0;
      const f1 = !((s[0] === 0 && s[1] === 0 && t[0] === fx && t[1] === fy) ||
        (s[0] === fx && s[1] === fy && t[0] === 0 && t[1] === 0));
      const f2 = !corner(s) && !corner(t) && ((w === 2 && s[1] === t[1]) || (h === 2 && s[0] === t[0]));
      const isW3 = w === 3;
      const oppOdd = isW3 ? oh : ow;
      const c0 = isW3 ? s[1] : s[0], c1 = isW3 ? t[1] : t[0], oc = isW3 ? s[0] : s[1];
      const gr = c1 < c0;
      const dist = gr ? sub(c0, c1) : sub(c1, c0);
      const dsat = oc === 1 ? 0 < dist : 1 < dist;
      const f3 = !oppOdd && ps !== pt && dsat && ((gr && !ps) || (!gr && ps));
      let forb;
      if (w === 1 || h === 1) forb = f1;
      else if (w === 2 || h === 2) forb = f2;
      else if (w === 3 || h === 3) forb = f3;
      else forb = false;
      return cc && !forb;
    }

    function leafOk(P) {
      const [ox, oy, pw, ph, segs] = P;
      if (segs.length !== 1) return false;
      const [a, b] = segs[0];
      if (eq(a, b)) return pw === 1 && ph === 1 && a[0] === ox && a[1] === oy;
      return regionB(P, a) && regionB(P, b) &&
        accB(pw, ph, [sub(a[0], ox), sub(a[1], oy)], [sub(b[0], ox), sub(b[1], oy)]);
    }

    function check(T, P) {
      if (T === null) return leafOk(P);
      const [vert, pos, ks, left, right] = T;
      if (!inside(vert, pos, P)) return false;
      const sp = split(vert, pos, ks, P[4], [[], []]);
      if (sp === null) return false;
      return check(left, pieceLo(P, vert, pos, sp[0])) && check(right, pieceHi(P, vert, pos, sp[1]));
    }

    const rootPiece = (I) => [0, 0, I.R, I.C, [[I.s0, I.t0], [I.s1, I.t1]]];
    const tcheck = (T, I) => check(instOf(T, I), rootPiece(I));

    // --- building the solution of a checked template ---

    // `joinL`: join the segments a -> u and v -> b. `List.erase` removes the first element
    // equal to x, which is x itself (the first with its ends); likewise for y in the rest.
    //
    function joinL(a, u, v, b, ps) {
      const i = ps.findIndex((x) => eq(x[0], a) && eq(x[1], u));
      if (i < 0) return ps;
      const x = ps[i];
      const rest = ps.slice(0, i).concat(ps.slice(i + 1));
      const j = rest.findIndex((y) => eq(y[0], v) && eq(y[1], b));
      if (j < 0) return ps;
      const y = rest[j];
      return [[a, b, x[2].concat(y[2])]].concat(rest.slice(0, j), rest.slice(j + 1));
    }

    // `unsplit`: join the segments across a cut, the last pair first (ks and ss from index i).
    //
    function unsplit(vert, pos, ks, ss, i, acc, ps) {
      if (i >= ks.length || i >= ss.length) return ps;
      const k = ks[i], a = ss[i][0], b = ss[i][1], s = k[1];
      if (k[0] === "stay") return unsplit(vert, pos, ks, ss, i + 1, put(s, [a, b], acc), ps);
      if (k[0] === "cross") {
        const y = k[2];
        const acc2 = put(!s, [cutc(vert, pos, !s, y), b], put(s, [a, cutc(vert, pos, s, y)], acc));
        return joinL(a, cutc(vert, pos, s, y), cutc(vert, pos, !s, y), b,
          unsplit(vert, pos, ks, ss, i + 1, acc2, ps));
      }
      const y = k[2], z = k[3];
      const acc2 = put(!s, [cutc(vert, pos, !s, y), cutc(vert, pos, !s, z)],
        put(s, [cutc(vert, pos, s, z), b], put(s, [a, cutc(vert, pos, s, y)], acc)));
      const inner = joinL(a, cutc(vert, pos, s, y), cutc(vert, pos, !s, y), cutc(vert, pos, !s, z),
        unsplit(vert, pos, ks, ss, i + 1, acc2, ps));
      return joinL(a, cutc(vert, pos, !s, z), cutc(vert, pos, s, z), b, inner);
    }

    function leafP(P) {
      const [ox, oy, pw, ph, segs] = P;
      if (segs.length !== 1) return [];
      const [a, b] = segs[0];
      if (eq(a, b)) return [[a, a, [a]]];
      const p = ipsP(pw + ph, pw, ph, [sub(a[0], ox), sub(a[1], oy)], [sub(b[0], ox), sub(b[1], oy)]);
      return [[a, b, p.map((v) => [v[0] + ox, v[1] + oy])]];
    }

    function buildT(T, P) {
      if (T === null) return leafP(P);
      const [vert, pos, ks, left, right] = T;
      const sp = split(vert, pos, ks, P[4], [[], []]);
      if (sp === null) return [];
      return unsplit(vert, pos, ks, P[4], 0, [[], []],
        buildT(left, pieceLo(P, vert, pos, sp[0])).concat(buildT(right, pieceHi(P, vert, pos, sp[1]))));
    }

    function solOf(I, ps) {
      const x = ps.find((e) => eq(e[0], I.s0) && eq(e[1], I.t0));
      const y = ps.find((e) => eq(e[0], I.s1) && eq(e[1], I.t1));
      return [x ? x[2] : [], y ? y[2] : []];
    }
    const tsol = (T, I) => solOf(I, buildT(instOf(T, I), rootPiece(I)));

    // --- the constructive IPS path ---
    function colSeg(c, lo, k) {
      const out = [];
      for (let j = k; j >= 0; j--) out.push([c, lo + j]);
      return out;
    }
    const rightDetour = (w, h, y) =>
      colSeg(w, 0, y).concat(rev(colSeg(w + 1, 0, sub(h, 1))), colSeg(w, y + 1, sub(sub(h, 1), y + 1)));

    function colEdge(X, l) {
      for (let i = 0; i < l.length - 1; i++) {
        if (l[i][0] === X && l[i + 1][0] === X) return [l.slice(0, i), l[i], l[i + 1], l.slice(i + 2)];
      }
      return null;
    }

    function stripRightP(width, height, p) {
      const ce = colEdge(sub(width, 3), p);
      if (ce === null) return p;
      const [l1, a, b, l2] = ce;
      if (b[1] === a[1] + 1) return l1.concat([a], rightDetour(sub(width, 2), height, a[1]), [b], l2);
      return rev(rev(l2).concat([b], rightDetour(sub(width, 2), height, b[1]), [a], rev(l1)));
    }

    function stripLeftP(width, height, p) {
      const q = stripRightP(width, height, p.map((v) => reflX(sub(width, 2), v)));
      return q.map((v) => reflX(width, v));
    }

    const notPrime = (w, h) =>
      !((w <= 3 && h <= 3) || (w === 4 && h === 4) || (w === 4 && h === 5) || (w === 5 && h === 4));

    function rChoice(sx, sy, h) {
      if ((sx + sy) % 2 === 0) return 0;
      if (sx === 0 && sy === 1 && 1 < sub(h, 1)) return 3;
      return 1;
    }

    function primeLookup(w, h, s, t) {
      const e = data().prime.find((e) => e[0] === w && e[1] === h);
      if (!e) return [];
      const x = e[2].find((x) => eq(x[0], s) && eq(x[1], t));
      return x ? x[2].map((v) => [v[0], v[1]]) : [];
    }

    function normP(f, w, h, s, t) {
      if (notPrime(w, h)) {
        if (2 <= s[0]) return stripLeftP(w, h, f(sub(w, 2), h, [sub(s[0], 2), s[1]], [sub(t[0], 2), t[1]]));
        if (t[0] + 2 < w) return stripRightP(w, h, f(sub(w, 2), h, s, t));
        const r = rChoice(s[0], s[1], h);
        return f(2, h, s, [1, r]).concat(f(sub(w, 2), h, [0, r], [sub(t[0], 2), t[1]]).map((v) => [v[0] + 2, v[1]]));
      }
      return primeLookup(w, h, s, t);
    }

    function stepP(f, w, h, s, t) {
      if (h <= w) return s[0] <= t[0] ? normP(f, w, h, s, t) : rev(normP(f, w, h, t, s));
      const p = s[1] <= t[1] ? normP(f, h, w, swp(s), swp(t)) : rev(normP(f, h, w, swp(t), swp(s)));
      return p.map(swp);
    }

    function ipsP(n, w, h, s, t) {
      if (n === 0) return [];
      return stepP((w2, h2, s2, t2) => ipsP(n - 1, w2, h2, s2, t2), w, h, s, t);
    }

    // --- stored paths ---

    // `decPath`: byte k of code is the cell 16 * x + y.
    //
    function decPath(n, code) {
      let c = BigInt(code);
      const out = [];
      for (let k = 0; k < n; k++) {
        const b = Number(c & 255n);
        c >>= 8n;
        out.push([b >> 4, b & 15]);
      }
      return out;
    }

    function chainAdjacent(p) {
      for (let i = 0; i + 1 < p.length; i++) {
        if (Math.abs(p[i][0] - p[i + 1][0]) + Math.abs(p[i][1] - p[i + 1][1]) !== 1) return false;
      }
      return true;
    }

    function maskOk(w, h, vs) {
      const seen = new Set();
      for (const v of vs) {
        if (!(v[0] < w && v[1] < h)) return false;
        const k = v[0] * h + v[1];
        if (seen.has(k)) return false;
        seen.add(k);
      }
      return true;
    }

    const solF = (I, p, q) =>
      p.length > 0 && eq(p[0], I.s0) && eq(p[p.length - 1], I.t0) && chainAdjacent(p) &&
      q.length > 0 && eq(q[0], I.s1) && eq(q[q.length - 1], I.t1) && chainAdjacent(q) &&
      maskOk(I.R, I.C, p.concat(q)) && p.length + q.length === I.R * I.C;

    // --- the lookup ---
    const inBox = (w, h) => 11 <= w && w <= h && h <= 16;
    const tabAll = (w, h) => (inBox(w, h) ? data().boxes.get(w + "x" + h) : []);

    // `entryP`: solve K from the slice d = [rows, pairs, sols]: [[p, q], how] with how
    // ["pair", i] or ["sol", i], or null.
    //
    function entryP(K, d) {
      const pairs = d[1], sols = d[2];
      for (let i = 0; i < pairs.length; i += 2) {
        const T = data().templates[pairs[i]], sigma = symOfInt(pairs[i + 1]);
        const J = applySym(sigma, K);
        if (tcheck(T, J)) return [unSym(sigma, K, tsol(T, J)), ["pair", i / 2]];
      }
      const lane = idx(K.C, colsOf(K));
      for (let i = 0; i < sols.length; i++) {
        const e = sols[i];
        if (e[0] === lane) {
          const p = decPath(e[1], e[2]), q = decPath(e[3], e[4]);
          if (solF(K, p, q)) return [[p, q], ["sol", i]];
        }
      }
      return null;
    }

    function lookK(K, trace) {
      let i;
      if (inBox(K.R, K.C)) i = data().rows.get(K.R + "x" + K.C).get(rowsOf(K).join(","));
      if (i === undefined) return null;
      const r = entryP(K, tabAll(K.R, K.C)[i]);
      if (r === null) return null;
      if (trace) { trace.slice = i; trace.entry = r[1]; }
      return r[0];
    }

    function lookLe(J, trace) {
      const sigma = canonSym(J);
      if (trace) trace.sym = sigma;
      const s = lookK(applySym(sigma, J), trace);
      return s === null ? null : unSym(sigma, J, s);
    }

    // `lookJ tabAll`: a solution [p, q] of I, or null. `trace` (an object), if given, receives
    // the chosen symmetry, slice index and entry. The cells are fresh arrays.
    //
    function lookJ(I, trace) {
      const s = I.R <= I.C ? lookLe(I, trace) : lookLe(transpose(I), trace);
      if (s === null) return null;
      const f = I.R <= I.C ? (v) => [v[0], v[1]] : swp;
      return [s[0].map(f), s[1].map(f)];
    }

    return { lookJ, setLookData, data, entryP, decPath, solF };
  })();


  /** Step 3 of the solver (see solver.py): block deletion on the whole instance, then the rest. */
  function solveTop(S, I) {
    if (Math.min(I.R, I.C) <= THIN) return S.thin(I);
    const f = firesI(I);
    if (f) { S.log("fires", I, f); return null; }
    const [leaf, steps] = blkPlan(I);
    let tr = false, cur = I;
    for (const [b, J, t] of steps) {
      tr = tr !== t;
      S.log("block", cur, tr ? 1 : 0, b);
      cur = tr ? transposeI(J) : J;
    }
    const [leaf2, steps2] = plan2(leaf);
    for (const [P, d, t] of steps2) {
      tr = tr !== t;
      S.log("reduce", cur, tr ? 1 : 0, d);
      const J = deleteAt(P, d);
      cur = tr ? transposeI(J) : J;
    }
    const sol = leafL(S, leaf2);
    if (!sol) throw new Error("internal error: leaf of a passing instance unsolvable");
    const [p, q] = liftAll2(steps2, sol[0], sol[1]);
    return blkLiftAll(steps, p, q);
  }

  /** `leafL`: the plug DP when a side is at most 10, else the certificate lookup. */
  function leafL(S, L) {
    if (Math.min(L.R, L.C) <= THIN) return S.thin(L);
    S.log("leaf", L);
    return look.lookJ(L);
  }

  /** A solution [pathA, pathB], or null if unsolvable. `trace` (an array) collects the steps. */
  function solve(I, trace) {
    I = checkInst(I);
    const sol = solveTop(new Solver(trace || null), I);
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
    checkSolution, render, wellFormed, setLookData: look.setLookData, version: "1.0.0",
    optimized: { decide: decideOptimized, solve: solveOptimized, solvePaths: solvePathsOptimized },
  };
});

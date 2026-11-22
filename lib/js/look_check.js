#!/usr/bin/env node
// SPDX-License-Identifier: CC0-1.0
// To the extent possible under law, the author has waived all copyright and related or
// neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

/*
 * Compare the JavaScript leaf lookup with Python's look_j on the records of js/look_dump.py:
 *   python3 js/look_dump.py 50 1 /tmp/look.json --lanes && node js/look_check.js /tmp/look.json
 * The internal `look` object of zzn.js is reached by compiling a copy of the source that also
 * exports it; the public API is unchanged. Exit status 1 on any difference.
 */
"use strict";
const fs = require("fs");
const path = require("path");
const Module = require("module");

const file = path.join(__dirname, "zzn.js");
const anchor = "  return {\n    Instance: inst,";
const src = fs.readFileSync(file, "utf8");
if (!src.includes(anchor)) throw new Error("export anchor not found in zzn.js");
const m = new Module(file, module);
m.filename = file;
m.paths = Module._nodeModulePaths(__dirname);
m._compile(src.replace(anchor, "  return {\n    _look: look, Instance: inst,"), file);
const zzn = m.exports, look = zzn._look;

const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);
const symInt = (s) => s.reduce((k, b) => 2 * k + (b ? 1 : 0), 0);

let t0 = process.hrtime.bigint();
look.data();
const tLoad = Number(process.hrtime.bigint() - t0) / 1e6;

const recs = JSON.parse(fs.readFileSync(process.argv[2], "utf8"));
const count = {}, perBox = {};
let bad = 0, tLeaf = 0, nLeaf = 0, tLane = 0, nLane = 0;
for (const r of recs) {
  const [R, C, s0, t0_, s1, t1] = r.I;
  const I = zzn.Instance(R, C, s0, t0_, s1, t1);
  const tr = {};
  const a = process.hrtime.bigint();
  const s = look.lookJ(I, tr);
  const dt = Number(process.hrtime.bigint() - a) / 1e6;
  if (r.kind === "leaf") { tLeaf += dt; nLeaf++; } else { tLane += dt; nLane++; }
  let ok = same(s, r.sol) && (r.sym === null || symInt(tr.sym) === r.sym) &&
    (tr.slice === undefined ? null : tr.slice) === r.slice && same(tr.entry === undefined ? null : tr.entry, r.entry);
  if (ok && r.kind === "leaf" && !(s && zzn.checkSolution(I, s))) ok = false;
  if (ok && r.kind === "lane") {
    const d = look.data().boxes.get(r.box)[r.sliceIdx];
    if (!same(look.entryP(I, d), r.entryP)) ok = false;
  }
  const k = r.kind + (ok ? " same" : " DIFFERENT");
  count[k] = (count[k] || 0) + 1;
  if (r.kind === "leaf") {
    const b = R + "x" + C;
    perBox[b] = (perBox[b] || 0) + (ok ? 1 : 0);
  }
  if (!ok) { bad++; if (bad <= 5) console.log("DIFF", JSON.stringify(r.I), r.kind); }
}
const boxes = Object.keys(perBox);
console.log(`boxes ${boxes.length}, identical per box min ${Math.min(...boxes.map((b) => perBox[b]))}` +
  ` max ${Math.max(...boxes.map((b) => perBox[b]))}`);
console.log(JSON.stringify(count));
console.log(`data load ${tLoad.toFixed(0)} ms; mean lookJ: leaves ${(tLeaf / Math.max(nLeaf, 1)).toFixed(3)} ms` +
  ` (${nLeaf}), lanes ${(tLane / Math.max(nLane, 1)).toFixed(3)} ms (${nLane})`);
console.log(bad ? `FAILED ${bad}` : "ALL SAME");
process.exitCode = bad ? 1 : 0;

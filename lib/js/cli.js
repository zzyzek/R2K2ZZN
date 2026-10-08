#!/usr/bin/env node
// SPDX-License-Identifier: CC0-1.0
// To the extent possible under law, the author has waived all copyright and related or
// neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

/*
 * Command line: decide or solve instances.
 *   node cli.js R C s0r s0c t0r t0c s1r s1c t1r t1c [--decide] [--grid] [--trace] [--json] [--optimized]
 *   node cli.js [options] < instances.txt      (one instance per line)
 */
"use strict";
const zzn = require("./zzn.js");

const USAGE = "usage: node cli.js R C s0r s0c t0r t0c s1r s1c t1r t1c [--decide] [--grid] [--trace] [--json] [--optimized]\n" +
  "   or: node cli.js [options] < instances.txt\n";

function run(v, opts) {
  const I = zzn.Instance(v[0], v[1], [v[2], v[3]], [v[4], v[5]], [v[6], v[7]], [v[8], v[9]]);
  if (!zzn.wellFormed(I)) { process.stdout.write("error: endpoints must be four distinct cells inside the grid\n"); return 2; }
  const out = [];
  if (opts.has("--decide")) {
    const d = (opts.has("--optimized") ? zzn.optimized : zzn).decide(I);
    out.push(opts.has("--json") ? JSON.stringify({ solvable: d }) : d ? "solvable" : "unsolvable: " + zzn.explain(I));
    process.stdout.write(out.join("\n") + "\n");
    return 0;
  }
  const trace = opts.has("--trace") ? [] : null;
  const sol = (opts.has("--optimized") ? zzn.optimized : zzn).solve(I, trace);
  if (opts.has("--json")) {
    process.stdout.write(JSON.stringify({ solvable: !!sol, paths: sol }) + "\n");
    return 0;
  }
  if (!sol) out.push("unsolvable: " + zzn.explain(I));
  else {
    out.push("solvable");
    out.push("A: " + sol[0].map((x) => x.join(",")).join(" "));
    out.push("B: " + sol[1].map((x) => x.join(",")).join(" "));
  }
  if (trace) {
    for (const step of trace) {
      const [kind, J] = step, size = `${J.R}x${J.C}`;
      if (kind === "reduce") out.push(`  reduce ${size}: delete ${step[2] === 0 ? "rows" : "columns"} ${step[3]},${step[3] + 1}`);
      else if (kind === "move") {
        const [axis, k] = step[3];
        out.push(`  move ${size}: ${step[2]}, cut between ${axis === 0 ? "rows" : "columns"} ${k - 1} and ${k}`);
      } else if (kind === "same") {
        const [axis, k] = step[2];
        out.push(`  same ${size}: cut between ${axis === 0 ? "rows" : "columns"} ${k - 1} and ${k}`);
      } else out.push(`  ${kind} ${size}` + (step.length > 2 ? `: ${step[2]}` : ""));
    }
  }
  if (opts.has("--grid")) out.push(zzn.render(I, sol));
  process.stdout.write(out.join("\n") + "\n");
  return 0;
}

function main() {
  const args = process.argv.slice(2);
  const opts = new Set(args.filter((a) => a.startsWith("-")));
  const nums = args.filter((a) => !a.startsWith("-")).map(Number);
  if (opts.has("-h") || opts.has("--help")) { process.stdout.write(USAGE); return 0; }
  if (nums.length) {
    if (nums.length !== 10 || nums.some((x) => !Number.isInteger(x))) { process.stdout.write(USAGE); return 2; }
    return run(nums, opts);
  }
  const lines = require("fs").readFileSync(0, "utf8").split("\n");
  let rc = 0;
  for (const line of lines) {
    const v = line.trim().split(/\s+/).filter((x) => x).map(Number);
    if (v.length === 0) continue;
    if (v.length !== 10) { process.stdout.write("error: expected 10 integers\n"); rc = 2; continue; }
    rc = Math.max(rc, run(v, opts));
  }
  return rc;
}

process.exitCode = main();

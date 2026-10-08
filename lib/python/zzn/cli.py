# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Command line: decide or solve instances.

    zzn_cli.py R C s0r s0c t0r t0c s1r s1c t1r t1c [--decide] [--grid] [--trace] [--json] [--optimized]
    zzn_cli.py [options] < instances.txt        (one instance per line)
"""
import json
import sys

from .grid import Instance, well_formed, render
from .solver import decide, solve, explain
from . import optimized

USAGE = __doc__


def _run(nums, opts, out):
    inst = Instance(nums[0], nums[1], (nums[2], nums[3]), (nums[4], nums[5]),
                    (nums[6], nums[7]), (nums[8], nums[9]))
    if not well_formed(inst):
        out.write("error: endpoints must be four distinct cells inside the grid\n")
        return 2
    if "--decide" in opts:
        d = (optimized.decide if "--optimized" in opts else decide)(inst)
        if "--json" in opts:
            out.write(json.dumps({"solvable": d}) + "\n")
        else:
            out.write(("solvable" if d else "unsolvable: " + explain(inst)) + "\n")
        return 0
    trace = [] if "--trace" in opts else None
    sol = (optimized.solve if "--optimized" in opts else solve)(inst, trace)
    if "--json" in opts:
        out.write(json.dumps({"solvable": sol is not None,
                              "paths": None if sol is None else [list(map(list, p)) for p in sol]}) + "\n")
        return 0
    if sol is None:
        out.write("unsolvable: " + explain(inst) + "\n")
    else:
        out.write("solvable\n")
        for name, p in (("A", sol[0]), ("B", sol[1])):
            out.write(name + ": " + " ".join(f"{r},{c}" for r, c in p) + "\n")
    if trace:
        for step in trace:
            kind, I = step[0], step[1]
            size = f"{I.R}x{I.C}"
            if kind == "reduce":
                out.write(f"  reduce {size}: delete {'rows' if step[2] == 0 else 'columns'} {step[3]},{step[3] + 1}\n")
            elif kind == "move":
                axis, k = step[3]
                out.write(f"  move {size}: {step[2]}, cut between {'rows' if axis == 0 else 'columns'} {k - 1} and {k}\n")
            elif kind == "same":
                axis, k = step[2]
                out.write(f"  same {size}: cut between {'rows' if axis == 0 else 'columns'} {k - 1} and {k}\n")
            else:
                out.write(f"  {kind} {size}" + (f": {step[2]}" if len(step) > 2 else "") + "\n")
    if "--grid" in opts:
        out.write(render(inst, sol) + "\n")
    return 0


def main(argv=None, out=sys.stdout):
    argv = sys.argv[1:] if argv is None else argv
    opts = [a for a in argv if a.startswith("-")]
    nums = [a for a in argv if not a.startswith("-")]
    if "-h" in opts or "--help" in opts:
        out.write(USAGE)
        return 0
    try:
        if nums:
            vals = list(map(int, nums))
            if len(vals) != 10:
                raise ValueError
            return _run(vals, opts, out)
        rc = 0
        for line in sys.stdin:
            vals = line.split()
            if not vals:
                continue
            if len(vals) != 10:
                out.write("error: expected 10 integers\n")
                rc = 2
                continue
            rc = max(rc, _run(list(map(int, vals)), opts, out))
        return rc
    except ValueError:
        out.write(USAGE)
        return 2

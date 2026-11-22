# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Decide and solve two-colour Zig-Zag Numberlink on rectangles.

decide(inst) -> bool        solvable?  (plug DP if a side is <= 10, else the catalogue)
solve(inst)  -> (p0, p1)    a solution, or None if unsolvable
explain(inst) -> str        why it is unsolvable (catalogue entry), or how it was solved

`solve`:
  1. a side <= 10:         the plug DP algorithm (plugdp.py)
  2. catalogue fires:      unsolvable
  3. otherwise:            the Lean construction solveZ3 (leafL thinSolveW2 tabAll)
                           (proof/ZZN/Look/Main.lean, solveZ3L_main):
     a. delete blocks of 2k free lines (solveR; blocks.py), leaving sides <= 37;
     b. delete two lines at a time by RedX or RedB (solveRec2; reduce2.py), leaving both sides
        in 11-16;
     c. solve the leaf (leafL): the plug DP if a side is <= 10, else the certificate lookup
        lookJ tabAll (look.py);
     d. lift the solution back through the reductions and the blocks.
The library's plug DP stands in for Lean's thinSolveW2; starting from both sides >= 11 the leaf
always has both sides 11-16, so it is not reached there. Every solution is checked.
"""
from .grid import Instance, well_formed, check_solution
from .catalogue import fires
from . import plugdp, blocks, reduce2, look

THIN = 10


class SolverError(RuntimeError):
    pass


def _check(inst):
    if not isinstance(inst, Instance):
        inst = Instance(*inst)
    if not well_formed(inst):
        raise ValueError("instance must have four distinct endpoints inside the grid")
    return inst


def decide(inst):
    inst = _check(inst)
    if min(inst.R, inst.C) <= THIN:
        return plugdp.solvable_paths(inst.R, inst.C, [(inst.s0, 0), (inst.t0, 0), (inst.s1, 1), (inst.t1, 1)])
    return fires(inst.R, inst.C, inst.s0, inst.t0, inst.s1, inst.t1) is None


def solve(inst, trace=None):
    """A solution (path0, path1), or None if the instance is unsolvable. If `trace` is a list,
    the steps taken are appended to it as tuples (see `_Solver`)."""
    inst = _check(inst)
    sol = _Solver(trace).solve(inst)
    if sol is not None and not check_solution(inst, sol):
        raise SolverError("internal error: produced an invalid solution")
    return sol


def explain(inst):
    inst = _check(inst)
    if min(inst.R, inst.C) <= THIN:
        return "thin: decided by the plug DP"
    f = fires(inst.R, inst.C, inst.s0, inst.t0, inst.s1, inst.t1)
    return f"catalogue entry {f} fires" if f else "passes the catalogue"


class _Solver:
    """Steps recorded in the trace: ("thin", I), ("fires", I, entry), ("block", I, axis, blk)
    where blk is as in blocks.blk_x on that axis, ("reduce", I, axis, d) for lines d, d + 1, and
    ("leaf", L) for the lookup. Each I is in the orientation of the input; L is in the frame of the
    last step."""

    def __init__(self, trace=None):
        self.trace = trace

    def log(self, *step):
        if self.trace is not None:
            self.trace.append(step)

    def solve(self, I):
        if min(I.R, I.C) <= THIN:
            self.log("thin", I)
            return plugdp.solve_instance(I)
        f = fires(I.R, I.C, I.s0, I.t0, I.s1, I.t1)
        if f:
            self.log("fires", I, f)
            return None
        leaf, steps = blocks.plan(I)

        # Each trace entry is in the orientation of the input. After a transposed step the
        # recursion stays in the transposed frame (as in Lean), so tr tracks the frame.
        #
        tr, cur = False, I
        for b, J, t in steps:
            tr = tr != t
            self.log("block", cur, 1 if tr else 0, b)
            cur = J if not tr else blocks.transpose(J)
        leaf2, steps2 = reduce2.plan2(leaf)
        for P, d, t in steps2:
            tr = tr != t
            self.log("reduce", cur, 1 if tr else 0, d)
            J = reduce2.delete_at(P, d)
            cur = J if not tr else blocks.transpose(J)
        sol = self.leaf(leaf2)
        if sol is None:
            raise SolverError(f"internal error: leaf {leaf2} of a passing instance unsolvable")
        p, q = reduce2.lift_all2(steps2, list(sol[0]), list(sol[1]))
        return blocks.lift_all(steps, p, q)

    def leaf(self, L):
        """`leafL`: the plug DP when a side is at most 10, else the certificate lookup."""
        if min(L.R, L.C) <= THIN:
            self.log("thin", L)
            return plugdp.solve_instance(L)
        self.log("leaf", L)
        return look.look_j(L)

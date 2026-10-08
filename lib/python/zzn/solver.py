# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Decide and solve two-colour Zig-Zag Numberlink on rectangles.

decide(inst) -> bool        solvable?  (plug DP if a side is <= 10, else the catalogue)
solve(inst)  -> (p0, p1)    a solution, or None if unsolvable
explain(inst) -> str        why it is unsolvable (catalogue entry), or how it was solved

The constructive algorithm follows the proof (docs/ALGORITHM.md):
  1. a side <= 10:         plug DP
  2. catalogue fires:      unsolvable
  3. a reduction applies:  delete two empty lines, solve, band-extend the solution back
  4. same-colour split:    two Hamiltonian paths (IPS)
  5. otherwise:            sides <= 22; find a valid move, solve the pieces, glue
"""
from .grid import (Instance, well_formed, ends, GEOS, apply_geo, relabel, map_back, orient,
                   check_solution)
from .catalogue import fires
from . import plugdp, ips, lift

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


# --- reductions ---------------------------------------------------------------------------

def _coord(x, axis):
    return x[axis]


def find_reduction(inst):
    """(axis, d): delete lines d, d+1 on that axis (a strip, compression or interior
    compression). None if no reduction applies."""
    for axis in (0, 1):
        n = inst.R if axis == 0 else inst.C
        if n < 13:
            continue
        lines = [_coord(x, axis) for x in ends(inst)]
        free = lambda k: k not in lines
        below = lambda k: any(v < k for v in lines)
        above = lambda k: any(v > k for v in lines)
        if all(free(k) for k in range(4)):
            return axis, 0
        if all(free(k) for k in range(n - 4, n)):
            return axis, n - 2
        for lo in range(0, n - 9):
            if all(free(k) for k in range(lo, lo + 10)) and below(lo) and above(lo + 9):
                return axis, lo + 4
        for d in range(8, n - 9):
            if (free(d) and free(d + 1) and ((d >= 1 and free(d - 1)) or free(d + 2)) and
                    below(d) and above(d + 1)):
                return axis, d
    return None


def delete_lines(inst, axis, d):
    def f(x):
        v = x[axis]
        if v > d + 1:
            v -= 2
        return (v, x[1]) if axis == 0 else (x[0], v)
    R, C = (inst.R - 2, inst.C) if axis == 0 else (inst.R, inst.C - 2)
    return Instance(R, C, f(inst.s0), f(inst.t0), f(inst.s1), f(inst.t1))


# --- moves --------------------------------------------------------------------------------

def tw(w, h):
    """The thin width of a two-path piece (0 if not thin)."""
    return min(w, h) if (w <= THIN or h <= THIN) else 0


LABS = {
    0: [(False, False, False)],
    1: [(False, False, False), (False, False, True)],
    2: [(False, False, False), (True, False, False), (False, False, True), (False, True, True)],
    3: [(False, False, False), (True, False, False), (False, True, False), (True, True, False)],
    4: [(False, False, False), (False, False, True)],
}
TYPE_SYMS = [(t, g, lab) for t in range(5) for g in GEOS for lab in LABS[t]]


def _parity_ok(J):
    s = sum(1 if (x[0] + x[1]) % 2 == 0 else -1 for x in ends(J))
    return s == 2 * ((J.R * J.C) % 2)


def _sh(x, p):
    return (x[0] - p, x[1])


MOVE_NAMES = {0: "strip", 1: "2/2 same", 2: "1/3", 3: "2/2 cross", 4: "excursion"}


class _Solver:
    """Steps recorded in the trace: ("thin", I), ("fires", I, entry), ("reduce", I, axis, d),
    ("same", I), ("move", I, name, cut) where cut = (axis, p) in I's coordinates."""

    def __init__(self, trace=None):
        self.feas = {}
        self.trace = trace

    def log(self, *step):
        if self.trace is not None:
            self.trace.append(step)

    # a two-path piece is OK: thin and solvable, or not thin and passing
    def piece_ok(self, J):
        if not well_formed(J):
            return False
        if J.R <= THIN or J.C <= THIN:
            if not _parity_ok(J):
                return False
            if J not in self.feas:
                self.feas[J] = plugdp.solvable_paths(J.R, J.C, [(J.s0, 0), (J.t0, 0), (J.s1, 1), (J.t1, 1)])
            return self.feas[J]
        return fires(J.R, J.C, J.s0, J.t0, J.s1, J.t1) is None

    def piece_solve(self, J):
        sol = self.solve(J)
        if sol is None:
            raise SolverError(f"internal error: piece {J} unsolvable")
        return sol

    def solve(self, I):
        if min(I.R, I.C) <= THIN:
            self.log("thin", I)
            return plugdp.solve_instance(I)
        f = fires(I.R, I.C, I.s0, I.t0, I.s1, I.t1)
        if f:
            self.log("fires", I, f)
            return None
        red = find_reduction(I)
        if red:
            axis, d = red
            self.log("reduce", I, axis, d)
            Ir = delete_lines(I, axis, d)
            sol = self.solve(Ir)
            if sol is None:
                raise SolverError("internal error: reduced instance unsolvable")
            return orient(I, lift.extend(Ir.R, Ir.C, list(sol), axis, d))
        sol = self.same_split(I)
        if sol:
            return sol
        sol = self.move(I)
        if sol is None:
            raise SolverError(f"no valid move found for {I} (contradicts Theorem A)")
        return sol

    def same_split(self, I):
        for g in ((False, False, False), (True, False, False)):
            J0 = apply_geo(g, I)
            for J in (J0, relabel((False, False, True), J0)):
                for p in range(1, J.R):
                    if (J.s0[0] < p and J.t0[0] < p and J.s1[0] >= p and J.t1[0] >= p and
                            ips.acceptable(p, J.C, J.s0, J.t0) and
                            ips.acceptable(J.R - p, J.C, _sh(J.s1, p), _sh(J.t1, p))):
                        self.log("same", I, (1 if g[0] else 0, p))
                        a = ips.hamiltonian_path(p, J.C, J.s0, J.t0)
                        b = ips.hamiltonian_path(J.R - p, J.C, _sh(J.s1, p), _sh(J.t1, p))
                        return map_back(g, I, [a, [(r + p, c) for r, c in b]])
        return None

    def move(self, I):
        for m in range(THIN + 1):
            for t, g, lab in TYPE_SYMS:
                J = relabel(lab, apply_geo(g, I))
                mark = len(self.trace) if self.trace is not None else 0
                res = self.canon(t, m, J)
                if res is not None:
                    sol, p = res
                    if self.trace is not None:
                        self.trace.insert(mark, ("move", I, MOVE_NAMES[t], _cut_back(g, I, p)))
                    return map_back(g, I, sol)
        return None

    def canon(self, t, m, J):
        """A canonical move of type t (cut between rows p-1 and p) whose widest thin piece has
        width m; returns (glued solution of J in any labelling, p), or None."""
        R, C = J.R, J.C
        s0, t0, s1, t1 = J.s0, J.t0, J.s1, J.t1
        for p in range(1, R):
            if t == 0:  # strip: all endpoints above the cut, an empty even block below
                if (max(s0[0], t0[0], s1[0], t1[0]) < p and R - p >= 2 and ((R - p) * C) % 2 == 0
                        and C >= 5 and tw(p, C) == m):
                    L = Instance(p, C, s0, t0, s1, t1)
                    if self.piece_ok(L):
                        a, b = self.piece_solve(L)
                        return lift.add_block(p, C, [a, b], R - p), p
            elif t == 1:  # 2/2 same: each colour on its own side, two Hamiltonian paths
                if (m == 0 and s0[0] < p and t0[0] < p and s1[0] >= p and t1[0] >= p and
                        ips.acceptable(p, C, s0, t0) and ips.acceptable(R - p, C, _sh(s1, p), _sh(t1, p))):
                    a = ips.hamiltonian_path(p, C, s0, t0)
                    b = ips.hamiltonian_path(R - p, C, _sh(s1, p), _sh(t1, p))
                    return [a, [(r + p, c) for r, c in b]], p
            elif t == 2:  # 1/3: s0 alone above the cut
                if (s0[0] < p and t0[0] >= p and s1[0] >= p and t1[0] >= p and tw(R - p, C) == m):
                    for y in range(C):
                        if not ips.acceptable(p, C, s0, (p - 1, y)):
                            continue
                        Rr = Instance(R - p, C, (0, y), _sh(t0, p), _sh(s1, p), _sh(t1, p))
                        if self.piece_ok(Rr):
                            a = ips.hamiltonian_path(p, C, s0, (p - 1, y))
                            r0, r1 = self.piece_solve(Rr)
                            up = lambda path: [(r + p, c) for r, c in path]
                            return [a + up(r0), up(r1)], p
            elif t == 3:  # 2/2 cross: s0, s1 above; t0, t1 below
                if (s0[0] < p and s1[0] < p and t0[0] >= p and t1[0] >= p and
                        max(tw(p, C), tw(R - p, C)) == m):
                    for y0 in range(C):
                        for y1 in range(C):
                            L = Instance(p, C, s0, (p - 1, y0), s1, (p - 1, y1))
                            Rr = Instance(R - p, C, (0, y0), _sh(t0, p), (0, y1), _sh(t1, p))
                            first, second = (L, Rr) if p <= R - p else (Rr, L)
                            if self.piece_ok(first) and self.piece_ok(second):
                                l0, l1 = self.piece_solve(L)
                                r0, r1 = self.piece_solve(Rr)
                                up = lambda path: [(r + p, c) for r, c in path]
                                return [l0 + up(r0), l1 + up(r1)], p
            else:  # excursion: colour 0 above, crossing the cut twice; colour 1 below
                if (s0[0] < p and t0[0] < p and s1[0] >= p and t1[0] >= p and
                        max(tw(p, C), tw(R - p, C)) == m):
                    for ya in range(C):
                        for yb in range(C):
                            N = Instance(p, C, s0, (p - 1, ya), (p - 1, yb), t0)
                            F = Instance(R - p, C, _sh(s1, p), _sh(t1, p), (0, ya), (0, yb))
                            first, second = (N, F) if p <= R - p else (F, N)
                            if self.piece_ok(first) and self.piece_ok(second):
                                n0, n1 = self.piece_solve(N)
                                f0, f1 = self.piece_solve(F)
                                up = lambda path: [(r + p, c) for r, c in path]
                                return [n0 + up(f1) + n1, up(f0)], p
        return None


def _cut_back(g, I, p):
    """The cut between rows p-1 and p of apply_geo(g, I), in I's coordinates: (axis, k) is the
    line between lines k-1 and k on that axis."""
    tr, fr, fc = g
    R2 = I.C if tr else I.R
    k = R2 - p if fr else p
    return (1, k) if tr else (0, k)

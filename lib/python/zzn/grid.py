# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Instances, solutions, symmetries and the solution checker.

Conventions: a grid has R rows and C columns; a cell is (r, c) with 0 <= r < R, 0 <= c < C.
An instance has endpoints s0, t0 (colour 0) and s1, t1 (colour 1). A solution is a pair of
paths (lists of cells) s0 -> t0 and s1 -> t1, vertex-disjoint, covering every cell.
"""
from collections import namedtuple

Instance = namedtuple("Instance", "R C s0 t0 s1 t1")


def ends(inst):
    return [inst.s0, inst.t0, inst.s1, inst.t1]


def well_formed(inst):
    """Positive size, the four endpoints distinct and inside the grid."""
    if inst.R < 1 or inst.C < 1:
        return False
    e = ends(inst)
    if any(not (0 <= r < inst.R and 0 <= c < inst.C) for r, c in e):
        return False
    return len(set(e)) == 4


def adjacent(u, v):
    return abs(u[0] - v[0]) + abs(u[1] - v[1]) == 1


def check_path(R, C, s, t, p):
    if not p or p[0] != s or p[-1] != t or len(set(p)) != len(p):
        return False
    if any(not (0 <= r < R and 0 <= c < C) for r, c in p):
        return False
    return all(adjacent(p[i], p[i + 1]) for i in range(len(p) - 1))


def check_solution(inst, sol):
    """True when `sol` = (path0, path1) solves `inst`."""
    if sol is None:
        return False
    p, q = sol
    if not check_path(inst.R, inst.C, inst.s0, inst.t0, p):
        return False
    if not check_path(inst.R, inst.C, inst.s1, inst.t1, q):
        return False
    cells = set(p) | set(q)
    return len(cells) == len(p) + len(q) == inst.R * inst.C


# --- symmetries --------------------------------------------------------------------------
# A geometric symmetry is (tr, fr, fc): optionally transpose, then flip rows, then flip columns.

def geo_cell(g, R, C, x):
    tr, fr, fc = g
    r, c = x
    if tr:
        r, c, R, C = c, r, C, R
    if fr:
        r = R - 1 - r
    if fc:
        c = C - 1 - c
    return (r, c)


def geo_dims(g, R, C):
    return (C, R) if g[0] else (R, C)


def geo_inverse_cell(g, R, C, x):
    """Inverse of geo_cell: R, C are the dimensions of the ORIGINAL grid."""
    tr, fr, fc = g
    R2, C2 = geo_dims(g, R, C)
    r, c = x
    if fc:
        c = C2 - 1 - c
    if fr:
        r = R2 - 1 - r
    if tr:
        r, c = c, r
    return (r, c)


GEOS = [(tr, fr, fc) for tr in (False, True) for fr in (False, True) for fc in (False, True)]


def apply_geo(g, inst):
    R2, C2 = geo_dims(g, inst.R, inst.C)
    f = lambda x: geo_cell(g, inst.R, inst.C, x)
    return Instance(R2, C2, f(inst.s0), f(inst.t0), f(inst.s1), f(inst.t1))


def relabel(lab, inst):
    """Label symmetry (r0, r1, sw): reverse path 0, reverse path 1, then swap the colours."""
    r0, r1, sw = lab
    s0, t0, s1, t1 = inst.s0, inst.t0, inst.s1, inst.t1
    if r0:
        s0, t0 = t0, s0
    if r1:
        s1, t1 = t1, s1
    if sw:
        s0, t0, s1, t1 = s1, t1, s0, t0
    return Instance(inst.R, inst.C, s0, t0, s1, t1)


def orient(inst, paths):
    """Given two disjoint paths joining the endpoint pairs in some order and direction, return
    them as (s0 -> t0, s1 -> t1)."""
    out = [None, None]
    for p in paths:
        for col, (s, t) in enumerate(((inst.s0, inst.t0), (inst.s1, inst.t1))):
            if p[0] == s and p[-1] == t:
                out[col] = list(p)
            elif p[0] == t and p[-1] == s:
                out[col] = list(reversed(p))
    if out[0] is None or out[1] is None:
        raise ValueError("paths do not match the endpoints")
    return (out[0], out[1])


def map_back(g, inst, sol_image):
    """A solution of apply_geo(g, inst) (any labelling) -> a solution of inst."""
    f = lambda x: geo_inverse_cell(g, inst.R, inst.C, x)
    return orient(inst, [[f(x) for x in p] for p in sol_image])


def render(inst, sol=None):
    """ASCII picture: endpoints as A/B, path cells as a/b, empty as '.'."""
    g = [["." for _ in range(inst.C)] for _ in range(inst.R)]
    if sol:
        for (r, c) in sol[0]:
            g[r][c] = "a"
        for (r, c) in sol[1]:
            g[r][c] = "b"
    for (r, c) in (inst.s0, inst.t0):
        g[r][c] = "A"
    for (r, c) in (inst.s1, inst.t1):
        g[r][c] = "B"
    return "\n".join("".join(row) for row in g)

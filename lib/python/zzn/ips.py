# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Hamiltonian paths in rectangles (Itai, Papadimitriou, Szwarcfiter 1982).

`acceptable(R, C, s, t)` is the IPS criterion (as in `lean/GridHam/Forbidden.lean`): a
Hamiltonian s-t path exists in the R x C grid iff it holds. `hamiltonian_path(R, C, s, t)`
constructs one: small rectangles by the plug DP; otherwise peel two lines from an edge with three
endpoint-free lines
(when the rest is still acceptable) and splice them back, or split between s and t.
"""
from .plugdp import solve_paths
from . import lift


def _par(v):
    return (v[0] + v[1]) % 2


def color_compatible(R, C, s, t):
    if (R * C) % 2 == 1:
        return _par(s) == 0 and _par(t) == 0
    return _par(s) != _par(t)


def _is_corner(w, h, v):
    return v in ((0, 0), (w - 1, 0), (0, h - 1), (w - 1, h - 1))


def _forbidden(w, h, s, t):
    # the three forbidden cases of IPS, with w = R and h = C as in the Lean transcription
    if w == 1 or h == 1:
        isw = w == 1
        bound = h if isw else w
        far = (0, bound - 1) if isw else (bound - 1, 0)
        return not ((s == (0, 0) and t == far) or (s == far and t == (0, 0)))
    if w == 2 or h == 2:
        return (not _is_corner(w, h, s) and not _is_corner(w, h, t) and
                ((w == 2 and s[1] == t[1]) or (h == 2 and s[0] == t[0])))
    if w == 3 or h == 3:
        isw = w == 3
        opp = h if isw else w
        if not (opp % 2 == 0 and _par(s) != _par(t)):
            return False
        c0 = s[1] if isw else s[0]
        c1 = t[1] if isw else t[0]
        oc = s[0] if isw else s[1]
        greater = c1 < c0
        dist = c0 - c1 if greater else c1 - c0
        dist_ok = dist > 0 if oc == 1 else dist > 1
        return dist_ok and ((greater and _par(s) != 1) or (not greater and _par(s) != 0))
    return False


def acceptable(R, C, s, t):
    if s == t:
        return R * C == 1
    if not (0 <= s[0] < R and 0 <= s[1] < C and 0 <= t[0] < R and 0 <= t[1] < C):
        return False
    return color_compatible(R, C, s, t) and not _forbidden(R, C, s, t)


SMALL = 6


def hamiltonian_path(R, C, s, t):
    """A Hamiltonian path s -> t of the R x C grid, or None if there is none."""
    if not acceptable(R, C, s, t):
        return None
    if s == t:
        return [s]
    if min(R, C) <= SMALL:
        return solve_paths(R, C, [(s, 0), (t, 0)])[0]
    # peel two empty edge lines whose removal keeps the instance acceptable
    for side in ("top", "bottom", "left", "right"):
        if side == "top" and s[0] >= 3 and t[0] >= 3 and acceptable(R - 2, C, _sh(s, -2, 0), _sh(t, -2, 0)):
            p = hamiltonian_path(R - 2, C, _sh(s, -2, 0), _sh(t, -2, 0))
            return lift.insert_two_lines(R - 2, C, [p], axis=0, after=-1)[0]
        if side == "bottom" and s[0] < R - 3 and t[0] < R - 3 and acceptable(R - 2, C, s, t):
            p = hamiltonian_path(R - 2, C, s, t)
            return lift.insert_two_lines(R - 2, C, [p], axis=0, after=R - 3)[0]
        if side == "left" and s[1] >= 3 and t[1] >= 3 and acceptable(R, C - 2, _sh(s, 0, -2), _sh(t, 0, -2)):
            p = hamiltonian_path(R, C - 2, _sh(s, 0, -2), _sh(t, 0, -2))
            return lift.insert_two_lines(R, C - 2, [p], axis=1, after=-1)[0]
        if side == "right" and s[1] < C - 3 and t[1] < C - 3 and acceptable(R, C - 2, s, t):
            p = hamiltonian_path(R, C - 2, s, t)
            return lift.insert_two_lines(R, C - 2, [p], axis=1, after=C - 3)[0]
    # split between s and t (rows), with a crossing edge (p-1, y) - (p, y)
    a, b = (s, t) if s[0] <= t[0] else (t, s)
    for p in range(a[0] + 1, b[0] + 1):
        for y in range(C):
            u, v = (p - 1, y), (p, y)
            if acceptable(p, C, a, u) and acceptable(R - p, C, (0, y), (b[0] - p, b[1])):
                top = hamiltonian_path(p, C, a, u)
                bot = hamiltonian_path(R - p, C, (0, y), (b[0] - p, b[1]))
                path = top + [(r + p, c) for r, c in bot]
                return path if path[0] == s else list(reversed(path))
    # split between s and t (columns)
    a, b = (s, t) if s[1] <= t[1] else (t, s)
    for p in range(a[1] + 1, b[1] + 1):
        for x in range(R):
            u = (x, p - 1)
            if acceptable(R, p, a, u) and acceptable(R, C - p, (x, 0), (b[0], b[1] - p)):
                left = hamiltonian_path(R, p, a, u)
                rgt = hamiltonian_path(R, C - p, (x, 0), (b[0], b[1] - p))
                path = left + [(r, c + p) for r, c in rgt]
                return path if path[0] == s else list(reversed(path))
    # not expected for acceptable instances; fall back to the exact DP
    res = solve_paths(R, C, [(s, 0), (t, 0)])
    return None if res is None else res[0]


def _sh(v, dr, dc):
    return (v[0] + dr, v[1] + dc)

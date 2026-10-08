# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Optimized solving for thin instances: guess splits, fall back to the plug DP.

The plug DP's cost grows exponentially with its frontier, the shorter side of the grid: a 10 x 80
grid takes seconds, a 10 x 8 one milliseconds. `solve` cuts a thin instance into pieces, guesses
how the solution crosses each cut, and solves the pieces the same way, so the plug DP only runs on
pieces with a short side. Each cut has at least MARGIN endpoint-free lines on both sides (endpoints
include the crossing points of earlier cuts), across the longer side first, then the shorter:

    all endpoints on one side   strip: solve that side, splice the empty block into a path
                                running along the cut (as the strip move does)
    one whole colour per side   two one-path pieces (IPS, exact)
    one colour split            it crosses once, at a guessed row; the piece holding only one
                                endpoint is a one-path piece (IPS)
    both colours split          each crosses once, at guessed rows

A piece is reported unsolvable only after an exact test (parity, IPS, or the plug DP), so the
answers are exact: when the guesses at a piece fail, it goes to the plug DP. Small or narrow pieces
go to the plug DP directly. Instances with both sides >= 11 use the ordinary solver
(`solver.solve`).

The candidate order is fixed (integer scores, ties by position), so the JavaScript and C versions
return the same paths.
"""
from types import SimpleNamespace

from .grid import Instance, check_solution
from .ips import acceptable, hamiltonian_path
from .lift import block_cycle, _flip_path, _splice
from .plugdp import parity_ok, solve_paths
from . import solver as _solver

# Free columns required on each side of a cut, between it and every endpoint.
#
MARGIN = 3

# Pieces with a side at most NARROW go straight to the plug DP (its frontier is the shorter side
# plus one, so these are cheap).
#
NARROW = 6

# Pieces of at most this many cells go straight to the plug DP.
#
AREA = 60

# Pieces with a side at most this get one cut and one crossing guess: their plug DP is cheap,
# and an unsolvable piece would otherwise try every guess at every level below it.
#
SMALL = 7

# Crossing guesses tried at a cut, and cuts tried at a piece, before falling back to the plug DP.
#
TRIES = 4
CUTS = 2

# Work allowed for guessing at a piece, in multiples of its own estimated plug DP cost.
#
BUDGET = 1


def decide(inst):
    inst = _solver._check(inst)
    if min(inst.R, inst.C) > _solver.THIN:
        return _solver.decide(inst)
    return solve(inst) is not None


def solve(inst, trace=None):
    """As `solver.solve`; thin instances are solved by guessed splits with the plug DP as the
    fallback. Trace steps: ("split", piece, kind and column), ("ips", piece), ("dp", piece),
    ("fallback", piece) when every guess at a cut failed."""
    inst = _solver._check(inst)
    if min(inst.R, inst.C) > _solver.THIN:
        return _solver.solve(inst, trace)
    terms = [(inst.s0, 0), (inst.t0, 0), (inst.s1, 1), (inst.t1, 1)]
    R, C = inst.R, inst.C
    tr = R > C
    if tr:
        R, C = C, R
        terms = [((c, r), k) for (r, c), k in terms]
    log = (lambda *s: trace.append(s)) if trace is not None else (lambda *s: None)
    res = _piece(R, C, terms, _Ctx(log))
    if res is None:
        return None
    sol = (res[0], res[1])
    if tr:
        sol = tuple([(c, r) for r, c in p] for p in sol)
    if not check_solution(inst, sol):
        raise _solver.SolverError("internal error: produced an invalid solution")
    return sol


def solve_paths_optimized(R, C, terms):
    """As `plugdp.solve_paths` (terms: ((r, c), colour) pairs), by guessed splits."""
    tr = R > C
    if tr:
        R, C = C, R
        terms = [((c, r), k) for (r, c), k in terms]
    res = _piece(R, C, terms, _Ctx(lambda *s: None))
    if res is None or not tr:
        return res
    return {k: [(c, r) for r, c in p] for k, p in res.items()}


class _Ctx:
    """The trace function, and the work done so far in estimated plug DP steps (`_est`)."""

    def __init__(self, log):
        self.log = log
        self.work = 0


def _est(R, C):
    """Estimated plug DP cost of an R x C piece: the number of cells times a bound on the states
    per cell, which grows exponentially with the shorter side."""
    return R * C * 3 ** min(R, C)


def _size(R, C):
    return SimpleNamespace(R=R, C=C)


def _orient(paths, terms):
    """Each colour's path starts at that colour's first term."""
    out = {}
    for k, p in paths.items():
        first = next(x for x, kk in terms if kk == k)
        out[k] = p if p[0] == first else p[::-1]
    return out


def _transpose(terms):
    return [((c, r), k) for (r, c), k in terms]


def _piece(R, C, terms, ctx):
    """Paths {colour: path} covering the R x C piece, or None if there is no covering. Exact."""
    if not parity_ok(R, C, terms):
        return None
    cols = sorted({k for _, k in terms})
    if len(cols) == 1:
        ctx.log("ips", _size(R, C))
        ctx.work += R * C
        p = hamiltonian_path(R, C, terms[0][0], terms[1][0])
        return None if p is None else {cols[0]: p}
    if min(R, C) > NARROW and R * C > AREA:
        # Guessing here, including the pieces below, may cost at most BUDGET times what this
        # piece's own plug DP would; then the plug DP decides. This bounds the search below an unsolvable
        # piece, which would otherwise try every guess at every level.
        #
        limit = ctx.work + BUDGET * _est(R, C)
        small = min(R, C) <= SMALL
        cuts, tries = (1, 1) if small else (CUTS, TRIES)
        tried = 0
        for tr, m in _options(R, C, terms):
            if tried == cuts or ctx.work >= limit:
                break
            RR, CC, tt = (C, R, _transpose(terms)) if tr else (R, C, terms)
            res = _guess(RR, CC, tt, m, tries, limit, ctx)
            if res is _NONE:
                continue
            tried += 1
            if res is not None:
                if tr:
                    res = {k: [(c, r) for r, c in p] for k, p in res.items()}
                return _orient(res, terms)
        if tried:
            ctx.log("fallback", _size(R, C))
    ctx.log("dp", _size(R, C))
    ctx.work += _est(R, C)
    res = solve_paths(R, C, terms)
    return None if res is None else _orient(res, terms)


def _options(R, C, terms):
    """Cuts to try, as (transposed, m): across the longer side first, then the shorter; with
    MARGIN free lines next to the cut, then with 1."""
    axes = (False, True) if C >= R else (True, False)
    out = []
    for margin in (MARGIN, 1):
        for tr in axes:
            RR, CC, tt = (C, R, _transpose(terms)) if tr else (R, C, terms)
            for m in _cuts(RR, CC, tt, margin):
                if (tr, m) not in out:
                    out.append((tr, m))
    return out


def _cuts(R, C, terms, margin):
    """Cuts between columns m-1 and m with at least `margin` endpoint-free columns on each side
    and both pieces at least 2 wide, best first: strips (all endpoints on one side, the empty
    block of even area, largest first), then cuts in the gaps between endpoint columns, farthest
    from the endpoints first, ties nearest the middle."""
    xs = sorted({x[1] for x, _ in terms})
    strips = []
    m = xs[0] - margin
    if (m * R) % 2 == 1:
        m -= 1
    if m >= 2:
        strips.append((m, m))
    m = xs[-1] + 1 + margin
    if ((C - m) * R) % 2 == 1:
        m += 1
    if C - m >= 2:
        strips.append((C - m, m))
    inner = []
    for a, b in zip(xs, xs[1:]):
        for m in range(a + 1 + margin, b - margin + 1):
            inner.append((-min(m - 1 - a, b - m), abs(2 * m - C), m))
    return [m for _, m in sorted(strips, key=lambda s: (-s[0], s[1]))] + [m for *_, m in sorted(inner)]


def _floordiv(a, b):
    return a // b


def _target(lo, hi, m):
    """The row where the straight line from `lo` (left of the cut) to `hi` meets the cut, rounded
    down: r1 + (r2 - r1) (m - 1/2 - c1) / (c2 - c1)."""
    (r1, c1), (r2, c2) = lo, hi
    return r1 + _floordiv((r2 - r1) * (2 * (m - c1) - 1), 2 * (c2 - c1))


def _shift(terms, dc):
    return [((r, c + dc), k) for (r, c), k in terms]


# Returned by `_guess` when no guess at the cut passes the cheap exact tests (nothing was tried).
#
_NONE = object()


def _guess(R, C, terms, m, tries, limit, ctx):
    """Paths for the piece by one of the guesses at cut m, None if they all fail, or _NONE if no
    guess passes the cheap exact tests."""
    L = [t for t in terms if t[0][1] < m]
    Rt = [t for t in terms if t[0][1] >= m]
    if not L or not Rt:
        return _strip(R, C, terms, m, bool(L), ctx)
    cols = sorted({k for _, k in terms})
    split = [k for k in cols if sum(1 for _, kk in L if kk == k) == 1]
    if not split:
        if not (_viable(R, m, L) and _viable(R, C - m, _shift(Rt, -m))):
            return _NONE
        ctx.log("split", _size(R, C), f"same, column {m}")
        pl = _piece(R, m, L, ctx)
        if pl is None:
            return None
        pr = _piece(R, C - m, _shift(Rt, -m), ctx)
        if pr is None:
            return None
        return {**pl, **{k: [(r, c + m) for r, c in p] for k, p in pr.items()}}

    # The crossing rows: one per split colour. Crossings on the border rows (a corner of both
    # pieces) or next to each other often leave a local obstruction, so they come last; then the
    # distance from the straight line between that colour's two endpoints; ties by row.
    #
    def ends_of(k):
        a = next(x for x, kk in L if kk == k)
        b = next(x for x, kk in Rt if kk == k)
        return a, b

    tgt = [_target(*ends_of(k), m) for k in split]

    def score(rows):
        pen = sum(1 for a in rows if a == 0 or a == R - 1)
        if len(rows) == 2 and abs(rows[0] - rows[1]) == 1:
            pen += 1
        return (pen, sum(abs(a - g) for a, g in zip(rows, tgt)), rows)

    if len(split) == 1:
        cands = sorted(((a,) for a in range(R)), key=score)
    else:
        cands = sorted(((a, b) for a in range(R) for b in range(R) if a != b), key=score)
    tried = 0
    for rows in cands:
        lt = L + [((a, m - 1), k) for a, k in zip(rows, split)]
        rt = _shift(Rt, -m) + [((a, 0), k) for a, k in zip(rows, split)]
        if not (_viable(R, m, lt) and _viable(R, C - m, rt)):
            continue
        if tried == tries or ctx.work >= limit:
            break
        tried += 1
        kind = "2/2 cross" if len(split) == 2 else "1/3"
        ctx.log("split", _size(R, C), f"{kind}, column {m}, rows {','.join(map(str, rows))}")
        res = _pair(R, C, m, lt, rt, ctx)
        if res is None:
            continue
        for a, k in zip(rows, split):
            lp = res[0][k] if res[0][k][-1] == (a, m - 1) else res[0][k][::-1]
            rp = [(r, c + m) for r, c in res[1][k]]
            rp = rp if rp[0] == (a, m) else rp[::-1]
            res[0][k] = lp + rp
        for k, p in res[1].items():
            if k not in split:
                res[0][k] = [(r, c + m) for r, c in p]
        return res[0]
    return None if tried else _NONE


def _viable(R, C, terms):
    """Cheap exact rejections for a piece: parity, and IPS for a one-path piece."""
    if not parity_ok(R, C, terms):
        return False
    if len({k for _, k in terms}) == 1:
        return acceptable(R, C, terms[0][0], terms[1][0])
    return True


def _pair(R, C, m, lt, rt, ctx):
    """Solve both pieces of a guess: the one-path piece first, else the smaller one first (a
    failure is found sooner)."""
    nl, nr = len({k for _, k in lt}), len({k for _, k in rt})
    left_first = nl < nr or (nl == nr and m <= C - m)
    first, second = ((m, lt), (C - m, rt)) if left_first else ((C - m, rt), (m, lt))
    a = _piece(R, first[0], first[1], ctx)
    if a is None:
        return None
    b = _piece(R, second[0], second[1], ctx)
    if b is None:
        return None
    return (a, b) if left_first else (b, a)


def _strip(R, C, terms, m, left, ctx):
    """All endpoints on one side of the cut: solve that side, then splice the empty block into a
    path running along the cut."""
    ctx.log("split", _size(R, C), f"strip, column {m}")
    if left:
        res = _piece(R, m, terms, ctx)
        edge_col, w = m - 1, C - m
        cell = lambda i, j: (j, m + i)
    else:
        res = _piece(R, C - m, _shift(terms, -m), ctx)
        if res is not None:
            res = {k: [(r, c + m) for r, c in p] for k, p in res.items()}
        edge_col, w = m, m
        cell = lambda i, j: (j, m - 1 - i)
    if res is None:
        return None
    used = set()
    for p in res.values():
        for u, v in zip(p, p[1:]):
            used.add((u, v))
            used.add((v, u))
    for a in range(R - 1):
        if ((a, edge_col), (a + 1, edge_col)) in used:
            mid = [cell(i, j) for i, j in _flip_path(block_cycle(w, R), a)]
            paths = [list(res[k]) for k in sorted(res)]
            _splice(paths, (a, edge_col), (a + 1, edge_col), mid)
            return dict(zip(sorted(res), paths))
    return None

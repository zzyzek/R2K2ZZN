# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Extending solutions: band extension (insert two empty lines) and strip splicing.

Paths are lists of cells. `extend(R, C, paths, axis, k)` inserts two empty lines so that they
become lines k, k+1 of the new grid (axis 0: rows, axis 1: columns); a line next to the insertion
must hold no path endpoint. `add_block(R, C, paths, w)` appends an empty w x C block below the
grid (w*C even, C >= 2), spliced into a path through an edge along the last row.
"""


def _splice(paths, u, v, mid):
    """Replace the edge u-v of some path by u -> mid... -> v."""
    for p in paths:
        for i in range(len(p) - 1):
            if p[i] == u and p[i + 1] == v:
                p[i + 1:i + 1] = mid
                return
            if p[i] == v and p[i + 1] == u:
                p[i + 1:i + 1] = list(reversed(mid))
                return
    raise ValueError("edge not in any path")


def block_cycle(w, L):
    """A Hamiltonian cycle of the w x L block (block coordinates) through every edge of row 0,
    listed from (0, 0) along row 0. Needs w >= 2, L >= 2 and w*L even."""
    cyc = [(0, j) for j in range(L)]
    if w % 2 == 0:
        # serpentine through rows 1..w-1 in columns 1..L-1, back up column 0
        for i in range(1, w):
            cols = range(L - 1, 0, -1) if i % 2 == 1 else range(1, L)
            cyc += [(i, j) for j in cols]
        cyc += [(i, 0) for i in range(w - 1, 0, -1)]
    else:
        # L even: column snakes through rows 1..w-1, from column L-1 to column 0
        for j in range(L - 1, -1, -1):
            rows = range(1, w) if (L - 1 - j) % 2 == 0 else range(w - 1, 0, -1)
            cyc += [(i, j) for i in rows]
    return cyc


def _flip_path(cyc, a):
    """The cycle minus its edge (0, a)-(0, a+1), as a path from (0, a) to (0, a+1)."""
    return cyc[a::-1] + cyc[:a:-1]


def _band_rows(R, C, paths, r):
    """Insert two rows directly below row r (row r endpoint-free). Returns new paths."""
    shift = lambda x: x if x[0] <= r else (x[0] + 2, x[1])
    paths = [[shift(x) for x in p] for p in paths]
    n1, n2 = r + 1, r + 2
    # step 1: extend crossing edges
    xs = []
    for p in paths:
        for i in range(len(p) - 1):
            a, b = p[i], p[i + 1]
            if a[1] == b[1] and {a[0], b[0]} == {r, r + 3}:
                xs.append(a[1])
    xs.sort()
    for c in xs:
        _splice(paths, (r, c), (r + 3, c), [(n1, c), (n2, c)])
    # runs between crossings
    bounds = [-1] + xs + [C]
    runs = [(bounds[i] + 1, bounds[i + 1] - 1) for i in range(len(bounds) - 1)]
    m = len(xs)
    horiz = set()
    for p in paths:
        for i in range(len(p) - 1):
            a, b = p[i], p[i + 1]
            if a[0] == b[0] == r and abs(a[1] - b[1]) == 1:
                horiz.add(min(a[1], b[1]))
    j = next((i for i, (lo, hi) in enumerate(runs) if lo > hi), None)
    if j is None:
        j = next(i for i, (lo, hi) in enumerate(runs) if any(lo <= a < hi for a in horiz))
    # step 2: U-detours; crossing i (1-based) absorbs run i-1 if i <= j, else run i
    for i, c in enumerate(xs, start=1):
        lo, hi = runs[i - 1] if i <= j else runs[i]
        if lo > hi:
            continue
        if i <= j:  # block to the left
            mid = [(n1, y) for y in range(c - 1, lo - 1, -1)] + [(n2, y) for y in range(lo, c)]
        else:
            mid = [(n1, y) for y in range(c + 1, hi + 1)] + [(n2, y) for y in range(hi, c, -1)]
        _splice(paths, (n1, c), (n2, c), mid)
    # step 3: the last block, by a square flip with an edge of row r inside it
    lo, hi = runs[j]
    if lo <= hi:
        a = next(a for a in sorted(horiz) if lo <= a < hi)
        cyc = [(n1 + i, lo + y) for i, y in block_cycle(2, hi - lo + 1)]
        mid = _flip_path(cyc, a - lo)
        _splice(paths, (r, a), (r, a + 1), mid)
    return paths


def _ends(paths):
    return {p[0] for p in paths} | {p[-1] for p in paths}


def _rows_extend(R, C, paths, k):
    ends = _ends(paths)
    if k >= 1 and not any(x[0] == k - 1 for x in ends):
        return _band_rows(R, C, paths, k - 1)
    if k < R and not any(x[0] == k for x in ends):
        # mirror: the free row k sits just below the insertion point
        refl = lambda x, n: (n - 1 - x[0], x[1])
        mp = [[refl(x, R) for x in p] for p in paths]
        out = _band_rows(R, C, mp, R - 1 - k)
        return [[refl(x, R + 2) for x in p] for p in out]
    raise ValueError("no endpoint-free line next to the insertion point")


def extend(R, C, paths, axis, k):
    """Insert two empty lines at position k (they become lines k and k+1)."""
    paths = [list(p) for p in paths]
    if axis == 0:
        return _rows_extend(R, C, paths, k)
    tp = [[(c, r) for r, c in p] for p in paths]
    out = _rows_extend(C, R, tp, k)
    return [[(c, r) for r, c in p] for p in out]


def insert_two_lines(R, C, paths, axis, after):
    return extend(R, C, paths, axis, after + 1)


def add_block(R, C, paths, w):
    """Append an empty w x C block below row R-1 (w >= 2, w*C even, C >= 2), spliced through a
    used edge along row R-1."""
    paths = [list(p) for p in paths]
    a = None
    for p in paths:
        for i in range(len(p) - 1):
            x, y = p[i], p[i + 1]
            if x[0] == y[0] == R - 1 and abs(x[1] - y[1]) == 1:
                a = min(x[1], y[1])
                break
        if a is not None:
            break
    if a is None:
        raise ValueError("no edge along the last row")
    cyc = [(R + i, y) for i, y in block_cycle(w, C)]
    _splice(paths, (R - 1, a), (R - 1, a + 1), _flip_path(cyc, a))
    return paths

# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""The forbidden-pattern catalogue: `fires(R, C, s0, t0, s1, t1)`.

A transcription of `fires3` in `lean/ZZN/Catalogue.lean` (the definition the Lean theorems are
about). Returns the name of an entry that fires, or None if the instance passes.

Entries: P (parity), T1 (perimeter alternation), T2 (alternating unit square), L1 (isolated
endpoint), L6 (double corner closure), and per corner frame L2-L5 (corner blocks), E1 (edge
closure), B (boundary-only corner triples), C4 (corner configurations), and R (forced corner
rewrites, then alternation along the new outer boundary).
"""

CORNER4 = [
    ([(0, 1), (0, 3)], [(1, 1), (1, 3)]), ([(0, 1), (0, 6)], [(0, 7), (1, 1)]),
    ([(0, 1), (0, 6)], [(1, 1), (7, 0)]), ([(0, 1), (0, 6)], [(1, 2), (6, 0)]),
    ([(0, 1), (0, 7)], [(1, 1), (6, 0)]), ([(0, 1), (1, 3)], [(1, 1), (1, 2)]),
    ([(0, 1), (1, 3)], [(1, 2), (2, 2)]), ([(0, 1), (1, 3)], [(1, 2), (3, 1)]),
    ([(0, 1), (2, 2)], [(1, 1), (1, 2)]), ([(0, 1), (2, 2)], [(1, 2), (3, 1)]),
    ([(0, 1), (2, 2)], [(1, 3), (3, 0)]), ([(0, 1), (7, 0)], [(1, 1), (6, 0)]),
    ([(0, 2), (1, 1)], [(2, 1), (3, 0)]), ([(0, 2), (2, 0)], [(1, 2), (2, 1)]),
    ([(0, 3), (2, 1)], [(3, 1), (4, 0)]), ([(0, 6), (2, 1)], [(1, 2), (6, 0)]),
    ([(1, 2), (2, 2)], [(1, 3), (2, 1)]), ([(1, 2), (3, 1)], [(1, 3), (2, 1)]),
    ([(0, 1), (1, 2)], [(0, 4), (2, 2)]), ([(0, 1), (1, 2)], [(0, 4), (3, 1)]),
    ([(0, 1), (1, 2)], [(1, 3), (2, 0)]), ([(0, 1), (1, 2)], [(1, 3), (4, 0)]),
    ([(0, 1), (1, 2)], [(2, 0), (2, 2)]), ([(0, 1), (1, 2)], [(2, 2), (4, 0)]),
    ([(0, 1), (1, 2)], [(3, 1), (4, 0)]), ([(0, 1), (1, 3)], [(0, 3), (0, 4)]),
    ([(0, 1), (1, 3)], [(0, 3), (2, 0)]), ([(0, 1), (1, 3)], [(0, 3), (4, 0)]),
    ([(0, 1), (2, 1)], [(0, 2), (2, 2)]), ([(0, 1), (2, 1)], [(0, 2), (3, 1)]),
    ([(0, 1), (2, 1)], [(0, 4), (1, 3)]), ([(0, 1), (2, 1)], [(0, 4), (2, 2)]),
    ([(0, 1), (2, 1)], [(0, 4), (3, 1)]), ([(0, 1), (2, 1)], [(1, 3), (4, 0)]),
    ([(0, 1), (2, 1)], [(2, 2), (4, 0)]), ([(0, 1), (2, 1)], [(3, 1), (4, 0)])]

CORNER4_ODD = [
    ([(0, 0), (0, 1)], [(1, 1), (2, 0)]), ([(0, 0), (1, 4)], [(0, 2), (1, 3)]),
    ([(0, 0), (2, 3)], [(0, 2), (1, 3)])]

BOUNDARY3_EVEN = [
    ((0, 0), (1, 1), (1, 2)), ((0, 1), (0, 2), (1, 1)), ((0, 1), (0, 2), (1, 2)),
    ((0, 1), (0, 3), (1, 1)), ((0, 1), (0, 4), (1, 1)), ((0, 1), (0, 4), (1, 2)),
    ((0, 1), (0, 5), (1, 1)), ((0, 1), (1, 2), (1, 1)), ((0, 1), (1, 2), (1, 3)),
    ((0, 1), (1, 2), (2, 2)), ((0, 1), (1, 2), (3, 1)), ((0, 1), (1, 3), (0, 3)),
    ((0, 1), (2, 1), (1, 3)), ((0, 1), (2, 1), (2, 2)), ((0, 1), (2, 1), (3, 1)),
    ((0, 2), (2, 1), (1, 0)), ((0, 3), (1, 1), (1, 0)), ((0, 4), (1, 1), (1, 0)),
    ((0, 4), (2, 1), (1, 0)), ((0, 4), (2, 1), (1, 2)), ((0, 5), (1, 1), (1, 0))]

BOUNDARY3_ODD = [
    ((0, 0), (1, 1), (1, 2)), ((0, 0), (1, 1), (2, 2)), ((0, 1), (0, 2), (1, 1)),
    ((0, 1), (0, 4), (1, 1)), ((0, 4), (1, 1), (1, 0))]

def ns(a, b):
    """Natural-number subtraction, as in the Lean definition (never negative)."""
    return a - b if a > b else 0


FRAMES = [(fr, fc, tr) for fr in (False, True) for fc in (False, True) for tr in (False, True)]


def sgn(p):
    return 1 if (p[0] + p[1]) % 2 == 0 else -1


def parity_ok(R, C, pts):
    return sum(sgn(q[0]) for q in pts) == 2 * ((R * C) % 2)


def perim_index(R, C, p):
    r, c = p
    if r == 0:
        return c
    if c == C - 1:
        return (C - 1) + r
    if r == R - 1:
        return (C - 1) + (R - 1) + (C - 1 - c)
    if c == 0:
        return 2 * (C - 1) + (R - 1) + (R - 1 - r)
    return None


def alternating(cols):
    return len(cols) == 4 and cols[0] != cols[1] and cols[1] != cols[2] and cols[2] != cols[3]


def t1_fires(R, C, pts):
    idx = [perim_index(R, C, q[0]) for q in pts]
    if any(i is None for i in idx):
        return False
    order = [col for _, col in sorted(zip(idx, [q[1] for q in pts]), key=lambda x: x[0])]
    return alternating(order)


def t2_fires(cells):
    rs = [x[0] for x in cells]
    cs = [x[1] for x in cells]
    return (max(rs) - min(rs) == 1 and max(cs) - min(cs) == 1 and
            rs[0] != rs[1] and cs[0] != cs[1])


def l1_fires(R, C, pts):
    for (p, col) in pts:
        nb = [(p[0] + dr, p[1] + dc) for dr, dc in ((-1, 0), (1, 0), (0, -1), (0, 1))]
        nb = [q for q in nb if 0 <= q[0] < R and 0 <= q[1] < C]
        if all(any(e == q and ecol != col for e, ecol in pts) for q in nb):
            return True
    return False


def _find(pts, x):
    for q in pts:
        if q[0] == x:
            return q
    return None


def l6_fires(R, C, pts):
    closures = []
    for cr, cc, dr, dc in ((0, 0, 1, 1), (0, C - 1, 1, -1), (R - 1, 0, -1, 1), (R - 1, C - 1, -1, -1)):
        n1 = (cr, max(cc + dc, 0))
        n2 = (max(cr + dr, 0), cc)
        e1, e2 = _find(pts, n1), _find(pts, n2)
        corner_empty = _find(pts, (cr, cc)) is None
        if e1 and e2 and e1[1] == e2[1] and corner_empty:
            closures.append(e1[1])
    return 0 in closures and 1 in closures and R * C > 6


# --- corner frames ------------------------------------------------------------------------

def frame_to(R, C, f, p):
    fr, fc, tr = f
    a = ns(ns(R, 1), p[0]) if fr else p[0]
    b = ns(ns(C, 1), p[1]) if fc else p[1]
    return (b, a) if tr else (a, b)


def frame_back(R, C, f, q):
    fr, fc, tr = f
    r = q[1] if tr else q[0]
    c = q[0] if tr else q[1]
    return (ns(ns(R, 1), r) if fr else r, ns(ns(C, 1), c) if fc else c)


class View:
    """The endpoints as seen from a corner frame: `at(r, c)` is a colour or None."""

    def __init__(self, R, C, f, pts):
        self.H = C if f[2] else R
        self.W = R if f[2] else C
        self.pts = [(frame_to(R, C, f, q[0]), q[1]) for q in pts]

    def at(self, r, c):
        for x, col in self.pts:
            if x == (r, c):
                return col
        return None

    def empty(self, cells):
        return all(self.at(r, c) is None for r, c in cells)


def test_l2(v):
    a, b = v.at(0, 1), v.at(1, 0)
    return a is not None and b is not None and a != b and v.empty([(0, 0)])


def test_l3(v):
    a = v.at(0, 2)
    return (a is not None and v.at(1, 1) == a and v.at(1, 0) == 1 - a and
            v.empty([(0, 0), (0, 1)]))


def test_l4(v):
    a = v.at(0, 0)
    return (a is not None and v.at(1, 1) == a and v.at(0, 2) == 1 - a and v.H >= 3 and
            v.empty([(0, 1), (1, 0)]))


def test_l5(v):
    b = v.at(0, 0)
    return (b is not None and v.at(0, 2) == 1 - b and v.at(2, 0) == 1 - b and
            v.empty([(0, 1), (1, 0), (1, 1)]))


def edge_closure(v):
    for k in range(v.W):
        if k + 3 < v.W:
            a = v.at(0, k)
            if (a is not None and v.at(1, k + 1) == a and v.at(0, k + 3) == 1 - a and
                    v.at(1, k + 2) == 1 - a):
                return True
    return False


def boundary_only(R, C, f, pts):
    lst = BOUNDARY3_ODD if (R % 2 == 1 and C % 2 == 1) else BOUNDARY3_EVEN
    fp = [(frame_to(R, C, f, q[0]), q[1]) for q in pts]
    H = C if f[2] else R
    W = R if f[2] else C
    for (a1, a2, b) in lst:
        for A in (0, 1):
            if not any(col == 1 - A and x == b for x, col in fp):
                continue
            if not (any(col == A and x == a1 for x, col in fp) and any(col == A and x == a2 for x, col in fp)):
                continue
            fourth = next((x for x, col in fp if col == 1 - A and x != b), None)
            if fourth is None:
                continue
            on_perim = fourth[0] == 0 or fourth[1] == 0 or fourth[0] == H - 1 or fourth[1] == W - 1
            in_win = fourth[0] < 6 and fourth[1] < 6
            if on_perim and not in_win:
                return True
    return False


def same_set(a, b):
    return len(a) == len(b) and all(x in b for x in a)


def corner4(R, C, f, pts):
    A0 = [frame_to(R, C, f, q[0]) for q in pts if q[1] == 0]
    A1 = [frame_to(R, C, f, q[0]) for q in pts if q[1] == 1]
    lst = CORNER4 if (R * C) % 2 == 0 else CORNER4_ODD
    return any((same_set(A, A0) and same_set(B, A1)) or (same_set(A, A1) and same_set(B, A0))
               for A, B in lst)


def frame_fires(R, C, pts, f):
    v = View(R, C, f, pts)
    for name, test in (("L2", test_l2), ("L3", test_l3), ("L4", test_l4), ("L5", test_l5),
                       ("E1", edge_closure)):
        if test(v):
            return name
    if boundary_only(R, C, f, pts):
        return "B"
    if R >= 10 and C >= 10 and corner4(R, C, f, pts):
        return "C4"
    return None


# --- R: forced corner rewrites and the outer walk -----------------------------------------

def rewrites_at(v):
    """The rewrite at a corner frame: (settled cells, endpoint moves), or None."""
    x, y = v.at(1, 2), v.at(2, 1)
    if (x is not None and y is not None and x != y and v.H >= 4 and v.W >= 4 and
            v.empty([(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (2, 0), (3, 0)])):
        return ([(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0), (1, 2), (2, 1)],
                [((1, 2), (0, 3)), ((2, 1), (3, 0))])
    a = v.at(0, 0)
    if (a is not None and v.at(1, 1) == a and v.H >= 3 and v.W >= 3 and
            v.empty([(0, 1), (1, 0), (0, 2), (2, 0)])):
        return ([(0, 0), (0, 1), (1, 0), (1, 1)], [((0, 0), (0, 2)), ((1, 1), (2, 0))])
    if v.at(0, 1) is not None and v.empty([(0, 0), (1, 0)]) and v.H >= 2:
        return ([(0, 0), (0, 1)], [((0, 1), (1, 0))])
    return None


def rewrite_all(R, C, pts):
    eff, removed, anyrw = list(pts), [], False
    for f in FRAMES:
        rw = rewrites_at(View(R, C, f, eff))
        if rw is None:
            continue
        cells = [frame_back(R, C, f, x) for x in rw[0]]
        moves = [(frame_back(R, C, f, a), frame_back(R, C, f, b)) for a, b in rw[1]]
        if any(x in removed for x in cells) or any(m[1] in removed for m in moves):
            continue
        for a, b in moves:
            for i, q in enumerate(eff):
                if q[0] == a:
                    eff[i] = (b, q[1])
                    break
        removed = removed + cells
        anyrw = True
    return eff, removed, anyrw


FTL, FTR, FBR, FBL = (False, False, False), (False, True, False), (True, True, False), (True, False, False)


def notch_len(R, C, f, removed, i):
    return sum(1 for j in range(4) if frame_back(R, C, f, (i, j)) in removed)


def staircase(lam):
    k = sum(1 for i in range(4) if lam(i) > 0)
    out = [(k, 0)]
    for i in reversed(range(k)):
        out += [(i + 1, lam(i + 1) + 1 + j) for j in range(ns(lam(i), lam(i + 1)))]
        out.append((i, lam(i)))
    return out


def stair_of(R, C, f, removed):
    return [frame_back(R, C, f, x) for x in staircase(lambda i: notch_len(R, C, f, removed, i))]


def walk3(R, C, removed):
    """The outer boundary walk of the grid minus the settled corner staircases."""
    tl = stair_of(R, C, FTL, removed)
    trr = list(reversed(stair_of(R, C, FTR, removed)))
    br = stair_of(R, C, FBR, removed)
    bl = list(reversed(stair_of(R, C, FBL, removed)))
    lam = lambda f: notch_len(R, C, f, removed, 0)
    k = lambda f: sum(1 for i in range(4) if notch_len(R, C, f, removed, i) > 0)
    lTL, lTR, lBR, lBL = lam(FTL), lam(FTR), lam(FBR), lam(FBL)
    kTL, kTR, kBR, kBL = k(FTL), k(FTR), k(FBR), k(FBL)
    top = [(0, y) for y in range(C) if lTL < y and y + 1 + lTR < C]
    right = [(x, C - 1) for x in range(R) if kTR < x and x + 1 + kBR < R]
    bottom = list(reversed([(R - 1, y) for y in range(C) if lBL < y and y + 1 + lBR < C]))
    left = list(reversed([(x, 0) for x in range(R) if kTL < x and x + 1 + kBL < R]))
    return tl + top + trr + right + br + bottom + bl + left


def eff_alt(R, C, pts):
    eff, removed, anyrw = rewrite_all(R, C, pts)
    if not anyrw:
        return False
    if any(q[0] in removed for q in eff):
        return False
    if len(set(q[0] for q in eff)) != 4:
        return False
    walk = walk3(R, C, removed)
    places = []
    for q in eff:
        pos = [i for i, x in enumerate(walk) if x == q[0]]
        if len(pos) != 1:
            return False
        places.append((pos[0], q[1]))
    return alternating([col for _, col in sorted(places, key=lambda x: x[0])])


def fires(R, C, s0, t0, s1, t1):
    """Name of a catalogue entry that fires on the instance, or None if it passes."""
    pts = [(s0, 0), (t0, 0), (s1, 1), (t1, 1)]
    if not parity_ok(R, C, pts):
        return "P"
    if t1_fires(R, C, pts):
        return "T1"
    if t2_fires([s0, t0, s1, t1]):
        return "T2"
    if l1_fires(R, C, pts):
        return "L1"
    if l6_fires(R, C, pts):
        return "L6"
    for f in FRAMES:
        name = frame_fires(R, C, pts, f)
        if name:
            return name
    if eff_alt(R, C, pts):
        return "R"
    return None


def passes(inst):
    return fires(inst.R, inst.C, inst.s0, inst.t0, inst.s1, inst.t1) is None

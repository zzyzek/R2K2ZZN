# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Two-line reductions: the inner layer of the Lean construction, `solveZ2`.

A transcription of `proof/ZZN/Constr/Solve2.lean` (`redBB`, `redAny`, `findRed2`, `solveRec2`) and
of `proof/ZZN/Statement.lean` (`freeLineB`, `endBelowB`, `endAboveB`, `redB`, `delAt`,
`Inst.deleteAt`, `shiftAt`, `gap`, `stretch`, `insB`, `spliceE`, `absorbE`, `flipE`, `sweepLeftE`,
`sweepRightE`, `SeedAt`, `bandExtE`, `liftE`). The choices are the same as in Lean: the same line
to delete, the same seed column, the same detours.

Lean's cell (x, y) on a w x h grid is the library's (r, c) on an R x C grid: x = r, w = R, y = c,
h = C. `solve_rec2(I, leaf)` deletes two lines at a time (`RedX` or `RedB`, first d on the x-axis,
then on the transposed instance), solves the last instance with `leaf`, and lifts back by band
extension. It runs on the instance left by block deletion (sides at most 37), so the quadratic
list operations below cost a bounded amount.
"""
from .grid import Instance, ends


def free_line(I, k):
    """`freeLineB`."""
    return all(e[0] != k for e in ends(I))


def end_below(I, k):
    """`endBelowB`."""
    return any(e[0] < k for e in ends(I))


def end_above(I, k):
    """`endAboveB`."""
    return any(k < e[0] for e in ends(I))


def red_x(I, d):
    """`redB` (Statement.lean), the decided form of `RedX`."""
    w = I.R
    if not (13 <= w):
        return False
    if d == 0 and all(free_line(I, k) for k in range(4)):
        return True
    if d + 2 == w and all((not (w <= k + 4)) or free_line(I, k) for k in range(w)):
        return True
    for lo in range(d + 1):
        if (d + 1 <= lo + 9 and lo + 10 <= w and all(free_line(I, lo + j) for j in range(10)) and
                end_below(I, lo) and end_above(I, lo + 9)):
            return True
    return (8 <= d and d + 10 <= w and free_line(I, d) and free_line(I, d + 1) and
            ((1 <= d and free_line(I, d - 1)) or free_line(I, d + 2)) and
            end_below(I, d) and end_above(I, d + 1))


def red_b(I, d):
    """`redBB` (Solve2.lean), the decided form of `RedB`."""
    w = I.R
    return (13 <= w and 5 <= d and d + 7 <= w and free_line(I, d) and free_line(I, d + 1) and
            ((1 <= d and free_line(I, d - 1)) or free_line(I, d + 2)) and
            end_below(I, d) and end_above(I, d + 1))


def find_red2(I):
    """`findRed2`: the first d in 0 … w - 1 with `redAny` (`RedX` or `RedB`), or None."""
    for d in range(I.R):
        if red_x(I, d) or red_b(I, d):
            return d
    return None


def delete_at(I, d):
    """`Inst.deleteAt`: delete the lines d, d + 1 (`delAt`)."""
    f = lambda v: v if v[0] < d else (v[0] - 2, v[1])
    return Instance(I.R - 2, I.C, f(I.s0), f(I.t0), f(I.s1), f(I.t1))


def transpose(I):
    sw = lambda v: (v[1], v[0])
    return Instance(I.C, I.R, sw(I.s0), sw(I.t0), sw(I.s1), sw(I.t1))


# --- band extension (Statement.lean) ------------------------------------------------------

def _stretch(r, L):
    """`stretch r`: shift the cells after line r by 2 and fill each crossing of r | r + 1."""
    sh = lambda v: v if v[0] <= r else (v[0] + 2, v[1])
    out = []
    for i, a in enumerate(L):
        out.append(sh(a))
        if i + 1 < len(L):
            b = L[i + 1]
            if a[0] == r and b[0] == r + 1 and a[1] == b[1]:
                out += [(r + 1, a[1]), (r + 2, a[1])]
            elif a[0] == r + 1 and b[0] == r and a[1] == b[1]:
                out += [(r + 2, a[1]), (r + 1, a[1])]
    return out


def _has_edge(L, a, b):
    """`[a, b] <:+: L`."""
    return any(L[i] == a and L[i + 1] == b for i in range(len(L) - 1))


def _ins_b(a, b, X, L):
    """`insB a b X L`: insert X between the first consecutive a, b."""
    for i in range(len(L) - 1):
        if L[i] == a and L[i + 1] == b:
            return L[:i + 1] + X + L[i + 1:]
    return L


def _splice(P, Q, a, b, X):
    """`spliceE`."""
    if _has_edge(P, a, b):
        return _ins_b(a, b, X, P), Q
    return P, _ins_b(a, b, X, Q)


def _absorb(r, y, y2, P, Q):
    """`absorbE r y y2`: cover column y by a detour of the middle edge of column y2."""
    u, v = (r + 1, y2), (r + 2, y2)
    if _has_edge(P, u, v) or _has_edge(Q, u, v):
        return _splice(P, Q, u, v, [(r + 1, y), (r + 2, y)])
    return _splice(P, Q, v, u, [(r + 2, y), (r + 1, y)])


def _flip(r, y, P, Q):
    """`flipE r y`: cover columns y, y + 1 by a detour of the row-r edge between them."""
    u, v = (r, y), (r, y + 1)
    if _has_edge(P, u, v) or _has_edge(Q, u, v):
        return _splice(P, Q, u, v, [(r + 1, y), (r + 2, y), (r + 2, y + 1), (r + 1, y + 1)])
    return _splice(P, Q, v, u, [(r + 1, y + 1), (r + 2, y + 1), (r + 2, y), (r + 1, y)])


def _sweep_left(r, n, U, P, Q):
    """`sweepLeftE r n U`: columns n - 1, n - 2, …, 0 in U, each from the column above it."""
    U = set(U)
    while n > 0:
        L = n - 1
        if L in U:
            P, Q = _absorb(r, L, L + 1, P, Q)
            U.discard(L)
        n = L
    return P, Q


def _sweep_right(r, h, n, R, U, P, Q):
    """`sweepRightE r h n R U`: columns R + 1, R + 2, … in U, each from the column below it."""
    U = set(U)
    while n > 0:
        if R + 1 in U:
            P, Q = _absorb(r, R + 1, R, P, Q)
            U.discard(R + 1)
        elif not (R + 1 < h):
            return P, Q
        n, R = n - 1, R + 1
    return P, Q


def band_ext(I, r, p, q):
    """`bandExtE I r p q`: insert two lines after line r of I into the solution p, q."""
    h = I.C
    cross = set()
    vert = set()
    for L in (p, q):
        for i in range(len(L) - 1):
            a, b = L[i], L[i + 1]
            if a[1] == b[1] and {a[0], b[0]} == {r, r + 1}:
                cross.add(a[1])
            elif a[0] == r and b[0] == r and abs(a[1] - b[1]) == 1:
                vert.add(max(a[1], b[1]))
    U0 = {y for y in range(h) if y not in cross}
    P0, Q0 = _stretch(r, p), _stretch(r, q)
    for R in range(h + 1):
        A = (R == 0 or (R - 1) in cross) and (R == h or R in cross)
        B = 1 <= R < h and (R - 1) not in cross and R not in cross and R in vert
        if A or B:
            break
    else:
        return P0, Q0
    if A:
        if R == 0:
            return _sweep_right(r, h, h, 0, U0, P0, Q0)
        if R == h:
            return _sweep_left(r, R - 1, U0, P0, Q0)
        P1, Q1 = _sweep_left(r, R - 1, U0, P0, Q0)
        return _sweep_right(r, h, h - R, R, {y for y in U0 if R - 1 < y}, P1, Q1)
    U1 = U0 - {R - 1, R}
    P1, Q1 = _flip(r, R - 1, P0, Q0)
    P2, Q2 = _sweep_left(r, R - 1, U1, P1, Q1)
    return _sweep_right(r, h, h - R, R, {y for y in U1 if R - 1 < y}, P2, Q2)


def lift_e(I, d, p, q):
    """`liftE I d`: put the deleted lines d, d + 1 of I back into a solution of I.deleteAt d."""
    J = delete_at(I, d)
    if d + 3 <= I.R and free_line(I, d + 2):
        return band_ext(J, d, p, q)
    return band_ext(J, d - 1, p, q)


# --- the recursion of solveRec2 -----------------------------------------------------------

def plan2(I):
    """Delete two lines at a time as `solveRec2` does, until a side is at most 10 or no reduction
    applies on either axis. Returns (leaf, steps); each step (I, d, tr) deleted lines d, d + 1 from
    I (from I's transpose when tr), and the recursion continues in that frame, as in Lean."""
    steps = []
    while I.R > 10 and I.C > 10:
        d = find_red2(I)
        if d is not None:
            steps.append((I, d, False))
            I = delete_at(I, d)
            continue
        T = transpose(I)
        d = find_red2(T)
        if d is not None:
            steps.append((T, d, True))
            I = delete_at(T, d)
            continue
        break
    return I, steps


def lift_all2(steps, p, q):
    """Lift a solution of the leaf of `plan2` back to a solution of the first instance."""
    for P, d, tr in reversed(steps):
        p, q = lift_e(P, d, p, q)
        if tr:
            p = [(c, r) for r, c in p]
            q = [(c, r) for r, c in q]
    return p, q

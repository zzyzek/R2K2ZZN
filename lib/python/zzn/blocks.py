# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Block deletion: the outer layer of the Lean construction `solveR`.

A transcription of `proof/ZZN/Constr/Round.lean` (`leftK`, `rightK`, `innerK`, `gapOK`,
`innerPair`, `blkX`, `Blk.del`, `Blk.lift`, `seedW`, `cvW`, `innerLift`, `solveR`),
`proof/ZZN/Constr/EdgeBlock.lean` (`colSnake`, `edgeBlock`, `findV`, `blkE`, `edgeLift`,
`edgeLiftL`) and `proof/ZZN/Constr/WideBand.lean` (`runDn`, `runUp`, `grpW`, `snW`, `flipW`,
`GW`, `wideExt`). The choices are the same as in Lean: the same block, the same seed row, the same
detours.

Lean's cell (x, y) on a w x h grid is the library's (r, c) on an R x C grid: x = r, w = R, y = c,
h = C (as in ips.py). A block is 2k free lines on the x-axis: at the left edge (lines 0 … 2k-1),
at the right edge (the last 2k lines), or after a free line r inside a gap between endpoint lines
(lines r+1 … r+2k). `plan` deletes blocks, on the x-axis first and then on the transposed
instance, until both sides are at most 10 or no block is left. `lift_all` puts the blocks back
into a solution of the last instance. Each lift is one pass over the paths.
"""
from .grid import Instance, ends


def _sub(a, b):
    """Natural-number subtraction, as in Lean (never negative)."""
    return a - b if a > b else 0


def _xs(I):
    return [e[0] for e in ends(I)]


def left_k(I):
    return min(_sub(min(_xs(I)), 2) // 2, _sub(I.R, 11) // 2)


def right_k(I):
    return min(_sub(_sub(I.R, 3), max(_xs(I))) // 2, _sub(I.R, 11) // 2)


def inner_k(I, a, b):
    return min(_sub(_sub(b, a), 9) // 2, _sub(I.R, 11) // 2)


def _gap_ok(I, a, b):
    xs = _xs(I)
    return a < b and all(not (a < x < b) for x in xs) and inner_k(I, a, b) >= 1


def inner_pair(I):
    xs = _xs(I)
    for a in xs:
        for b in xs:
            if _gap_ok(I, a, b):
                return a, b
    return None


def blk_x(I):
    """The block to delete on the x-axis: ("left", k), ("right", k), ("inner", r, k), or None."""
    k = left_k(I)
    if k >= 1:
        return ("left", k)
    k = right_k(I)
    if k >= 1:
        return ("right", k)
    ab = inner_pair(I)
    if ab is not None:
        a, b = ab
        return ("inner", a + 1, inner_k(I, a, b))
    return None


def _map_ends(I, R, f):
    return Instance(R, I.C, f(I.s0), f(I.t0), f(I.s1), f(I.t1))


def delete(blk, I):
    """`Blk.del`: the instance with the block deleted."""
    if blk[0] == "left":
        m = 2 * blk[1]
        return _map_ends(I, I.R - m, lambda v: (v[0] - m, v[1]))
    if blk[0] == "right":
        m = 2 * blk[1]
        return _map_ends(I, I.R - m, lambda v: v)
    r, m = blk[1], 2 * blk[2]
    return _map_ends(I, I.R - m, lambda v: v if v[0] <= r else (v[0] - m, v[1]))


def transpose(I):
    sw = lambda v: (v[1], v[0])
    return Instance(I.C, I.R, sw(I.s0), sw(I.t0), sw(I.s1), sw(I.t1))


# --- edge blocks (EdgeBlock.lean) ---------------------------------------------------------

def col_snake(x, A, k):
    """`colSnake`: k pairs of lines from x; the first of each pair walks A, the second walks it
    back."""
    out = []
    Ar = A[::-1]
    for i in range(k):
        out.extend((x + 2 * i, y) for y in A)
        out.extend((x + 2 * i + 1, y) for y in Ar)
    return out


def edge_block(w, h, y, k):
    """`edgeBlock`: the lines w … w + 2k - 1, from (w, y) to (w, y + 1)."""
    down = list(range(y, -1, -1))
    up = list(range(y + 1, h))
    return col_snake(w, down, k) + col_snake(w, up, k)[::-1]


def _find_v(x, L):
    """`findV`: the index i of the first step L[i], L[i+1] along the line x, or None."""
    for i in range(len(L) - 1):
        u, v = L[i], L[i + 1]
        if u[0] == x and v[0] == x and abs(u[1] - v[1]) == 1:
            return i
    return None


def _blk_e(w, h, k, a, b):
    return edge_block(w, h, a[1], k) if a[1] < b[1] else edge_block(w, h, b[1], k)[::-1]


def edge_lift(w, h, k, p, q):
    """`edgeLift`: splice the block of the new lines w … w + 2k - 1 into the first step along the
    line w - 1, of p if it has one, else of q."""
    i = _find_v(w - 1, p)
    if i is not None:
        return p[:i + 1] + _blk_e(w, h, k, p[i], p[i + 1]) + p[i + 1:], q
    i = _find_v(w - 1, q)
    if i is not None:
        return p, q[:i + 1] + _blk_e(w, h, k, q[i], q[i + 1]) + q[i + 1:]
    return p, q


def edge_lift_l(w, h, k, p, q):
    """`edgeLiftL`: reflect, lift at the right edge, reflect back."""
    rf = lambda W: (lambda v: (W - 1 - v[0], v[1]))
    f, g = rf(w), rf(w + 2 * k)
    p2, q2 = edge_lift(w, h, k, [f(v) for v in p], [f(v) for v in q])
    return [g(v) for v in p2], [g(v) for v in q2]


# --- the inner block: the wide band (Round.lean, WideBand.lean) ----------------------------

def seed_w(h, p, q, r):
    """`seedW`: (R, flip, cross), where R is the first row in 0 … h satisfying `SeedAt`, flip the
    flag of `seedW`, and cross the set of rows y where a path steps between lines r and r + 1
    (`Cross`)."""

    # The rows where a path steps between lines r and r + 1, and the rows y >= 1 where a path
    # steps between (r, y - 1) and (r, y).
    #
    cross, vert = set(), set()
    for L in (p, q):
        for i in range(len(L) - 1):
            u, v = L[i], L[i + 1]
            if u[1] == v[1] and {u[0], v[0]} == {r, r + 1}:
                cross.add(u[1])
            elif u[0] == r and v[0] == r and abs(u[1] - v[1]) == 1:
                vert.add(max(u[1], v[1]))
    for R in range(h + 1):
        a = ((R == 0 or (R - 1) in cross) and (R == h or R in cross))
        b = (1 <= R < h and (R - 1) not in cross and R not in cross and R in vert)
        if a or b:
            return R, not a, cross
    return 0, False, cross


def inner_lift(J, r, k, p, q):
    """`innerLift`: insert 2k lines after line r of J, with the seed row and flip of `seedW`."""
    h = J.C
    R, flip, cross = seed_w(h, p, q, r)

    def cv(y):
        return (y in cross) or (flip and (y + 1 == R or y == R))

    def grp(a):
        out = [a]
        if a < R:
            y = a - 1
            while y >= 0 and not cv(y):
                out.append(y)
                y -= 1
        else:
            y = a + 1
            while y < h and not cv(y):
                out.append(y)
                y += 1
        return out

    W = 2 * k
    sn = lambda a: col_snake(r + 1, grp(a), k)
    flip_w = (sn(R - 1) + sn(R)[::-1]) if flip else None

    def gw(u, v):
        if u[0] == r and v[0] == r + W + 1 and u[1] == v[1]:
            return sn(u[1])
        if u[0] == r + W + 1 and v[0] == r and u[1] == v[1]:
            return sn(u[1])[::-1]
        if flip and u == (r, R - 1) and v == (r, R):
            return flip_w
        if flip and u == (r, R) and v == (r, R - 1):
            return flip_w[::-1]
        return ()

    def wide_ext(L):
        S = [v if v[0] <= r else (v[0] + W, v[1]) for v in L]
        out = []
        for i in range(len(S) - 1):
            out.append(S[i])
            out.extend(gw(S[i], S[i + 1]))
        if S:
            out.append(S[-1])
        return out

    return wide_ext(p), wide_ext(q)


def lift(blk, J, p, q):
    """`Blk.lift`: put the block back into a solution p, q of the reduced instance J."""
    if blk[0] == "left":
        return edge_lift_l(J.R, J.C, blk[1], p, q)
    if blk[0] == "right":
        return edge_lift(J.R, J.C, blk[1], p, q)
    return inner_lift(J, blk[1], blk[2], p, q)


# --- the recursion of solveR --------------------------------------------------------------

def plan(I):
    """Delete blocks as `solveR` does. Returns (leaf, steps): `leaf` is the last instance, and each
    step (blk, J, tr) deleted `blk` from the previous instance (transposed first when tr), giving
    J. After a transposed step the recursion continues in the transposed frame, as in Lean."""
    steps = []
    while I.R > 10 and I.C > 10:
        b = blk_x(I)
        if b is not None:
            J = delete(b, I)
            steps.append((b, J, False))
            I = J
            continue
        T = transpose(I)
        b = blk_x(T)
        if b is not None:
            J = delete(b, T)
            steps.append((b, J, True))
            I = J
            continue
        break
    return I, steps


def lift_all(steps, p, q):
    """Lift a solution of the leaf of `plan` back to a solution of the first instance."""
    for b, J, tr in reversed(steps):
        p, q = lift(b, J, p, q)
        if tr:
            p = [(c, r) for r, c in p]
            q = [(c, r) for r, c in q]
    return p, q

# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""The plug DP: exact solver for a grid with one or two coloured paths.

Cells are processed column by column, top to bottom within a column (the grid is transposed first
so that columns are the short side). The state is the frontier: one slot per row plus one for the
plug leaving the current cell downwards. Each slot is 3 bits:
    0 empty, 1/2 anchor of colour 0/1 (a path piece ending at an endpoint),
    3/4 open/close bracket of colour 0, 5/6 open/close bracket of colour 1
(a path piece with both ends on the frontier is an open/close bracket pair).

`solve_paths(R, C, terms)` returns, for each colour present in `terms` (a list of
((r, c), colour)), the path between its two endpoints, or None if there is no covering by
disjoint paths. A forward pass keeps one checkpoint of states per column; a backward pass re-runs
each column from its checkpoint, keeping predecessors, to recover the chosen edges. Checkpoint
states are visited in increasing order and predecessors are the first found, so the result is
deterministic (the JavaScript and C versions return the same paths).
See docs/PLUGDP.md.
"""

EM, A0, A1, O0, C0, O1, C1 = range(7)


def _gv(s, i):
    return (s >> (3 * i)) & 7


def _sv(s, i, v):
    return (s & ~(7 << (3 * i))) | (v << (3 * i))


def _is_anchor(v):
    return v == A0 or v == A1


def _is_open(v):
    return v == O0 or v == O1


def _is_close(v):
    return v == C0 or v == C1


def _color(v):
    return v - 1 if _is_anchor(v) else (v - 3) >> 1


def _partner(s, i, n):
    v, depth = _gv(s, i), 0
    if _is_open(v):
        for j in range(i + 1, n):
            w = _gv(s, j)
            if _is_open(w):
                depth += 1
            elif _is_close(w):
                if depth == 0:
                    return j
                depth -= 1
    else:
        for j in range(i - 1, -1, -1):
            w = _gv(s, j)
            if _is_close(w):
                depth += 1
            elif _is_open(w):
                if depth == 0:
                    return j
                depth -= 1
    return -1


def _step(s, r, n, tc, can_right, can_down, ncol):
    """Successor states after processing the cell in row r (tc: endpoint colour or -1)."""
    out = []
    budget = 1 if tc >= 0 else 2
    navail = int(can_right) + int(can_down)
    up, lf = _gv(s, r), _gv(s, r + 1)
    have = (up != EM) + (lf != EM)
    if have > budget:
        return out
    need = budget - have
    if need > navail:
        return out
    base = _sv(_sv(s, r, EM), r + 1, EM)
    if have == 0:
        if tc >= 0:
            v = 1 + tc
            if can_right:
                out.append(_sv(base, r, v))
            if can_down:
                out.append(_sv(base, r + 1, v))
        else:
            for col in range(ncol):
                out.append(_sv(_sv(base, r, 3 + 2 * col), r + 1, 4 + 2 * col))
    elif have == 1:
        p = up if up != EM else lf
        pos = r if up != EM else r + 1
        pc = _color(p)
        if need == 0:
            if pc != tc:
                return out
            if _is_anchor(p):
                out.append(base)
            else:
                out.append(_sv(base, _partner(s, pos, n), 1 + pc))
        else:
            if can_right:
                out.append(_sv(base, r, p))
            if can_down:
                out.append(_sv(base, r + 1, p))
    else:
        col = _color(up)
        if col != _color(lf):
            return out
        if _is_anchor(up) and _is_anchor(lf):
            out.append(base)
        elif _is_anchor(up) or _is_anchor(lf):
            bpos = r + 1 if _is_anchor(up) else r
            out.append(_sv(base, _partner(s, bpos, n), 1 + col))
        elif _is_open(up) and _is_close(lf):
            return out
        elif _is_close(up) and _is_open(lf):
            out.append(base)
        elif _is_open(up):
            out.append(_sv(base, _partner(s, r + 1, n), 3 + 2 * col))
        else:
            out.append(_sv(base, _partner(s, r, n), 4 + 2 * col))
    return out


def parity_ok(R, C, terms):
    """Necessary for any covering by paths: the endpoint signs (+1 on cells with r + c even,
    -1 otherwise) sum to 2 (R C mod 2). Each path's cells alternate in sign, so a path's sign sum
    is half its two endpoints' signs; the whole grid sums to R C mod 2."""
    return sum(1 if (r + c) % 2 == 0 else -1 for (r, c), _ in terms) == 2 * ((R * C) % 2)


def solve_paths(R, C, terms):
    """terms: list of ((r, c), colour) with two endpoints per colour present (colours 0, 1).
    Returns {colour: path} or None."""
    cols = sorted(set(col for _, col in terms))
    if any(sum(1 for _, c in terms if c == col) != 2 for col in cols) or not cols:
        raise ValueError("each colour needs exactly two endpoints")
    if not parity_ok(R, C, terms):
        return None
    ncol = max(cols) + 1
    transposed = R > C
    if transposed:
        R, C = C, R
        terms = [((c, r), col) for (r, c), col in terms]
    term = {}
    for x, col in terms:
        term[x] = col
    n = R + 1
    mask = (1 << (3 * n)) - 1
    ckpt = []
    cur = {0}
    for c in range(C):
        if c > 0:
            cur = {(s << 3) & mask for s in cur}
        ckpt.append(sorted(cur))
        for r in range(R):
            tc = term.get((r, c), -1)
            nxt = set()
            for s in cur:
                nxt.update(_step(s, r, n, tc, c < C - 1, r < R - 1, ncol))
            cur = nxt
            if not cur:
                return None
    if 0 not in cur:
        return None
    # backward pass: per column, re-run from the checkpoint, keep predecessors, prune by target
    sig = lambda v: 0 if v == EM else 1 + _color(v)
    right = {}
    down = {}
    target = 0
    for c in range(C - 1, -1, -1):
        layers = [dict.fromkeys(ckpt[c])]
        for r in range(R):
            tc = term.get((r, c), -1)
            nxt = {}
            for s in layers[r]:
                for t in _step(s, r, n, tc, c < C - 1, r < R - 1, ncol):
                    if t in nxt:
                        continue
                    if all(sig(_gv(t, j)) == sig(_gv(target, j)) for j in range(r + 1)):
                        nxt[t] = s
            layers.append(nxt)
        s = target
        if s not in layers[R]:
            raise RuntimeError("plug DP: backward pass lost the target")
        for r in range(R, 0, -1):
            ru, dn = _gv(s, r - 1), _gv(s, r)
            if ru != EM:
                right[(r - 1, c)] = _color(ru)
            if dn != EM:
                down[(r - 1, c)] = _color(dn)
            s = layers[r][s]
        target = s >> 3
    # walk the chosen edges
    out = {}
    for col in cols:
        a, b = [x for x, cc in terms if cc == col]
        path, prev, x = [a], None, a
        while x != b:
            r, c = x
            cand = []
            if right.get((r, c)) == col:
                cand.append((r, c + 1))
            if down.get((r, c)) == col:
                cand.append((r + 1, c))
            if c > 0 and right.get((r, c - 1)) == col:
                cand.append((r, c - 1))
            if r > 0 and down.get((r - 1, c)) == col:
                cand.append((r - 1, c))
            nxt = [y for y in cand if y != prev]
            if not nxt:
                raise RuntimeError("plug DP: broken path")
            prev, x = x, nxt[0]
            path.append(x)
        out[col] = [(cc, rr) for rr, cc in path] if transposed else path
    return out


def solvable_paths(R, C, terms):
    """Forward pass only: is there a covering by disjoint paths?"""
    if not parity_ok(R, C, terms):
        return False
    cols = sorted(set(col for _, col in terms))
    ncol = max(cols) + 1
    if R > C:
        R, C = C, R
        terms = [((c, r), col) for (r, c), col in terms]
    term = {x: col for x, col in terms}
    n = R + 1
    mask = (1 << (3 * n)) - 1
    cur = {0}
    for c in range(C):
        if c > 0:
            cur = {(s << 3) & mask for s in cur}
        for r in range(R):
            tc = term.get((r, c), -1)
            nxt = set()
            for s in cur:
                nxt.update(_step(s, r, n, tc, c < C - 1, r < R - 1, ncol))
            cur = nxt
            if not cur:
                return False
    return 0 in cur


def solve_instance(inst):
    """Both paths of a two-colour instance, or None."""
    res = solve_paths(inst.R, inst.C, [(inst.s0, 0), (inst.t0, 0), (inst.s1, 1), (inst.t1, 1)])
    if res is None:
        return None
    return (res[0], res[1])

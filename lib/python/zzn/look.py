# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Irreducible leaves by certificate lookup: the Lean leaf solver `lookJ tabAll`.

A transcription of `proof/ZZN/Look/Leaf.lean` (`entryP`, `sameX`, `lookK`, `argminS`, `lookLe`,
`lookJ`) and of what it calls: the symmetries (`Sym`, `Sym.geo`, `Sym.lab`, `Sym.apply` in
`proof/ZZN/Moves.lean`; `unLab`, `unRy`, `unGeo`, `unSym` in `proof/ZZN/Look/Sym.lean`), the
canonical form (`rowsOf`, `colsOf`, `key2`, `G32`, `Gbox` in `proof/ZZN/BoxK/Box.lean`, `keyR`,
`idx`, `allSym`), the templates and their checker (`proof/ZZN/Cut/Template.lean`,
`proof/ZZN/Cut/Tree.lean`, `accB` in `proof/ZZN/Cut/LaneV.lean`), the solution builder
(`proof/ZZN/Look/Build.lean`), the constructive IPS path (`ipsP`, `proof/ZZN/Look/IPS.lean`, with
`primeLookup` and the helpers of `proof/GridHam/`) and the stored paths (`decPath`, `solF`,
`proof/ZZN/Cut/SolF.lean`). The choices are the same as in Lean: the same canonical symmetry, the
same slice, the same first template that checks, the same stored-path fallback, the same pull-back.

The table `tabAll` (`proof/ZZN/Look/Table.lean`) is read lazily from `lib/data/look.json.gz`,
written by `lib/tools/export_look.py` from the Lean sources (its docstring gives the format).

Lean's cell (x, y) on a w x h grid is the library's (r, c) on an R x C grid: x = r, w = R, y = c,
h = C. A symmetry σ is a tuple of six bools (tr, rx, ry, r0, r1, sw), the field order of `Sym`.
A template is in the exported form: 0 for `CTree.leaf`, [vert, a, o, kinds, L, R] for a cut.
An instantiated tree (`CTree ℕ`) is None for a leaf and (vert, pos, kinds, L, R) for a cut, with
kinds ("stay", s), ("cross", s, y), ("exc", s, y, z). A piece is (ox, oy, pw, ph, segs); a path
segment `Seg` is (a, b, p).
"""
import gzip
import json
import os

from .grid import Instance

DATA = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                    "data", "look.json.gz")

_DATA = None


def _sub(a, b):
    """Natural-number subtraction, as in Lean (never negative)."""
    return a - b if a > b else 0


def data():
    """The exported table: {"templates", "boxes", "prime", "rows"} (loaded once). "rows" maps
    (w, h) to {row tuple: index of its first slice}."""
    global _DATA
    if _DATA is None:
        with gzip.open(DATA, "rb") as f:
            d = json.loads(f.read().decode())
        if d.get("format") != "zzn-look-1":
            raise ValueError("unknown look data format")
        boxes = {}
        rows = {}
        for k, sl in d["boxes"].items():
            w, h = (int(x) for x in k.split("x"))
            boxes[(w, h)] = sl
            first = {}
            for i, s in enumerate(sl):
                first.setdefault(tuple(s[0]), i)
            rows[(w, h)] = first
        prime = [(w, h, [((e[0], e[1]), (e[2], e[3]), [(e[4][i], e[4][i + 1])
                                                         for i in range(0, len(e[4]), 2)])
                         for e in es])
                 for w, h, es in d["prime"]]
        _DATA = {"templates": d["templates"], "boxes": boxes, "prime": prime, "rows": rows}
    return _DATA


def template(n):
    """The Lean template `tN` (`proof/BoxKGen/Templates*.lean`), in the exported form."""
    return data()["templates"][n]


# --- symmetries ------------------------------------------------------------------------------

def transpose(I):
    """`Inst.transpose` (`proof/ZZN/Statement.lean:484`)."""
    sw = lambda v: (v[1], v[0])
    return Instance(I.C, I.R, sw(I.s0), sw(I.t0), sw(I.s1), sw(I.t1))


def refl_x(w, v):
    """`reflX` (`proof/ZZN/Symmetry.lean:79`) and `GridHam.reflectX`: x -> w - 1 - x."""
    return (_sub(_sub(w, 1), v[0]), v[1])


def reflect_x(I):
    """`Inst.reflectX` (`proof/ZZN/Symmetry.lean:81`)."""
    f = lambda v: refl_x(I.R, v)
    return Instance(I.R, I.C, f(I.s0), f(I.t0), f(I.s1), f(I.t1))


def reflect_y(I):
    """`Inst.reflectY = I.transpose.reflectX.transpose` (`proof/ZZN/Moves.lean:120`)."""
    return transpose(reflect_x(transpose(I)))


def rev0(I):
    """`Inst.rev0` (`proof/ZZN/Moves.lean:101`)."""
    return Instance(I.R, I.C, I.t0, I.s0, I.s1, I.t1)


def rev1(I):
    """`Inst.rev1` (`proof/ZZN/Moves.lean:98`)."""
    return Instance(I.R, I.C, I.s0, I.t0, I.t1, I.s1)


def swap_colors(I):
    """`Inst.swapColors` (`proof/ZZN/Glue.lean:105`)."""
    return Instance(I.R, I.C, I.s1, I.t1, I.s0, I.t0)


def sym_of_int(k):
    """The symmetry with index k in `allSym`: bits 32 tr, 16 rx, 8 ry, 4 r0, 2 r1, 1 sw."""
    return tuple(bool((k >> (5 - i)) & 1) for i in range(6))


def sym_to_int(sigma):
    k = 0
    for b in sigma:
        k = 2 * k + (1 if b else 0)
    return k


SYM_ID = (False,) * 6

# `allSym` (`proof/ZZN/Orbit.lean:196`): nested flatMaps over tr, rx, ry, r0, r1, sw, false first.
ALL_SYM = [sym_of_int(k) for k in range(64)]

# `G32` (`proof/ZZN/BoxK/Box.lean:31`): the symmetries without transposition.
G32 = [s for s in ALL_SYM if not s[0]]


def gbox(w, h):
    """`Gbox` (`proof/ZZN/BoxK/Box.lean:54`): all 64 symmetries on a square box, else `G32`."""
    return ALL_SYM if w == h else G32


def sym_geo(sigma, I):
    """`Sym.geo` (`proof/ZZN/Moves.lean:182`): transpose, reflect x, reflect y."""
    tr, rx, ry = sigma[0], sigma[1], sigma[2]
    I1 = transpose(I) if tr else I
    I2 = reflect_x(I1) if rx else I1
    return reflect_y(I2) if ry else I2


def sym_lab(sigma, I):
    """`Sym.lab` (`proof/ZZN/Moves.lean:188`): reverse path 0, reverse path 1, swap colours."""
    r0, r1, sw = sigma[3], sigma[4], sigma[5]
    I3 = rev0(I) if r0 else I
    I4 = rev1(I3) if r1 else I3
    return swap_colors(I4) if sw else I4


def apply_sym(sigma, I):
    """`Sym.apply σ I = σ.lab (σ.geo I)` (`proof/ZZN/Moves.lean:193`)."""
    return sym_lab(sigma, sym_geo(sigma, I))


def un_lab(sigma, s):
    """`unLab` (`proof/ZZN/Look/Sym.lean:77`)."""
    s1 = (s[1], s[0]) if sigma[5] else s
    s2 = (s1[0], s1[1][::-1]) if sigma[4] else s1
    return (s2[0][::-1], s2[1]) if sigma[3] else s2


def un_ry(hh, p):
    """`unRy` (`proof/ZZN/Look/Sym.lean:103`): swap, reflX hh, swap."""
    out = []
    for v in p:
        u = refl_x(hh, (v[1], v[0]))
        out.append((u[1], u[0]))
    return out


def un_geo(sigma, J, s):
    """`unGeo` (`proof/ZZN/Look/Sym.lean:116`)."""
    tr, rx, ry = sigma[0], sigma[1], sigma[2]
    I1 = transpose(J) if tr else J
    I2 = reflect_x(I1) if rx else I1
    s4 = (un_ry(I2.C, s[0]), un_ry(I2.C, s[1])) if ry else s
    if rx:
        s5 = ([refl_x(I1.R, v) for v in s4[0]], [refl_x(I1.R, v) for v in s4[1]])
    else:
        s5 = s4
    if tr:
        return ([(v[1], v[0]) for v in s5[0]], [(v[1], v[0]) for v in s5[1]])
    return s5


def un_sym(sigma, J, s):
    """`unSym σ J s = unGeo σ J (unLab σ s)` (`proof/ZZN/Look/Sym.lean:137`): from a solution of
    `σ.apply J`, one of J."""
    return un_geo(sigma, J, un_lab(sigma, s))


# --- canonical form --------------------------------------------------------------------------

def rows_of(I):
    """`rowsOf` (`proof/ZZN/BoxK/Box.lean:25`): the x-coordinates of s0 t0 s1 t1."""
    return (I.s0[0], I.t0[0], I.s1[0], I.t1[0])


def cols_of(I):
    """`colsOf` (`proof/ZZN/BoxK/Box.lean:26`): the y-coordinates of s0 t0 s1 t1."""
    return (I.s0[1], I.t0[1], I.s1[1], I.t1[1])


def key_r(x):
    """`keyR` (`proof/ZZN/BoxK/Slice.lean:191`)."""
    return ((x[0] * 32 + x[1]) * 32 + x[2]) * 32 + x[3]


def key2(K):
    """`key2` (`proof/ZZN/BoxK/Box.lean:94`): rows first, then columns."""
    return key_r(rows_of(K)) * 2 ** 20 + key_r(cols_of(K))


def idx(w, x):
    """`idx` (`proof/ZZN/BoxK/Rows.lean:53`)."""
    return ((x[0] * w + x[1]) * w + x[2]) * w + x[3]


def argmin_s(f, syms):
    """`argminS` (`proof/ZZN/Look/Leaf.lean:102`): the first element of least f; `Sym.id` on []."""
    if not syms:
        return SYM_ID
    b = syms[0]
    fb = f(b)
    for c in syms[1:]:
        fc = f(c)
        if fc < fb:
            b, fb = c, fc
    return b


def canon_sym(J):
    """The symmetry `lookLe` chooses: `argminS (fun σ => key2 (σ.apply J)) (Gbox J.w J.h)`."""
    return argmin_s(lambda s: key2(apply_sym(s, J)), gbox(J.R, J.C))


# --- templates and the cut-tree checker ------------------------------------------------------

def off_n(a, o):
    """`offN` (`proof/ZZN/Cut/Template.lean:30`): a + o, truncated at 0."""
    return a + o if o >= 0 else _sub(a, -o)


def anchors(e, n, a):
    """`anchors` (`proof/ZZN/Cut/Template.lean:62`): 0-3 the endpoints, 4 zero, otherwise n."""
    if a <= 3:
        return e[a]
    return 0 if a == 4 else n


def pos_n(e, n, p):
    """`posN` (`proof/ZZN/Cut/Template.lean:66`)."""
    return off_n(anchors(e, n, p[0]), p[1])


def inst_k(f, k):
    """`instK` (`proof/ZZN/Cut/Template.lean:38`), on an exported kind."""
    if len(k) == 1:
        return ("stay", bool(k[0]))
    if len(k) == 3:
        return ("cross", bool(k[0]), f((k[1], k[2])))
    return ("exc", bool(k[0]), f((k[1], k[2])), f((k[3], k[4])))


def inst(fR, fC, T):
    """`inst` (`proof/ZZN/Cut/Template.lean:44`): positions on the cut's axis, crossings on the
    other."""
    if T == 0:
        return None
    vert, a, o, ks, left, right = T
    vert = bool(vert)
    pos = fC((a, o)) if vert else fR((a, o))
    g = fR if vert else fC
    return (vert, pos, [inst_k(g, k) for k in ks], inst(fR, fC, left), inst(fR, fC, right))


def inst_of(T, I):
    """The instantiated tree of `tcheck` and `tsol`."""
    er, ec = rows_of(I), cols_of(I)
    return inst(lambda p: pos_n(er, I.R, p), lambda p: pos_n(ec, I.C, p), T)


def cutc(vert, pos, s, y):
    """`cutc` (`proof/ZZN/Cut/Tree.lean:72`): the crossing cell at y along the cut, on side s."""
    x = pos if s else _sub(pos, 1)
    return (y, x) if vert else (x, y)


def put(s, e, LR):
    """`put` (`proof/ZZN/Cut/Tree.lean:77`): append e to side s."""
    return (LR[0], LR[1] + [e]) if s else (LR[0] + [e], LR[1])


def split(vert, pos, ks, ss, acc):
    """`split` (`proof/ZZN/Cut/Tree.lean:81`), or None."""
    if len(ks) != len(ss):
        return None
    for k, (a, b) in zip(ks, ss):
        s = k[1]
        if k[0] == "stay":
            acc = put(s, (a, b), acc)
        elif k[0] == "cross":
            y = k[2]
            acc = put(not s, (cutc(vert, pos, not s, y), b), put(s, (a, cutc(vert, pos, s, y)), acc))
        else:
            y, z = k[2], k[3]
            acc = put(not s, (cutc(vert, pos, not s, y), cutc(vert, pos, not s, z)),
                      put(s, (cutc(vert, pos, s, z), b), put(s, (a, cutc(vert, pos, s, y)), acc)))
    return acc


def piece_lo(P, vert, pos, L):
    """`Piece.lo` (`proof/ZZN/Cut/Tree.lean:95`)."""
    ox, oy, pw, ph, _ = P
    return (ox, oy, pw, _sub(pos, oy), L) if vert else (ox, oy, _sub(pos, ox), ph, L)


def piece_hi(P, vert, pos, R):
    """`Piece.hi` (`proof/ZZN/Cut/Tree.lean:98`)."""
    ox, oy, pw, ph, _ = P
    if vert:
        return (ox, pos, pw, _sub(oy + ph, pos), R)
    return (pos, oy, _sub(ox + pw, pos), ph, R)


def inside(vert, pos, P):
    """`inside` (`proof/ZZN/Cut/Tree.lean:101`)."""
    ox, oy, pw, ph, _ = P
    return (oy < pos < oy + ph) if vert else (ox < pos < ox + pw)


def region_b(P, v):
    """`Piece.regionB` (`proof/ZZN/Cut/Tree.lean:105`)."""
    ox, oy, pw, ph, _ = P
    return ox <= v[0] < ox + pw and oy <= v[1] < oy + ph


def acc_b(w, h, s, t):
    """`Lane.accB` (`proof/ZZN/Cut/LaneV.lean:336`): IPS acceptability, as written there."""
    ps = (s[0] + s[1]) % 2 == 1
    pt = (t[0] + t[1]) % 2 == 1
    ow = w % 2 == 1
    oh = h % 2 == 1
    cc = (not ps and not pt) if (ow and oh) else (ps != pt)
    w1, h1 = _sub(w, 1), _sub(h, 1)

    def corner(v):
        return (v[0] == 0 or v[0] == w1) and (v[1] == 0 or v[1] == h1)

    isW1 = w == 1
    fx = 0 if isW1 else w1
    fy = h1 if isW1 else 0
    f1 = not ((s[0] == 0 and s[1] == 0 and t[0] == fx and t[1] == fy) or
              (s[0] == fx and s[1] == fy and t[0] == 0 and t[1] == 0))
    f2 = (not corner(s) and not corner(t) and
          ((w == 2 and s[1] == t[1]) or (h == 2 and s[0] == t[0])))
    isW3 = w == 3
    opp_odd = oh if isW3 else ow
    c0 = s[1] if isW3 else s[0]
    c1 = t[1] if isW3 else t[0]
    oc = s[0] if isW3 else s[1]
    gr = c1 < c0
    dist = _sub(c0, c1) if gr else _sub(c1, c0)
    dsat = (0 < dist) if oc == 1 else (1 < dist)
    f3 = not opp_odd and (ps != pt) and dsat and ((gr and not ps) or (not gr and ps))
    if w == 1 or h == 1:
        forb = f1
    elif w == 2 or h == 2:
        forb = f2
    elif w == 3 or h == 3:
        forb = f3
    else:
        forb = False
    return cc and not forb


def leaf_ok(P):
    """`leafOK` (`proof/ZZN/Cut/Tree.lean:117`): one pair, a single cell or an IPS-acceptable
    rectangle."""
    ox, oy, pw, ph, segs = P
    if len(segs) != 1:
        return False
    a, b = segs[0]
    if a == b:
        return pw == 1 and ph == 1 and a == (ox, oy)
    return (region_b(P, a) and region_b(P, b) and
            acc_b(pw, ph, (_sub(a[0], ox), _sub(a[1], oy)), (_sub(b[0], ox), _sub(b[1], oy))))


def check(T, P):
    """`check` (`proof/ZZN/Cut/Tree.lean:125`), on an instantiated tree."""
    if T is None:
        return leaf_ok(P)
    vert, pos, ks, left, right = T
    if not inside(vert, pos, P):
        return False
    sp = split(vert, pos, ks, P[4], ([], []))
    if sp is None:
        return False
    L, R = sp
    return check(left, piece_lo(P, vert, pos, L)) and check(right, piece_hi(P, vert, pos, R))


def root_piece(I):
    """`rootPiece` (`proof/ZZN/Cut/Tree.lean:291`)."""
    return (0, 0, I.R, I.C, [(I.s0, I.t0), (I.s1, I.t1)])


def tcheck(T, I):
    """`tcheck` (`proof/ZZN/Cut/Template.lean:68`): the instantiated template checks on I."""
    return check(inst_of(T, I), root_piece(I))


# --- building the solution of a checked template ---------------------------------------------

def join_l(a, u, v, b, ps):
    """`joinL` (`proof/ZZN/Look/Build.lean:54`): join the segments a -> u and v -> b."""
    i = next((i for i, x in enumerate(ps) if (x[0], x[1]) == (a, u)), None)
    if i is None:
        return ps

    # `List.erase` removes the first element equal to x; that is x itself, the first with its
    # ends. Likewise for y in the rest.
    #
    x = ps[i]
    rest = ps[:i] + ps[i + 1:]
    j = next((j for j, y in enumerate(rest) if (y[0], y[1]) == (v, b)), None)
    if j is None:
        return ps
    y = rest[j]
    return [(a, b, x[2] + y[2])] + rest[:j] + rest[j + 1:]


def unsplit(vert, pos, ks, ss, acc, ps):
    """`unsplit` (`proof/ZZN/Look/Build.lean:145`): join the segments across a cut, the last
    pair first."""
    if not ks:
        return ps
    if not ss:
        return ps
    k, (a, b) = ks[0], ss[0]
    s = k[1]
    if k[0] == "stay":
        return unsplit(vert, pos, ks[1:], ss[1:], put(s, (a, b), acc), ps)
    if k[0] == "cross":
        y = k[2]
        acc2 = put(not s, (cutc(vert, pos, not s, y), b), put(s, (a, cutc(vert, pos, s, y)), acc))
        return join_l(a, cutc(vert, pos, s, y), cutc(vert, pos, not s, y), b,
                      unsplit(vert, pos, ks[1:], ss[1:], acc2, ps))
    y, z = k[2], k[3]
    acc2 = put(not s, (cutc(vert, pos, not s, y), cutc(vert, pos, not s, z)),
               put(s, (cutc(vert, pos, s, z), b), put(s, (a, cutc(vert, pos, s, y)), acc)))
    inner = join_l(a, cutc(vert, pos, s, y), cutc(vert, pos, not s, y), cutc(vert, pos, not s, z),
                   unsplit(vert, pos, ks[1:], ss[1:], acc2, ps))
    return join_l(a, cutc(vert, pos, not s, z), cutc(vert, pos, s, z), b, inner)


def leaf_p(P):
    """`leafP` (`proof/ZZN/Look/Build.lean:229`): the IPS path of a leaf, or its single cell."""
    ox, oy, pw, ph, segs = P
    if len(segs) != 1:
        return []
    a, b = segs[0]
    if a == b:
        return [(a, a, [a])]
    p = ips_p(pw + ph, pw, ph, (_sub(a[0], ox), _sub(a[1], oy)), (_sub(b[0], ox), _sub(b[1], oy)))
    return [(a, b, [(v[0] + ox, v[1] + oy) for v in p])]


def build_t(T, P):
    """`buildT` (`proof/ZZN/Look/Build.lean:237`), on an instantiated tree."""
    if T is None:
        return leaf_p(P)
    vert, pos, ks, left, right = T
    sp = split(vert, pos, ks, P[4], ([], []))
    if sp is None:
        return []
    L, R = sp
    return unsplit(vert, pos, ks, P[4], ([], []),
                   build_t(left, piece_lo(P, vert, pos, L)) + build_t(right, piece_hi(P, vert, pos, R)))


def sol_of(I, ps):
    """`solOf` (`proof/ZZN/Look/Build.lean:342`): the segments s0 -> t0 and s1 -> t1, or []."""
    p = next((x[2] for x in ps if (x[0], x[1]) == (I.s0, I.t0)), [])
    q = next((x[2] for x in ps if (x[0], x[1]) == (I.s1, I.t1)), [])
    return (p, q)


def tsol(T, I):
    """`tsol` (`proof/ZZN/Look/Build.lean:428`): the solution built from template T on I."""
    return sol_of(I, build_t(inst_of(T, I), root_piece(I)))


# --- the constructive IPS path ---------------------------------------------------------------

def col_seg(c, lo, k):
    """`colSeg` (`proof/GridHam/StripSplit.lean:476`): (c, lo + k), …, (c, lo)."""
    return [(c, lo + j) for j in range(k, -1, -1)]


def right_detour(w, h, y):
    """`rightDetour` (`proof/GridHam/StripSplit.lean:770`)."""
    return (col_seg(w, 0, y) + col_seg(w + 1, 0, _sub(h, 1))[::-1] +
            col_seg(w, y + 1, _sub(_sub(h, 1), y + 1)))


def col_edge(X, l):
    """`colEdge` (`proof/ZZN/Look/IPS.lean:202`): the first consecutive pair in column X."""
    for i in range(len(l) - 1):
        if l[i][0] == X and l[i + 1][0] == X:
            return (l[:i], l[i], l[i + 1], l[i + 2:])
    return None


def strip_right_p(width, height, p):
    """`stripRightP` (`proof/ZZN/Look/IPS.lean:246`)."""
    ce = col_edge(_sub(width, 3), p)
    if ce is None:
        return p
    l1, a, b, l2 = ce
    if b[1] == a[1] + 1:
        return l1 + [a] + right_detour(_sub(width, 2), height, a[1]) + [b] + l2
    return (l2[::-1] + [b] + right_detour(_sub(width, 2), height, b[1]) + [a] + l1[::-1])[::-1]


def strip_left_p(width, height, p):
    """`stripLeftP` (`proof/ZZN/Look/IPS.lean:330`): reflect, strip on the right, reflect back."""
    q = strip_right_p(width, height, [refl_x(_sub(width, 2), v) for v in p])
    return [refl_x(width, v) for v in q]


def not_prime(w, h):
    """`NotPrime` (`proof/GridHam/Reduction.lean:267`)."""
    return not ((w <= 3 and h <= 3) or (w == 4 and h == 4) or (w == 4 and h == 5) or
                (w == 5 and h == 4))


def r_choice(sx, sy, h):
    """`rChoice` (`proof/GridHam/Reduction.lean:400`)."""
    if (sx + sy) % 2 == 0:
        return 0
    if sx == 0 and sy == 1 and 1 < _sub(h, 1):
        return 3
    return 1


def prime_lookup(w, h, s, t):
    """`primeLookup` (`proof/GridHam/PrimeTable.lean:659`): the stored path, or []."""
    e = next((e for e in data()["prime"] if e[0] == w and e[1] == h), None)
    if e is None:
        return []
    x = next((x for x in e[2] if x[0] == s and x[1] == t), None)
    return [] if x is None else list(x[2])


def norm_p(f, w, h, s, t):
    """`normP` (`proof/ZZN/Look/IPS.lean:386`): one step for h <= w, s.x <= t.x."""
    if not_prime(w, h):
        if 2 <= s[0]:
            return strip_left_p(w, h, f(_sub(w, 2), h, (_sub(s[0], 2), s[1]), (_sub(t[0], 2), t[1])))
        if t[0] + 2 < w:
            return strip_right_p(w, h, f(_sub(w, 2), h, s, t))
        r = r_choice(s[0], s[1], h)
        return (f(2, h, s, (1, r)) +
                [(v[0] + 2, v[1]) for v in f(_sub(w, 2), h, (0, r), (_sub(t[0], 2), t[1]))])
    return prime_lookup(w, h, s, t)


def step_p(f, w, h, s, t):
    """`stepP` (`proof/ZZN/Look/IPS.lean:395`)."""
    if h <= w:
        return norm_p(f, w, h, s, t) if s[0] <= t[0] else norm_p(f, w, h, t, s)[::-1]
    sw = lambda v: (v[1], v[0])
    if s[1] <= t[1]:
        p = norm_p(f, h, w, sw(s), sw(t))
    else:
        p = norm_p(f, h, w, sw(t), sw(s))[::-1]
    return [sw(v) for v in p]


def ips_p(n, w, h, s, t):
    """`ipsP` (`proof/ZZN/Look/IPS.lean:402`): the IPS path with fuel n."""
    if n == 0:
        return []
    return step_p(lambda w2, h2, s2, t2: ips_p(n - 1, w2, h2, s2, t2), w, h, s, t)


# --- stored paths ----------------------------------------------------------------------------

def dec_path(n, code):
    """`decPath` (`proof/ZZN/Cut/SolF.lean:75`): byte k of code is the cell 16 * x + y."""
    out = []
    for k in range(n):
        b = (code >> (8 * k)) & 255
        out.append((b // 16, b % 16))
    return out


def chain_adjacent(p):
    """`chainAdjacent` (`proof/ZZN/Statement.lean:41`)."""
    return all(abs(p[i][0] - p[i + 1][0]) + abs(p[i][1] - p[i + 1][1]) == 1
               for i in range(len(p) - 1))


def mask_ok(w, h, vs):
    """`maskOK w h 0` (`proof/ZZN/Cut/SolF.lean:24`): in bounds, no cell twice."""
    seen = set()
    for v in vs:
        if not (v[0] < w and v[1] < h):
            return False
        k = v[0] * h + v[1]
        if k in seen:
            return False
        seen.add(k)
    return True


def sol_f(I, p, q):
    """`solF` (`proof/ZZN/Cut/SolF.lean:53`): p, q solve I."""
    return (len(p) > 0 and p[0] == I.s0 and p[-1] == I.t0 and chain_adjacent(p) and
            len(q) > 0 and q[0] == I.s1 and q[-1] == I.t1 and chain_adjacent(q) and
            mask_ok(I.R, I.C, p + q) and len(p) + len(q) == I.R * I.C)


# --- the lookup ------------------------------------------------------------------------------

def tab_all(w, h):
    """`tabAll` (`proof/ZZN/Look/Table.lean:64`): the slices of box w x h, [] unless
    11 <= w <= h <= 16."""
    if 11 <= w <= h <= 16:
        return data()["boxes"][(w, h)]
    return []


def entry_p(K, d):
    """`entryP` (`proof/ZZN/Look/Leaf.lean:46`): solve K from the slice d = [rows, pairs, sols].
    Returns ((p, q), how) with how = ("pair", i) or ("sol", i), or None."""
    pairs, sols = d[1], d[2]
    for i in range(0, len(pairs), 2):
        T, sigma = template(pairs[i]), sym_of_int(pairs[i + 1])
        J = apply_sym(sigma, K)
        if tcheck(T, J):
            return un_sym(sigma, K, tsol(T, J)), ("pair", i // 2)
    lane = idx(K.C, cols_of(K))
    for i, e in enumerate(sols):
        if e[0] == lane:
            p, q = dec_path(e[1], e[2]), dec_path(e[3], e[4])
            if sol_f(K, p, q):
                return (p, q), ("sol", i)
    return None


def look_k(K, trace=None):
    """`lookK tabAll` (`proof/ZZN/Look/Leaf.lean:96`): the first slice with K's rows (`sameX`)."""
    if 11 <= K.R <= K.C <= 16:
        i = data()["rows"][(K.R, K.C)].get(rows_of(K))
    else:
        i = None
    if i is None:
        return None
    r = entry_p(K, tab_all(K.R, K.C)[i])
    if r is None:
        return None
    if trace is not None:
        trace["slice"] = i
        trace["entry"] = r[1]
    return r[0]


def look_le(J, trace=None):
    """`lookLe tabAll` (`proof/ZZN/Look/Leaf.lean:136`): canonical form, table, pull back."""
    sigma = canon_sym(J)
    if trace is not None:
        trace["sym"] = sigma
    s = look_k(apply_sym(sigma, J), trace)
    return None if s is None else un_sym(sigma, J, s)


def look_j(I, trace=None):
    """`lookJ tabAll` (`proof/ZZN/Look/Leaf.lean:141`): a solution (p, q) of I or None. On a
    well-formed passing instance with sides 11-16 and no reduction on either axis it answers
    (`lookJ_complete`); every answer is a solution (`lookJ_sound`). If `trace` is a dict, it
    receives the chosen symmetry, slice index and entry ("pair", i) / ("sol", i)."""
    if I.R <= I.C:
        return look_le(I, trace)
    s = look_le(transpose(I), trace)
    if s is None:
        return None
    return ([(v[1], v[0]) for v in s[0]], [(v[1], v[0]) for v in s[1]])

# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Minimal SVG renderer for grid figures (instances, paths, cuts, shading, labels)."""

COL = {"A": "#1D9E75", "B": "#D85A30"}
LIGHT = {"A": "#E1F5EE", "B": "#FAECE7"}
CUT = "#7F77DD"


def grid_svg(R, C, ends=(), paths=(), cuts=(), shade=(), checker=False, marks=(), virtual=(),
             cs=26, title=None, note=None, coords=False):
    """ends: [((r, c), label, 'A'|'B')]; paths: [('A'|'B', [cells])]; cuts: [('h', k)] = line
    between rows k-1 and k, [('v', k)] between columns; shade: [(cells, fill, opacity)];
    marks: [((r, c), text)]; virtual: [((r, c), label, 'A'|'B')] dashed endpoints."""
    m = 14
    top = m + (22 if title else 0)
    W = 2 * m + C * cs + (12 if coords else 0)
    H = top + R * cs + m + (18 if note else 0)
    ox = m + (12 if coords else 0)
    X = lambda c: ox + c * cs
    Y = lambda r: top + r * cs
    o = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}" '
         f'font-family="Helvetica, Arial, sans-serif">', '<rect width="100%" height="100%" fill="white"/>']
    if title:
        o.append(f'<text x="{ox}" y="{m + 12}" font-size="13" font-weight="700" fill="#222">{title}</text>')
    if checker:
        for r in range(R):
            for c in range(C):
                if (r + c) % 2 == 0:
                    o.append(f'<rect x="{X(c)}" y="{Y(r)}" width="{cs}" height="{cs}" fill="#d9d9d9"/>')
    for col, p in paths:
        for r, c in p:
            o.append(f'<rect x="{X(c)}" y="{Y(r)}" width="{cs}" height="{cs}" fill="{LIGHT[col]}"/>')
    for cells, fill, op in shade:
        for r, c in cells:
            o.append(f'<rect x="{X(c)}" y="{Y(r)}" width="{cs}" height="{cs}" fill="{fill}" fill-opacity="{op}"/>')
    for r in range(R + 1):
        o.append(f'<line x1="{X(0)}" y1="{Y(r)}" x2="{X(C)}" y2="{Y(r)}" stroke="#c8c8c8" stroke-width="0.6"/>')
    for c in range(C + 1):
        o.append(f'<line x1="{X(c)}" y1="{Y(0)}" x2="{X(c)}" y2="{Y(R)}" stroke="#c8c8c8" stroke-width="0.6"/>')
    o.append(f'<rect x="{X(0)}" y="{Y(0)}" width="{C * cs}" height="{R * cs}" fill="none" stroke="#333" stroke-width="1.4"/>')
    if coords:
        for r in range(R):
            o.append(f'<text x="{ox - 3}" y="{Y(r) + cs / 2 + 3}" font-size="8" fill="#888" text-anchor="end">{r}</text>')
    for col, p in paths:
        pts = " ".join(f"{X(c) + cs / 2},{Y(r) + cs / 2}" for r, c in p)
        o.append(f'<polyline points="{pts}" fill="none" stroke="{COL[col]}" stroke-width="{max(2, cs // 9)}" '
                 f'stroke-linejoin="round" stroke-linecap="round"/>')
    for kind, k in cuts:
        if kind == "h":
            o.append(f'<line x1="{X(0) - 6}" y1="{Y(k)}" x2="{X(C) + 6}" y2="{Y(k)}" stroke="{CUT}" stroke-width="2.4" stroke-dasharray="7 4"/>')
        else:
            o.append(f'<line x1="{X(k)}" y1="{Y(0) - 6}" x2="{X(k)}" y2="{Y(R) + 6}" stroke="{CUT}" stroke-width="2.4" stroke-dasharray="7 4"/>')
    rad = cs * 0.36
    for (r, c), lab, col in virtual:
        o.append(f'<circle cx="{X(c) + cs / 2}" cy="{Y(r) + cs / 2}" r="{rad}" fill="white" stroke="{COL[col]}" '
                 f'stroke-width="2" stroke-dasharray="3 2"/>')
        if lab:
            o.append(f'<text x="{X(c) + cs / 2}" y="{Y(r) + cs / 2 + 3.5}" font-size="{int(cs * 0.36)}" font-weight="700" '
                     f'fill="{COL[col]}" text-anchor="middle">{lab}</text>')
    for (r, c), lab, col in ends:
        o.append(f'<circle cx="{X(c) + cs / 2}" cy="{Y(r) + cs / 2}" r="{rad}" fill="{COL[col]}"/>')
        if lab:
            o.append(f'<text x="{X(c) + cs / 2}" y="{Y(r) + cs / 2 + 3.5}" font-size="{int(cs * 0.36)}" font-weight="700" '
                     f'fill="white" text-anchor="middle">{lab}</text>')
    for (r, c), text in marks:
        o.append(f'<text x="{X(c) + cs / 2}" y="{Y(r) + cs / 2 + 4}" font-size="{int(cs * 0.5)}" font-weight="700" '
                 f'fill="#333" text-anchor="middle">{text}</text>')
    if note:
        o.append(f'<text x="{ox}" y="{H - 6}" font-size="11" fill="#555">{note}</text>')
    o.append("</svg>")
    return "\n".join(o)


def inst_ends(I, labels=("s0", "t0", "s1", "t1")):
    return [(I.s0, labels[0], "A"), (I.t0, labels[1], "A"), (I.s1, labels[2], "B"), (I.t1, labels[3], "B")]


def sol_paths(sol):
    return [("A", sol[0]), ("B", sol[1])] if sol else []


def save(name, svg):
    with open(name, "w") as f:
        f.write(svg)

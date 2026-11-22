# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Export the certificate table of the Lean lookup leaves to lib/data/look.json.gz, from lib/:

    python3 tools/export_look.py [--proof=../proof] [--out=data/look.json.gz]

Reads the generated Lean sources (regular, one definition per line):

- `proof/ZZN/LookGen/N{w}x{h}.lean`: `tab : List CData := [dA, dB, …]`, the slice order of
  `tabCore w h` (`proof/ZZN/Look/Table.lean`), for 11 <= w <= h <= 16;
- `proof/BoxKGen/N{w}x{h}/S*.lean`: the slices `dK : CData := (![x0,x1,x2,x3], chain, pairs,
  fires, sols)` (`CData`: `proof/ZZN/BoxK/SliceC.lean`);
- `proof/BoxKGen/Templates0.lean`, `Templates1.lean`: the templates `tN : CTree TPos`;
- `proof/GridHam/PrimeTable.lean`: `primeTable`, the stored paths of the prime shapes used by
  `ipsP` (`primeLookup`).

Only the fields that `lookJ` reads are written: the row tuple `d.1`, the pairs `d.2.2.1` and the
stored solutions `d.2.2.2.2`; the chain `d.2.1` and the firing lanes `d.2.2.2.1` serve the
certificate proof only.

Format: gzip-compressed JSON, one object:

    {"format": "zzn-look-1",
     "templates": [T0, T1, …],            # T_N is the Lean template tN
     "boxes": {"11x11": [slice, …], …},   # key "{w}x{h}", slices in tab order
     "prime": [[w, h, [[sx, sy, tx, ty, [x0, y0, x1, y1, …]], …]], …]}  # primeTable, in order

    slice = [[x0, x1, x2, x3], pairs, sols]
    pairs = [N, sym, N, sym, …]           # (tN, σ) in order; sym = 32 tr + 16 rx + 8 ry + 4 r0
                                          #   + 2 r1 + sw (Lean field order of `Sym`, most
                                          #   significant first: the index of σ in `allSym`)
    sols  = [[lane, n0, code0, n1, code1], …]  # in order (paths packed as in `decPath`)

    T = 0                                 # CTree.leaf
      | [vert, a, o, kinds, L, R]         # CTree.cut vert (a, o) kinds L R; vert as 0/1
    kind = [s]                            # Kind.stay s
         | [s, a, o]                      # Kind.cross s (a, o)
         | [s, a, o, a2, o2]              # Kind.exc s (a, o) (a2, o2)

Bools are 0/1, offsets `o` are signed integers. Every template is exported (t0 … t11028), so
template ids index the list directly. Prints the counts and the file size.
"""
import glob
import gzip
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
LIB = os.path.dirname(HERE)


# --- templates -------------------------------------------------------------------------------

TOK = re.compile(r"\s*(CTree\.cut|CTree\.leaf|Kind\.stay|Kind\.cross|Kind\.exc|true|false|-?\d+|[()\[\],])")


def tokens(s):
    out, i = [], 0
    s = s.rstrip()
    while i < len(s):
        m = TOK.match(s, i)
        if m is None:
            raise ValueError("bad token at %r" % s[i:i + 40])
        out.append(m.group(1))
        i = m.end()
    return out


class Parser:
    def __init__(self, toks):
        self.t, self.i = toks, 0

    def peek(self):
        return self.t[self.i]

    def eat(self, x=None):
        v = self.t[self.i]
        if x is not None and v != x:
            raise ValueError("expected %s, got %s at %d" % (x, v, self.i))
        self.i += 1
        return v

    def bool(self):
        v = self.eat()
        if v not in ("true", "false"):
            raise ValueError("expected a Bool, got " + v)
        return 1 if v == "true" else 0

    def int(self):
        return int(self.eat())

    def pos(self):
        self.eat("(")
        a = self.int()
        self.eat(",")
        o = self.int()
        self.eat(")")
        return a, o

    def kind(self):
        k = self.eat()
        s = self.bool()
        if k == "Kind.stay":
            return [s]
        if k == "Kind.cross":
            return [s, *self.pos()]
        if k == "Kind.exc":
            return [s, *self.pos(), *self.pos()]
        raise ValueError("expected a Kind, got " + k)

    def kinds(self):
        self.eat("[")
        out = []
        if self.peek() != "]":
            out.append(self.kind())
            while self.peek() == ",":
                self.eat(",")
                out.append(self.kind())
        self.eat("]")
        return out

    def tree(self):
        v = self.peek()
        if v == "(":
            self.eat("(")
            t = self.tree()
            self.eat(")")
            return t
        if v == "CTree.leaf":
            self.eat()
            return 0
        self.eat("CTree.cut")
        vert = self.bool()
        a, o = self.pos()
        ks = self.kinds()
        left = self.tree()
        right = self.tree()
        return [vert, a, o, ks, left, right]


TDEF = re.compile(r"^noncomputable def t(\d+) : CTree TPos := (.*)$")


def read_templates(proof):
    tpl = {}
    for f in sorted(glob.glob(os.path.join(proof, "BoxKGen", "Templates*.lean"))):
        for line in open(f, encoding="utf-8"):
            m = TDEF.match(line)
            if m is None:
                continue
            p = Parser(tokens(m.group(2)))
            t = p.tree()
            if p.i != len(p.t):
                raise ValueError("trailing tokens in t" + m.group(1))
            tpl[int(m.group(1))] = t
    n = max(tpl) + 1
    if sorted(tpl) != list(range(n)):
        raise ValueError("template ids are not 0 … %d" % (n - 1))
    return [tpl[i] for i in range(n)]


# --- slices ----------------------------------------------------------------------------------

def top_split(s):
    """Split the body of a parenthesised tuple at its top-level commas."""
    assert s[0] == "(" and s[-1] == ")", s[:20]
    out, depth, start = [], 0, 1
    for i, ch in enumerate(s):
        if ch in "([⟨":
            depth += 1
        elif ch in ")]⟩":
            depth -= 1
        elif ch == "," and depth == 1:
            out.append(s[start:i].strip())
            start = i + 1
    out.append(s[start:-1].strip())
    return out


DDEF = re.compile(r"^noncomputable def d(\d+) : CData := (.*)$")
ROWS = re.compile(r"^!\[(\d+),(\d+),(\d+),(\d+)\]$")
B = r"(true|false)"
PAIR = re.compile(r"\(t(\d+), ⟨" + ", ".join([B] * 6) + r"⟩\)")
SOL = re.compile(r"\((\d+), (\d+), (\d+), (\d+), (\d+)\)")


def parse_slice(body):
    f = top_split(body)
    if len(f) != 5:
        raise ValueError("CData with %d fields" % len(f))
    m = ROWS.match(f[0])
    if m is None:
        raise ValueError("row tuple " + f[0])
    rows = [int(x) for x in m.groups()]
    pairs = []
    for pm in PAIR.finditer(f[2]):
        sym = 0
        for b in pm.groups()[1:]:
            sym = 2 * sym + (1 if b == "true" else 0)
        pairs += [int(pm.group(1)), sym]

    # Every pair must have been matched: compare with the number of top-level entries.
    #
    if f[2] != "[]" and len(top_split("(" + f[2][1:-1] + ")")) != len(pairs) // 2:
        raise ValueError("unparsed pairs")
    sols = [[int(x) for x in sm.groups()] for sm in SOL.finditer(f[4])]
    if f[4] != "[]" and len(top_split("(" + f[4][1:-1] + ")")) != len(sols):
        raise ValueError("unparsed sols")
    return [rows, pairs, sols]


TAB = re.compile(r"^noncomputable def tab : List CData := \[(.*)\]$", re.M)


def read_box(proof, w, h):
    box = "N%dx%d" % (w, h)
    src = open(os.path.join(proof, "ZZN", "LookGen", box + ".lean"), encoding="utf-8").read()
    names = [s.strip() for s in TAB.search(src).group(1).split(",")]
    ds = {}
    for f in glob.glob(os.path.join(proof, "BoxKGen", box, "S*.lean")):
        text = open(f, encoding="utf-8").read()
        if ("namespace BoxKGen.%s\n" % box) not in text:
            raise ValueError("unexpected namespace in " + f)
        for line in text.split("\n"):
            m = DDEF.match(line)
            if m is not None:
                ds["d" + m.group(1)] = m.group(2)
    return [parse_slice(ds[n]) for n in names]


# --- prime table -----------------------------------------------------------------------------

PDEF = re.compile(r"^def primePaths_(\d+)x(\d+) : List \(Coord × Coord × List Coord\) := \[(.*?)\]$",
                  re.M | re.S)
PENTRY = re.compile(r"\(\((\d+), (\d+)\), \((\d+), (\d+)\), \[([^\]]*)\]\)")
PTABLE = re.compile(r"^def primeTable : [^\n]*\n\s*\[(.*?)\]$", re.M | re.S)


def read_prime(proof):
    src = open(os.path.join(proof, "GridHam", "PrimeTable.lean"), encoding="utf-8").read()
    paths = {}
    for m in PDEF.finditer(src):
        es = []
        for e in PENTRY.finditer(m.group(3)):
            cells = [int(x) for x in re.findall(r"\d+", e.group(5))]
            es.append([int(e.group(i)) for i in range(1, 5)] + [cells])
        paths["primePaths_%sx%s" % (m.group(1), m.group(2))] = es
    order = re.findall(r"\((\d+), (\d+), (primePaths_\d+x\d+)\)", PTABLE.search(src).group(1))
    return [[int(w), int(h), paths[n]] for w, h, n in order]


def main():
    proof = next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--proof=")),
                 os.path.join(os.path.dirname(LIB), "proof"))
    out = next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--out=")),
               os.path.join(LIB, "data", "look.json.gz"))
    tpl = read_templates(proof)
    boxes = {}
    for w in range(11, 17):
        for h in range(w, 17):
            boxes["%dx%d" % (w, h)] = read_box(proof, w, h)
    for k, sl in boxes.items():
        for rows, pairs, sols in sl:
            assert all(pairs[i] < len(tpl) for i in range(0, len(pairs), 2)), k
    prime = read_prime(proof)
    data = {"format": "zzn-look-1", "templates": tpl, "boxes": boxes, "prime": prime}
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    raw = json.dumps(data, separators=(",", ":")).encode()
    with gzip.GzipFile(out, "wb", compresslevel=9, mtime=0) as f:
        f.write(raw)
    print("templates %d, slices %d, pairs %d, sols %d, prime shapes %d" % (
        len(tpl), sum(len(s) for s in boxes.values()),
        sum(len(p) // 2 for s in boxes.values() for _, p, _ in s),
        sum(len(q) for s in boxes.values() for _, _, q in s), len(prime)))
    print("%s: %d bytes (JSON %d bytes)" % (out, os.path.getsize(out), len(raw)))


if __name__ == "__main__":
    main()

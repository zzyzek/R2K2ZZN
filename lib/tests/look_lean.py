# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""The certificate lookup (python/zzn/look.py) against the Lean definitions, from lib/:

    python3 tests/look_lean.py N SEED --proof=DIR [--dir=OUT]

DIR is a `proof/` directory whose `ZZN.Look.Table` is built (Lean uses about 7 GB). Two runs of
`lake env lean --run tests/lean/LookEval.lean` there (see LookEval.lean):

1. **data**: Lean prints the templates, the slice tables of all 21 boxes (rows, pairs, stored
   solutions, in `tab` order) and the prime paths, read from the elaborated Lean definitions. They
   must equal `lib/data/look.json.gz` line for line. This checks the exporter.
2. **cases**: Python writes the table in text form and cases with the library's values; Lean
   evaluates its definitions on them and reports every difference:
   - `look`: `lookJ tab I` (with `tab` built from the table file) on N irreducible passing
     instances per box R x C, 11 <= R, C <= 16 (drawn as in look_test.py), and on 10 N random
     passing instances with sides 11-16;
   - `entry`: `entryP` on the canonical instance and slice of each `look` case, and on the lane
     instances of 10 N stored solutions (most of them answered by the stored paths);
   - `tpl`: `tcheck` and `tsol` on every template tried by those lookups (up to the first that
     checks, and two more), and on 10 N random (template, symmetry, lane) triples from the table;
   - `canon`: `argminS … key2 … Gbox` and `key2` on each `look` instance (in its w <= h frame);
   - `sym`, `unsym`: `Sym.apply` and `unSym` (on random cell lists) for all 64 symmetries on
     the first N `look` instances;
   - `dec`, `solf`: `decPath` and `solF` on those 10 N stored solutions, and `solF` on two broken
     variants of each;
   - `ips`: `accB` and `ipsP (w + h)` on every pair s != t of every rectangle up to 5 x 5, and on
     20 N random rectangles up to 16 x 16.

Prints both summaries; exit status 0 when both agree.
"""
import gzip
import json
import os
import random
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
LIB = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(LIB, "python"))
from look_test import draw  # noqa: E402
from zzn import check_solution  # noqa: E402
from zzn.catalogue import fires  # noqa: E402
from zzn.grid import Instance  # noqa: E402
from zzn import look  # noqa: E402


def inst_s(I):
    return " ".join(map(str, [I.R, I.C, *I.s0, *I.t0, *I.s1, *I.t1]))


def cells_s(L):
    return " ".join("%d,%d" % (r, c) for r, c in L)


def sol_f(s):
    return ["none"] if s is None else [cells_s(s[0]), cells_s(s[1])]


def tree_s(T):
    """A template in the prefix form of LookEval.lean."""
    out = []

    def go(T):
        if T == 0:
            out.append("L")
            return
        vert, a, o, ks, left, right = T
        out.extend(["C", str(vert), str(a), str(o), str(len(ks))])
        for k in ks:
            out.append({1: "S", 3: "X", 5: "E"}[len(k)])
            out.extend(str(x) for x in k)
        go(left)
        go(right)

    go(T)
    return " ".join(out)


def slice_s(d):
    return (" ".join(map(str, d[0])) + " ; " + " ".join(map(str, d[1])) + " ; " +
            " ".join(" ".join(map(str, e)) for e in d[2]))


def expected_data():
    """The export in the text form of LookEval.lean's data mode."""
    with gzip.open(look.DATA, "rb") as f:
        d = json.loads(f.read().decode())
    out = ["T %d %s" % (i, tree_s(T)) for i, T in enumerate(d["templates"])]
    for w in range(11, 17):
        for h in range(w, 17):
            for k, s in enumerate(d["boxes"]["%dx%d" % (w, h)]):
                out.append("D %d %d %d %s" % (w, h, k, slice_s(s)))
    for w, h, es in d["prime"]:
        for e in es:
            out.append("P %d %d %d %d %d %d %s" % (w, h, e[0], e[1], e[2], e[3], " ".join(map(str, e[4]))))
    return out


def table_text():
    D = look.data()
    lines = ["T %d %s" % (i, tree_s(T)) for i, T in enumerate(D["templates"])]
    for (w, h), sl in sorted(D["boxes"].items()):
        for s in sl:
            lines.append("D %d %d %s" % (w, h, slice_s(s)))
    return lines


def rand_inst(rng, R, C):
    cells = rng.sample([(r, c) for r in range(R) for c in range(C)], 4)
    return Instance(R, C, *cells)


def cases(n, seed):
    rng = random.Random(seed)
    D = look.data()
    out = []

    # Lookups: irreducible instances on every box, then random passing ones.
    #
    insts = []
    for R in range(11, 17):
        for C in range(11, 17):
            for _ in range(n):
                insts.append(draw(rng, R, C))
    m = 0
    while m < 10 * n:
        R, C = rng.randint(11, 16), rng.randint(11, 16)
        I = rand_inst(rng, R, C)
        if fires(R, C, I.s0, I.t0, I.s1, I.t1) is None:
            insts.append(I)
            m += 1
    for I in insts:
        tr = {}
        s = look.look_j(I, tr)
        if s is not None:
            assert check_solution(I, s), I
        out.append("\t".join(["look", inst_s(I)] + sol_f(s)))
        J = I if I.R <= I.C else look.transpose(I)
        sigma = look.canon_sym(J)
        out.append("\t".join(["canon", inst_s(J), str(look.sym_to_int(sigma)), str(look.key2(J))]))
        K = look.apply_sym(sigma, J)
        if "slice" not in tr:
            continue
        d = D["boxes"][(K.R, K.C)][tr["slice"]]
        r = look.entry_p(K, d)
        out.append("\t".join(["entry", "%d %d" % (K.R, K.C), str(tr["slice"]), inst_s(K)] +
                             sol_f(None if r is None else r[0])))

        # The templates tried: up to the first that checks, and two more.
        #
        npairs = len(d[1]) // 2
        last = tr["entry"][1] if tr["entry"][0] == "pair" else npairs - 1
        for i in range(min(npairs, last + 3)):
            T, sg = look.template(d[1][2 * i]), look.sym_of_int(d[1][2 * i + 1])
            KK = look.apply_sym(sg, K)
            c = look.tcheck(T, KK)
            p, q = look.tsol(T, KK)
            out.append("\t".join(["tpl", tree_s(T), inst_s(KK), "1" if c else "0", cells_s(p), cells_s(q)]))

    # Random (template, symmetry, lane) triples from the table.
    #
    boxes = sorted(D["boxes"])
    m = 0
    while m < 10 * n:
        w, h = rng.choice(boxes)
        d = rng.choice(D["boxes"][(w, h)])
        if not d[1]:
            continue
        i = rng.randrange(len(d[1]) // 2)
        cols = [rng.randrange(h) for _ in range(4)]
        K = Instance(w, h, *[(d[0][j], cols[j]) for j in range(4)])
        if len(set([K.s0, K.t0, K.s1, K.t1])) < 4:
            continue
        T, sg = look.template(d[1][2 * i]), look.sym_of_int(d[1][2 * i + 1])
        KK = look.apply_sym(sg, K)
        c = look.tcheck(T, KK)
        p, q = look.tsol(T, KK)
        out.append("\t".join(["tpl", tree_s(T), inst_s(KK), "1" if c else "0", cells_s(p), cells_s(q)]))
        m += 1

    # All 64 symmetries and their pull-backs on the first n instances.
    #
    for I in insts[:n]:
        for k, sg in enumerate(look.ALL_SYM):
            J = look.apply_sym(sg, I)
            out.append("\t".join(["sym", inst_s(I), str(k), inst_s(J)]))
            p = [(rng.randrange(J.R), rng.randrange(J.C)) for _ in range(6)]
            q = [(rng.randrange(J.R), rng.randrange(J.C)) for _ in range(5)]
            p2, q2 = look.un_sym(sg, I, (p, q))
            out.append("\t".join(["unsym", str(k), inst_s(I), cells_s(p), cells_s(q), cells_s(p2), cells_s(q2)]))

    # Stored solutions.
    #
    stored = [(w, h, k, d, e) for (w, h), sl in D["boxes"].items() for k, d in enumerate(sl) for e in d[2]]
    for w, h, k, d, e in rng.sample(stored, min(10 * n, len(stored))):
        j = e[0]
        cols = [(j // h ** (3 - i)) % h for i in range(4)]
        K = Instance(w, h, *[(d[0][i], cols[i]) for i in range(4)])
        r = look.entry_p(K, d)
        out.append("\t".join(["entry", "%d %d" % (w, h), str(k), inst_s(K)] +
                             sol_f(None if r is None else r[0])))
        p, q = look.dec_path(e[1], e[2]), look.dec_path(e[3], e[4])
        out.append("\t".join(["dec", str(e[1]), str(e[2]), cells_s(p)]))
        out.append("\t".join(["dec", str(e[3]), str(e[4]), cells_s(q)]))
        for pp, qq in ((p, q), (p[:-1], q), (q, p)):
            out.append("\t".join(["solf", inst_s(K), cells_s(pp), cells_s(qq),
                                  "1" if look.sol_f(K, pp, qq) else "0"]))

    # IPS paths: every s != t up to 5 x 5, then random rectangles up to 16 x 16.
    #
    def ips_case(w, h, s, t):
        a = look.acc_b(w, h, s, t)
        p = look.ips_p(w + h, w, h, s, t)
        return "\t".join(["ips", "%d %d %d %d %d %d" % (w, h, s[0], s[1], t[0], t[1]),
                          "1" if a else "0", cells_s(p)])

    for w in range(1, 6):
        for h in range(1, 6):
            cs = [(x, y) for x in range(w) for y in range(h)]
            for s in cs:
                for t in cs:
                    if s != t:
                        out.append(ips_case(w, h, s, t))
    for _ in range(20 * n):
        w, h = rng.randint(1, 16), rng.randint(1, 16)
        if w * h < 2:
            continue
        s, t = rng.sample([(x, y) for x in range(w) for y in range(h)], 2)
        out.append(ips_case(w, h, s, t))
    return out


def run_lean(proof, args):
    lean = os.path.join(HERE, "lean", "LookEval.lean")
    r = subprocess.run(["lake", "env", "lean", "--run", lean] + args, cwd=proof,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    return r.returncode, r.stdout


def main():
    nums = [a for a in sys.argv[1:] if not a.startswith("--")]
    n, seed = (int(x) for x in nums[:2])
    proof = next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--proof=")), None)
    out = next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--dir=")), None)
    if proof is None:
        print(__doc__)
        return 2
    if out is None:
        out = tempfile.mkdtemp()
    os.makedirs(out, exist_ok=True)
    out = os.path.abspath(out)
    status = 0

    # 1. The export against the elaborated Lean definitions.
    #
    data = os.path.join(out, "lean_data.txt")
    rc, txt = run_lean(proof, ["data", data])
    print(txt.strip())
    if rc != 0:
        return rc
    got = open(data).read().split("\n")
    if got and got[-1] == "":
        got.pop()
    exp = expected_data()
    diff = sum(1 for a, b in zip(got, exp) if a != b) + abs(len(got) - len(exp))
    for a, b in zip(got, exp):
        if a != b:
            print("DATA DIFFERS: lean %r / export %r" % (a[:120], b[:120]))
            break
    print("data: %d lines from Lean, %d from the export, %d differ" % (len(got), len(exp), diff))
    if diff:
        status = 1

    # 2. The cases.
    #
    table = os.path.join(out, "table.txt")
    with open(table, "w") as f:
        f.write("\n".join(table_text()) + "\n")
    path = os.path.join(out, "cases.txt")
    with open(path, "w") as f:
        f.write("\n".join(cases(n, seed)) + "\n")
    rc, txt = run_lean(proof, ["cases", path, table])
    print(txt.strip())
    return status or rc


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Write Lean modules for slice certificates checked by `sliceCOK` (ZZN/BoxK/SliceC.lean).

gen_cbox.py W H CERT BASE NAME [BASE_TEMPLATES TEMPLATES_OUT]
CERT: from src/slicehyb.c then tools/FireGen.lean: TARGET g w0 a,b,c,d n / LANES / PAIR / SOL, then
CSLICE a,b,c,d g steps / FIRE lane code / PAIR / SOL.
BASE: from tools/BaseGen.lean: CLASS k L / BASE k hex / SLICE a,b,c,d k.
With BASE_TEMPLATES and TEMPLATES_OUT (slicehyb TOUT), templates past the base set go to TX.lean.

Modules in gen/BoxKGen/NAME: Base (stabiliser lists, base masks, one check each), T{i} (targets:
literal lane mask and one check that the target's pairs and solutions cover it), S{i} (slices,
each with its `SliceGood`), Main (`BoxCert`; meaningful for a whole box only).
A target with one slice, no rows removed, is inlined in that slice (`M = 0`).
"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_box import conv, sym, HDR, GEN

# Slices per S module. Each module pays about 4 s to load its imports (Templates and Mathlib),
# so fewer, larger modules cost less; the default 40 was sized for many parallel workers.
#
PER_S = int(os.environ.get('PER_S', '160'))
PER_T = 40

def pack_sol(line):
    lane, rest = line.split(None, 2)[1:]
    def pack(txt):
        cells = [tuple(map(int, c.split(','))) for c in re.findall(r'\((\d+, \d+)\)', txt)]
        return len(cells), sum((16 * r + c) << (8 * k) for k, (r, c) in enumerate(cells))
    a, b = rest.strip().split('] [')
    (np_, cp), (nq, cq) = pack(a), pack(b)
    return f"({lane}, {np_}, {cp}, {nq}, {cq})"

def step(s):
    if s == 'B': return 'RStep.bot'
    if s == 'T': return 'RStep.top'
    return f'RStep.band {int(s[1:])}'

def ps(pairs):
    return "[" + ", ".join(f"(t{k}, {sym(s)})" for k, s in pairs) + "]"

def main():
    w, h, cert, basef, name = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4], sys.argv[5]
    targets, slices, cur = {}, [], None
    for line in open(cert):
        t = line.split()
        if not t: continue
        if t[0] == 'TARGET':
            cur = {'w0': int(t[2]), 'x0': t[3], 'pairs': [], 'sols': [], 'lanes': [], 'insts': []}
            targets[int(t[1])] = cur
        elif t[0] == 'LANES':
            cur['lanes'] = [int(v) for v in t[1:]]
        elif t[0] == 'CSLICE':
            ss = [] if t[3] == '-' else [step(s) for s in t[3].split(',')]
            cur = {'x': t[1], 'g': int(t[2]), 'ss': ss, 'pairs': [], 'fires': [], 'sols': []}
            slices.append(cur)
        elif t[0] == 'PAIR':
            cur['pairs'].append((int(t[1]), int(t[2])))
        elif t[0] == 'INST':
            cur['insts'].append(f"({t[1]}, {sym(int(t[3]))}, t{int(t[2])})")
        elif t[0] == 'FIRE':
            cur['fires'].append(f"({t[1]}, {t[2]})")
        elif t[0] == 'SOL':
            cur['sols'].append(pack_sol(line))
        elif t[0] == 'UNSOLVED':
            raise SystemExit('unsolved lane')
    cls, base, scls = {}, {}, {}
    for line in open(basef):
        t = line.rstrip('\n').split(' ', 2)
        if t[0] == 'CLASS': cls[int(t[1])] = t[2]
        elif t[0] == 'BASE': base[int(t[1])] = t[2]
        elif t[0] == 'SLICE': scls[t[1]] = int(t[2])
    d = os.path.join(GEN, name); os.makedirs(d, exist_ok=True)
    ns = f"BoxKGen.{name}"
    opn = ["set_option Elab.async false", f"namespace {ns}", "open ZZN ZZN.Cut ZZN.BoxK BoxKGen", ""]
    files = []

    def write(fn, imports, body):
        open(os.path.join(d, fn + '.lean'), 'w').write('\n'.join([HDR] + imports + opn + body + [f"end {ns}"]) + '\n')
        files.append(fn)

    tmpl = ["import BoxKGen.Templates"]
    if len(sys.argv) > 7:
        nb = sum(1 for _ in open(sys.argv[6]))
        extra = open(sys.argv[7]).readlines()[nb:]
        if extra:
            out = [HDR, "import ZZN.BoxK.Box", "namespace BoxKGen", "open ZZN ZZN.Cut", ""]
            for k, l in enumerate(extra):
                out.append(f"def t{nb + k} : CTree TPos := {conv(l)}")
            out.append("end BoxKGen")
            open(os.path.join(d, 'TX.lean'), 'w').write('\n'.join(out) + '\n')
            tmpl.append(f"import {ns}.TX")

    used = sorted({scls[s['x']] for s in slices})
    body = []
    for k in used:
        body.append(f"def L{k} : List Sym := {cls[k]}")
        body.append(f"def b{k} : ℕ := 0x{base[k]}")
        body.append(f"theorem base{k} : baseM {h} L{k} = b{k} := by decide +kernel")
    write("Base", ["import ZZN.BoxK.SliceC"], body)

    members = {}
    for n, s in enumerate(slices):
        members.setdefault(s['g'], []).append(n)
    inline = {g for g, m in members.items()
              if len(m) == 1 and not slices[m[0]]['ss'] and targets[g]['w0'] == w}
    shared = [g for g in sorted(members) if g not in inline]
    tmods = []
    for i in range(0, len(shared), PER_T):
        body = []
        for g in shared[i:i + PER_T]:
            tg = targets[g]
            m = sum(1 << (8 * l) for l in tg['lanes'])
            body.append(f"def tp{g} : List (CTree TPos × Sym) := {ps(tg['pairs'])}")
            body.append(f"def ts{g} : List (ℕ × ℕ × ℕ × ℕ × ℕ) := [{', '.join(tg['sols'])}]")
            body.append(f"def m{g} : ℕ := {hex(m)}")
            body.append(f"theorem tg{g} : subM m{g} (tgtM {tg['w0']} {h} ![{tg['x0']}] tp{g} ts{g}) = true := "
                        "by decide +kernel")
        fn = f"T{i // PER_T}"
        write(fn, tmpl + ["import ZZN.BoxK.SliceC"], body)
        tmods.append(fn)

    for i in range(0, len(slices), PER_S):
        body = []
        for n in range(i, min(i + PER_S, len(slices))):
            s = slices[n]; g = s['g']; k = scls[s['x']]; tg = targets[g]
            if g in inline:
                pairs, sols, w0, x0, M = tg['pairs'] + s['pairs'], tg['sols'] + s['sols'], w, s['x'], "0"
                insts = tg['insts']
            else:
                pairs, sols, w0, x0, M = s['pairs'], s['sols'], tg['w0'], tg['x0'], f"m{g}"
                insts = []
            body.append(f"def d{n} : CData := (![{s['x']}], [{', '.join(s['ss'])}], {ps(pairs)}, "
                        f"[{', '.join(s['fires'])}], [{', '.join(sols)}])")
            body.append(f"theorem sl{n} : sliceCOK {w} {h} d{n}.1 L{k} b{k} {w0} ![{x0}] d{n}.2.1 {M} "
                        f"d{n}.2.2.1 d{n}.2.2.2.1 [{', '.join(insts)}] d{n}.2.2.2.2 = true := by decide +kernel")
            hM = f"(subM_zero (tgtM {w} {h} ![{x0}] [] []))" if g in inline else f"tg{g}"
            body.append(f"theorem g{n} : SliceGood {w} {h} d{n}.1 := sliceCOK_sound (by decide) (by decide) "
                        f"(by decide) (by decide) base{k} {hM} sl{n}")
        write(f"S{i // PER_S}", tmpl + [f"import {ns}.Base"] + [f"import {ns}.{t}" for t in tmods], body)
    smods = [f for f in files if f.startswith('S')]
    xs = ", ".join(f"d{n}.1" for n in range(len(slices)))
    body = ["set_option maxRecDepth 100000",
            f"theorem rows : rowsOK {w} [{xs}] = true := by decide +kernel",
            f"theorem all : List.Forall (SliceGood {w} {h}) [{xs}] :=",
            "  ⟨" + ", ".join(f"g{n}" for n in range(len(slices))) + "⟩",
            f"theorem box : BoxCert {w} {h} := boxCert_of_good _ rows all"]
    write("Main", [f"import {ns}.{m}" for m in smods], body)
    print(name, 'targets', len(targets), 'shared', len(shared), 'inline', len(inline), 'slices', len(slices),
          'classes', len(used), 'modules', files)

main()

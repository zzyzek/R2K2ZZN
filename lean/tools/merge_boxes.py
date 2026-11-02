#!/usr/bin/env python3
"""Merge per-box certificates whose folded templates were appended separately.

Each box run of `slicehyb` (FOLD=1) reads the same base set and appends its own folded templates
(TOUT). The global set is the base followed by every folded template once; PAIR and INST lines
are renumbered to it.
usage: merge_boxes.py BASE DIR OUT_TEMPLATES   (DIR holds t{w}x{h}.txt and c{w}x{h}.txt; writes g{w}x{h}.txt)
"""
import sys, os, glob, re
base, d, outT = sys.argv[1], sys.argv[2], sys.argv[3]
def body(l): return l.split(':', 1)[1].strip()
B = [l.rstrip('\n') for l in open(base)]
nb = len(B)
glob_idx = {body(l): i for i, l in enumerate(B)}
G = list(B)
for tf in sorted(glob.glob(os.path.join(d, 't*x*.txt'))):
    m = re.search(r't(\d+)x(\d+)\.txt$', tf)
    w, h = m.group(1), m.group(2)
    T = [l.rstrip('\n') for l in open(tf)]
    assert [body(l) for l in T[:nb]] == [body(l) for l in B], tf
    remap = {}
    for k, l in enumerate(T):
        b = body(l)
        if b not in glob_idx:
            glob_idx[b] = len(G); G.append(l)
        remap[k] = glob_idx[b]
    out = []
    for l in open(os.path.join(d, f'c{w}x{h}.txt')):
        t = l.split()
        if t and t[0] == 'PAIR':
            l = f"PAIR {remap[int(t[1])]} {t[2]}\n"
        elif t and t[0] == 'INST':
            l = f"INST {t[1]} {remap[int(t[2])]} {t[3]}\n"
        out.append(l)
    open(os.path.join(d, f'g{w}x{h}.txt'), 'w').write(''.join(out))
open(outT, 'w').write('\n'.join(G) + '\n')
print('templates', len(G), 'base', nb)

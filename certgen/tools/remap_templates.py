#!/usr/bin/env python3
"""Renumber the PAIR/INST template indices of a slicehyb run (indices into its TOUT file) to a
global template set; templates missing from it are appended (gen_cbox puts them in TX.lean).

usage: remap_templates.py CERT TOUT GLOBAL OUT_CERT OUT_TEMPLATES
"""
import sys
def body(l): return l.split(':', 1)[1].strip()
cert, tout, glob_, oc, ot = sys.argv[1:6]
G = [l.rstrip('\n') for l in open(glob_)]
gi = {body(l): i for i, l in enumerate(G)}
extra, remap = [], {}
for k, l in enumerate(open(tout)):
    l = l.rstrip('\n'); b = body(l)
    if b not in gi: gi[b] = len(G) + len(extra); extra.append(l)
    remap[k] = gi[b]
out = []
for l in open(cert):
    t = l.split()
    if t and t[0] == 'PAIR': l = f"PAIR {remap[int(t[1])]} {t[2]}\n"
    elif t and t[0] == 'INST': l = f"INST {t[1]} {remap[int(t[2])]} {t[3]}\n"
    out.append(l)
open(oc, 'w').write(''.join(out)); open(ot, 'w').write('\n'.join(G + extra) + '\n')
print('extra', len(extra))

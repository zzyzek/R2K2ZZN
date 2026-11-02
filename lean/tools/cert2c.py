#!/usr/bin/env python3
"""Convert a slicehyb certificate (SLICE / PAIR / INST / FIRE / SOL) to the cslice format read by
gen_cbox.py, without compression: each slice is its own target (inlined by gen_cbox).

usage: cert2c.py W CERT OUT
"""
import sys
w, cert, out = sys.argv[1], sys.argv[2], sys.argv[3]
slices = []
for line in open(cert):
    t = line.split()
    if not t: continue
    if t[0] == 'SLICE':
        slices.append((t[1], [], []))
    elif t[0] in ('PAIR', 'SOL', 'INST'):
        slices[-1][1].append(line.rstrip('\n'))
    elif t[0] == 'FIRE':
        slices[-1][2].append(line.rstrip('\n'))
    else:
        raise SystemExit(f'unexpected line: {line}')
with open(out, 'w') as f:
    for g, (x, cov, _) in enumerate(slices):
        f.write(f"TARGET {g} {w} {x} 0\nLANES\n" + ''.join(l + '\n' for l in cov))
    for g, (x, _, fires) in enumerate(slices):
        f.write(f"CSLICE {x} {g} -\n" + ''.join(l + '\n' for l in fires))
print('slices', len(slices))

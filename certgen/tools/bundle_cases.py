#!/usr/bin/env python3
"""Bundle the WinKU case modules (gen/WinKU/<case>/Main.lean) into K modules gen/WinKU/Bundle<i>.lean
and point gen/WinKU/Facts.lean at them. Each module pays about 4 s to load its imports, and the
cases share their imports; every case keeps its own namespace block. Cases are dealt to bundles
by size (largest first, to the lightest bundle).

usage: bundle_cases.py K
"""
import os, re, sys, glob
K = int(sys.argv[1])
G = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'gen', 'WinKU')
cases = sorted(os.path.basename(os.path.dirname(f)) for f in glob.glob(os.path.join(G, '*', 'Main.lean'))
               if os.path.basename(os.path.dirname(f)) != 'Shared')
size = {c: os.path.getsize(os.path.join(G, c, 'Main.lean')) for c in cases}
bins = [[] for _ in range(K)]; load = [0] * K
for c in sorted(cases, key=lambda c: -size[c]):
    i = load.index(min(load)); bins[i].append(c); load[i] += size[c]
for i, b in enumerate(bins):
    imps, body = [], []
    for c in sorted(b):
        for l in open(os.path.join(G, c, 'Main.lean')):
            if l.startswith('import '):
                if l not in imps: imps.append(l)
            elif l.startswith('set_option Elab.async'):
                continue
            else:
                body.append(l)
    open(os.path.join(G, f'Bundle{i}.lean'), 'w').write(''.join(imps) + 'set_option Elab.async false\n' + ''.join(body))
f = os.path.join(G, 'Facts.lean'); s = open(f).read()
s = re.sub(r'(?m)^import WinKU\.(?!Shared)\w+\.Main\n', '', s)
s = re.sub(r'(?m)^(import ZZN\.C8R\n)', r'\1' + ''.join(f'import WinKU.Bundle{i}\n' for i in range(K)), s, count=1)
open(f, 'w').write(s)
print(len(cases), 'cases in', K, 'bundles; sizes', load)

#!/usr/bin/env python3
"""Post-process gen/WinKU/Shared/G*.lean (tools/WinGenU.lean): check each final bucket for all
specifications in one declaration (`finalSigOKL`, ZZN/WinK/SigL.lean), so the kernel decodes each
final state once, and derive the per-specification theorems `fsig{f}_{j}` from it. The number of
G modules and every theorem name used by Main stay the same.

usage: fsig_combine.py SHARED_DIR
"""
import glob, os, re, sys
d = sys.argv[1]
files = sorted(glob.glob(os.path.join(d, 'G*.lean')), key=lambda p: int(re.search(r'G(\d+)\.lean$', p).group(1)))
hdr, fs, other = None, {}, []
pat = re.compile(r'theorem fsig(\d+)_(\d+) : finalSigOK (\d+) (\d+) \((.*)\) UB(\d+)_\2\.1 UB\6_\2\.2 SA\1 NS\1 = true := by decide \+kernel$')
for p in files:
    lines = open(p).read().split('\n')
    if hdr is None:
        hdr = [l for l in lines if not l.startswith('theorem') and not l.startswith('end ') and l.strip()]
    for l in lines:
        if l.startswith('theorem fsig'):
            m = pat.match(l)
            assert m, l
            f, j, a, b, F, n = int(m[1]), int(m[2]), m[3], m[4], m[5], m[6]
            fs.setdefault(j, {})[f] = (F, a, b, n)
        elif l.startswith('theorem'):
            other.append(l)
ns = [l for l in hdr if l.startswith('namespace ')][0].split()[1]
blocks = []
for j in sorted(fs):
    specs = fs[j]
    fl = sorted(specs)
    assert fl == list(range(len(fl))), (j, fl)
    F0, a, b, n = specs[0]
    L = ", ".join(f"(({specs[f][0]}), SA{f}, NS{f})" for f in fl)
    s = [f"theorem fall_{j} : finalSigOKL {a} {b} UB{n}_{j}.1 UB{n}_{j}.2 [{L}] = true := by decide +kernel"]
    for f in fl:
        F = specs[f][0]
        s.append(f"theorem fsig{f}_{j} : finalSigOK {a} {b} ({F}) UB{n}_{j}.1 UB{n}_{j}.2 SA{f} NS{f} = true :=\n"
                 f"  finalSigOKL_get fall_{j} {f} (by decide)")
    blocks.append('\n'.join(s))
blocks += other
k = len(files)
groups = [blocks[i::k] for i in range(k)]
imports = [l for l in hdr if l.startswith('import ')] + ['import ZZN.WinK.SigL']
rest = [l for l in hdr if not l.startswith('import ')]
for i, g in enumerate(groups):
    open(os.path.join(d, f'G{i}.lean'), 'w').write('\n'.join(imports + rest + g + [f'end {ns}', '']))
print('buckets', len(fs), 'other', len(other), 'files', k)

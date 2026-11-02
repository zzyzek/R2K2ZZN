#!/usr/bin/env python3
"""Post-process generated window modules (tools/WinGenU.lean): check each stage bucket with
`stepOKD` (ZZN/WinK/FastE.lean, about 1.6 times faster in the kernel) and derive the original
`stepOK` theorem from it by `stepOKD_eq`. Theorem names and module names stay the same.

usage: stage_fast.py FILE.lean ...
"""
import glob, os, re, sys
pat = re.compile(r'^theorem (\S+) : stepOK (.*) = true := by decide \+kernel$')
n = 0
for p in sys.argv[1:]:
    if 'stepOKD' in open(p).read():
        continue
    out = []
    for l in open(p).read().split('\n'):
        m = pat.match(l)
        if m:
            name, args = m[1], m[2]
            out.append(f"theorem {name}D : stepOKD {args} = true := by decide +kernel")
            out.append(f"theorem {name} : stepOK {args} = true := by rw [← stepOKD_eq]; exact {name}D")
            n += 1
        elif l.startswith('import ') and 'import ZZN.WinK.FastE' not in out:
            out.append(l)
            out.append('import ZZN.WinK.FastE')
        else:
            out.append(l)
    open(p, 'w').write('\n'.join(out))
print('stage theorems', n)

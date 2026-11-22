#!/usr/bin/env python3
"""Check proof/ against Palomar's file rules: every .lean file but lakefile.lean starts with
`module` (after its comment header), no file is over 10 000 lines, each challenge is at most
1 000 lines and 100 KiB and imports only Mathlib, and each comparator configuration names its
challenge, solution and theorems (the theorems must be stated in the challenge).

usage: check_palomar.py PROOF_DIR
"""
import glob, json, os, re, sys

OUT = sys.argv[1]
bad = []
n_files = 0
for r, ds, fs in os.walk(OUT):
    ds[:] = [d for d in ds if d != '.lake']
    for f in fs:
        # lakefile.lean is Lake's configuration, not a module.
        #
        if not f.endswith('.lean') or (r == OUT and f == 'lakefile.lean'):
            continue
        n_files += 1
        p = os.path.join(r, f)
        t = open(p).read()
        code = re.sub(r'(?s)^\s*/-.*?-/\s*', '', t)
        if not code.startswith('module\n'):
            bad.append(f'{p}: no `module` header')
        if t.count('\n') > 10000:
            bad.append(f'{p}: {t.count(chr(10))} lines')

for cfg in sorted(glob.glob(os.path.join(OUT, 'comparator*.json'))):
    c = json.load(open(cfg))
    chal = os.path.join(OUT, c['challenge_module'] + '.lean')
    sol = os.path.join(OUT, c['solution_module'] + '.lean')
    for p in (chal, sol):
        if not os.path.exists(p):
            bad.append(f'{cfg}: missing {p}')
    t = open(chal).read()
    lines, kib = t.count('\n'), len(t.encode()) / 1024
    if lines > 1000 or kib > 100:
        bad.append(f'{chal}: {lines} lines, {kib:.1f} KiB')
    imps = re.findall(r'(?m)^(?:public )?import (\S+)', t)
    if imps != ['Mathlib']:
        bad.append(f'{chal}: imports {imps}')
    for th in c['theorem_names']:
        short = th.split('.')[-1]
        if not re.search(rf'(?m)^theorem {short}\b', t):
            bad.append(f'{chal}: theorem {th} not stated')
    if sorted(c['permitted_axioms']) != ['Classical.choice', 'Quot.sound', 'propext']:
        bad.append(f'{cfg}: permitted_axioms {c["permitted_axioms"]}')
    print(f'{os.path.basename(cfg)}: {os.path.basename(chal)} {lines} lines {kib:.1f} KiB, '
          f'theorems {c["theorem_names"]}')

print(f'{n_files} .lean files checked')
for b in bad:
    print('FAIL', b)
sys.exit(1 if bad else 0)

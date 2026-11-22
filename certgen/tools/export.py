#!/usr/bin/env python3
"""Write the generated certificate modules into proof/, and proof/'s Palomar files.

The generated modules (certgen/gen: BoxKGen, WinKU, FinalN, from regen.sh) become modules of the
Lean module system with `@[expose] public section`, so definitions unfold across modules for the
kernel checks. Their data definitions are `noncomputable`: Lake would otherwise emit C for the
large literals, which costs about as much as checking them. The template set is split into parts
of at most MAX_LINES lines (Palomar allows 10 000 lines per file).

The Palomar files (two challenges, their solutions and comparator configurations) are written by
palomar.py.

usage: export.py PROOF_DIR   (run by regen.sh)
"""
import os, re, shutil, subprocess, sys

OUT = sys.argv[1]
TOOLS = os.path.dirname(os.path.abspath(__file__))
GEN = os.path.join(os.path.dirname(TOOLS), 'gen')
MAX_LINES = 9000

HDR = ("/-\nSPDX-License-Identifier: CC0-1.0\n"
       "Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.\n-/\n")

def split_header(text):
    """(imports, body) of a generated module: import lines, and the rest without the leading comment header."""
    imps, body, seen_code = [], [], False
    for l in text.split('\n'):
        if not seen_code and (l.startswith('--') or not l.strip()):
            continue
        if l.startswith('import '):
            imps.append(l.split()[1]); continue
        seen_code = True
        body.append(l)
    return imps, '\n'.join(body).rstrip('\n') + '\n'

def to_module(imps, body):
    body = re.sub(r'(?m)^#print axioms.*\n', '', body)
    body = re.sub(r'(?m)^-- Which axioms each result depends on.*\n', '', body)
    body = body.rstrip('\n') + '\n' if body.strip() else body
    return (HDR + "module\n\n" + ''.join(f"public import {i}\n" for i in imps) +
            "\n@[expose] public section\n\n" + body)

def write(rel, text):
    p = os.path.join(OUT, rel)
    os.makedirs(os.path.dirname(p) or '.', exist_ok=True)
    open(p, 'w').write(text)
    assert text.count('\n') <= 10000, (rel, text.count('\n'))

# Replace the generated modules.
for d in ['BoxKGen', 'WinKU']:
    shutil.rmtree(os.path.join(OUT, d), ignore_errors=True)
def gen_path(m):
    return os.path.join(GEN, *m.split('.')) + '.lean'

# The generated modules FinalN imports, directly or not (the per-case window modules are bundled
# and not imported themselves).
gen, todo = set(), ['FinalN']
while todo:
    m = todo.pop()
    if m in gen or not os.path.exists(gen_path(m)): continue
    gen.add(m)
    todo += re.findall(r'(?m)^import (\S+)', open(gen_path(m)).read())
gen = sorted(gen)

templ_parts = []
for m in gen:
    imps, body = split_header(open(gen_path(m)).read())
    if m == 'BoxKGen.Templates' and body.count('\n') > MAX_LINES:
        # Split the template definitions into parts of at most MAX_LINES lines.
        lines = body.split('\n')
        pre = '\n'.join(l for l in lines if l.strip() and not l.startswith('def t')
                        and not l.startswith('end BoxKGen')) + '\n'
        defs = [l for l in lines if l.startswith('def t')]
        for k in range(0, len(defs), MAX_LINES):
            name = f'BoxKGen.Templates{k // MAX_LINES}'
            write(name.replace('.', '/') + '.lean', to_module(templ_parts[-1:] or imps,
                  pre + '\n'.join('noncomputable ' + d for d in defs[k:k + MAX_LINES]) + '\nend BoxKGen\n'))
            templ_parts.append(name)
        write('BoxKGen/Templates.lean', to_module(templ_parts[-1:], ''))
        continue
    write(m.replace('.', '/') + '.lean', to_module(imps, re.sub(r'(?m)^def ', 'noncomputable def ', body)))

# Lake builds as many modules at once as there are cores, and a certificate module needs up to
# about 13 GB. The certificate modules (box slices, shared window checks) form CHAINS chains, each
# module importing the previous one in its chain, so at most CHAINS of them build at once on any
# machine. Modules go to the chain with the least build time so far (build_times.txt, seconds
# measured with two Lean processes), longest first; WinKU.Shared.D comes first, since the other
# shared window modules import it.
#
CHAINS = 2
times = dict((m, float(t)) for m, t in (l.split() for l in open(os.path.join(TOOLS, 'build_times.txt'))))
members = [m for m in gen if re.fullmatch(r'BoxKGen\.N\d+x\d+\.S\d+|WinKU\.Shared\.(D|T\d+|G\d+)', m)]
assert set(members) == set(times), set(members) ^ set(times)
members.sort(key=lambda m: (m != 'WinKU.Shared.D', -times[m], m))
chains = [[] for _ in range(CHAINS)]
for m in members:
    min(chains, key=lambda c: sum(times[x] for x in c)).append(m)
for c in chains:
    for prev, m in zip(c, c[1:]):
        p = os.path.join(OUT, *m.split('.')) + '.lean'
        t = open(p).read()
        t = t.replace('\n\n@[expose] public section\n',
                      f'\n-- Build order only (at most {CHAINS} certificate modules build at once).\n'
                      f'import {prev}\n\n@[expose] public section\n', 1)
        open(p, 'w').write(t)

# Every certificate is a kernel check (decide +kernel).
for r, ds, fs in os.walk(OUT):
    ds[:] = [d for d in ds if d != '.lake']
    for f in fs:
        if f.endswith('.lean'):
            t = open(os.path.join(r, f)).read()
            assert 'native_decide' not in re.sub(r'--.*|/-.*?-/', '', t, flags=re.S), f

# Palomar files: the challenges, solutions and comparator configurations (palomar.py).
#
subprocess.run([sys.executable, os.path.join(TOOLS, 'palomar.py'), OUT], check=True)
print('generated modules', len(gen), 'templates parts', len(templ_parts))

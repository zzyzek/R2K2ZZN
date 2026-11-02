#!/usr/bin/env python3
"""Move the definitions of the main statements into one module, ZZN/Statement.lean.

Palomar's comparator checks a Challenge file (the definitions plus the theorems, importing only
Mathlib) against the library. Lean shares auxiliary definitions (matchers) only within a module,
so the library must define the statement closure in one module that the Challenge copies.

DECLS lists the closure as lines `DECL module first_line last_line name` (the declaration ranges,
docstrings included, printed by a metaprogram over the built library). Each range is cut from its
module and written to Statement.lean in import order, wrapped in the namespaces and `open`s in
effect at its old position; the module then imports ZZN.Statement.

With TARGET and BASE, the declarations go to TARGET instead, which imports only BASE (used for
ZZN/TimedStatement.lean, the timed definitions of the step bounds, on top of ZZN.Statement).

usage: extract_statement.py DECLS [TARGET BASE]   (run from lean/)
"""
import os, re, sys
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
HDR = ("-- SPDX-License-Identifier: CC0-1.0\n"
       "-- To the extent possible under law, the author has waived all copyright and related or\n"
       "-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).\n")

def path(m): return os.path.join(ROOT, *m.split('.')) + '.lean'
def imports(m): return [x.group(1) for l in open(path(m)) for x in [re.match(r'import\s+(\S+)', l)] if x]

TARGET, BASE = (sys.argv[2], sys.argv[3]) if len(sys.argv) > 3 else ('ZZN.Statement', 'Mathlib')

ranges = defaultdict(set)
for l in open(sys.argv[1]):
    _, m, a, b, _n = l.split()
    ranges[m].add((int(a), int(b)))
# A structure, its constructor and its fields share one range; keep each range once, and drop
# ranges inside another.
ranges = {m: sorted(r for r in rs if not any(o != r and o[0] <= r[0] and r[1] <= o[1] for o in rs))
          for m, rs in ranges.items()}
mods = set(ranges)

# Import order: a module after every moved module it imports, directly or not.
order, seen = [], set()
memo = {}
def closure_of(m):
    if m in memo: return memo[m]
    memo[m] = set()
    if os.path.exists(path(m)):
        for i in imports(m):
            memo[m] |= {i} | closure_of(i)
    return memo[m]
def visit2(m):
    if m in seen: return
    seen.add(m)
    for j in sorted(closure_of(m) & mods): visit2(j)
    order.append(m)
for m in sorted(mods): visit2(m)

def context(lines, upto):
    """Namespaces, and `open` / `variable` lines, in effect before line `upto` (1-based)."""
    stack, scoped = [], []
    for l in lines[:upto - 1]:
        s = l.strip()
        if mm := re.match(r'namespace\s+(\S+)', s):
            stack.append(('ns', mm.group(1)))
        elif re.match(r'(noncomputable\s+)?section\b', s):
            stack.append(('sec', ''))
        elif re.match(r'end(\s+\S+)?$', s):
            if stack: stack.pop()
            scoped = [(d, x) for d, x in scoped if d <= len(stack)]
        elif (s.startswith('open ') or s.startswith('variable ')) and not s.endswith(' in'):
            scoped.append((len(stack), s))
    return [n for k, n in stack if k == 'ns'], [x for _, x in scoped]

out = []
imps = set()
for m in order:
    lines = open(path(m)).read().split('\n')
    rs = sorted(ranges[m])
    for i in imports(m):
        imps.add(i)
    keep = [True] * len(lines)
    for a, b in rs:
        nss, opens = context(lines, a)
        text = '\n'.join(lines[a - 1:b])
        # Consecutive declarations of one module in the same context share a block; within a
        # block, declarations follow each other without blank lines (Challenge.lean is this file
        # plus the theorems, under Palomar's 1 000-line limit).
        text = re.sub(r'\n\s*\n', '\n', text.strip('\n'))
        if out and out[-1][0] == (m, tuple(nss), tuple(opens)):
            out[-1][1].append(text)
        else:
            out.append(((m, tuple(nss), tuple(opens)), [text]))
        for k in range(a - 1, b): keep[k] = False
    # The module keeps everything else and imports the statement module.
    new = [l for l, k in zip(lines, keep) if k]
    first = next(k for k, l in enumerate(new) if l.startswith('import '))
    new.insert(first, f'import {TARGET}')
    open(path(m), 'w').write('\n'.join(new))

# Imports of the statement module: what the moved modules import, minus the moved modules and
# anything that imports one of them.
imps = {i for i in imps if i not in mods and not (closure_of(i) & mods)}
if BASE == 'Mathlib':
    # Mathlib brings the rest (Std, Mathlib submodules); the Challenge may import only Mathlib.
    assert all(i == 'Mathlib' or i.startswith('Mathlib.') or i.startswith('Std.') for i in imps), imps
imps = {BASE}
blocks = ''.join(f"\n-- {m}\n" + ''.join(f"namespace {n}\n" for n in nss) +
                 ''.join(o + '\n' for o in opens) + '\n'.join(texts) + '\n' +
                 ''.join(f"end {n}\n" for n in reversed(nss))
                 for (m, nss, opens), texts in out)
DOC = '''
/-!
# The statements: definitions

The definitions the main theorems mention, in one module (Palomar's `Challenge.lean` is this file
plus the theorems): grids and paths (`GridHam`), instances and solutions (`ZZN.Defs`), the
forbidden-pattern catalogue (`ZZN.Catalogue`), the plug DP for thin rectangles (`ZZN.Thin`), the
decision procedure `solvableB`, and the construction `solveZZN`. Each block names the module it
was moved from, where its lemmas remain.
-/
''' if TARGET == 'ZZN.Statement' else '''
/-!
# The step bounds: definitions

The definitions the step bounds mention beyond `ZZN.Statement`, in one module (Palomar's
`Challenge.lean` is the part of `ZZN.Statement` they use, this file, and the theorems): the
step-counting monad `TimeM`, the counted decision procedure `solvableBT` with its constant `Cdec`,
and the counted construction `solveZZNT`. Each block names the module it was moved from, where its
lemmas remain.
-/
'''
body = HDR + ''.join(f"import {i}\n" for i in sorted(imps)) + DOC + blocks
open(path(TARGET), 'w').write(body)
print('moved', sum(len(v) for v in ranges.values()), 'declarations from', len(mods), 'modules;',
      'statement lines', body.count('\n'), 'imports', sorted(imps))

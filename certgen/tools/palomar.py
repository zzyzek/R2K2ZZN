#!/usr/bin/env python3
"""Write proof/'s Palomar files: two registrations, each a challenge, a solution and a comparator
configuration.

- Decide: `solvableBRT_main` (decision procedure with its step bound) and `fires3T_iff_solvable`
  (the catalogue characterization), in ChallengeDecide.lean, SolutionDecide.lean,
  comparator_decide.json.
- Construct: `solveZ3RT_main` (construction with its step bound), in ChallengeConstruct.lean,
  SolutionConstruct.lean, comparator_construct.json.

A challenge holds the library declarations its statements depend on, copied without
documentation (Palomar allows 1 000 lines), then the theorems with `sorry`. The declarations are
listed, with their source ranges, in palomar_{decide,construct}_decls.txt, written by Closure.lean
(`MOD` lines give the modules in import order). Both statements together need more than 1 000
lines, so they are registered separately.

usage: palomar.py PROOF_DIR   (run by export.py)
"""
import os, re, sys

OUT = sys.argv[1]
TOOLS = os.path.dirname(os.path.abspath(__file__))

HDR = ("/-\nSPDX-License-Identifier: CC0-1.0\n"
       "Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.\n-/\n")

# Registrations: (suffix, declaration list, [(module, theorem)], description).
REGS = [
    ('Decide', 'palomar_decide_decls.txt',
     [('ZZN.Timed.DecideR', 'solvableBRT_main'), ('ZZN.Timed.Main', 'fires3T_iff_solvable')]),
    ('Construct', 'palomar_construct_decls.txt',
     [('ZZN.Timed.RoundTimeR', 'solveZ3RT_main')]),
]

# Definitions whose matchers would otherwise be shared with those of declarations copied before
# them. Lean shares a matcher only within a module and only between definitions with the same
# code-generation setting, so `genMatcherCode false` keeps these apart, as they are in the library.
#
NOREUSE = ['optsL', 'stretchT', 'chainT', 'insSortedT', 'crossRowsT', 'flipRowsT', 'extLT', 'segNewRT',
           'thinSolveWRT', 'liftBT', 'liftBTT']


def text_of(m):
    """A module of proof/."""
    return open(os.path.join(OUT, *m.split('.')) + '.lean').read()


def theorems(reg):
    out = ''
    for m, t in reg:
        src = text_of(m)
        stmt = re.search(rf'(?ms)^(/--(?:(?!-/).)*-/\n)?theorem {t}\b.*?(?=:=)', src)[0].rstrip()
        ns = 'ZZN.T' if 'namespace ZZN.T\n' in src else 'ZZN'
        out += f"namespace {ns}\nopen GridHam\n{stmt} := by\n  sorry\nend {ns}\n"
    return out


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


def read_decls(path):
    """(modules in import order, {module: [(start, end, name)]})."""
    mods, decls = [], {}
    for l in open(path):
        f = l.split()
        if f[0] == 'MOD':
            mods.append(f[1])
        else:
            _, m, a, b, n = f
            decls.setdefault(m, []).append((int(a), int(b), n))
    assert set(decls) <= set(mods), set(decls) - set(mods)
    return [m for m in mods if m in decls], decls


def subset(m, ds):
    """The declarations of module m at the given source line ranges, in their contexts."""
    lines = text_of(m).split('\n')
    rs = set()
    for a, b, n in ds:
        # The range must still hold the declaration (ranges go stale when the module changes).
        # Generated names (instances, constructors, fields) are checked through their parent.
        last = n.split('.')[-1] if not n.split('.')[-1].startswith('inst') else 'instance'
        assert any(x in '\n'.join(lines[a - 1:b]) for x in (last, n.split('.')[-2])), (m, n)
        rs.add((a, b))
    rs = sorted(r for r in rs if not any(o != r and o[0] <= r[0] and r[1] <= o[1] for o in rs))
    out = []
    for a, b in rs:
        ctx = context(lines, a)
        text = '\n'.join(lines[a - 1:b]).strip('\n')
        if out and out[-1][0] == ctx: out[-1][1].append(text)
        else: out.append((ctx, [text]))
    return ''.join(''.join(f"namespace {n}\n" for n in nss) + ''.join(o + '\n' for o in opens) +
                   '\n'.join(texts) + '\n' + ''.join(f"end {n}\n" for n in reversed(nss))
                   for (nss, opens), texts in out)


def bare(text):
    """Without docstrings, comments and blank lines (kept under Palomar's 1 000-line limit)."""
    text = re.sub(r'(?ms)^\s*/-[-!].*?-/\n', '', text)
    text = re.sub(r'(?m)^\s*--.*\n', '', text)
    return re.sub(r'\n\s*\n', '\n', text)


def noreuse(text):
    for d in NOREUSE:
        text = re.sub(rf'(?m)^def {d}\b', f'set_option bootstrap.genMatcherCode false in\ndef {d}', text)
    return text


def merge_blocks(text):
    """Join `end N` / `namespace N` when both blocks open the same names and declare no variables."""
    out, opens, has_var = [], None, False
    lines = text.split('\n')
    i = 0
    while i < len(lines):
        l = lines[i]
        m = re.match(r'end (\S+)$', l)
        if m and i + 1 < len(lines) and lines[i + 1] == f'namespace {m.group(1)}':
            j = i + 2
            nxt = []
            while j < len(lines) and lines[j].startswith('open '):
                nxt.append(lines[j]); j += 1
            nvar = j < len(lines) and lines[j].startswith('variable ')
            if nxt == opens and not has_var and not nvar:
                i = j
                continue
        if re.match(r'namespace ', l):
            opens, has_var = [], False
        elif l.startswith('open ') and opens is not None and out and (
                out[-1].startswith('namespace ') or out[-1].startswith('open ')):
            opens.append(l)
        elif l.startswith('variable '):
            has_var = True
        out.append(l)
        i += 1
    return '\n'.join(out)


def comparator(chal, sol, reg):
    names = ', '.join(f'"{"ZZN.T" if "namespace ZZN.T" in text_of(m) else "ZZN"}.{t}"' for m, t in reg)
    return f'''{{
  "challenge_module": "{chal}",
  "solution_module": "{sol}",
  "theorem_names": [{names}],
  "definition_names": [],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
  "enable_nanoda": true
}}
'''


def write(rel, text):
    open(os.path.join(OUT, rel), 'w').write(text)


for old in ['Challenge.lean', 'Solution.lean', 'comparator.json']:
    if os.path.exists(os.path.join(OUT, old)):
        os.remove(os.path.join(OUT, old))

for suf, dfile, reg in REGS:
    mods, decls = read_decls(os.path.join(TOOLS, dfile))
    body = ''.join(bare(subset(m, decls[m])) for m in mods)
    chal = (HDR + "module\n\npublic import Mathlib\n\n@[expose] public section\n\n"
            "-- Undocumented copies (1 000-line limit) of the definitions the statements use, from\n" +
            ''.join(f"-- {m}\n" for m in mods) +
            merge_blocks(noreuse(body) + theorems(reg)))
    write(f'Challenge{suf}.lean', chal)
    write(f'Solution{suf}.lean', HDR + "module\n\n-- The solution for Palomar's comparator: the registered theorems, proved in\n"
          f"-- {', '.join('`' + m.replace('.', '/') + '.lean`' for m in sorted({m for m, _ in reg}))}.\n--\n" +
          ''.join(f"public import {m}\n" for m in sorted({m for m, _ in reg})))
    write(f'comparator_{suf.lower()}.json', comparator(f'Challenge{suf}', f'Solution{suf}', reg))
    n, kib = chal.count('\n'), len(chal.encode()) / 1024
    assert n <= 1000 and kib <= 100, (suf, n, kib)
    print(f'Challenge{suf}.lean: {n} lines, {kib:.1f} KiB')

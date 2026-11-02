#!/usr/bin/env python3
"""Write the generated certificate modules into proof/, and proof/'s Palomar files.

The generated modules (certgen/gen: BoxKGen, WinKU, FinalN, from regen.sh) become modules of the
Lean module system with `@[expose] public section`, so definitions unfold across modules for the
kernel checks. Their data definitions are `noncomputable`: Lake would otherwise emit C for the
large literals, which costs about as much as checking them. The template set is split into parts
of at most MAX_LINES lines (Palomar allows 10 000 lines per file).

Challenge.lean, the Palomar registration, holds the counted statements: the part of
proof/ZZN/Statement.lean they use (the declaration ranges in timed_statement_decls.txt) and
proof/ZZN/TimedStatement.lean, without documentation, then the registered theorems with `sorry`.
The counted procedures return what the plain ones do (`solvableBT_ret`, `solveZZNT_ret`), so these
theorems carry correctness, the characterization and the step bounds in one file under Palomar's
1 000-line limit. Solution.lean and comparator.json name the same theorems.

usage: export.py PROOF_DIR   (run by regen.sh)
"""
import os, re, shutil, sys

OUT = sys.argv[1]
TOOLS = os.path.dirname(os.path.abspath(__file__))
GEN = os.path.join(os.path.dirname(TOOLS), 'gen')
MAX_LINES = 9000
# Registered with Palomar: (module, theorem).
REGISTERED = [('ZZN.Timed.Main', 'solvableBT_main'), ('ZZN.Timed.Main', 'fires3T_iff_solvable'),
              ('ZZN.Timed.Construct', 'solveZZNT_main')]

HDR = ("/-\nSPDX-License-Identifier: CC0-1.0\n"
       "Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.\n-/\n")

def text_of(m):
    """A module of proof/."""
    return open(os.path.join(OUT, *m.split('.')) + '.lean').read()

def module_body(text):
    """The body of a proof/ module, after its header."""
    return text.split('@[expose] public section\n\n', 1)[1]

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

# No native_decide anywhere in the project.
for r, ds, fs in os.walk(OUT):
    ds[:] = [d for d in ds if d != '.lake']
    for f in fs:
        if f.endswith('.lean'):
            t = open(os.path.join(r, f)).read()
            assert 'native_decide' not in re.sub(r'--.*|/-.*?-/', '', t, flags=re.S), f

# Palomar files.
def module_imports(text):
    return re.findall(r'(?m)^public import (\S+)$', text.split('@[expose] public section', 1)[0])

# The statement modules import only Mathlib, and ZZN.Statement, respectively.
assert module_imports(text_of('ZZN.Statement')) == ['Mathlib']
assert module_imports(text_of('ZZN.TimedStatement')) == ['ZZN.Statement']

def theorems(reg, compact=False):
    out = ''
    for m, t in reg:
        src = text_of(m)
        stmt = re.search(rf'(?ms)^(/--(?:(?!-/).)*-/\n)?theorem {t}\b.*?(?=:=)', src)[0].rstrip()
        ns = 'ZZN.T' if 'namespace ZZN.T\n' in src else 'ZZN'
        out += (f"namespace {ns}\nopen GridHam\n{stmt} := by\n  sorry\nend {ns}\n" if compact else
                f"\nnamespace {ns}\n\nopen GridHam\n\n{stmt} := by\n  sorry\n\nend {ns}\n")
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

def subset(m, decls):
    """The declarations of module m at the given (lean/ source) line ranges, in their contexts."""
    lines = text_of(m).split('\n')
    rs = set()
    for l in open(decls):
        _, mm, a, b, n = l.split()
        assert mm == m
        a, b = int(a), int(b)
        # The range must still hold the declaration (ranges go stale when the module changes).
        # Generated names (instances, constructors, fields) are checked through their parent.
        last = n.split('.')[-1] if not n.split('.')[-1].startswith('inst') else 'instance'
        assert any(x in '\n'.join(lines[a - 1:b]) for x in (last, n.split('.')[-2])), n
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

def comparator(chal, sol, reg):
    names = ', '.join(f'"{"ZZN.T" if "Timed" in m else "ZZN"}.{t}"' for m, t in reg)
    return f'''{{
  "challenge_module": "{chal}",
  "solution_module": "{sol}",
  "theorem_names": [{names}],
  "definition_names": [],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
  "enable_nanoda": true
}}
'''

t_body = module_body(text_of('ZZN.TimedStatement'))
def bare(text):
    """Without docstrings, comments and blank lines (kept under Palomar's 1 000-line limit)."""
    text = re.sub(r'(?ms)^\s*/-[-!].*?-/\n', '', text)
    text = re.sub(r'(?m)^\s*--.*\n', '', text)
    return re.sub(r'\n\s*\n', '\n', text)

# Timed definitions whose matchers would otherwise be shared with ZZN.Statement ones (see below).
NOREUSE = ['optsL', 'stretchT', 'chainT', 'insSortedT']

def noreuse(text):
    for d in NOREUSE:
        text, k = re.subn(rf'(?m)^def {d}\b', f'set_option bootstrap.genMatcherCode false in\ndef {d}', text)
        assert k == 1, d
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

chal = to_module(['Mathlib'],
                  "-- Undocumented copies (1 000-line limit) of ZZN/Statement.lean (part) and\n"
                  "-- ZZN/TimedStatement.lean.\n" +
                  bare(subset('ZZN.Statement', os.path.join(TOOLS, 'timed_statement_decls.txt'))) +
                  # A matcher is shared within a module only between definitions with the same
                  # code-generation setting; this keeps the NOREUSE definitions from sharing the
                  # matchers of the ZZN.Statement part, as they cannot in the library.
                  merge_blocks(noreuse(bare(t_body)) + theorems(REGISTERED, compact=True)))
write('Challenge.lean', chal)
write('Solution.lean', HDR + "module\n\n-- The solution for Palomar's comparator: the registered theorems, proved in\n"
      "-- `ZZN/Timed/Main.lean` and `ZZN/Timed/Construct.lean`.\n--\n" +
      ''.join(f"public import {m}\n" for m in sorted({m for m, _ in REGISTERED})))
open(os.path.join(OUT, 'comparator.json'), 'w').write(comparator('Challenge', 'Solution', REGISTERED))
print('generated modules', len(gen), 'templates parts', len(templ_parts),
      'challenge lines', chal.count('\n'), 'KiB', len(chal.encode()) // 1024)

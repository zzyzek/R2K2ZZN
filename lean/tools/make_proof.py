#!/usr/bin/env python3
"""Export the kernel-checked proof as a self-contained Lake project (Lean module system).

The project holds the generated certificate modules (gen/: BoxKGen, WinKU, FinalN), the library
modules they and the main results import, and the Palomar files. Every file is a `module` with
`@[expose] public section`, so definitions unfold across modules for the kernel checks.

`ZZN.Main` is replaced: `passes_iff_solvable` comes from `passes_iff_solvable_K` (FinalN, checked
by the kernel) instead of the `native_decide` certificates of `ZZN.Final` / `ZZN.Boxes`, which are
not exported. The results built on it (the decision procedure, the construction, the time
bounds) follow unchanged.

Challenge.lean, the one Palomar registration, holds the counted statements: the part of
ZZN/Statement.lean they use (the declaration ranges in proof_files/timed_statement_decls.txt) and
ZZN/TimedStatement.lean, without documentation, then the registered theorems with `sorry`. The
counted procedures return what the plain ones do (`solvableBT_ret`, `solveZZNT_ret`), so these
theorems carry correctness, the characterization and the step bounds in one file under Palomar's
1 000-line limit.

usage: GEN=DIR make_proof.py OUT_DIR   (GEN: generated modules, default lean/gen)
"""
import os, re, shutil, sys

OUT = sys.argv[1]
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GEN = os.environ.get('GEN', os.path.join(ROOT, 'gen'))
MAX_LINES = 9000
# Main results exported besides the generated modules (their statements are in ZZN.Statement).
RESULTS = ['ZZN.Main', 'ZZN.Thin.Decide', 'ZZN.Constr.Main', 'ZZN.Timed.Main', 'ZZN.Timed.Construct']
# Registered with Palomar: (module, theorem).
REGISTERED = [('ZZN.Timed.Main', 'solvableBT_main'), ('ZZN.Timed.Main', 'fires3T_iff_solvable'),
              ('ZZN.Timed.Construct', 'solveZZNT_main')]

HDR = ("/-\nSPDX-License-Identifier: CC0-1.0\n"
       "Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.\n-/\n")

MAIN = '''import FinalN

/-!
# The characterization

On rectangles with both sides at least 11, an instance of two-color Zig-Zag Numberlink is
solvable exactly when it passes the forbidden-pattern catalogue. The proof is
`passes_iff_solvable_K` (`FinalN.lean`): Theorem A over the boxes (`BoxKGen`) and Theorem B over
the windows (`WinKU`), every certificate checked by the kernel.
-/

namespace ZZN

/-- **Passing the catalogue is equivalent to solvability**, for both sides at least 11. -/
theorem passes_iff_solvable (I : Inst) (hwf : I.WellFormed) (hw : 11 ≤ I.w) (hh : 11 ≤ I.h) :
    Passes I ↔ Solvable I :=
  passes_iff_solvable_K I hwf hw hh

end ZZN
'''

def lib_src(m):
    p = os.path.join(ROOT, *m.split('.')) + '.lean'
    return p if os.path.exists(p) else None

def gen_src(m):
    p = os.path.join(GEN, *m.split('.')) + '.lean'
    return p if os.path.exists(p) else None

def text_of(m):
    if m == 'ZZN.Main': return MAIN
    return open(gen_src(m) or lib_src(m)).read()

def imports(m):
    return [x.group(1) for l in text_of(m).split('\n') for x in [re.match(r'import\s+(\S+)', l)] if x]

def closure(roots):
    seen, st = set(), list(roots)
    while st:
        m = st.pop()
        if m in seen or not (m == 'ZZN.Main' or gen_src(m) or lib_src(m)): continue
        seen.add(m); st += imports(m)
    return seen

mods = closure(['FinalN'] + RESULTS)
assert 'ZZN.Final' not in mods and 'ZZN.Boxes' not in mods
assert not any('native_decide' in re.sub(r'--.*|/-.*?-/', '', text_of(m), flags=re.S) for m in mods)

def split_header(text):
    """(imports, body): import lines, and the rest without the leading comment header."""
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

# Replace everything but the build directory (.lake: Mathlib and built modules).
os.makedirs(OUT, exist_ok=True)
for e in os.listdir(OUT):
    if e == '.lake': continue
    p = os.path.join(OUT, e)
    shutil.rmtree(p) if os.path.isdir(p) else os.remove(p)

templ_parts = []
for m in sorted(mods):
    imps, body = split_header(text_of(m))
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
    if gen_src(m):
        # Certificate data is only read by the kernel; without `noncomputable`, Lake's C output
        # for the large literals costs about as much as checking them.
        body = re.sub(r'(?m)^def ', 'noncomputable def ', body)
    write(m.replace('.', '/') + '.lean', to_module(imps, body))

# Palomar files.
s_imps, _ = split_header(text_of('ZZN.Statement'))
assert s_imps == ['Mathlib'], s_imps

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

t_imps, t_body = split_header(text_of('ZZN.TimedStatement'))
assert t_imps == ['ZZN.Statement'], t_imps
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
                  bare(subset('ZZN.Statement', os.path.join(ROOT, 'tools', 'proof_files',
                                                           'timed_statement_decls.txt'))) +
                  # A matcher is shared within a module only between definitions with the same
                  # code-generation setting; this keeps the NOREUSE definitions from sharing the
                  # matchers of the ZZN.Statement part, as they cannot in the library.
                  merge_blocks(noreuse(bare(t_body)) + theorems(REGISTERED, compact=True)))
write('Challenge.lean', chal)
write('Solution.lean', HDR + "module\n\n-- The solution for Palomar's comparator: the registered theorems, proved in\n"
      "-- `ZZN/Timed/Main.lean` and `ZZN/Timed/Construct.lean`.\n--\n" +
      ''.join(f"public import {m}\n" for m in sorted({m for m, _ in REGISTERED})))
open(os.path.join(OUT, 'comparator.json'), 'w').write(comparator('Challenge', 'Solution', REGISTERED))
libs = sorted({m.split('.')[0] for m in mods} - {'FinalN'})
lake = (HDR + "import Lake\nopen Lake DSL\n\npackage «r2k2zzn» where\n\n"
        "require mathlib from git\n  \"https://github.com/leanprover-community/mathlib4.git\"\n\n"
        "-- The main results; their imports bring in the generated certificate modules.\n--\n"
        "@[default_target]\nlean_lib «Results» where\n"
        f"  roots := #[{', '.join('`' + m for m in RESULTS)}]\n  precompileModules := false\n\n"
        "lean_lib «FinalN» where\n  precompileModules := false\n\n")
for l in libs:
    lake += f"lean_lib «{l}» where\n  globs := #[.submodules `{l}]\n  precompileModules := false\n\n"
lake += ("-- The Palomar registry statement (`Challenge`, imports only Mathlib) and its solution.\n--\n"
         "lean_lib «Challenge» where\n\nlean_lib «Solution» where\n")
open(os.path.join(OUT, 'lakefile.lean'), 'w').write(lake)
for f in ['lean-toolchain', 'lake-manifest.json']:
    shutil.copy(os.path.join(ROOT, f), os.path.join(OUT, f))
for f in ['README.md', 'formalization.yaml']:
    shutil.copy(os.path.join(ROOT, 'tools', 'proof_files', f), os.path.join(OUT, f))
AXIOMS = ['ZZN.solvableB_iff', 'ZZN.passes_iff_solvable', 'ZZN.solveZZN_sound', 'ZZN.solveZZN_complete',
          'ZZN.passes_iff_solvable_K', 'ZZN.T.solvableBT_main', 'ZZN.T.solveZZNT_time', 'ZZN.T.solveZZNT_ret',
          'ZZN.T.solveZZNT_main', 'ZZN.T.fires3T_iff_solvable']
write('Axioms.lean', HDR + "module\n\n" + ''.join(f"public import {m}\n" for m in RESULTS) +
      "\n-- The axioms of the main results; expected: propext, Classical.choice, Quot.sound.\n--\n" +
      ''.join(f"#print axioms {a}\n" for a in AXIOMS))
print('modules', len(mods), 'templates parts', len(templ_parts),
      'challenge lines', chal.count('\n'), 'KiB', len(chal.encode()) // 1024)

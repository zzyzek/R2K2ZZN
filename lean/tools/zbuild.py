#!/usr/bin/env python3
"""Rebuild stale ZZN modules in import order with P parallel `lean` workers.

Lake (5.0.0) has no job-count option. A module is rebuilt when its source is newer than its
.olean or a dependency was rebuilt. Outputs go to Lake's own .lake/build/lib/lean, so
`lake env lean` sees them (Lake's traces are not updated).

usage: zbuild.py P TARGET_MODULE [TARGET_MODULE ...]
"""
import os, re, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor, FIRST_COMPLETED, wait

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, '.lake', 'build', 'lib', 'lean')
LEAN = subprocess.run(['lake', 'env', 'which', 'lean'], cwd=ROOT, capture_output=True, text=True).stdout.strip()
env = dict(os.environ)
env['LEAN_PATH'] = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, capture_output=True,
                                  text=True).stdout.strip()

def src(m): return os.path.join(ROOT, *m.split('.')) + '.lean'
def olean(m): return os.path.join(OUT, *m.split('.')) + '.olean'
def ilean(m): return os.path.join(OUT, *m.split('.')) + '.ilean'

def deps(m):
    out = []
    for line in open(src(m)):
        mm = re.match(r'import\s+(\S+)', line)
        if mm and os.path.exists(src(mm.group(1))):
            out.append(mm.group(1))
    return out

def closure(targets):
    seen, order = set(), []
    def visit(m):
        if m in seen: return
        seen.add(m)
        for d in deps(m): visit(d)
        order.append(m)
    for t in targets: visit(t)
    return order

def main():
    P = int(sys.argv[1]); targets = sys.argv[2:]
    order = closure(targets)
    D = {m: deps(m) for m in order}
    stale = set()
    for m in order:
        o = olean(m)
        if (not os.path.exists(o) or os.path.getmtime(src(m)) > os.path.getmtime(o) or
                any(d in stale or os.path.getmtime(olean(d)) > os.path.getmtime(o) for d in D[m])):
            stale.add(m)
    todo = [m for m in order if m in stale]
    print(f'{len(todo)} stale of {len(order)}', flush=True)
    done = set(m for m in order if m not in stale)
    running = {}
    t0 = time.time()
    def run(m):
        os.makedirs(os.path.dirname(olean(m)), exist_ok=True)
        t = time.time()
        r = subprocess.run([LEAN, '-o', olean(m), '-i', ilean(m), src(m)], cwd=ROOT, env=env,
                           capture_output=True, text=True)
        return m, r.returncode, r.stdout + r.stderr, time.time() - t
    with ThreadPoolExecutor(P) as ex:
        while todo or running:
            for m in list(todo):
                if len(running) >= P: break
                if all(d in done for d in D[m]):
                    todo.remove(m); running[ex.submit(run, m)] = m
            if not running:
                print('blocked', todo, flush=True); return 1
            fin, _ = wait(running, return_when=FIRST_COMPLETED)
            for fu in fin:
                m, rc, out, dt = fu.result(); del running[fu]
                print(f'{"OK " if rc == 0 else "ERR"} {m} {dt:.0f}s', flush=True)
                if rc != 0:
                    print(out[-3000:], flush=True); return 1
                done.add(m)
    print(f'all done {time.time() - t0:.0f}s', flush=True)
    return 0

sys.exit(main())

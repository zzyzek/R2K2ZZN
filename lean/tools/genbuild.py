#!/usr/bin/env python3
"""Build generated modules under gen/ with a fixed number of parallel `lean` workers.

Lake (5.0.0) has no job-count option and starts one lean process per hardware thread, which
exceeds memory on these modules. This driver compiles each module with `lean -o` into
genbuild/ (on LEAN_PATH), in import order, with P workers.

usage: genbuild.py P TARGET_MODULE [TARGET_MODULE ...]
"""
import os, re, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor, FIRST_COMPLETED, wait

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GEN = os.path.join(ROOT, 'gen')
OUT = os.path.join(ROOT, 'genbuild')
base_path = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, capture_output=True,
                           text=True).stdout.strip()
env = dict(os.environ, LEAN_PATH=OUT + ':' + base_path)
LEAN = subprocess.run(['lake', 'env', 'which', 'lean'], cwd=ROOT, capture_output=True, text=True).stdout.strip()

def src(m): return os.path.join(GEN, *m.split('.')) + '.lean'
def olean(m): return os.path.join(OUT, *m.split('.')) + '.olean'

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

def stale(m):
    o = olean(m)
    return not os.path.exists(o) or os.path.getmtime(o) < os.path.getmtime(src(m))

def build(m):
    os.makedirs(os.path.dirname(olean(m)), exist_ok=True)
    t = time.time()
    r = subprocess.run([LEAN, '-o', olean(m), src(m)], env=env, cwd=ROOT, capture_output=True, text=True)
    ok = r.returncode == 0 and 'error' not in r.stdout
    return m, ok, time.time() - t, (r.stdout + r.stderr)[-2000:]

def main():
    P = int(sys.argv[1]); targets = sys.argv[2:]
    order = [m for m in closure(targets)]
    todo = [m for m in order if stale(m)]
    done = set(m for m in order if m not in todo)
    pending = {m: set(d for d in deps(m) if d in todo) for m in todo}
    t0 = time.time(); total = 0.0; nb = 0
    with ThreadPoolExecutor(P) as ex:
        running = {}
        while pending or running:
            ready = [m for m, ds in pending.items() if not (ds - done)]
            while ready and len(running) < P:
                m = ready.pop(0); del pending[m]
                running[ex.submit(build, m)] = m
            if not running:
                print('stuck: unresolved dependencies', file=sys.stderr); sys.exit(1)
            fin, _ = wait(running, return_when=FIRST_COMPLETED)
            for f in fin:
                m, ok, dt, log = f.result(); del running[f]
                total += dt; nb += 1
                if not ok:
                    print(f'FAIL {m} ({dt:.0f}s)\n{log}', flush=True); sys.exit(1)
                done.add(m)
                print(f'ok {m} {dt:.1f}s [{nb}/{len(todo)}] wall {time.time() - t0:.0f}s', flush=True)
    print(f'DONE {nb} modules, CPU {total:.0f}s, wall {time.time() - t0:.0f}s', flush=True)

main()

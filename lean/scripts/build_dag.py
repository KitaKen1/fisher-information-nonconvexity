#!/usr/bin/env python3
"""Build every module reachable from the root `Fisher41` in dependency order, running at most
N concurrent `lake build <module>` jobs (each compiles exactly one module, because all of its
imports are already built when it starts).  Usage: `python3 scripts/build_dag.py [N]`."""
import os
import re
import subprocess
import sys
import time
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
N = int(sys.argv[1]) if len(sys.argv) > 1 else 1


def modules():
    res = {'Fisher41': os.path.join(ROOT, 'Fisher41.lean')}
    for dp, _, fns in os.walk(os.path.join(ROOT, 'Fisher41')):
        for fn in fns:
            if fn.endswith('.lean'):
                p = os.path.join(dp, fn)
                res[os.path.relpath(p, ROOT)[:-5].replace(os.sep, '.')] = p
    return res


MODS = modules()
DEPS = {}
for m, p in MODS.items():
    with open(p, encoding='utf-8') as fh:
        imps = re.findall(r'^import\s+(\S+)', fh.read(), re.M)
    DEPS[m] = {i for i in imps if i in MODS}

NEED, stack = set(), ['Fisher41']
while stack:
    m = stack.pop()
    if m not in NEED:
        NEED.add(m)
        stack.extend(DEPS[m])


def build(m):
    t = time.time()
    for _ in range(2):  # one retry: concurrent `lake build` runs can fail transiently
        r = subprocess.run(['lake', 'build', m], cwd=ROOT, capture_output=True, text=True)
        if r.returncode == 0:
            break
    return m, r.returncode == 0, time.time() - t, r.stdout + r.stderr


def main():
    print(f'{len(NEED)} modules, at most {N} concurrent jobs', flush=True)
    t0 = time.time()
    done, futs = set(), {}
    with ThreadPoolExecutor(N) as ex:
        while len(done) < len(NEED):
            running = set(futs.values())
            ready = sorted(m for m in NEED - done - running if DEPS[m] <= done)
            for m in ready[:N - len(futs)]:
                futs[ex.submit(build, m)] = m
            fin, _ = wait(futs, return_when=FIRST_COMPLETED)
            for f in fin:
                m, ok, dt, out = f.result()
                del futs[f]
                print(f'{"OK " if ok else "ERR"} {dt:6.0f}s  {m}', flush=True)
                if not ok:
                    print(out[-4000:], flush=True)
                    sys.exit(1)
                done.add(m)
    print(f'all {len(done)} modules built in {time.time() - t0:.0f}s', flush=True)


if __name__ == '__main__':
    main()

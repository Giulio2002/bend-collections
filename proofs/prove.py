#!/usr/bin/env python3
"""Check every proof.

Each package of src/ has its proof package here: proofs/containers/<pkg>/ and
proofs/math/<pkg>/ (spec.bend, the lemmas, and proof.bend, the entry point).
A proof file that no other package file imports is a root; checking the
roots checks every file. PROOF.bend and END_TO_END.bend (the whole-library
gates) are roots too. This script checks all roots (or those of the packages named),
several at a time, and reports each.

  python3 proofs/prove.py                  every package
  python3 proofs/prove.py lru hash_table   only these packages
  python3 proofs/prove.py --list           the roots, without checking
  options: -j N (parallel checks, default 4), --bend PATH (default $BEND or bend),
           --timeout SECONDS (per root, default 21600)
"""
import argparse, os, re, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
IMP = re.compile(r'^import (\S+\.bend) as \w+$', re.M)


def package(f):
    parts = f.relative_to(HERE).parts
    if parts[0] in ('containers', 'math', 'crypto') and len(parts) > 2:
        return parts[1]
    return parts[0] if len(parts) > 1 else f.stem


def roots():
    files = sorted(HERE.rglob('*.bend'))
    imported = set()
    for f in files:
        if f.parent == HERE:          # PROOF.bend and END_TO_END.bend aggregate the packages
            continue
        for p in IMP.findall(f.read_text()):
            imported.add((f.parent / p).resolve())
    return [f for f in files if f.resolve() not in imported]


def check(bend, f, timeout):
    t0 = time.time()
    try:
        p = subprocess.run([bend, str(f.relative_to(ROOT))], cwd=ROOT, capture_output=True, text=True, timeout=timeout)
        ok = p.returncode == 0 and 'All terms check' in p.stdout
        out = (p.stdout + p.stderr).strip()
    except subprocess.TimeoutExpired:
        ok, out = False, 'timeout after %ds' % timeout
    return f, ok, time.time() - t0, out


def main():
    ap = argparse.ArgumentParser(description='Check every proof.')
    ap.add_argument('packages', nargs='*')
    ap.add_argument('-j', type=int, default=4)
    ap.add_argument('--bend', default=os.environ.get('BEND', 'bend'))
    ap.add_argument('--timeout', type=int, default=21600)
    ap.add_argument('--list', action='store_true')
    a = ap.parse_args()
    rs = [f for f in roots() if not a.packages or package(f) in a.packages]
    if a.list:
        for f in rs:
            print('%-24s %s' % (package(f), f.relative_to(ROOT)))
        return 0
    if not rs:
        print('no proofs for', a.packages)
        return 1
    failed = 0
    with ThreadPoolExecutor(max_workers=a.j) as ex:
        for f, ok, dt, out in ex.map(lambda f: check(a.bend, f, a.timeout), rs):
            print('%-4s %-24s %-60s %7.1fs' % ('ok' if ok else 'FAIL', package(f), f.relative_to(ROOT), dt), flush=True)
            if not ok:
                failed += 1
                print('\n'.join('     ' + l for l in out.splitlines()[-15:]), flush=True)
    print('%d of %d proofs check' % (len(rs) - failed, len(rs)))
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())

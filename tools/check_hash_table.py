#!/usr/bin/env python3
"""Differential test: a hash table driver (HT_TEST, default tests/hash_table/main.bend),
built natively) against a Python dict oracle.

Random operation histories over a key pool that mixes one-character keys
(the check-word fast path), multi-character, empty and non-ASCII keys, with
enough inserts to force several table growths and enough removals to
exercise backward-shift deletion across clusters. `keys` is compared as a
multiset (the table answers in bucket order).

    python3 tools/check_hash_table.py [--histories N] [--ops N] [--seed S]
"""
import argparse
import random
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
import sys; sys.path.insert(0, str(Path(__file__).resolve().parent))
from toolchain import BEND, ENV as BENV
TEST = __import__('os').environ.get('HT_TEST', 'tests/hash_table/main.bend')
BIN = ROOT / 'build' / ('hash_table_test' + __import__('os').environ.get('HT_SUFFIX', ''))
NONE = 4294967295


def build():
    BIN.parent.mkdir(parents=True, exist_ok=True)
    p = subprocess.run([BEND, '' + TEST + '', '-o', str(BIN)],
                       cwd=ROOT, capture_output=True, text=True, env=BENV)
    if not BIN.exists():
        sys.exit(p.stdout + p.stderr)


def key_pool(rng):
    one = [chr(c) for c in range(ord('a'), ord('z') + 1)] + ['é', '中', '😀', '0', 'Z']
    multi = ['ab', 'ba', 'abc', 'key7', 'k' * 12, 'éé', '中文', 'a😀', 'aa', 'aaa']
    extra = [''.join(rng.choice('xyz01') for _ in range(rng.randint(2, 6))) for _ in range(20)]
    return one + multi + extra + ['']


def history(rng, n_ops, pool):
    ops, model, out = [], {}, []
    for _ in range(n_ops):
        r = rng.random()
        k = rng.choice(pool)
        if r < 0.40:
            v = rng.randrange(0, NONE)
            ops.append(f'set:{k}:{v}'); model[k] = v; out.append('OK')
        elif r < 0.55:
            ops.append(f'get:{k}'); out.append(f'V {model.get(k, NONE)}')
        elif r < 0.65:
            ops.append(f'has:{k}'); out.append(f'B {int(k in model)}')
        elif r < 0.80:
            ops.append(f'pop:{k}')
            out.append(f'M {model.pop(k)}' if k in model else 'M -')
        elif r < 0.88:
            ops.append(f'del:{k}'); model.pop(k, None); out.append('OK')
        elif r < 0.95:
            ops.append('size'); out.append(f'N {len(model)}')
        else:
            ops.append('keys'); out.append(('K', sorted(model)))
    return ops, out


def parse_keys(line):
    body = line[2:]
    return sorted(body.split(',')) if body != '' or False else []


def check(ops, want):
    p = subprocess.run([str(BIN)] + ops, capture_output=True, text=True, timeout=120)
    got = p.stdout.split('\n')[:len(want)]
    if p.returncode != 0 or len(got) != len(want):
        return f'exit {p.returncode}, {len(got)} lines for {len(want)} ops: {p.stderr[-300:]}'
    for i, (g, w) in enumerate(zip(got, want)):
        if isinstance(w, tuple):
            if not g.startswith('K '):
                return f'op {i} {ops[i]}: got {g!r}'
            # the empty key renders as an empty field; count fields instead of splitting blindly
            fields = g[2:].split(',') if w[1] else ([] if g == 'K ' else g[2:].split(','))
            if sorted(fields) != w[1]:
                return f'op {i} {ops[i]}: keys {sorted(fields)} != {w[1]}'
        elif g != w:
            return f'op {i} {ops[i]}: got {g!r}, want {w!r}'
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--histories', type=int, default=150)
    ap.add_argument('--ops', type=int, default=400)
    ap.add_argument('--seed', type=int, default=20260922)
    a = ap.parse_args()
    build()
    rng = random.Random(a.seed)
    fails = 0
    for h in range(a.histories):
        pool = key_pool(rng)
        ops, want = history(rng, a.ops, pool)
        err = check(ops, want)
        if err:
            fails += 1
            print(f'history {h}: {err}')
            if fails >= 5:
                break
    total = a.histories * a.ops
    print(f'{a.histories} histories, {total} ops, {fails} failing histories')
    sys.exit(1 if fails else 0)


if __name__ == '__main__':
    main()

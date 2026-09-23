#!/usr/bin/env python3
"""Render BENCHMARK.md from build/bench/full.json (full_sweep.py) and
build/bench/crypto.json (crypto.py).

  python3 benchmarks/render.py
"""
import json, platform, statistics, subprocess, sys
from collections import OrderedDict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'benchmarks'))
from workloads import TABLE  # noqa: E402

NAMES = OrderedDict([
    ('dynamic_array', 'Dynamic array'), ('deque', 'Deque'), ('queue', 'FIFO queue'), ('stack', 'Stack'),
    ('lifo_queue', 'LIFO queue'), ('simple_queue', 'Simple queue'), ('priority_queue', 'Priority queue'),
    ('binary_heap', 'Binary heap'), ('doubly_linked_list', 'Doubly linked list'),
    ('dlist_iterator', 'List iterator'), ('balanced_search_tree', 'Tree map'), ('bitset', 'Bitset'),
    ('hash_table', 'Hash map'), ('lru', 'LRU cache')])
HASHES = OrderedDict([
    ('sha256', ('SHA-256', 'portable FIPS 180-4 C (`benchmarks/native/sha256.c`)')),
    ('keccak256', ('Keccak-256', 'XKCP `plain-64bits` fully unrolled (`benchmarks/native/xkcp/`)')),
    ('blake2s', ('BLAKE2s', 'official BLAKE2 reference `blake2s-ref.c`')),
    ('blake2b', ('BLAKE2b', 'official BLAKE2 reference `blake2b-ref.c`')),
    ('blake3', ('BLAKE3', 'official BLAKE3 C, portable only (no SIMD)')),
])


def load(p):
    p = ROOT / p
    return json.loads(p.read_text()) if p.exists() else None


def ns(x):
    if x is None:
        return '-'
    return '%.0f' % x if x >= 100 else '%.1f' % x if x >= 10 else '%.2f' % x


def per_op(row, key):
    d = row.get(key)
    if not d or not row.get('operations_per_sample'):
        return None
    return statistics.median(d) / row['operations_per_sample']


def main():
    full, crypto = load('build/bench/full.json'), load('build/bench/crypto.json')
    out = ['# Benchmarks', '',
           'Every row runs the same algorithm in Bend (native C backend, one thread) and in C',
           '(`-O3 -march=native`), with identical inputs, and the two results must agree',
           '(a checksum of every result, or the full digests). **Ratio = Bend time / C time**:',
           'below 1 Bend is faster.', '']
    env = (full or {}).get('environment', {})
    out += ['Machine: %s, %s. Measured while other work was running on the machine, so' % (platform.machine(), platform.platform()),
            'absolute times are noisy; each sample alternates Bend and C under the same load,',
            'so the ratios are the meaningful column.', '']
    out += ['Reproduce:', '', '```sh', 'python3 benchmarks/full_sweep.py --report build/bench/full.json   # containers',
            'python3 benchmarks/crypto.py --report build/bench/crypto.json      # hashes',
            'python3 benchmarks/maps/compare.py --report build/bench/maps.json  # HashMap vs Base.Map',
            'python3 benchmarks/render.py                                        # this file', '```', '']

    # ---- hashes ----
    out += ['## Hashes', '',
            'Median of five alternating samples per size, after a warm-up; inputs prepared',
            'before the timed region. Microseconds per hash.', '']
    if crypto:
        for algo, (title, ref) in HASHES.items():
            rows = [r for r in crypto['rows'] if r['algorithm'] == algo]
            if not rows:
                continue
            worst = max(r['ratio'] for r in rows if r['ratio'])
            out += ['### %s' % title, '', 'C reference: %s. Worst ratio %.2f.' % (ref, worst), '',
                    '| Message | Bend (us) | C (us) | Ratio |', '|---:|---:|---:|---:|']
            for r in rows:
                b = r['bytes']
                size = '%d B' % b if b < 1024 else '%d KiB' % (b // 1024) if b < 1048576 else '%d MiB' % (b // 1048576)
                out.append('| %s | %s | %s | %.2f |' % (size, ns(r['us_per_hash']['bend']), ns(r['us_per_hash']['c']), r['ratio']))
            out.append('')
    else:
        out += ['(not measured yet)', '']

    # ---- containers ----
    out += ['## Containers', '',
            'Each row measures one public operation at three structure sizes. The time of',
            'an operation is the difference between two regions that run 2k and k of them',
            '(build, settle and teardown cancel); removals are measured in a restoring pair',
            'with the insertion that puts the element back. Nanoseconds per operation,',
            'median of six samples. See `benchmarks/run.py` for the method.', '']
    done = {}
    for r in (full or {}).get('benchmarks', []):
        done[(r['operation'], r['workload'])] = r
    by = OrderedDict((k, []) for k in NAMES)
    for t in TABLE:
        by.setdefault(t['structure'], []).append(t)
    pending = 0
    for s, title in NAMES.items():
        rows = by.get(s, [])
        if not rows:
            continue
        out += ['### %s' % title, '', '| Operation | Size | Bend (ns) | C (ns) | Ratio |', '|---|---:|---:|---:|---:|']
        for t in rows:
            key = (t['operation'], t['workload'])
            r = done.get(key)
            op = t['operation'].split('.', 1)[1]
            if r is None:
                out.append('| %s | %s | | | pending |' % (op, t['workload']))
                pending += 1
            elif r.get('ratio') is None:
                out.append('| %s | %s | | | not timeable |' % (op, t['workload']))
            else:
                out.append('| %s | %s | %s | %s | %.2f%s |' % (op, t['workload'], ns(per_op(r, 'bend_delta_ns')),
                           ns(per_op(r, 'reference_delta_ns')), r['ratio'], ''))
        out.append('')
    # ---- HashMap vs Base.Map ----
    maps = load('build/bench/maps.json')
    out += ['## Hash map vs Base.Map', '',
            'Both sides are Bend: the hash map of `src/containers/hash_table.bend` against',
            "the standard library's `Base.Map` (a crit-bit tree over String keys), on the",
            'same operations, String keys and inputs, with identical checksums. Same',
            'differential method as the containers. **Ratio = HashMap time / Base.Map time**:',
            'below 1 the hash map is faster. `Base.Map.size` walks the tree, so the',
            'hash map\'s O(1) size is compared against an O(n) walk. See',
            '`benchmarks/maps/compare.py`.', '']
    if maps:
        out += ['| Operation | Size | HashMap (ns) | Base.Map (ns) | Ratio |', '|---|---:|---:|---:|---:|']
        for r in maps['rows']:
            op = r['operation'].split('.', 1)[1]
            if r.get('ratio') is None:
                out.append('| %s | %d | | | not timeable |' % (op, r['size']))
            else:
                out.append('| %s | %d | %s | %s | %.2f |' % (op, r['size'], ns(per_op(r, 'bend_delta_ns')),
                           ns(per_op(r, 'reference_delta_ns')), r['ratio']))
        out.append('')
    else:
        out += ['(not measured yet)', '']
    if pending:
        out.insert(out.index('## Containers') + 2, '**%d of %d container rows are still being measured; they show as pending.**\n' % (pending, len(TABLE)))
    (ROOT / 'BENCHMARK.md').write_text('\n'.join(out) + '\n')
    print('BENCHMARK.md: %d container rows, %d pending' % (len(done), pending))


if __name__ == '__main__':
    main()

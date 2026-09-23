#!/usr/bin/env python3
"""HashMap (src/containers/hash_table.bend) against Base.Map, both in Bend.

  python3 benchmarks/maps/compare.py --report build/bench/maps.json

Both drivers are generated from body.bend (the operations of
benchmarks/bend/hash_table.bend) and one adapter each (hash_table.head,
base_map.head), so they run the identical operation sequence on the identical
String keys and must print identical checksums. Timing is the A - B
differential of benchmarks/run.py (calibration, six alternating samples);
both binaries run with --threads 1. Ratio = HashMap time / Base.Map time.

Unlike the C comparison, set does not ask for the size afterwards and build
probes one key instead of the size: Base.Map's size walks the whole tree.
"""
import argparse, json, statistics, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'benchmarks'))
import run as bench  # noqa: E402

OUT = ROOT / 'build' / 'bench' / 'maps'
SIDES = ['hash_table', 'base_map']
# (operation, selector, sizes, starting counts)
ROWS = [
    ('set', 0, (64, 4096, 262144), (100000, 50000, 20000)),
    ('get', 1, (64, 4096, 262144), (100000, 50000, 20000)),
    ('has', 2, (64, 4096, 262144), (100000, 50000, 20000)),
    ('pop', 3, (64, 4096, 262144), (100000, 50000, 20000)),
    ('size', 4, (64, 4096, 262144), (200000, 2000, 20)),
    ('keys', 5, (64, 4096, 32768), (20000, 500, 40)),
    ('build', 6, (64, 4096, 32768), (2000, 40, 4)),
]


def generate():
    OUT.mkdir(parents=True, exist_ok=True)
    body = (HERE / 'body.bend').read_text()
    srcs = {}
    for s in SIDES:
        # generated beside the sources so the relative imports resolve
        p = HERE / ('gen_%s.bend' % s)
        p.write_text((HERE / ('%s.head' % s)).read_text() + '\n' + body)
        srcs[s] = p
    return srcs


def build(srcs):
    bins = {}
    for s, p in srcs.items():
        out = OUT / s
        r = subprocess.run([bench.BEND, str(p), '-o', str(out)], cwd=ROOT, env=bench.ENV,
                           capture_output=True, text=True)
        if r.returncode or not out.exists():
            raise SystemExit('build failed for %s:\n%s%s' % (s, r.stdout[-3000:], r.stderr[-3000:]))
        bins[s] = out
    return bins


def rows():
    out = []
    for op, sel, sizes, counts in ROWS:
        for i, (n, c) in enumerate(zip(sizes, counts)):
            out.append({'structure': 'maps', 'operation': 'maps.' + op, 'op': sel,
                        'workload': ['small', 'medium', 'large'][i], 'size': n,
                        'count': c, 'reps': 1, 'grow': 'count' if op != 'build' else 'reps',
                        'seed': 7000 + len(out), 'method': 'pair' if op == 'pop' else 'batch'})
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--report', required=True)
    ap.add_argument('--only', help='comma-separated operations')
    ap.add_argument('--retry-failed', action='store_true', help='re-measure only the failed rows of --report')
    a = ap.parse_args()
    bins = build(generate())
    # the reference side is the Base.Map driver: a Bend binary too
    bench.run_ref = bench.run_bend
    # Base.Map.size walks the tree: a batch long enough to time the hash
    # map's O(1) size takes minutes on the Base.Map side
    bench.RUN_TIMEOUT_S = 900
    todo = [r for r in rows() if not a.only or r['operation'].split('.')[1] in a.only.split(',')]
    results, log = [], []
    if a.retry_failed:
        results = json.loads(Path(a.report).read_text())['rows']
        ok = {(m['operation'], m['workload']) for m in results if m.get('measurement') == 'ok'}
        todo = [r for r in todo if (r['operation'], r['workload']) not in ok]
    for r in todo:
        try:
            m = bench.measure(bins['hash_table'], bins['base_map'], r, log)
            m['ratio'] = statistics.median(m['bend_ns']) / statistics.median(m['reference_ns'])
            if not m['verified']:
                raise SystemExit('checksums differ for %s %s' % (r['operation'], r['workload']))
        except bench.Unmeasurable as e:
            m = {'operation': r['operation'], 'workload': r['workload'], 'size': r['size'],
                 'measurement': 'failed', 'reason': str(e)}
        results = [x for x in results if (x['operation'], x['workload']) != (r['operation'], r['workload'])] + [m]
        order = [(x['operation'], x['workload']) for x in rows()]
        results.sort(key=lambda x: order.index((x['operation'], x['workload'])))
        print('%-10s %-6s %s' % (r['operation'], r['workload'],
              '%.3f' % m['ratio'] if 'ratio' in m else 'FAILED ' + m['reason']), flush=True)
        Path(a.report).parent.mkdir(parents=True, exist_ok=True)
        Path(a.report).write_text(json.dumps({'rows': results}, indent=1))
    (OUT / 'samples.log').write_text('\n'.join(log) + '\n')


if __name__ == '__main__':
    main()

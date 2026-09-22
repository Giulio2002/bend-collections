#!/usr/bin/env python3
"""Measure the PROPOSED lru.* rows (benchmarks/experiments/lru_workloads.py)
with the unmodified machinery of benchmarks/run.py.

benchmarks/run.py only measures the canonical table, which does not contain
the lru rows yet (the operator applies them). This tool imports run.py as a
module -- it does not change it -- and calls its own `build_all` and
`measure` on the proposed rows, so calibration, the A/B/C regions, the
clock minima, checksum verification and the failure rules are exactly the
canonical ones. The output is a SUPPLEMENTAL report; it is never merged into
build/performance/report.json.

    python3 tools/lru_measure.py [--report build/performance/lru_experiment.json]
                                 [--filter add,get]
"""
import argparse
import importlib.util
import json
import statistics
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'benchmarks'))


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--report', default=str(ROOT / 'build' / 'performance' / 'lru_experiment.json'))
    ap.add_argument('--filter', default=None)
    args = ap.parse_args()
    run = load('bench_run', ROOT / 'benchmarks' / 'run.py')
    exp = load('lru_rows', ROOT / 'benchmarks' / 'experiments' / 'lru_workloads.py')
    base = len(run.TABLE)
    rows = [dict(r, seed=r.get("seed", 1000 + base + i)) for i, r in enumerate(exp.table())]
    if args.filter:
        keep = set(args.filter.split(','))
        rows = [r for r in rows if r['operation'].split('.', 1)[1] in keep]
    built = run.build_all(['lru'])
    bend_bin, ref_bin = built['lru']
    log, results = [], []
    for row in rows:
        try:
            res = run.measure(bend_bin, ref_bin, row, log)
        except run.Unmeasurable as exc:
            res = {'measurement': 'failed', 'reason': str(exc),
                   'operation': row['operation'], 'workload': row['workload'],
                   'size': row['size'], 'verified': False,
                   'bend_ns': [], 'reference_ns': []}
            print('%-16s %-11s size=%-7d FAILED MEASUREMENT (%s)'
                  % (row['operation'], row['workload'], row['size'], exc), flush=True)
            results.append(res)
            continue
        results.append(res)
        b = statistics.median(res['bend_ns'])
        c = statistics.median(res['reference_ns'])
        print('%-16s %-11s size=%-7d bend=%10.2fns ref=%10.2fns %6.2fx %s'
              % (res['operation'], res['workload'], res['size'], b, c,
                 b / c if c > 0 else float('inf'),
                 'ok' if res['verified'] else 'UNVERIFIED'), flush=True)
    out = Path(args.report)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({'supplemental': True,
                               'source': 'benchmarks/experiments/lru_workloads.py',
                               'benchmarks': results}, indent=1, sort_keys=True))
    print('report: %s' % out)


if __name__ == '__main__':
    main()

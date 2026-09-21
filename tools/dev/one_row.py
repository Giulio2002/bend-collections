#!/usr/bin/env python3
"""Development helper: run benchmarks/run.py's own measure() on ONE row.

  python3 tools/dev/one_row.py queue.dequeue large

Imports benchmarks/run.py as a module (it is not changed) and calls its
build_all / measure on the single matching row of benchmarks/workloads.py, so
the calibration, the regions and the failure rules are the canonical ones.
Used to reproduce a single row's calibration quickly instead of waiting for a
whole 408-row run. Numbers printed here are never acceptance evidence.
"""
import importlib.util
import statistics
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'benchmarks'))


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def main():
    op, workload = sys.argv[1], sys.argv[2]
    run = load('bench_run', ROOT / 'benchmarks' / 'run.py')
    table = [dict(r, seed=1000 + i) for i, r in enumerate(run.TABLE)]
    rows = [r for r in table if r['operation'] == op and r['workload'] == workload]
    if not rows:
        sys.exit('no such row')
    row = rows[0]
    built = run.build_all([row['structure']])
    bend_bin, ref_bin = built[row['structure']]
    log = []
    try:
        res = run.measure(bend_bin, ref_bin, row, log)
    except run.Unmeasurable as exc:
        print('FAILED MEASUREMENT: %s' % exc)
        print('\n'.join(log))
        return
    b = statistics.median(res['bend_ns'])
    c = statistics.median(res['reference_ns'])
    print('\n'.join(l for l in log if 'calibrate' in l))
    print('%s %s bend=%.2fns ref=%.2fns %.2fx count=%d reps=%d'
          % (op, workload, b, c, b / c, res['count'], res['reps']))


if __name__ == '__main__':
    main()

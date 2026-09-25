#!/usr/bin/env python3
"""Measure the emitted allocator, including transient tuples and closures.

The generated C alone is instrumented; the Bend source/compiler are unchanged.
The marker brackets the compiled churn function, excluding setup and teardown.
Run on one worker. A compiler change that loses the marker fails closed.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import statistics
import platform
from intrusive_measurement import instrument

ROOT = Path(__file__).resolve().parents[1]

def run(command):
    return subprocess.run(command, cwd=ROOT, check=True, capture_output=True,
                          text=True, timeout=120, env={**os.environ, 'BEND_NO_TELEMETRY': '1'})

def expected_checksum():
    nodes=list(range(1,32)); rng=1
    for _ in range(100000):
        n=1+rng%31; nodes.remove(n); nodes.insert(0,n)
        rng=(rng*1664525+1013904223)&0xffffffff
    cells=[0]*128;cells[0]=nodes[0]
    for i,n in enumerate(nodes):
        cells[32+n]=nodes[i+1] if i+1<len(nodes) else 0
        cells[64+n]=nodes[i-1] if i else 0
    h=0
    for v in reversed(cells): h=(h*33+v)&0xffffffff
    return h

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--bend', default='bend')
    p.add_argument('--cc', default='clang')
    args = p.parse_args()
    build = ROOT / 'build/intrusive-list'
    build.mkdir(parents=True, exist_ok=True)
    c = build / 'churn.c'
    run([args.bend, 'tests/intrusive_doubly_linked_list/churn.bend', '-o', str(c)])
    measured = build / 'churn-instrumented.c'
    measured.write_text(instrument(c.read_text()))
    exe = build / 'churn'
    run([args.cc, '-O3', '-std=gnu11', '-pthread', str(measured), '-lm', '-o', str(exe)])
    r = run([str(exe), '--threads', '1'])
    assert r.stdout.strip() == str(expected_checksum()), r.stdout
    assert re.fullmatch(r'IL_ALLOC 0 IL_NS [0-9]+\n', r.stderr), r.stderr
    times=[int(r.stderr.split()[-1])]
    for _ in range(6):
        sample=run([str(exe), '--threads', '1'])
        assert sample.stdout.strip()==str(expected_checksum())
        assert re.fullmatch(r'IL_ALLOC 0 IL_NS [0-9]+\n',sample.stderr),sample.stderr
        times.append(int(sample.stderr.split()[-1]))
    # Positive control: the counter must detect a forced allocation inside
    # the same interval. Never ship a permanently-zero measurement.
    control = measured.read_text().replace('il_active = 1;',
        'il_active = 1; Loc probe = heap_alloc(e, 0); heap_free(e, 0, probe);')
    measured.write_text(control)
    run([args.cc, '-O3', '-std=gnu11', '-pthread', str(measured), '-lm', '-o', str(exe)])
    positive = run([str(exe), '--threads', '1'])
    assert re.fullmatch(r'IL_ALLOC 1 IL_NS [0-9]+\n', positive.stderr), positive.stderr
    measured.write_text(instrument(c.read_text()))
    run([args.cc, '-O3', '-std=gnu11', '-pthread', str(measured), '-lm', '-o', str(exe)])
    native = build / 'churn-c'
    run([args.cc, '-O3', '-std=gnu11', 'benchmarks/native/intrusive_list.c', '-o', str(native)])
    native_times=[]
    for _ in range(7):
        r=run([str(native)])
        assert r.stdout.strip()==str(expected_checksum()), r.stdout
        assert re.fullmatch(r'IL_NS [0-9]+\n',r.stderr),r.stderr
        native_times.append(int(r.stderr.split()[-1]))
    pool_c = build / 'pool.c'
    run([args.bend, 'tests/intrusive_doubly_linked_list/pool_churn.bend', '-o', str(pool_c)])
    pool_instrumented = build / 'pool-instrumented.c'
    pool_instrumented.write_text(instrument(pool_c.read_text()))
    pool_exe = build / 'pool'
    run([args.cc, '-O3', '-std=gnu11', '-pthread', str(pool_instrumented), '-lm', '-o', str(pool_exe)])
    pool_result = run([str(pool_exe), '--threads', '1'])
    assert pool_result.stdout.strip() == '4', pool_result.stdout
    assert re.fullmatch(r'IL_ALLOC 0 IL_NS [0-9]+\n', pool_result.stderr), pool_result.stderr
    report = {'platform': platform.platform(), 'compiler': run([args.bend, 'version']).stdout.strip(),
              'edits': 400000, 'heap_allocations': 0, 'positive_control': 1,
              'pool_operations': 200000, 'pool_heap_allocations': 0,
              'scope': 'fixed array adapter, prepend/remove, single worker',
              'passed': True, 'checksum': expected_checksum(),
              'bend_median_ns': statistics.median(times), 'c_median_ns': statistics.median(native_times),
              'samples': 7, 'timing_note': 'hot loop only; descriptive, not a timing gate'}
    (build / 'allocations.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report))

if __name__ == '__main__':
    main()

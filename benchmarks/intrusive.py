#!/usr/bin/env python3
"""Known-entity transfers and prewarmed transient-object pulses.

Compare the new intrusive API, the existing public checked DList API,
its generation-free storage diagnostic, and plain indexed C.
All use the same identities, payloads, seeds and work.
--check-only runs correctness/allocation checks, not a performance gate.
"""
import argparse
from collections import OrderedDict
from datetime import datetime, timezone
from functools import lru_cache
import hashlib
import itertools
import json
import math
import os
from pathlib import Path
import platform
import re
import shutil
import statistics
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from intrusive_measurement import instrument

MASK = 0xffffffff
KINDS = ('intrusive', 'dlist', 'storage')
SOURCES = {f'{work}_{kind}': f'benchmarks/bend/intrusive_{work}{suffix}.bend'
           for work in ('transfer', 'pulses')
           for kind, suffix in [('intrusive', ''), ('dlist', '_dlist'), ('storage', '_storage')]}


def run(command, timeout=180):
    r = subprocess.run(list(map(str, command)), cwd=ROOT, capture_output=True,
                       text=True, timeout=timeout,
                       env={**os.environ, 'BEND_NO_TELEMETRY': '1'})
    if r.returncode:
        raise RuntimeError(f'{command}\n{r.stdout[-2000:]}\n{r.stderr[-2000:]}')
    return r


def mix(h, n):
    return (h * 33 + n) & MASK


def lcg(n):
    return (n * 1664525 + 1013904223) & MASK


@lru_cache(maxsize=128)
def reference(work, size, count, seed):
    """Independent ordered-map/stack model, with no intrusive links/handles."""
    h = 0
    if work == 'transfer':
        groups = [OrderedDict.fromkeys(range(1, size + 1)), OrderedDict()]
        payload = {n: mix(n, 17) for n in range(1, size + 1)}
        for _ in range(count):
            n = 1 + seed // 256 % size
            owner = 0 if n in groups[0] else 1
            del groups[owner][n]
            groups[1-owner][n] = None
            groups[1-owner].move_to_end(n, last=False)
            seed = lcg(seed)
        for group in groups:
            h = mix(h, MASK)
            for n in group:
                h = mix(h, n)
        made = 0
    else:
        pool = list(range(1, size + 1))
        payload = {}
        # One warm pulse (seed 0) occurs before the measured interval.
        for pulse in range(count + 1):
            active = OrderedDict()
            value = 0 if pulse == 0 else seed
            for _ in range(size):
                n = pool.pop()
                payload[n] = value
                active[n] = None
                value = lcg(value)
            for n in active:
                h = mix(mix(h, n), payload[n])
                pool.append(n)
            if pulse == 0:
                h = 0
            else:
                seed = lcg(seed)
        h = mix(h, len(pool))
        for n in reversed(pool):
            h = mix(h, n)
        h = mix(h, 0)  # no live membership remains
        made = size
    for n in range(size, 0, -1):
        h = mix(mix(h, n), payload[n])
    return f'{h} {made} 0'


def arguments(work, size, count, seed):
    return ['0' if work == 'transfer' else '1', str(size), str(count), '1', str(seed), '0']


def sample(build, work, kind, size, count, seed, mode='time'):
    args = arguments(work, size, count, seed)
    if kind == 'c':
        command = [build / 'reference', args[0], args[1], args[2], args[4]]
    elif mode == 'js':
        command = ['node', build / f'{work}_{kind}.js', *args]
    else:
        executable_kind = 'intrusive' if kind == 'intrusive_repeat' else kind
        command = [build / f'{work}_{executable_kind}-{mode}', '--threads', '1', *args]
    r = run(command)
    expected = reference(work, size, count, seed)
    if r.stdout.strip() != expected:
        raise RuntimeError(f'{command}: expected {expected!r}, got {r.stdout!r}')
    if mode == 'js':
        if r.stderr:
            raise RuntimeError(r.stderr)
        return {}
    m = re.fullmatch(r'(?:IL_BYTES (\d+) (\d+) (\d+)\n)?(?:IL_ALLOC (\d+) )?IL_NS (\d+)\n', r.stderr)
    if not m:
        raise RuntimeError(f'missing measurement: {r.stderr!r}')
    return {'ns': int(m[5]), 'allocations': int(m[4]) if m[4] else None,
            'live_bytes': ({'entry': int(m[1]), 'exit': int(m[2]), 'hot_peak': int(m[3])}
                           if m[1] else None)}


def compile_all(args, build):
    flags = ['-O3', '-std=gnu11', '-pthread']
    for name, source in SOURCES.items():
        checked = run([args.bend, source, '--check-only'])
        if (checked.stdout + checked.stderr).strip() != 'All terms check.':
            raise RuntimeError(f'{source}: checker not clean')
        emitted = build / f'{name}.c'
        run([args.bend, source, '-o', emitted])
        run([args.bend, source, '-o', build / f'{name}.js'])
        for mode in ('time', 'alloc', 'control', 'memory', 'memory_control'):
            text = instrument(emitted.read_text(), allocations=mode != 'time', memory=mode.startswith('memory'))
            if mode in ('control', 'memory_control'):
                if text.count('il_active = 1;') != 1:
                    raise RuntimeError('positive control marker changed')
                anchor = 'il_peak_bytes = il_live_bytes;' if mode == 'memory_control' else 'il_active = 1;'
                # Use a larger size class for a visible high-water positive
                # control; free it immediately so retained bytes are equal.
                probe = ' Loc probe = heap_alloc(e, 10); heap_free(e, 10, probe);'
                if mode == 'memory_control':
                    # The same expression also occurs in the allocator hook.
                    anchor = 'long long il_entry_bytes = il_live_bytes; il_peak_bytes = il_live_bytes;'
                if text.count(anchor) != 1:
                    raise RuntimeError('positive control boundary changed')
                text = text.replace(anchor, anchor + probe)
            c = build / f'{name}-{mode}.c'
            c.write_text(text)
            run([args.cc, *flags, c, '-lm', '-o', build / f'{name}-{mode}'])
    run([args.cc, *flags, 'benchmarks/native/intrusive_workloads.c', '-o', build / 'reference'])


def check(build):
    rows = []
    for work, size, seed in itertools.product(('transfer', 'pulses'), (1, 3, 32), (0, 1, MASK)):
        count = 257 if work == 'transfer' else 5
        for kind in KINDS:
            sample(build, work, kind, size, count, seed, 'js')
            sample(build, work, kind, size, count, seed)
        sample(build, work, 'c', size, count, seed)
        rows.append({'workload': work, 'size': size, 'count': count, 'seed': seed,
                     'output': reference(work, size, count, seed)})
    controls = {}
    memory_controls = {}
    for work, kind in itertools.product(('transfer', 'pulses'), KINDS):
        baseline = sample(build, work, kind, 32, 7, 1, 'alloc')['allocations']
        control = sample(build, work, kind, 32, 7, 1, 'control')['allocations']
        if control != baseline + 1:
            raise RuntimeError(f'{work}/{kind}: positive control did not add one allocation')
        if kind == 'intrusive' and baseline != 0:
            raise RuntimeError(f'{work}: intrusive hot path allocated {baseline} times')
        controls[f'{work}_{kind}'] = {'baseline': baseline, 'control': control}
        base = sample(build, work, kind, 32, 7, 1, 'memory')
        probe = sample(build, work, kind, 32, 7, 1, 'memory_control')
        b, c = base['live_bytes'], probe['live_bytes']
        if (b['entry'] != c['entry'] or b['exit'] != c['exit'] or
            c['hot_peak'] != max(b['hot_peak'], b['entry'] + 8192) or
            probe['allocations'] != base['allocations'] + 1):
            raise RuntimeError(f'{work}/{kind}: live-byte positive control failed: {base}, {probe}')
        memory_controls[f'{work}_{kind}'] = {'baseline': base, 'control': probe}
    return {'cases': rows, 'backends_per_case': 7, 'positive_controls': controls,
            'memory_controls': memory_controls, 'passed': True}


def measure(build, args, work, size):
    # Calibrate on the faster candidate. No subtractive timing, clamping,
    # empty-loop subtraction, or setup/destruction in the measured region.
    count = 16384 if work == 'transfer' else max(2, 16384 // size)
    for _ in range(10):
        times = [sample(build, work, kind, size, count, args.seed)['ns']
                 for kind in (*KINDS, 'c')]
        fastest = min(times)
        if fastest >= args.min_ms * 1e6:
            break
        factor = min(16, max(2, math.ceil(args.min_ms * 1e6 * 1.2 / max(fastest, 1))))
        count *= factor
        if count * (size if work == 'pulses' else 1) > 100_000_000:
            raise RuntimeError('unable to obtain a timeable batch within the work limit')
    else:
        raise RuntimeError('unable to calibrate')
    # The repeat label runs the exact same intrusive executable at independent
    # positions. Its A/A ratio measures order/noise without inventing a new
    # implementation. Cyclic rotations balance positions over five samples.
    kinds = (*KINDS, 'c', 'intrusive_repeat')
    for kind in kinds:
        sample(build, work, kind, size, count, args.seed)
    samples = {kind: [] for kind in kinds}
    orders = [kinds[i:] + kinds[:i] for i in range(len(kinds))]
    for i in range(args.samples):
        for kind in orders[i % len(orders)]:
            samples[kind].append(sample(build, work, kind, size, count, args.seed)['ns'])
    units = count * (size if work == 'pulses' else 1)
    metrics = {}
    for kind in kinds:
        values = samples[kind]
        allocation = sample(build, work, kind, size, count, args.seed, 'alloc') if kind != 'c' else None
        if kind == 'intrusive' and allocation['allocations'] != 0:
            raise RuntimeError(f'{work}/{size}: intrusive hot path allocated')
        metrics[kind] = {'samples_ns': values, 'median_ns_per_unit': statistics.median(values) / units,
                         'min_ns_per_unit': min(values) / units, 'max_ns_per_unit': max(values) / units,
                         'heap_alloc_calls': allocation['allocations'] if allocation else None}
        if kind in KINDS:
            metrics[kind]['live_bytes'] = sample(build, work, kind, size, count, args.seed, 'memory')['live_bytes']
    aa = metrics['intrusive_repeat']['median_ns_per_unit'] / metrics['intrusive']['median_ns_per_unit']
    return {'workload': work, 'size': size, 'iterations': count, 'units': units,
            'unit': 'transfer (remove + prepend)' if work == 'transfer' else 'complete node lifecycle',
            'seed': args.seed, 'output': reference(work, size, count, args.seed),
            'factory_calls_in_hot_loop': 0, 'metrics': metrics, 'aa_repeat_ratio': aa,
            'aa_within_10_percent': 0.9 <= aa <= 1.1}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--bend', default=os.environ.get('BEND', 'bend'))
    p.add_argument('--cc', default='clang')
    p.add_argument('--sizes', type=int, nargs='+', default=[32, 1024, 65536])
    p.add_argument('--samples', type=int, default=10)
    p.add_argument('--min-ms', type=float, default=10)
    p.add_argument('--seed', type=int, default=1)
    p.add_argument('--check-only', action='store_true')
    p.add_argument('--report', type=Path, default=ROOT / 'build/intrusive-bench/report.json')
    args = p.parse_args()
    if any(not 1 <= size <= 65536 for size in args.sizes) or args.samples < 5 or not math.isfinite(args.min_ms) or args.min_ms <= 0 or not 0 <= args.seed <= MASK:
        p.error('sizes must be 1..65536, samples >= 5, min-ms > 0, seed a U32')
    args.bend = shutil.which(args.bend) or str(Path(args.bend).resolve())
    args.cc = shutil.which(args.cc) or str(Path(args.cc).resolve())
    build = ROOT / 'build/intrusive-bench'
    build.mkdir(parents=True, exist_ok=True)
    compile_all(args, build)
    cpu = platform.processor()
    if Path('/proc/cpuinfo').exists():
        cpu = next((line.split(':', 1)[1].strip() for line in Path('/proc/cpuinfo').read_text().splitlines()
                    if line.startswith('model name')), cpu)
    elif sys.platform == 'darwin':
        cpu = run(['sysctl', '-n', 'machdep.cpu.brand_string']).stdout.strip()
    report = {'schema': 2, 'timestamp_utc': datetime.now(timezone.utc).isoformat(),
              'platform': platform.platform(), 'machine': platform.machine(), 'cpu': cpu,
              'compiler': run([args.bend, 'version']).stdout.strip(),
              'compiler_sha256': hashlib.sha256(Path(args.bend).read_bytes()).hexdigest(),
              'cc': run([args.cc, '--version']).stdout.splitlines()[0],
              'c_flags': '-O3 -std=gnu11 -pthread -lm', 'workers': 1,
              'samples': args.samples, 'min_batch_ms': args.min_ms,
              'allocation_scope': 'Bend heap_alloc calls; separate instrumented binaries; no timing counter',
              'memory_scope': 'live Bend heap blocks, rounded to allocator size classes; process-wide at churn entry/exit and peak during churn; excludes free lists, stack, runtime reservations and OS allocations',
              'comparison_scope': 'different contracts; storage diagnostic removes generation facade and generation handle-map traffic, retaining bounds/owner/live-slot checks, tail, count, arenas and slot mapping',
              'timing_scope': 'churn only; setup, prewarm, validation and destruction excluded',
              'checks': check(build), 'rows': []}
    print('126 C/JS/reference checks, six allocation and six live-byte positive controls passed.', flush=True)
    if not args.check_only:
        for work, size in itertools.product(('transfer', 'pulses'), args.sizes):
            row = measure(build, args, work, size)
            report['rows'].append(row)
            summary = ', '.join(f"{k} {v['median_ns_per_unit']:.2f} ns" for k, v in row['metrics'].items())
            print(f'{work}/{size}: {summary}', flush=True)
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps(report, indent=2) + '\n')
    paths = sorted({str(path.relative_to(ROOT)) for pattern in
                    ('benchmarks/bend/intrusive*.bend', 'benchmarks/native/intrusive_workloads.c',
                     'benchmarks/bend/common.bend', 'benchmarks/intrusive.py', 'tools/intrusive_measurement.py',
                     'src/containers/intrusive_doubly_linked_list.bend', 'src/containers/doubly_linked_list.bend',
                     'src/containers/internal/intrusive_list.bend',
                     'src/containers/internal/dlist_storage.bend', 'src/containers/types/internal_dlist.bend',
                     'src/containers/types/doubly_linked_list.bend', 'src/containers/types/intrusive_doubly_linked_list.bend')
                    for path in ROOT.glob(pattern)})
    report['source_sha256'] = {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in paths}
    report['passed'] = True
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(f'Report: {args.report}')


if __name__ == '__main__':
    main()

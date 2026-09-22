#!/usr/bin/env python3
"""Native benchmark runner: Bend (native C backend) against optimized C.

  python benchmarks/run.py --report build/performance/report.json

It always rebuilds both sides in release mode (there is no skip-build flag):

  * every benchmarks/bend/<id>.bend is compiled with the pinned Bend compiler
    to a native binary and run with `--threads 1` (one sequential thread),
  * every benchmarks/native/<id>.c is compiled with the system C compiler at -O3.

Each row measures one public operation. Both programs take the identical
arguments, draw operation arguments from the identical LCG and fold every
result into a checksum, and each runs THREE timed regions inside its own
process. Writing k for `count`, one round is "build a structure of `size`,
settle it, run the measured operation k1 times, destroy it", and the regions
are

  A = reps x round(k1 = 2k)
  B = reps x round(k1 = k)
  C = reps x round(k1 = 0)    (the build-and-destroy control)

so A - B is exactly `count x reps` measured operations, loop barrier and
argument generation included: the build, the settle, the process start-up,
all file IO and the destruction cancel.
Because A and B both end in a state that the measured operation has been
applied to, a size-changing operation can no longer move deallocation work
out of the difference (the two-region asymmetry this replaced made A - B
negative at large sizes). C is reported next to every row: it is what a
region that performs no measured operation at all costs, so a difference that
is small beside its own build is visible as such. `verified` is true only
when the Bend and C checksums for all three regions agree, which they cannot
unless both performed the same work.

The measured batch is lengthened until the difference is reliably timeable.
For a size-preserving operation the batch grows in `count` (more operations
inside one round, so the build is NOT multiplied). A size-changing operation
may only lengthen its batch up to the row's cap (`size` for an operation that
adds elements, `size / 2` for one that removes them), because beyond that the
batch would no longer be that operation at that size; it grows `count` up to
that cap first and multiplies whole rounds afterwards. More rounds scale the
difference and the region by the same factor, so they do not make a
build-dominated difference any easier to see; a longer batch does.

An operation that REMOVES elements cannot be measured this way at all: a
round can only remove what it built, so the batch is bounded by `size` while
the round also pays to build those `size` elements, and the difference stays
a small fraction of the round -- the earlier reports show exactly this, as
FAILED rows whose A - B came out at or below zero. Such an operation is
measured inside a RESTORING PAIR: the driver runs the removal together with
the insertion that puts the element back, the structure keeps its size, the
batch grows in `count` like any size-preserving row, and BOTH sides run the
identical pair. The nanoseconds reported for the row are the pair's, charged
to the removal: that over-charges the Bend side by one insertion and never
flatters it. Every row records which of the two it is in `method`
("pair" or "batch"), and benchmarks/workloads.py classifies every
operation.

Measurement integrity: nothing is clamped or floored. The batch is grown until
the measured difference A - B is at least MIN_DELTA_MS milliseconds on the
BEND side (the Bend runtime only exposes a millisecond clock, IO.now, so that
is at least MIN_DELTA_MS clock ticks and the quantisation error is at most
1/MIN_DELTA_MS) AND at least MIN_REF_DELTA_NS nanoseconds on the REFERENCE
side (clock_gettime, so thousands of ticks). A row whose difference cannot be
driven above those minima within MAX_REPS/MAX_OPS is a FAILED measurement and
aborts the run: it is never reported as a number.
"""

import argparse
import hashlib
import json
import os
import platform
import re
import statistics
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'benchmarks'))
from workloads import TABLE  # noqa: E402

LOCK = json.loads((ROOT / 'inventory' / 'toolchain.json').read_text())
CONTRACT = json.loads((ROOT / 'automation' / 'performance_contract.json').read_text())
BEND = LOCK['binary']
ENV = {**os.environ, 'BEND_NO_TELEMETRY': '1'}

BENDBIN = ROOT / 'build' / 'bench' / 'bend'
REFBIN = ROOT / 'build' / 'bench' / 'ref'
LOGDIR = ROOT / 'build' / 'bench' / 'logs'

CC = os.environ.get('CC', 'cc')
CFLAGS = ['-O3', '-march=native', '-std=c11', '-fno-strict-aliasing']
BEND_FLAGS = '-o <bin> (native C backend); run with --threads 1'

# The Bend runtime only exposes a millisecond clock (IO.now), so the measured
# difference has to span many of its ticks before the number means anything.
MIN_DELTA_MS = 50           # >= 50 Bend clock ticks  (<= 2% quantisation)
MIN_DELTA_NS = MIN_DELTA_MS * 1e6
MIN_REF_DELTA_NS = 1e5      # >= 100 us of clock_gettime on the reference
                            # side, i.e. thousands of its ~40 ns ticks
CAL_HEADROOM = 2.0          # calibrate to twice the minimum so that
                            # run-to-run variation cannot push a sample below
                            # it (every sample is checked, never clamped)
MAX_REPS = 1 << 22
MAX_OPS = 2 * 1000 * 1000 * 1000
MAX_REGION_MS = 20000       # stop growing the batch once a Bend region is this long
RUN_TIMEOUT_S = 120         # a single measured process may not take longer
SAMPLES = 6                 # alternating region orders, >= 5 as the contract asks


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def sh(cmd, **kw):
    return subprocess.run(cmd, cwd=str(ROOT), env=ENV, text=True,
                          capture_output=True, **kw)


# ------------------------------------------------------------------ building

def build_all(structures):
    BENDBIN.mkdir(parents=True, exist_ok=True)
    REFBIN.mkdir(parents=True, exist_ok=True)
    LOGDIR.mkdir(parents=True, exist_ok=True)
    built = {}
    for name in structures:
        src = ROOT / 'benchmarks' / 'bend' / ('%s.bend' % name)
        out = BENDBIN / name
        if out.exists():
            out.unlink()
        p = sh([BEND, str(src.relative_to(ROOT)), '-o', str(out.relative_to(ROOT))])
        if not out.exists():
            raise SystemExit('bend build failed for %s:\n%s' % (name, p.stdout + p.stderr))
        csrc = ROOT / 'benchmarks' / 'native' / ('%s.c' % name)
        cout = REFBIN / name
        if cout.exists():
            cout.unlink()
        p = sh([CC] + CFLAGS + ['-o', str(cout.relative_to(ROOT)), str(csrc.relative_to(ROOT))])
        if not cout.exists():
            raise SystemExit('cc build failed for %s:\n%s' % (name, p.stdout + p.stderr))
        built[name] = (out, cout)
        print('built %s' % name, flush=True)
    return built


# ------------------------------------------------------------------ measuring

TIME_RE = re.compile(r'TA=(\d+)\s+TB=(\d+)\s+TC=(\d+)')


def run_bend(binary, row, count, reps, order=0):
    p = subprocess.run([str(binary), '--threads', '1', '--',
                        str(row['op']), str(row['size']), str(count),
                        str(reps), str(row['seed']), str(order)],
                       env=ENV, text=True, capture_output=True, timeout=RUN_TIMEOUT_S)
    if p.returncode != 0:
        raise SystemExit('bend run failed: %s' % (p.stderr[-500:]))
    m = TIME_RE.search(p.stdout)
    if not m:
        raise SystemExit('bend produced no timing: %r %r' % (p.stdout, p.stderr))
    checks = [ln for ln in p.stderr.splitlines() if ln.strip().isdigit()]
    # The Bend driver prints each region's checksum as it computes it (that is
    # what forces the region), so with the reversed region order the lines
    # arrive as C, B, A. Normalise to A, B, C, which is what the reference
    # always prints, so the two sides are compared region for region.
    if order:
        checks = checks[::-1]
    return (int(m.group(1)) * 1e6, int(m.group(2)) * 1e6,
            int(m.group(3)) * 1e6, checks)


def run_ref(binary, row, count, reps, order=0):
    p = subprocess.run([str(binary), str(row['op']), str(row['size']),
                        str(count), str(reps), str(row['seed']), str(order)],
                       env=ENV, text=True, capture_output=True, timeout=RUN_TIMEOUT_S)
    if p.returncode != 0:
        raise SystemExit('reference run failed: %s' % (p.stderr[-500:]))
    m = TIME_RE.search(p.stdout)
    if not m:
        raise SystemExit('reference produced no timing: %r %r' % (p.stdout, p.stderr))
    checks = [ln for ln in p.stderr.splitlines() if ln.strip().isdigit()]
    return float(m.group(1)), float(m.group(2)), float(m.group(3)), checks


class Unmeasurable(Exception):
    """A - B could not be driven above the clock minima: a FAILED measurement.
    The row is reported with measurement="failed" and the raw numbers, never
    with a clamped or floored value."""


def deltas(bend_bin, ref_bin, row, count, reps, order=0):
    try:
        ba, bb, bc, _ = run_bend(bend_bin, row, count, reps, order)
        ra, rb, rc, _ = run_ref(ref_bin, row, count, reps, order)
    except subprocess.TimeoutExpired:
        raise Unmeasurable('a measured process exceeded %ds at count=%d reps=%d'
                           % (RUN_TIMEOUT_S, count, reps))
    return ba - bb, ra - rb, ba


def calibrate(bend_bin, ref_bin, row, log):
    """Lengthen the measured batch until A - B spans many clock ticks on BOTH
    sides, and return the (count, reps) that achieved it.

    For a size-preserving operation (`grow == 'count'`) the batch is
    lengthened by running the operation more times inside one round, so the
    structure is still built exactly `reps` times: a large structure with a
    cheap operation stays measurable because the build is not multiplied.
    For a size-changing operation only whole rounds may be repeated, because
    a longer batch would no longer be that operation at that size.
    """
    by_count = row.get('grow', 'reps') == 'count'
    # A size-changing operation is lengthened in whole rounds first. If the
    # round cap is reached without a timeable difference, the batch inside a
    # round is lengthened instead, but never past the row's `cap`: `size / 2`
    # for an operation that removes elements (the doubled region A is then
    # exactly the full sweep and never runs on an exhausted structure) and
    # `size` for one that adds them (the doubled region A at most trebles the
    # structure). Either way the row is still "this operation at this size"
    # and the build is paid once per round instead of once per batch.
    half = max(1, row.get('cap', max(1, row['size'] // 2)))
    count, reps = row['count'], row['reps']
    if not by_count and row['operation'] == 'lru.remove_seq' and (2 * count > row['size'] or 2 * half > row['size']):
        raise Unmeasurable('isolated-removal batch would exceed the prepared entries')
    turn = 0
    while True:
        bd, rd, ba = deltas(bend_bin, ref_bin, row, count, reps, turn % 2)
        turn += 1
        log.append('%s %s calibrate count=%d reps=%d bend_delta=%.0fns '
                   'ref_delta=%.0fns bendA=%.0fns'
                   % (row['operation'], row['workload'], count, reps, bd, rd, ba))
        if bd >= CAL_HEADROOM * MIN_DELTA_NS and rd >= CAL_HEADROOM * MIN_REF_DELTA_NS:
            return count, reps
        over_budget = ba > MAX_REGION_MS * 1e6
        # Whole rounds have run out of budget before the difference became
        # timeable: the round is build-dominated, so multiplying rounds only
        # multiplies the build. Jump the batch inside a round instead (up to
        # the row's cap) and start the round count again.
        if over_budget and not by_count and count < half:
            count = min(max(count * 2, half // 8), half)
            reps = row['reps']
            continue
        if over_budget:
            raise Unmeasurable(
                'a single Bend region already takes %.0fms at count=%d reps=%d '
                'while A-B is only %.0fns, so the row cannot be sampled %d times '
                'within the per-row budget' % (ba / 1e6, count, reps, bd, SAMPLES))
        grow = max(CAL_HEADROOM * MIN_DELTA_NS / max(bd, 1.0),
                   CAL_HEADROOM * MIN_REF_DELTA_NS / max(rd, 1.0))
        budget = (MAX_REGION_MS * 1e6) / max(ba, 1.0)
        factor = max(2, min(int(grow) + 1, 64, max(int(budget), 2)))
        if by_count:
            cap = max(1, MAX_OPS // max(reps, 1))
            if count >= cap:
                raise Unmeasurable(
                    'A-B stayed at %.0fns (bend) / %.0fns (reference) at the '
                    'operation cap count=%d reps=%d (bend region A %.0fms), below '
                    'the %.0fns / %.0fns minima'
                    % (bd, rd, count, reps, ba / 1e6, MIN_DELTA_NS, MIN_REF_DELTA_NS))
            count = min(count * factor, cap)
        else:
            cap = max(1, min(MAX_REPS, MAX_OPS // max(count, 1)))
            if count < half:
                # Lengthen the batch INSIDE a round first, up to the row's cap.
                # More rounds would raise the difference and the region by the
                # same factor -- the difference stays the same fraction of a
                # build-dominated round, and so does the noise around it -- so
                # only a longer batch actually improves the signal. The round
                # count starts again from the table's value each time.
                count = min(count * factor, half)
                reps = row['reps']
                continue
            if reps >= cap:
                raise Unmeasurable(
                    'A-B stayed at %.0fns (bend) / %.0fns (reference) at the '
                    'round cap count=%d reps=%d (bend region A %.0fms), below '
                    'the %.0fns / %.0fns minima'
                    % (bd, rd, count, reps, ba / 1e6, MIN_DELTA_NS, MIN_REF_DELTA_NS))
            reps = min(reps * factor, cap)


def measure(bend_bin, ref_bin, row, log):
    count, reps = calibrate(bend_bin, ref_bin, row, log)
    ops = reps * count
    bend_ns, ref_ns, bend_delta, ref_delta = [], [], [], []
    bend_control, ref_control = [], []
    bend_checks = ref_checks = None
    for i in range(SAMPLES):
        try:
            ba, bb, bctrl, bc = run_bend(bend_bin, row, count, reps, i % 2)
            ra, rb, rctrl, rc = run_ref(ref_bin, row, count, reps, i % 2)
        except subprocess.TimeoutExpired:
            raise Unmeasurable('a measured process exceeded %ds at count=%d reps=%d'
                               % (RUN_TIMEOUT_S, count, reps))
        log.append('%s %s count=%d reps=%d sample=%d order=%s bendA=%.0f '
                   'bendB=%.0f bendC=%.0f refA=%.0f refB=%.0f refC=%.0f '
                   'bend_chk=%s ref_chk=%s'
                   % (row['operation'], row['workload'], count, reps, i,
                      'CBA' if i % 2 else 'ABC', ba, bb, bctrl, ra, rb, rctrl,
                      bc, rc))
        bend_checks = bend_checks or bc
        ref_checks = ref_checks or rc
        if bc != bend_checks or rc != ref_checks:
            raise SystemExit('non-deterministic checksums for %s' % row['operation'])
        bd, rd = ba - bb, ra - rb
        if bd < MIN_DELTA_NS or rd < MIN_REF_DELTA_NS:
            raise Unmeasurable(
                'sample %d: A-B = %.0fns (bend) / %.0fns (reference), below '
                'the %.0fns / %.0fns minima'
                % (i, bd, rd, MIN_DELTA_NS, MIN_REF_DELTA_NS))
        bend_delta.append(bd)
        ref_delta.append(rd)
        bend_control.append(bctrl)
        ref_control.append(rctrl)
        bend_ns.append(bd / ops)
        ref_ns.append(rd / ops)
    verified = bool(bend_checks) and bend_checks == ref_checks
    return {
        'measurement': 'ok',
        'method': row.get('method', 'batch'),
        'operation': row['operation'],
        'workload': row['workload'],
        'size': row['size'],
        'verified': verified,
        'bend_ns': bend_ns,
        'reference_ns': ref_ns,
        'bend_delta_ns': bend_delta,
        'reference_delta_ns': ref_delta,
        'min_bend_delta_ns': MIN_DELTA_NS,
        'min_reference_delta_ns': MIN_REF_DELTA_NS,
        'bend_control_ns': bend_control,
        'reference_control_ns': ref_control,
        'operations_per_sample': ops,
        'reps': reps,
        'count': count,
        'grow': row.get('grow', 'reps'),
        'seed': row['seed'],
        'checksums': bend_checks,
    }


# ---------------------------------------------------------------------- main

def environment():
    cc_ver = sh([CC, '--version']).stdout.strip().splitlines()[:1]
    uname = platform.uname()
    cpu = sh(['sysctl', '-n', 'machdep.cpu.brand_string']).stdout.strip()
    if not cpu:
        cpu = uname.machine
    return {
        'cpu': '%s (%d logical cores; benchmarks pinned to one Bend worker thread)'
               % (cpu, os.cpu_count() or 1),
        'os': '%s %s %s' % (uname.system, uname.release, uname.machine),
        'bend_compiler': 'bend %s (%s, sha256 %s)' % (LOCK['version'], BEND, sha(BEND)),
        'reference_compiler': (cc_ver[0] if cc_ver else CC),
        'bend_flags': BEND_FLAGS,
        'reference_flags': ' '.join(CFLAGS),
        'reference_revision': 'benchmarks/native/ in this workspace, sha256 of every\n'
                              'file recorded in source_sha256',
    }


def source_hashes():
    hashes = {}
    # Exactly the folder list automation/performance_gate.py hashes. The live
    # C references are benchmarks/native/; native_bench/ is a stale copy left
    # over from an earlier iteration that the worker scope check forbids
    # deleting (a deletion counts as an out-of-scope change), so it is still
    # hashed here to keep the report consistent with the gate.
    for folder in ['src', 'types', 'proofs', 'spec', 'benchmarks', 'native_bench']:
        p = ROOT / folder
        if not p.exists():
            continue
        for f in sorted(p.rglob('*')):
            if f.is_file() and f.suffix in ['.bend', '.c', '.h', '.py', '.go', '.json', '.mod', '.sum', '.sh']:
                hashes[str(f.relative_to(ROOT))] = sha(f)
    for f in sorted(ROOT.glob('*.bend')):
        hashes[str(f.relative_to(ROOT))] = sha(f)
    return hashes


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--report', required=True)
    ap.add_argument('--only', default=None)
    args = ap.parse_args()

    rows = [dict(r, seed=r.get("seed", 1000 + i)) for i, r in enumerate(TABLE)]
    if args.only:
        rows = [r for r in rows if r['structure'] == args.only]
    structures = sorted({r['structure'] for r in rows})
    built = build_all(structures)

    log = []
    results = []
    t0 = time.time()
    failures = []
    partial = Path(args.report).with_suffix('.partial.json')
    partial.parent.mkdir(parents=True, exist_ok=True)
    for row in rows:
        bend_bin, ref_bin = built[row['structure']]
        try:
            res = measure(bend_bin, ref_bin, row, log)
        except Unmeasurable as exc:
            res = {'measurement': 'failed', 'reason': str(exc),
                   'operation': row['operation'], 'workload': row['workload'],
                   'size': row['size'], 'verified': False,
                   'bend_ns': [], 'reference_ns': [],
                   'operations_per_sample': row['count'] * row['reps'],
                   'reps': row['reps'], 'count': row['count'],
                   'seed': row['seed']}
            failures.append('%s/%s: %s' % (row['operation'], row['workload'], exc))
            log.append('%s %s FAILED MEASUREMENT: %s'
                       % (row['operation'], row['workload'], exc))
            print('%-34s %-16s size=%-8d FAILED MEASUREMENT (%s)'
                  % (res['operation'], res['workload'], res['size'], exc), flush=True)
            results.append(res)
            partial.write_text(json.dumps({'benchmarks': results, 'failed_measurements': failures},
                                          indent=1, sort_keys=True))
            continue
        results.append(res)
        partial.write_text(json.dumps({'benchmarks': results, 'failed_measurements': failures},
                                      indent=1, sort_keys=True))
        ratio = (statistics.median(res['bend_ns']) /
                 statistics.median(res['reference_ns'])
                 if statistics.median(res['reference_ns']) > 0 else float('inf'))
        print('%-34s %-16s size=%-8d ops=%-10d bend=%9.2fns ref=%9.2fns %6.2fx %s'
              % (res['operation'], res['workload'], res['size'],
                 res['operations_per_sample'],
                 statistics.median(res['bend_ns']),
                 statistics.median(res['reference_ns']), ratio,
                 'ok' if res['verified'] else 'UNVERIFIED'), flush=True)

    raw = LOGDIR / 'samples.log'
    raw.write_text('\n'.join(log))
    def cell(xs):
        return '%.3f' % statistics.median(xs) if xs else 'FAILED'

    summary = LOGDIR / 'summary.tsv'
    summary.write_text('\n'.join(
        '\t'.join([r['operation'], r['workload'], str(r['size']),
                   str(r['operations_per_sample']),
                   cell(r['bend_ns']), cell(r['reference_ns']),
                   r.get('measurement', 'ok')])
        for r in results))

    artifacts = {str(raw.relative_to(ROOT)): sha(raw),
                 str(summary.relative_to(ROOT)): sha(summary)}
    for name, (b, c) in built.items():
        artifacts[str(b.relative_to(ROOT))] = sha(b)
        artifacts[str(c.relative_to(ROOT))] = sha(c)

    report = {
        'backend': 'native-c',
        'reference': CONTRACT['reference'],
        'environment': environment(),
        'source_sha256': source_hashes(),
        'artifacts': artifacts,
        'benchmarks': [{k: v for k, v in r.items()} for r in results],
        'seconds': round(time.time() - t0, 1),
        'failed_measurements': failures,
    }
    out = Path(args.report)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=1, sort_keys=True))
    print('report: %s (%d workloads, %.0fs)' % (out, len(results), time.time() - t0))
    return 0


if __name__ == '__main__':
    sys.exit(main())

#!/usr/bin/env python3
"""Runtime validation of the bend-dsa structures.

  python tools/validate.py --report build/validation.json

For every structure in tests/structures.json this

  1. builds tests/<id>/main.bend with the pinned Bend compiler (native C
     backend) and runs the resulting binary,
  2. compares its output, line for line, with the independent Python oracle in
     tests/support/oracles.py, on
       - functional scenarios covering every inventoried operation,
       - boundary scenarios (empty structures, out-of-range indices, invalid
         ranges, foreign/stale handles, capacity limits), each of which ends by
         observing the whole state so that a rejected operation is checked to
         have preserved it,
       - deterministic seeded differential histories (seeds are recorded in the
         report),
  3. rebuilds the structure once per semantic mutant from tools/mutants.py and
     requires the mutant to produce a different, well-formed answer; a mutant
     that fails to compile or crashes is a failure of this validator, not a
     detection,
  4. re-runs the proof entry point `bend proofs/<id>.bend` for trace_proof.

The retained LRU is checked separately: its own PROOF/END_TO_END are re-checked
with the pinned compiler, the reuse entry points src/lru.bend and proofs/lru.bend
are checked, and tests/lru/main.bend is run against the LRU oracle. The LRU
cannot be built to a native binary with Bend 2.0.16 (see WORK_LOG.md and
tests/runtime_defects/wide_arity.bend), so it runs in `bend <file> -- args` mode.

Expected answers never reach the Bend side: the drivers receive operation
tokens only.
"""

import argparse
import hashlib
import json
import os
import platform
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tests' / 'support'))
sys.path.insert(0, str(ROOT / 'tools'))

import oracles  # noqa: E402
import scenarios  # noqa: E402
from mutants import MUTANTS  # noqa: E402

from toolchain import LOCK, BEND, BASE, ENV, PINNED, VERSION  # noqa: E402
BUILD = ROOT / 'build'
BIN = BUILD / 'bin'
MUTDIR = BUILD / 'mutants'
LOGDIR = BUILD / 'validation-logs'

FAILURES = []


def fail(where, message):
    FAILURES.append('%s: %s' % (where, message))
    print('FAIL %s: %s' % (where, message), file=sys.stderr)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run(cmd, cwd=ROOT, timeout=900):
    return subprocess.run(cmd, cwd=str(cwd), env=ENV, text=True,
                          capture_output=True, timeout=timeout)


def build_driver(name, src_root, out):
    """Compile tests/<name>/main.bend to a native binary. Returns (ok, log)."""
    out.parent.mkdir(parents=True, exist_ok=True)
    if out.exists():
        out.unlink()
    p = run([BEND, str(Path('tests') / name / 'main.bend'), '-o', str(out)], cwd=src_root)
    return out.exists(), (p.stdout + p.stderr)


def exec_driver(binary, args, timeout=300):
    p = subprocess.run([str(binary)] + list(args), env=ENV, text=True,
                       capture_output=True, timeout=timeout)
    return p


def lines_of(proc):
    return [ln for ln in proc.stdout.splitlines() if ln != '']


# --------------------------------------------------------------- comparisons

def check_scenarios(name, binary, cases, kind, log):
    """Run cases and compare with the oracle. Returns (ok, covered tokens)."""
    oracle = oracles.ORACLES[name]
    covered = set()
    ok = True
    for args in cases:
        proc = exec_driver(binary, args)
        got = lines_of(proc)
        want = oracle(list(args))
        log.append('[%s] %s %s' % (kind, name, ' '.join(args)))
        log.append('  bend  : %s' % got)
        log.append('  oracle: %s' % want)
        if proc.returncode != 0:
            fail(name, '%s scenario crashed (%s): %s' % (kind, ' '.join(args), proc.stderr.strip()[:200]))
            ok = False
            continue
        if got != want:
            first = next((i for i in range(max(len(got), len(want)))
                          if got[i:i + 1] != want[i:i + 1]), 0)
            fail(name, '%s mismatch at line %d for %s\n   bend  : %r\n   oracle: %r'
                 % (kind, first, ' '.join(args), got[first:first + 1], want[first:first + 1]))
            ok = False
            continue
        for tok in args:
            covered.add(tok.split(':')[0])
        for op, pred in scenarios.CTOR_OPS[name].items():
            if pred(list(args)):
                covered.add('\0' + op)
    return ok, covered


def operations_passed(name, covered):
    """Inventoried operations whose token appeared in a passing scenario."""
    table = scenarios.OPS[name]
    passed = []
    for op, tok in table.items():
        if tok == '':
            if ('\0' + op) in covered:
                passed.append(op)
        elif tok in covered:
            passed.append(op)
    return passed


# ------------------------------------------------------------------ mutation

def prepare_mutant(name, idx, search, replace, target):
    """Copy the sources into build/mutants/<name>/<idx> and apply one edit."""
    dst = MUTDIR / name / str(idx)
    if dst.exists():
        shutil.rmtree(dst)
    dst.mkdir(parents=True)
    for folder in ['src', 'tests']:
        if (ROOT / folder).exists():
            shutil.copytree(ROOT / folder, dst / folder,
                            ignore=shutil.ignore_patterns('__pycache__'))
    path = dst / target
    text = path.read_text()
    if text.count(search) != 1:
        return None, 'mutation site occurs %d times in %s' % (text.count(search), target)
    path.write_text(text.replace(search, replace))
    return dst, None


def check_mutants(name, cases, log):
    ok = True
    entries = MUTANTS.get(name, [])
    if len(entries) < 3:
        fail(name, 'fewer than three semantic mutants declared')
        return False, []
    results = []
    for idx, (label, target, search, replace) in enumerate(entries):
        root, err = prepare_mutant(name, idx, search, replace, target)
        if err:
            fail(name, 'mutant %r: %s' % (label, err))
            ok = False
            results.append({'mutant': label, 'status': 'not applied'})
            continue
        binary = root / 'mutant_bin'
        built, blog = build_driver(name, root, binary)
        if not built:
            fail(name, 'mutant %r did not compile (a compile error is not a '
                       'semantic rejection): %s' % (label, blog.strip()[-300:]))
            ok = False
            results.append({'mutant': label, 'status': 'compile error'})
            continue
        detected = False
        crashed = False
        for args in cases:
            try:
                proc = exec_driver(binary, args)
            except subprocess.TimeoutExpired:
                crashed = True
                continue
            if proc.returncode != 0:
                crashed = True
                continue
            got = lines_of(proc)
            want = oracles.ORACLES[name](list(args))
            if got != want and len(got) == len(want):
                detected = True
                log.append('[mutation] %s :: %s rejected on %s' % (name, label, ' '.join(args)))
                break
        if detected:
            results.append({'mutant': label, 'status': 'rejected'})
        elif crashed:
            fail(name, 'mutant %r only crashed; a crash does not count as a '
                       'semantic rejection' % label)
            ok = False
            results.append({'mutant': label, 'status': 'crashed'})
        else:
            fail(name, 'mutant %r survived every scenario' % label)
            ok = False
            results.append({'mutant': label, 'status': 'survived'})
    return ok, results


# ------------------------------------------------ the LRU and the hash table

def check_lru(log):
    """Differential checks for the key-value containers: the LRU against the
    optimized C reference and its sanitizer build (tools/lru_diff.py), the
    hash table against a Python dict oracle (tools/check_hash_table.py), the
    LRU against its specification (tools/check_lru_spec.py), and the
    refinement proofs of the hash table (proofs/hash_table.bend) and the LRU
    (proofs/lru.bend)."""
    ok = True
    checks = []
    for command in [[sys.executable, 'tools/lru_diff.py'],
                    [sys.executable, 'tools/check_hash_table.py'],
                    [sys.executable, 'tools/check_lru_spec.py'],
                    [BEND, 'proofs/containers/hash_table/proof.bend'],
                    [BEND, 'proofs/containers/lru/proof.bend']]:
        p = run(command, timeout=7200)
        good = p.returncode == 0 and (command[0] != BEND or 'All terms check' in p.stdout)
        last = (p.stdout.strip().splitlines() or [''])[-1]
        checks.append({'command': command, 'passed': good, 'output': last})
        log.append('[kv] %s -> %s' % (' '.join(command), last))
        if not good:
            fail('lru', '%s failed: %s' % (command[1], (p.stdout + p.stderr)[-300:]))
            ok = False
    return ok, {'checks': checks}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--report', required=True)
    ap.add_argument('--only', default=None, help='validate a single structure')
    args = ap.parse_args()

    if not PINNED:
        print('unpinned toolchain (BEND=%s): the report records it as such' % BEND, file=sys.stderr)
    elif sha(BEND) != LOCK['binary_sha256'] or sha(BASE) != LOCK['base_sha256']:
        print('pinned toolchain changed', file=sys.stderr)
        return 1

    inventory = json.loads((ROOT / 'tests' / 'structures.json').read_text())['new_structures']
    LOGDIR.mkdir(parents=True, exist_ok=True)
    started = time.time()

    rows = []
    for item in inventory:
        name = item['id']
        if args.only and name != args.only:
            continue
        if name in ('simple_queue', 'priority_queue'):
            # Queue facades: their drivers are checked by tools/check_queue_facades.py
            # against the stack / queue / heap oracles once all three are built.
            built = run([BEND, 'tests/%s/main.bend' % name, '-o', 'build/test-%s' % name], timeout=600)
            ok = (ROOT / 'build' / ('test-' + name)).exists()
            if not ok:
                fail(name, 'facade driver did not build: %s' % (built.stdout + built.stderr)[-300:])
            if name == 'priority_queue' and ok:
                facade = run([sys.executable, 'tools/check_queue_facades.py'], timeout=1200)
                ok = facade.returncode == 0
                if not ok:
                    fail(name, 'facade histories failed: %s' % (facade.stdout + facade.stderr)[-300:])
            state = 'passed' if ok else 'failed'
            rows.append({'id': name, 'runtime': state, 'boundaries': 'n/a', 'differential': state,
                         'structural': 'n/a', 'mutations': 'n/a', 'trace_proof': 'n/a'})
            print('%-22s runtime=%s differential=%s (facade)' % (name, state, state), flush=True)
            continue
        if name == 'balanced_search_tree':
            # The production module is the indexed TreeMap: its tests, the
            # oracle comparison, the component laws, and the universal
            # refinement proof proofs/tree_map.bend (every operation, every
            # good shadow, cursor and view, every lawful comparator).
            (ROOT/'build/tree-map').mkdir(parents=True, exist_ok=True)
            checks = []
            for command, limit in [([BEND, 'tests/tree_map/main.bend', '-o', 'build/tree-map/test'], 120),
                                   ([sys.executable, 'tools/check_tree_map.py'], 120),
                                   ([BEND, 'proofs/containers/balanced_search_tree/components.bend'], 120),
                                   ([BEND, 'proofs/containers/balanced_search_tree/range.bend'], 120),
                                   ([BEND, 'proofs/containers/balanced_search_tree/proof.bend'], 21600)]:
                result = run(command, timeout=limit)
                passed = result.returncode == 0 and (command[1] != 'proofs/containers/balanced_search_tree/proof.bend' or 'All terms check' in result.stdout)
                checks.append({'command': command, 'passed': passed,
                               'output': result.stdout + result.stderr})
                if not passed:
                    fail(name, 'TreeMap check failed: ' + repr(command))
                    break
            good = len(checks) == 5 and all(x['passed'] for x in checks)
            rows.append({'id': name, 'implementation': 'indexed TreeMap',
                         'runtime': 'passed' if good else 'failed',
                         'component_proof': 'passed' if good else 'failed',
                         'trace_proof': 'passed' if good else 'failed', 'checks': checks})
            (LOGDIR / (name + '.log')).write_text('\n'.join(x['output'] for x in checks))
            print('%-22s runtime=%s refinement_proof=%s' % (name, rows[-1]['runtime'], rows[-1]['trace_proof']), flush=True)
            continue
        log = []
        t0 = time.time()
        binary = BIN / name
        built, blog = build_driver(name, ROOT, binary)
        log.append('[build] %s -> %s' % (name, 'ok' if built else blog.strip()[-400:]))
        row = {'id': name, 'operations_passed': [], 'runtime': 'failed',
               'boundaries': 'failed', 'differential': 'failed',
               'structural': 'n/a', 'mutations': 'failed',
               'trace_proof': 'failed'}
        if not built:
            fail(name, 'driver did not build: %s' % blog.strip()[-300:])
            rows.append(row)
            (LOGDIR / (name + '.log')).write_text('\n'.join(log))
            continue

        func_ok, covered = check_scenarios(name, binary, scenarios.FUNCTIONAL[name],
                                           'functional', log)
        bnd_ok, bnd_cov = check_scenarios(name, binary, scenarios.BOUNDARY[name],
                                          'boundary', log)
        diff_cases = [scenarios.differential(name, s) for s in scenarios.SEEDS]
        diff_ok, diff_cov = check_scenarios(name, binary, diff_cases, 'differential', log)
        struct_cases = scenarios.STRUCTURAL.get(name, [])
        struct_ok, _ = check_scenarios(name, binary, struct_cases, 'structural', log)
        covered |= bnd_cov | diff_cov

        ops = operations_passed(name, covered) if func_ok else []
        missing = sorted(set(item['operations']) - set(ops))
        if missing:
            fail(name, 'operations not covered by a passing scenario: %s' % missing)

        mut_ok, mut_results = check_mutants(
            name, scenarios.FUNCTIONAL[name] + diff_cases + struct_cases, log)

        if not binary.exists():
            # The driver was built and exercised above; its disappearance
            # afterwards is recorded as a failure, never skipped silently.
            fail(name, 'driver binary %s disappeared during validation' % binary)
            func_ok = False
        p = run([BEND, 'proofs/containers/%s/proof.bend' % name], timeout=7200)
        proof_ok = p.returncode == 0 and 'All terms check' in p.stdout
        proof_line = (p.stdout.strip().splitlines() or [''])[-1]
        log.append('[proof] proofs/containers/%s/proof.bend -> %s' % (name, proof_line))
        if not proof_ok:
            fail(name, 'proofs/containers/%s/proof.bend did not check: %s' % (name, (p.stdout + p.stderr)[-300:]))

        row.update({
            'operations_passed': sorted(ops) if not missing else sorted(ops),
            'runtime': 'passed' if func_ok and not missing else 'failed',
            'boundaries': 'passed' if bnd_ok else 'failed',
            'differential': 'passed' if diff_ok else 'failed',
            'structural': ('passed' if struct_ok else 'failed') if struct_cases else 'n/a',
            'mutations': 'passed' if mut_ok else 'failed',
            'trace_proof': 'passed' if proof_ok else 'failed',
            'checker_output': proof_line,
            'mutants': mut_results,
            'scenarios': {'functional': len(scenarios.FUNCTIONAL[name]),
                          'boundary': len(scenarios.BOUNDARY[name]),
                          'differential': len(diff_cases),
                          'structural': len(struct_cases)},
            'trace_seeds': scenarios.SEEDS,
            'driver_sha256': sha(ROOT / 'tests' / name / 'main.bend'),
            'binary_sha256': sha(binary) if binary.exists() else None,
            'seconds': round(time.time() - t0, 1),
        })
        rows.append(row)
        (LOGDIR / (name + '.log')).write_text('\n'.join(log))
        print('%-22s runtime=%s boundaries=%s differential=%s structural=%s '
              'mutations=%s trace_proof=%s'
              % (name, row['runtime'], row['boundaries'], row['differential'],
                 row['structural'], row['mutations'], row['trace_proof']), flush=True)

    # src/math/natural.bend: differential test against CPython's math
    # module (tools/check_math.py) and the proof package proofs/math; the
    # templated math per type (tools/check_generic.py: U32, U64, F32, F64,
    # each case naming its spec/math/generic.bend clause) and the software
    # binary64 against the machine's doubles (tools/check_f64.py), the
    # binary64 specification itself against them (tools/check_f64_spec.py),
    # the typed clauses' checker-evaluated examples and the math specs.
    math_row = None
    if not args.only or args.only == 'math':
        (ROOT / 'build/math').mkdir(parents=True, exist_ok=True)
        checks = []
        math_checks = [([BEND, 'tests/math/natural.bend', '-o', 'build/math/natural'], 600),
                       ([sys.executable, 'tools/check_math.py'], 1200),
                       ([BEND, 'tests/math/generic.bend', '-o', 'build/math/generic'], 1800),
                       ([sys.executable, 'tools/check_generic.py'], 1800),
                       ([BEND, 'tests/math/f64.bend', '-o', 'build/math/f64'], 1800),
                       ([sys.executable, 'tools/check_f64.py'], 1800),
                       ([sys.executable, 'tools/check_f64_spec.py'], 1800),
                       ([BEND, 'proofs/math/proof.bend'], 3600),
                       ([BEND, 'proofs/math/typed/examples.bend'], 1800)] + \
                      [([BEND, str(f.relative_to(ROOT))], 1800) for f in sorted((ROOT / 'spec/math').glob('*.bend'))]
        for command, limit in math_checks:
            result = run(command, timeout=limit)
            passed = result.returncode == 0 and (not command[1].endswith('.bend') or '-o' in command or 'All terms check' in result.stdout)
            checks.append({'command': command, 'passed': passed, 'output': result.stdout + result.stderr})
            if not passed:
                fail('math', 'math check failed: ' + repr(command))
                break
        good = len(checks) == len(math_checks) and all(x['passed'] for x in checks)
        math_row = {'id': 'math', 'implementation': 'src/math/natural.bend, generic.bend, f64.bend',
                    'differential': 'passed' if good else 'failed',
                    'proof': 'passed' if good else 'failed', 'checks': checks}
        (LOGDIR / 'math.log').write_text('\n'.join(x['output'] for x in checks))
        print('%-22s differential=%s proof=%s' % ('math', math_row['differential'], math_row['proof']), flush=True)

    lru_log = []
    lru_ok, lru_detail = check_lru(lru_log)
    (LOGDIR / 'lru.log').write_text('\n'.join(lru_log))

    hashed = {}
    for folder in ['src', 'tests', 'tools']:
        for f in sorted((ROOT / folder).rglob('*')):
            if f.is_file() and f.suffix in ('.bend', '.py'):
                hashed[str(f.relative_to(ROOT))] = sha(f)
    for f in sorted(ROOT.glob('*.bend')):
        hashed[str(f.relative_to(ROOT))] = sha(f)

    complete = (not FAILURES) and lru_ok and len(rows) == len(inventory)
    report = {
        'structures': rows,
        'math': math_row,
        'lru_reuse': 'passed' if lru_ok else 'failed',
        'lru_detail': lru_detail,
        'complete': bool(complete),
        'failures': FAILURES,
        'trace_seeds': scenarios.SEEDS,
        'source_sha256': hashed,
        'toolchain': {'bend': BEND, 'bend_version': VERSION, 'pinned': PINNED,
                      'bend_sha256': sha(BEND),
                      'base_sha256': sha(BASE) if Path(BASE).exists() else None,
                      'backend': 'native-c (bend <file> -o <bin>)',
                      'lru_backend': 'retained reference: bend run mode (its Word(64n) metrics exceed the native arity limit); benchmarked port src/lru/fast.bend: native-c'},
        'environment': {'platform': platform.platform(),
                        'machine': platform.machine(),
                        'python': platform.python_version()},
        'logs': str((LOGDIR).relative_to(ROOT)),
        'seconds': round(time.time() - started, 1),
    }
    out = Path(args.report)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=1, sort_keys=True))
    print('report: %s (complete=%s, %d failures)'
          % (out, report['complete'], len(FAILURES)))
    return 0 if complete else 1


if __name__ == '__main__':
    sys.exit(main())

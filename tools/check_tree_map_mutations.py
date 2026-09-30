#!/usr/bin/env python3
"""Semantic mutants of the indexed TreeMap, each in an isolated scratch copy.

Every mutant is one textual edit of src/containers/balanced_search_tree.bend
(the production file is never touched). For each one this

  1. builds tests/tree_map/main.bend against the mutated source: a mutant
     that does not compile is a failure of this script, not a detection;
  2. runs the differential histories of tools/check_tree_map.py on it;
  3. checks the refinement proof proofs/containers/balanced_search_tree/
     proof.bend and the component laws components.bend against it.

A mutant is killed when the differential run fails or a proof is rejected.
Every mutant must be killed, and the proofs must reject every one of them:
the differential column says which ones the runtime tests also see (a wrong
capacity limit or a key left in a freed slot is invisible to them).

  python3 tools/check_tree_map_mutations.py [--seeds N] [--steps N]

Writes build/tree-map/mutations.json; exit 1 on a survivor.
"""
import argparse, json, shutil, subprocess, sys, tempfile, time
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))
from toolchain import BEND, ENV

SRC = 'src/containers/balanced_search_tree.bend'
PROOFS = ['proofs/containers/balanced_search_tree/proof.bend',
          'proofs/containers/balanced_search_tree/components.bend']
SET = 'Array.set(Maybe<&2, Maybe<&2, V>>, ps, U32.from_nat(i), Some{Some{v}})'

# edits a mutant needs besides its own to stay well-typed (a reusable binder)
EXTRA = {'replace_stored_key': [('Search{1n+i, p, on_left}}:\n      put_replaced(~K, ~V, ~cmp, exchange(~K, ~V, ~cmp, set_key',
                                 'Search{1n+ +i, p, on_left}}:\n      put_replaced(~K, ~V, ~cmp, exchange(~K, ~V, ~cmp, set_key')]}

# (name, area, old, new, the differential tests see it)
MUTATIONS = [
    ('red_root', 'balance',
     'set_red(~K, ~V, ~cmp, m1, r, False{})',
     'set_red(~K, ~V, ~cmp, m1, r, True{})', True),
    ('replace_stored_key', 'put',
     'put_replaced(~K, ~V, ~cmp, exchange(~K, ~V, ~cmp, m, 1n+i, Some{v}))',
     'put_replaced(~K, ~V, ~cmp, exchange(~K, ~V, ~cmp, set_key(~K, ~V, ~cmp, m, 1n+i, k), 1n+i, Some{v}))', True),
    ('skip_after_cursor_remove', 'cursor',
     '(Cursor{m, id, 0n, lower, upper, forward}, removed)',
     '(Cursor{m, 0n, 0n, lower, upper, forward}, removed)', True),
    ('set_left_writes_right_slot', 'node store',
     'NS{limit, depth, cap, used, Array.set(Nat, links, U32.from_nat(Nat.double(i)), v), keys}',
     'NS{limit, depth, cap, used, Array.set(Nat, links, U32.from_nat(1n+Nat.double(i)), v), keys}', True),
    ('parent_reads_tag_slot', 'node store',
     'ns_field_fin(~K, limit, depth, cap, used, keys, Array.get(Nat, links, U32.from_nat(1n+Nat.double(Nat.add(cap, i)))))',
     'ns_field_fin(~K, limit, depth, cap, used, keys, Array.get(Nat, links, U32.from_nat(Nat.double(Nat.add(cap, i)))))', True),
    ('grow_swaps_halves', 'node store',
     'ANode{ANode{lo, ns_nats(1n+depth)}, ANode{hi, ns_nats(1n+depth)}}',
     'ANode{ANode{hi, ns_nats(1n+depth)}, ANode{lo, ns_nats(1n+depth)}}', True),
    ('wipe_keeps_key', 'node store',
     'Array.set(Maybe<&2, K>, keys, U32.from_nat(i), None{})',
     'keys', False),
    ('limit_30', 'node store',
     'def ns_max() -> Nat:\n  29n',
     'def ns_max() -> Nat:\n  30n', False),
    ('fold_descends_right', 'fold',
     'walk(~K, ~V, ~cmp, ~A, ~f, g, Unbounded{}, upb, WDown{}, 0n, True{}, Array.get(Nat, lk, U32.from_nat(Nat.double(j))), Con{j, st0}, a, (ks, y), pq0)',
     'walk(~K, ~V, ~cmp, ~A, ~f, g, Unbounded{}, upb, WDown{}, 0n, True{}, Array.get(Nat, lk, U32.from_nat(1n+Nat.double(j))), Con{j, st0}, a, (ks, y), pq0)', True),
    ('fold_ignores_upper_bound', 'fold',
     'walk_apply(~K, ~V, ~A, ~f, inside, a, k, v)',
     'walk_apply(~K, ~V, ~A, ~f, True{}, a, k, v)', True),
    ('fold_loses_value', 'fold',
     '(' + SET + ', None{})',
     '(ps, None{})', True),
    ('fold_range_ignores_lower_bound', 'fold',
     'lower, upper, WDown{}, 0n, True{}, (lk, root), Nil{}, a,',
     'Unbounded{}, upper, WDown{}, 0n, True{}, (lk, root), Nil{}, a,', True),
    ('fold_short_fuel', 'fold',
     '1n+Nat.double(Nat.double(n))',
     '1n+Nat.double(n)', True),
    ('seek_side_inverted', 'fold',
     'def walk_side(+inside: Bool) -> Nat:\n  match inside:\n    case True{}:\n      0n\n    case False{}:\n      1n',
     'def walk_side(+inside: Bool) -> Nat:\n  match inside:\n    case True{}:\n      1n\n    case False{}:\n      0n', True),
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--seeds', type=int, default=4)
    ap.add_argument('--steps', type=int, default=150)
    args = ap.parse_args()
    source = (ROOT / SRC).read_text()
    report, survivors, t0 = [], [], time.time()
    for name, area, old, new, diff_expected in MUTATIONS:
        assert source.count(old) == 1, (name, 'anchor occurs %d times' % source.count(old))
        with tempfile.TemporaryDirectory(prefix='bend-tree-map-mutation-') as td:
            tmp = Path(td)
            for folder in ['src', 'spec', 'proofs', 'tests/support', 'tests/tree_map']:
                shutil.copytree(ROOT / folder, tmp / folder)
            (tmp / 'tools').mkdir()
            for f in ['check_tree_map.py', 'toolchain.py', 'toolchain.json']:
                if (ROOT / 'tools' / f).exists():
                    shutil.copy(ROOT / 'tools' / f, tmp / 'tools' / f)
            (tmp / 'build/tree-map').mkdir(parents=True)
            mutated = source.replace(old, new)
            for a, b in EXTRA.get(name, []):
                assert mutated.count(a) == 1, (name, 'extra anchor')
                mutated = mutated.replace(a, b)
            (tmp / SRC).write_text(mutated)
            built = subprocess.run([BEND, 'tests/tree_map/main.bend', '-o', 'build/tree-map/test'],
                                   cwd=tmp, text=True, capture_output=True, timeout=300, env=ENV)
            assert (tmp / 'build/tree-map/test').exists(), (name, 'mutant must compile', (built.stdout + built.stderr)[-600:])
            tested = subprocess.run([sys.executable, 'tools/check_tree_map.py', '--seeds', str(args.seeds), '--steps', str(args.steps)],
                                    cwd=tmp, text=True, capture_output=True, timeout=600)
            diff_killed = tested.returncode != 0
            proofs = {}
            for p in PROOFS:
                r = subprocess.run([BEND, p], cwd=tmp, text=True, capture_output=True, timeout=1800, env=ENV)
                proofs[p] = r.returncode != 0 or 'ALL PROOFS CHECK' not in r.stdout
            proof_killed = any(proofs.values())
            row = {'mutation': name, 'area': area, 'compiles': True,
                   'differential_killed': diff_killed, 'differential_expected': diff_expected,
                   'proof_killed': proof_killed, 'proofs_rejecting': [p for p, k in proofs.items() if k],
                   'test_failure': (tested.stdout + tested.stderr)[-600:] if diff_killed else ''}
            report.append(row)
            if not proof_killed or (diff_expected and not diff_killed):
                survivors.append(name)
            print('%-32s %-10s differential=%-8s proofs=%s' % (name, area, 'killed' if diff_killed else 'survived',
                                                              'killed' if proof_killed else 'SURVIVED'), flush=True)
    n = len(report)
    summary = {'mutants': n,
               'killed': sum(1 for r in report if r['differential_killed'] or r['proof_killed']),
               'killed_by_proofs': sum(1 for r in report if r['proof_killed']),
               'killed_by_differential': sum(1 for r in report if r['differential_killed']),
               'survivors': survivors, 'passed': not survivors,
               'seconds': round(time.time() - t0, 1), 'mutations': report}
    (ROOT / 'build/tree-map').mkdir(parents=True, exist_ok=True)
    (ROOT / 'build/tree-map/mutations.json').write_text(json.dumps(summary, indent=2) + '\n')
    print('mutants %d: killed %d, by proofs %d, by differential %d; survivors %s'
          % (n, summary['killed'], summary['killed_by_proofs'], summary['killed_by_differential'], survivors))
    sys.exit(0 if not survivors else 1)


if __name__ == '__main__':
    main()

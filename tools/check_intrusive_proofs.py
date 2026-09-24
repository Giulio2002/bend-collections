#!/usr/bin/env python3
"""Check the semantic proof package and reject coordinated specification bugs.

The coordinated mutants deliberately keep implementation, write specification
and graph execution in agreement. They must pass the old write/refinement
checks, then fail the independent sequence-invariant theorem. A syntax error,
missing import or timeout never counts as a successful negative test.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = Path('proofs/containers/intrusive_doubly_linked_list')
IMPL = Path('src/containers/internal/intrusive_list.bend')


def check(bend, path, clean=True):
    p = subprocess.run([bend, str(path), '--check-only'], capture_output=True,
                       text=True, timeout=120,
                       env={**os.environ, 'BEND_NO_TELEMETRY': '1'})
    message = (p.stdout + p.stderr).strip()
    if clean:
        if p.returncode or message != 'All terms check.':
            raise RuntimeError(f'{path}: {message}')
    elif (p.returncode == 0 or 'Error:' not in message or
          '- expected :' not in message or '- observed :' not in message or
          any(x in message.lower() for x in ('not found', 'unbound', 'syntax', 'import error'))):
        raise RuntimeError(f'not a semantic rejection: {message}')
    return message


def replace(path, old, new):
    text = path.read_text()
    if text.count(old) != 1:
        raise RuntimeError(f'{path}: mutation anchor changed')
    path.write_text(text.replace(old, new))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bend', default=os.environ.get('BEND', 'bend'))
    args = parser.parse_args()
    bend = shutil.which(args.bend) or str(Path(args.bend).resolve())
    build = ROOT / 'build/intrusive-list'
    build.mkdir(parents=True, exist_ok=True)
    regenerated = []
    with tempfile.TemporaryDirectory(prefix='proof-source-', dir=build) as temporary:
        for source in sorted((ROOT / PACKAGE).glob('*.src')):
            output = Path(temporary) / source.with_suffix('.bend').name
            subprocess.run([sys.executable, str(ROOT / 'tools/generators/mac.py'),
                            str(source), str(output)], check=True, capture_output=True, timeout=30)
            if output.read_bytes() != source.with_suffix('.bend').read_bytes():
                raise RuntimeError(f'{source.name}: generated proof is stale')
            regenerated.append(source.name)
    check(bend, ROOT / PACKAGE / 'proof.bend')
    results = []
    with tempfile.TemporaryDirectory(prefix='proof-mutant-', dir=build) as temporary:
        stage = Path(temporary)
        shutil.copytree(ROOT / 'src', stage / 'src')
        shutil.copytree(ROOT / 'proofs', stage / 'proofs')
        package = stage / PACKAGE
        # Retain the old head: all three descriptions of execution agree on
        # this bug, while the ordered-sequence invariant remains unchanged.
        replace(stage / IMPL,
                'set_next(set_head(s, i, after), node, None{})',
                'set_next(s, node, None{})')
        replace(package / 'spec.bend',
                'Con{Head{root, None{}}, Con{Next{node, None{}}, Nil{}}}',
                'Con{Next{node, None{}}, Nil{}}')
        replace(package / 'spec.bend',
                'Con{Prev{q, None{}}, Con{Head{root, Some{q}}, Con{Next{node, None{}}, Nil{}}}}',
                'Con{Prev{q, None{}}, Con{Next{node, None{}}, Nil{}}}')
        replace(package / 'graph.bend',
                'case None{}: sn(~N,~R,~P,sh(~N,~R,~P,g,r,q),n,None{})',
                'case None{}: sn(~N,~R,~P,g,n,None{})')
        check(bend, stage / IMPL)
        check(bend, package / 'writes.bend')
        check(bend, package / 'adapter.bend')
        diagnostic = check(bend, package / 'edits.bend', clean=False)
        results.append({'mutant': 'retain-head-in-code-write-spec-and-graph',
                        'implementation_well_typed': True, 'write_gate_passed': True,
                        'adapter_gate_passed': True, 'semantic_gate_rejected': True,
                        'diagnostic': diagnostic})
    with tempfile.TemporaryDirectory(prefix='adapter-mutant-', dir=build) as temporary:
        stage = Path(temporary)
        shutil.copytree(ROOT / 'src', stage / 'src')
        shutil.copytree(ROOT / 'proofs', stage / 'proofs')
        path = stage / PACKAGE / 'array_adapter.bend'
        replace(path, 'Store{Array.set(Maybe<&2,Node>,cells,i,v),f}', 'Store{cells,f}')
        runtime = path.with_name('bad_adapter_runtime.bend')
        runtime.write_text(path.read_text().split('def next_law(')[0])
        check(bend, runtime)
        diagnostic = check(bend, path, clean=False)
        results.append({'mutant': 'array-setter-ignores-write',
                        'implementation_well_typed': True,
                        'adapter_law_rejected': True, 'diagnostic': diagnostic})
    report = {'regenerated': regenerated, 'mutants': results,
              'sources': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in sorted((ROOT / PACKAGE).glob('*')) if p.is_file()},
              'passed': True}
    (build / 'proofs.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'semantic_proofs': 'clean', 'negative_controls': len(results),
                      'regenerated_proofs': len(regenerated), 'passed': True}))


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Independent map observations and runtime red-black invariant checks."""
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tests/support'))
sys.path.insert(0, str(ROOT / 'tools'))
import oracles
import scenarios

cases = list(scenarios.FUNCTIONAL['balanced_search_tree'])
cases += scenarios.BOUNDARY['balanced_search_tree']
cases += scenarios.STRUCTURAL['balanced_search_tree']
for seed in range(100):
    ops = scenarios.differential('balanced_search_tree', seed)
    cases.append(ops)
    cases.append(['rb32' if ops[0] == 'u32' else 'rbstr'] + ops[1:])
for index, args in enumerate(cases):
    result = subprocess.run([str(ROOT / 'build/test-tree')] + args,
                            text=True, capture_output=True, timeout=30, check=True)
    expected = oracles.balanced_search_tree(args)
    assert result.stdout.splitlines() == expected, (index, args, result.stdout, expected)
report = {'histories': len(cases), 'operations': sum(len(x)-1 for x in cases),
          'passed': True, 'keys': ['U32', 'String'],
          'checks': ['independent dictionary oracle', 'black root', 'no red-red edge',
                     'equal black height', 'sorted keys', 'cached size']}
(ROOT / 'build/tree-tests.json').write_text(json.dumps(report, indent=2) + '\n')
print(report)

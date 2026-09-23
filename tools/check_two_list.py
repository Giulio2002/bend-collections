#!/usr/bin/env python3
"""Independent two-list runtime regression suite; not a proof gate."""
import json
import random
import subprocess
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT/'tools'), str(ROOT/'tests/support')]
import scenarios
import oracles

def main():
    report = []
    for name in ['deque', 'queue']:
        cases = scenarios.FUNCTIONAL[name] + scenarios.BOUNDARY[name]
        cases += [scenarios.differential(name, s) for s in scenarios.SEEDS]
        for seed in range(30):
            rng = random.Random(seed)
            pushes = ['pf', 'pb'] if name == 'deque' else ['enq']
            other = ['popf', 'popb', 'peekf', 'peekb', 'len', 'list'] if name == 'deque' else ['deq', 'peek', 'len', 'list']
            ops = []
            for _ in range(500):
                op = rng.choice(pushes + other)
                ops.append(op + ':' + str(rng.randrange(10000)) if op in pushes else op)
            cases.append(ops + ['list', 'len'])
        for n in [0, 1, 2, 3, 31, 32, 33, 1023]:
            cases.append([('pb:' if name == 'deque' else 'enq:') + str(i) for i in range(n)] + (['peekf', 'peekb', 'popf', 'popb'] if name == 'deque' else ['peek', 'deq']) * (n+2) + ['list', 'len'])
        for i, args in enumerate(cases):
            p = subprocess.run([str(ROOT/'build'/('two-'+name)), *args], capture_output=True, text=True, check=True, timeout=30)
            assert p.stdout.splitlines() == getattr(oracles, name)(args), (name, i)
        report.append({'structure': name, 'histories': len(cases), 'operations': sum(map(len, cases))})
    (ROOT/'build/two-list-differential.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report))
if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Exercise actual facade calls against independent sequence/heap oracles."""
import json,random,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tests/support'))
import oracles
report=[]
for name,base in [('simple_queue','queue'),('priority_queue','binary_heap')]:
    histories=[]
    for seed in range(20):
        rng=random.Random(seed);ops=[]
        for _ in range(400):
            verb=rng.choice(['push','push','pop','peek','len','list'])
            if base=='queue':verb={'push':'enq','pop':'deq'}.get(verb,verb)
            if base=='binary_heap' and verb=='list':verb='sorted'
            ops.append(verb+':'+str(rng.randrange(1000)) if verb in ['push','enq'] else verb)
        if base=='binary_heap':ops=['u32']+ops
        histories.append(ops)
    for ops in histories:
        p=subprocess.run([str(ROOT/'build'/('test-'+name)),*ops],capture_output=True,text=True,check=True,timeout=30)
        assert p.stdout.splitlines()==getattr(oracles,base)(ops),(name,ops,p.stdout)
    report.append({'structure':name,'histories':len(histories),'operations':8000,'passed':True})
(ROOT/'build/queue-facade-tests.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))

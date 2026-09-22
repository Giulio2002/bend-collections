#!/usr/bin/env python3
"""Calibrated before/after tree updates; identical workloads and C reference.

Pass an archived pre-change Bend binary. Build the current benchmark first.
Results retain raw samples, binary hashes, and the exact production sources.
"""
import argparse
import json
from pathlib import Path
import statistics
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'benchmarks'))
import run as b
import bench
from workloads import TABLE

p = argparse.ArgumentParser()
p.add_argument('--before', type=Path, required=True)
p.add_argument('--after', type=Path, default=ROOT/'build/bench/bend/balanced_search_tree')
a = p.parse_args()
a.before = a.before.resolve(); a.after = a.after.resolve()
ref = b.REFBIN/'balanced_search_tree'
report = {'environment': b.environment(), 'scope': 'insert and remove/reinsert pair, three sizes',
          'target_ratio': 2.5, 'source_sha256': bench.fingerprints(),
          'binary_sha256': {str(x): b.sha(x) for x in [a.before, a.after, ref]},
          'results': []}
log=[]
for row in TABLE:
    if row['operation'] not in ['balanced_search_tree.insert', 'balanced_search_tree.remove']:
        continue
    count, reps = b.calibrate(a.after, ref, row, log)
    samples=[]
    for i in range(b.SAMPLES):
        paths=[('before',a.before),('after',a.after)]
        if i%2: paths.reverse()
        sample={}
        for name, binary in paths:
            ta,tb,tc,checks=b.run_bend(binary,row,count,reps,i%2)
            assert ta-tb>=b.MIN_DELTA_NS, (name,row,ta,tb)
            sample[name]={'A_ns':ta,'B_ns':tb,'control_ns':tc,'checksums':checks,'ns':(ta-tb)/(count*reps)}
        ta,tb,tc,checks=b.run_ref(ref,row,count,reps,i%2)
        assert ta-tb>=b.MIN_REF_DELTA_NS
        sample['c']={'A_ns':ta,'B_ns':tb,'control_ns':tc,'checksums':checks,'ns':(ta-tb)/(count*reps)}
        assert checks == sample['before']['checksums'] == sample['after']['checksums']
        samples.append(sample)
    med={name:statistics.median(s[name]['ns'] for s in samples) for name in ['before','after','c']}
    result={'operation':row['operation'],'size':row['size'],'seed':row['seed'],'count':count,'reps':reps,
            'method':row['method'],'samples':samples,'medians_ns':med,
            'speedup':med['before']/med['after'],'ratio':med['after']/med['c']}
    report['results'].append(result)
    (ROOT/'build/tree-opt/update-comparison.json').write_text(json.dumps(report,indent=2)+'\n')
    (ROOT/'build/tree-opt/calibration.log').write_text('\n'.join(log)+'\n')
    print(row['operation'],row['size'],med,'speedup',result['speedup'],'ratio',result['ratio'],flush=True)

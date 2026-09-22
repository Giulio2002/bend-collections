#!/usr/bin/env python3
"""Alternating before/after measurements; C unchanged and checksums required."""
import json,statistics,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'benchmarks'))
import run as b
from workloads import TABLE
records=[]
for op in ['balanced_search_tree.min','balanced_search_tree.max']:
 row=next(r for r in TABLE if r['operation']==op and r['workload']=='small');samples=[]
 for i in range(6):
  paths=[('before',ROOT/'build/tree-baseline'),('after',b.BENDBIN/'balanced_search_tree')]
  if i%2:paths.reverse()
  sample={}
  for name,path in paths:
   *times,chk=b.run_bend(path,row,3000000,1,i%2)
   sample[name]={'times':times,'checksums':chk}
  *times,chk=b.run_ref(b.REFBIN/'balanced_search_tree',row,3000000,1,i%2)
  sample['c']={'times':times,'checksums':chk}
  assert sample['before']['checksums']==sample['after']['checksums']==chk
  samples.append(sample)
 records.append({'operation':op,'samples':samples})
(ROOT/'build/tree-comparison.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps(records))

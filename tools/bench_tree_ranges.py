#!/usr/bin/env python3
"""Calibrated TreeMap vs the unchanged optimized C red-black reference."""
import argparse,json,statistics,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'benchmarks'))
import run as b
from workloads import TABLE
p=argparse.ArgumentParser();p.add_argument('--all',action='store_true');a=p.parse_args()
bin=ROOT/'build/tree-range/narrow';before=ROOT/'build/tree-range/before';ref=b.REFBIN/'balanced_search_tree';log=[]
report={'environment':b.environment(),'target_ratio':2.5,'reference':'unchanged benchmarks/native/balanced_search_tree.c and redblack.h','binary_sha256':{str(x):b.sha(x) for x in [before,bin,ref]},'source_sha256':{str(x.relative_to(ROOT)):b.sha(x) for x in [ROOT/'src/balanced_search_tree.bend',ROOT/'src/dynamic_array.bend',ROOT/'benchmarks/bend/tree_map.bend',ROOT/'benchmarks/native/balanced_search_tree.c',ROOT/'benchmarks/native/redblack.h']},'notes':['Public API; no FFI or patched generated C.','Range and ordered iteration fold entries directly on BOTH sides.','Remove means remove/reinsert pair.','Insert workload contains both fresh insertion and replacement.'],'results':[]}
selected=[row for row in TABLE if row['operation'].startswith('balanced_search_tree.') and row['op'] in [7,8]]
report['expected_rows']=len(selected);report['complete']=False
for row in selected:
 try:
  count,reps=b.calibrate(bin,ref,row,log);samples=[]
  for i in range(b.SAMPLES):
   fns=[('before',b.run_bend,before),('bend',b.run_bend,bin),('c',b.run_ref,ref)]
   if i%2:fns.reverse()
   sample={}
   for name,fn,path in fns:
    ta,tb,tc,checks=fn(path,row,count,reps,i%2)
    assert ta-tb >= (b.MIN_DELTA_NS if name!='c' else b.MIN_REF_DELTA_NS),(name,ta,tb)
    sample[name]={'A_ns':ta,'B_ns':tb,'control_ns':tc,'checksums':checks,'ns':(ta-tb)/(count*reps)}
   assert sample['before']['checksums']==sample['bend']['checksums']==sample['c']['checksums'],sample
   samples.append(sample)
  med={name:statistics.median(s[name]['ns'] for s in samples) for name in ['before','bend','c']}
  result={'operation':row['operation'].replace('balanced_search_tree','tree_map').replace('.to_list','.iterate'),'size':row['size'],'seed':row['seed'],'count':count,'reps':reps,'method':row['method'],'samples':samples,'medians_ns':med,'ratio':med['bend']/med['c'],'speedup':med['before']/med['bend']}
 except Exception as e:
  result={'operation':row['operation'].replace('balanced_search_tree','tree_map').replace('.to_list','.iterate'),'size':row['size'],'seed':row['seed'],'error':str(e)}
 report['results'].append(result)
 (ROOT/'build/tree-range/benchmarks.json').write_text(json.dumps(report,indent=2)+'\n')
 (ROOT/'build/tree-range/calibration.log').write_text('\n'.join(log)+'\n')
 print({k:v for k,v in result.items() if k!='samples'},flush=True)

report['complete']=len(report['results'])==report['expected_rows']
(ROOT/'build/tree-range/benchmarks.json').write_text(json.dumps(report,indent=2)+'\n')

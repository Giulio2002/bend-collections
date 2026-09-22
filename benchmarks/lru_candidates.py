#!/usr/bin/env python3
"""Screen compiled LRU candidates with unchanged canonical workloads/timing rules.
Waits for the frozen full sweep, then compares every candidate sequentially.
This is a candidate screen, not the final 51-row acceptance report.
"""
import argparse,json,statistics,time,sys
from pathlib import Path
import run as b
from workloads import TABLE
sys.path.insert(0,str(b.ROOT/"tools"))
from render_lru_optimization import render

def main():
 p=argparse.ArgumentParser();p.add_argument('--wait-for',type=Path);p.add_argument('--output',type=Path,default=Path('build/lru-opt/candidates.json'));p.add_argument('--candidates',default='before,lookup,zero,packed,promote,find');a=p.parse_args()
 if a.wait_for:
  while json.loads(a.wait_for.read_text())['status']!='finished':time.sleep(10)
 candidates=a.candidates.split(',')
 root=b.ROOT/'build/lru-opt';out={'status':'running','environment':b.environment(),'max_ratio':b.CONTRACT['max_ratio'],'benchmarks':[],'artifacts':{n:b.sha(root/n) for n in candidates+['c']},'source_sha256':b.source_hashes()};logs=[]
 def save():
  a.output.write_text(json.dumps(out,indent=2)+'\n');a.output.with_suffix('.log').write_text('\n'.join(logs)+'\n')
  render(a.output,Path.home()/'progress-dashboard/site/lru-optimization.html')
 save()
 rows=[r for r in TABLE if r['structure']=='lru' and r['workload']=='medium' and r['operation'] in ['lru.add','lru.get','lru.peek','lru.set_lifetime','lru.expiry']]
 for row in rows:
  for n in candidates:
   try:
    r=b.measure(root/n,root/'c',row,logs);r['ratio']=statistics.median(r['bend_ns'])/statistics.median(r['reference_ns'])
   except (Exception,SystemExit) as e:r={'measurement':'failed','operation':row['operation'],'workload':row['workload'],'reason':str(e)}
   r['candidate']=n;out['benchmarks'].append(r);save()
   print(n,row['operation'],round(r['ratio'],3) if 'ratio' in r else r['reason'],flush=True)
 out['status']='finished';save()
if __name__=='__main__':main()

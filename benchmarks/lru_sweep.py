#!/usr/bin/env python3
"""All 51 LRU rows using canonical sampling, with explicit per-row timeouts.
Timeouts are failures, never passes. The reference/workloads are unchanged
apart from the corrected isolated-removal cap documented in LRU_OPTIMIZATION.
"""
import argparse,json,statistics,signal,sys,time
from pathlib import Path
import run as b
from workloads import TABLE
sys.path.insert(0,str(b.ROOT/'tools'))
from render_lru_optimization import render

def timeout(signum,frame):raise TimeoutError('per-row wall-time budget exhausted; measurement failed')
def main():
 p=argparse.ArgumentParser();p.add_argument('--report',type=Path,default=Path('build/lru-opt/final.json'));p.add_argument('--row-seconds',type=int,default=30);a=p.parse_args()
 a.report.parent.mkdir(parents=True,exist_ok=True)
 if a.row_seconds<=0:p.error('--row-seconds must be positive')
 built=b.build_all(['lru']);start=time.time();initial=b.source_hashes();log=[]
 out={'status':'running','expected_rows':51,'max_ratio':b.CONTRACT['max_ratio'],'row_wall_time_budget_s':a.row_seconds,'environment':b.environment(),'source_sha256':initial,'benchmarks':[]}
 def save():
  out['seconds']=time.time()-start;a.report.write_text(json.dumps(out,indent=1)+'\n');a.report.with_suffix('.log').write_text('\n'.join(log)+'\n');render('build/lru-opt/native-candidates.json',Path.home()/'progress-dashboard/site/lru-optimization.html',a.report)
 signal.signal(signal.SIGALRM,timeout);save()
 for w in [r for r in TABLE if r['structure']=='lru']:
  signal.alarm(a.row_seconds)
  try:
   r=b.measure(*built['lru'],w,log);r['ratio']=statistics.median(r['bend_ns'])/statistics.median(r['reference_ns']);r['passes_speed']=r['verified'] and r['ratio']<=out['max_ratio']
  except (Exception,SystemExit) as e:r={'operation':w['operation'],'workload':w['workload'],'size':w['size'],'measurement':'failed','verified':False,'reason':str(e)}
  finally:signal.alarm(0)
  out['benchmarks'].append(r);save();print(len(out['benchmarks']),r['operation'],r['workload'],r.get('ratio',r.get('reason')),flush=True)
 out['status']='finished';out['source_unchanged']=initial==b.source_hashes();out['artifacts']={str(p.relative_to(b.ROOT)):b.sha(p) for p in built['lru']};save()
if __name__=='__main__':main()

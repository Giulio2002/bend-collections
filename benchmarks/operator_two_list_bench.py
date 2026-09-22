"""Two-list implementations: unchanged calibrated C/Bend workloads."""
import json,statistics,time
from pathlib import Path
import run as bench
from workloads import TABLE
root=Path(__file__).resolve().parents[1]
output=root/'benchmarks/evidence/operator-two-list-20260922'
output.mkdir(parents=True,exist_ok=True)
built=bench.build_all(['deque','queue'])
rows=[dict(r,seed=1000+i) for i,r in enumerate(TABLE) if r['structure'] in built]
result={'note':'C and Bend two-list queue and deque. FIFO full reversal and deque half split; no DLL dependency. Original workloads, calibration, six samples, thresholds and checksums retained. Formal migration status is tracked separately.','environment':bench.environment(),'source_sha256':bench.source_hashes(),'rows':[]}
for row in rows:
 log=[]
 try:
  v=bench.measure(*built[row['structure']],row,log)
  if not v['verified']:raise RuntimeError('checksum mismatch')
  v['ratio']=statistics.median(v['bend_ns'])/statistics.median(v['reference_ns'])
  print(row['operation'],row['workload'],round(v['ratio'],3),flush=True)
 except (bench.Unmeasurable,SystemExit) as exc:
  v={'operation':row['operation'],'workload':row['workload'],'measurement':'failed','reason':str(exc)}
  print(v,flush=True)
 result['rows'].append(v)
 (output/'report.json').write_text(json.dumps(result,indent=2)+'\n')
 with (output/'samples.log').open('a') as f:f.write('\n'.join(log)+'\n')

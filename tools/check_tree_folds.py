#!/usr/bin/env python3
"""Exact ordered fold outputs, boundary combinations and unchanged-map checks."""
import json,random,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
binary=ROOT/'build/tree-fold/test'
cases=0
for kind,key in [('ascending',lambda k:k),('reverse',lambda k:-k),('groups',lambda k:k//10)]:
 for seed in range(8):
  rng=random.Random(seed);model={};setup=[]
  for k in rng.sample(range(100),60):
   kk=key(k);model[kk]=(model.get(kk,(k,0))[0],k+100);setup.append(f'0:{k}:{k+100}')
  for k in rng.sample(range(100),30):model.pop(key(k),None);setup.append(f'2:{k}:0')
  args=setup+['99'];expected=[]
  for _ in range(40):
   lo,hi=rng.randrange(110),rng.randrange(110)
   if rng.randrange(4)==0:hi=lo
   if key(lo)>key(hi):lo,hi=hi,lo
   for variant in range(8):
    entries=[v for kk,v in sorted(model.items(),reverse=bool(variant&4)) if (kk>=key(lo) if variant&1 else kk>key(lo)) and (kk<=key(hi) if variant&2 else kk<key(hi))]
    expected.append('entries'+''.join(f';{k}={v}' for k,v in entries));args += [f'{51+variant}:{lo}:{hi}','99']
  r=subprocess.run([str(binary),kind]+args,text=True,capture_output=True,check=True,timeout=60)
  lines=r.stdout.splitlines()[1+len(setup):];original=lines.pop(0)
  assert len(lines)==2*len(expected)
  for i,want in enumerate(expected):
   assert lines[2*i]==want,(kind,seed,i,want,lines[2*i])
   assert lines[2*i+1]==original,('fold changed map',kind,seed,i)
  cases+=len(expected)
report={'passed':True,'bounded_fold_cases':cases,'checks':['exact ordered output vs independent Python map','inclusive/exclusive/equal bounds','ascending/descending views','reverse/equivalence-class comparators','complete arena unchanged after every fold']}
(ROOT/'build/tree-fold/boundaries.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

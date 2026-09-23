#!/usr/bin/env python3
"""Independent randomized oracle for arrays of owning nested arrays."""
import json, random, subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def oracle(limit,ops):
    cap=1; xs=[]; out=[]
    for op in ops:
        p=op.split(':'); name=p[0]
        if name=='push':
            v=int(p[1])
            if len(xs)==2**limit: out.append(f'ERR CapacityExceeded RETURN {v}')
            else:
                if len(xs)==cap: cap*=2
                xs.append(v); out.append('OK')
        elif name=='pop': out.append(f'OK {xs.pop()}' if xs else 'ERR EmptyArray')
        elif name=='get':
            i=int(p[1]); out.append(f'OK {xs[i]}' if i<len(xs) else 'ERR IndexOutOfRange')
        elif name=='set':
            i,v=map(int,p[1:])
            if i<len(xs):out.append(f'OLD {xs[i]}');xs[i]=v
            else:out.append(f'ERR IndexOutOfRange RETURN {v}')
        elif name=='reserve':
            n=int(p[1])
            if n>2**limit:out.append('ERR CapacityExceeded')
            else:
                while cap<n:cap*=2
                out.append('OK')
        elif name=='clear':xs=[];out.append('OK')
        elif name=='len':out.append(f'N {len(xs)}')
        elif name=='cap':out.append(f'N {cap}')
        else:out.append('LIST '+','.join(map(str,xs)))
    return out+['DRAIN '+','.join(map(str,xs))]

cases=[]
for limit in range(9):
    cases.append((limit,['pop','get:0','set:0:99']+[f'push:{i}' for i in range(2**limit+2)]+['to_list',f'reserve:{2**limit+1}','cap']+['pop']*(2**limit+1)+['to_list']))
    cases.append((limit,[f'reserve:{2**limit}']+[f'push:{i}' for i in range(2**limit)]+['clear','len','cap','push:4294967295','get:0']))
for seed in range(100):
    rng=random.Random(seed);limit=rng.randrange(9);ops=[]
    for _ in range(250):
        op=rng.choice(['push','push','push','pop','get','set','reserve','clear','len','cap','to_list'])
        if op=='push':op+=f':{rng.randrange(2**32)}'
        elif op=='get':op+=f':{rng.randrange(2**limit+2)}'
        elif op=='set':op+=f':{rng.randrange(2**limit+2)}:{rng.randrange(2**32)}'
        elif op=='reserve':op+=f':{rng.randrange(2**limit+2)}'
        ops.append(op)
    cases.append((limit,ops))
for i,(limit,ops) in enumerate(cases):
    r=subprocess.run([str(ROOT/'build/indexed-tree/owned-test'),str(limit),*ops],capture_output=True,text=True,timeout=30,check=True)
    assert r.stdout.splitlines()==oracle(limit,ops),(i,r.stdout,oracle(limit,ops))
report={'passed':True,'histories':len(cases),'observations':sum(len(x)+1 for _,x in cases),'payload':'non-copyable Box containing DynArray<U32>','checks':['growth','reserve','swap returns old value','failed writes return input','scoped reads restore element','pop','clear retains capacity','ordered consuming drain']}
(ROOT/'build/indexed-tree/owned-tests.json').write_text(json.dumps(report,indent=2)+'\n')
print(report)

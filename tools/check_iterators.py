#!/usr/bin/env python3
"""Bend and C iterators compared with an independent Python sequence oracle."""
import argparse,json,random,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def oracle(tokens):
 a=[];i=0;last=None;out=[]
 for t in tokens:
  if t in ['first','last']:i=0 if t=='first' else len(a);last=None;out.append('OK')
  elif t=='next':
   if i==len(a):out.append('ERR end')
   else:last=i;i+=1;out.append('V '+str(a[last]))
  elif t=='prev':
   if i==0:out.append('ERR end')
   else:i-=1;last=i;out.append('V '+str(a[last]))
  elif t.startswith('add:'):a.insert(i,int(t[4:]));i+=1;last=None;out.append('OK')
  elif t.startswith('set:'):
   if last is None:out.append('ERR state')
   else:a[last]=int(t[4:]);out.append('OK')
  elif t=='remove':
   if last is None:out.append('ERR state')
   else:a.pop(last);i-=last<i;last=None;out.append('OK')
  elif t=='hn':out.append('B '+str(int(i<len(a))))
  elif t=='hp':out.append('B '+str(int(i>0)))
  elif t=='pos':out.append('N '+str(i))
  else:out.append('LIST '+','.join(map(str,a)))
 return out

def main():
 p=argparse.ArgumentParser();p.add_argument('--c',default='build/test-iterator-c');args=p.parse_args()
 programs=[['build/test-iterator'],[args.c]]
 cases=[['next','prev','set:1','remove','hn','hp','pos','list'],['add:1','add:2','first','next','prev','remove','remove','set:4','list','add:5','remove','prev','set:6','list','last','prev','remove','prev','remove','next','list']]
 for seed in range(100):
  rng=random.Random(seed);tokens=[]
  for _ in range(300):
   op=rng.choice(['next','next','prev','prev','add','add','remove','set','first','last','hn','hp','pos','list']);tokens.append(op+':'+str(rng.randrange(2**32)) if op in ['add','set'] else op)
  cases.append(tokens+['first']+['next']*10+['last']+['prev']*10+['list','pos'])
 for j,ops in enumerate(cases):
  expected=oracle(ops)
  for command in programs:
   r=subprocess.run(command+ops,cwd=ROOT,capture_output=True,text=True,timeout=30,check=True)
   assert r.stdout.splitlines()==expected,(command,j,r.stdout,expected)
 report={'histories':len(cases),'operations':sum(map(len,cases)),'programs':programs,'passed':True};(ROOT/'build/iterator-tests.json').write_text(json.dumps(report,indent=2)+'\n');print(report)
if __name__=='__main__':main()

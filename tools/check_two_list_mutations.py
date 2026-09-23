#!/usr/bin/env python3
import json,shutil,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'tools'),str(ROOT/'tests/support')]
from mutants import MUTANTS
import scenarios,oracles
import sys; sys.path.insert(0, str(Path(__file__).resolve().parent))
from toolchain import BEND, ENV
report=[]
with tempfile.TemporaryDirectory(prefix='bend-two-list-mutants-') as directory:
 root=Path(directory)
 for folder in ['src','tests']:
  shutil.copytree(ROOT/folder,root/folder)
 for name in ['deque','queue']:
  cases=scenarios.FUNCTIONAL[name]+scenarios.BOUNDARY[name]+[scenarios.differential(name,11)]
  for label,filename,old,new in MUTANTS[name]:
   p=root/filename;original=p.read_text();assert original.count(old)==1
   p.write_text(original.replace(old,new));binary=root/'mutant'
   try:
    build=subprocess.run([BEND,str(root/'tests'/name/'main.bend'),'-o',str(binary)],capture_output=True,text=True,timeout=60, env=ENV)
    assert build.returncode==0 and 'Error:' not in build.stdout+build.stderr,(label,build.stderr)
    detected=False
    for args in cases:
     run=subprocess.run([str(binary),*args],capture_output=True,text=True,timeout=15,check=True)
     if run.stdout.splitlines()!=getattr(oracles,name)(args):detected=True;break
    assert detected,label
    report.append({'structure':name,'mutation':label,'detected':True})
   finally:p.write_text(original)
(ROOT/'build/two-list-mutations.json').write_text(json.dumps(report,indent=2)+'\n')
print(len(report),'compiled semantic mutants detected')

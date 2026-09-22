#!/usr/bin/env python3
"""Require the optimization laws to reject concrete semantic faults."""
import shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
BEND=str(Path.home()/'.bend/bin/bend')
CASES=[('lifetime','src/lru/fast.bend','Bool.not(stamp_zero(ns))','stamp_zero(ns)','proofs/lru_fast/packed_zero.bend'),('expiry','src/lru/fast.bend','stamp_expired_choose(deadline,now,stamp_zero(deadline))','False{}','proofs/lru_fast/packed_order.bend'),('touch','src/lru/fast.bend','promote(c, s)','c','proofs/lru_fast/promote.bend')]
def main():
 out=ROOT/'build/lru-opt/mutations';out.mkdir(parents=True,exist_ok=True)
 with tempfile.TemporaryDirectory(prefix='lru-laws-') as td:
  root=Path(td)
  for folder in ['src','types','proofs','reference','spec']:shutil.copytree(ROOT/folder,root/folder)
  for name,file,old,new,gate in CASES:
   f=root/file;s=f.read_text()
   if old not in s:raise SystemExit('Mutation anchor missing: '+name)
   f.write_text(s.replace(old,new,1))
   try:r=subprocess.run([BEND,gate],cwd=root,text=True,capture_output=True,timeout=60)
   finally:f.write_text(s)
   text=r.stdout+r.stderr;(out/(name+'.log')).write_text(text)
   if 'Error:' not in text or 'All terms check' in text:raise SystemExit('Mutation not rejected: '+name+'\n'+text)
   print(name+': rejected',flush=True)
if __name__=='__main__':main()

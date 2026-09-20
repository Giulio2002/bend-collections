"""Frozen minimum mechanical gate; independent semantic audit is mandatory."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys
ROOT=Path(__file__).resolve().parents[1]
def require(ok,message):
 if not ok:raise RuntimeError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 lock=json.loads((ROOT/'inventory/toolchain.json').read_text())
 for key in ['binary','base']:require(sha(Path(lock[key]))==lock[key+'_sha256'],'Pinned toolchain changed: '+key)
 for name,digest in json.loads((ROOT/'inventory/reference-sha256.json').read_text()).items():
  require(sha(ROOT/name)==digest,'Retained LRU changed: '+name)
 inventory=json.loads((ROOT/'inventory/structures.json').read_text())['new_structures']
 for item in inventory:
  for directory in ['src','spec','proofs']:require((ROOT/directory/(item['id']+'.bend')).is_file(),'INCOMPLETE: '+directory+'/'+item['id']+'.bend')
 for name in ['PROOF.bend','END_TO_END.bend','src/lru.bend','proofs/lru.bend','tools/validate.py']:
  require((ROOT/name).is_file(),'INCOMPLETE: '+name)
 # Every required proof module must be in the actual checked import closure.
 seen=set()
 def visit(path):
  path=path.resolve();require(path.is_relative_to(ROOT),'Import escapes project: '+str(path))
  if path in seen:return
  seen.add(path);code='\n'.join(x.split('#',1)[0] for x in path.read_text().splitlines())
  require(not re.search(r'@unsafe|\?[A-Za-z_]|import\s+"',code),'Unsafe/hole/foreign import: '+str(path))
  for target in re.findall(r'^import\s+(\S+)',code,re.M):
   if target!='Base':visit(path.parent/target)
 visit(ROOT/'PROOF.bend')
 for name in ['END_TO_END.bend','proofs/lru.bend']+['proofs/'+x['id']+'.bend' for x in inventory]:
  require((ROOT/name).resolve() in seen,'Unreachable proof: '+name)
 for path in (ROOT/'spec').rglob('*.bend'):
  for target in re.findall(r'^import\s+(\S+)',path.read_text(),re.M):
   if target=='Base':continue
   resolved=(path.parent/target).resolve()
   require(any(resolved.is_relative_to(ROOT/d) for d in ['spec','types']),'Specification imports runtime/proofs: '+str(path))
 env={**os.environ,'BEND_NO_TELEMETRY':'1'}
 for name in ['PROOF.bend','END_TO_END.bend']:
  p=subprocess.run([lock['binary'],name],cwd=ROOT,env=env,text=True,capture_output=True,timeout=14400)
  print(p.stdout,flush=True);require(p.returncode==0 and 'All terms check' in p.stdout,'Checker failed: '+name+'\n'+p.stderr)
 report=ROOT/'build/validation.json';report.parent.mkdir(exist_ok=True);report.unlink(missing_ok=True)
 subprocess.run([sys.executable,'tools/validate.py','--report',str(report)],cwd=ROOT,env=env,check=True,timeout=14400)
 data=json.loads(report.read_text());rows=data.get('structures',[])
 require(len(rows)==len(inventory) and {x['id'] for x in rows}=={x['id'] for x in inventory},'Wrong/duplicate structure coverage')
 for item in inventory:
  row=next(x for x in rows if x['id']==item['id'])
  require(set(row.get('operations_passed',[]))==set(item['operations']),'Missing operation tests: '+item['id'])
  for key in ['runtime','boundaries','differential','mutations','trace_proof']:
   require(row.get(key)=='passed','Incomplete '+key+': '+item['id'])
 require(data.get('lru_reuse')=='passed','LRU compatibility/reuse not validated')
 require(data.get('complete') is True,'Incomplete report')
 print('Mechanical gates passed; independent full semantic audit still required.')
if __name__=='__main__':
 try:main()
 except Exception as e:print(str(e),file=sys.stderr);sys.exit(1)

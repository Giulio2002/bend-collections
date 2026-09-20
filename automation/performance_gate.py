"""Frozen numeric gate. Harness fairness/coverage require independent semantic audit.
Report: {backend:'native-c',reference:str,environment:{cpu,os,bend_compiler,
reference_compiler,bend_flags,reference_flags,reference_revision},
source_sha256:{relative_path:sha256},artifacts:{relative_path:sha256},
benchmarks:[{operation,workload,size,verified:true,bend_ns:[...],reference_ns:[...],
operations_per_sample:positive_int}]}. Timings are ns/operation, at least 5 samples.
All required operations must occur; ALL reported workloads must satisfy limit.
"""
from pathlib import Path
import hashlib,json,math,statistics,subprocess,sys
ROOT=Path.cwd().resolve()
C=json.loads((Path(__file__).parent/'performance_contract.json').read_text())
def require(x,message):
    if not x: raise SystemExit('PERFORMANCE GATE: '+message)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def within(name):
    p=(ROOT/name).resolve();require(p.is_relative_to(ROOT) and p.is_file(),'bad evidence path '+name);return p

def validate(r):
    require(r.get('backend')=='native-c','only native Bend C results qualify')
    require(r.get('reference')==C['reference'],'wrong reference')
    env=r.get('environment',{})
    for k in ['cpu','os','bend_compiler','reference_compiler','bend_flags','reference_flags','reference_revision']:
        require(bool(env.get(k)),'missing environment '+k)
    hashes=r.get('source_sha256',{})
    require(bool(hashes),'missing current source hashes')
    sources=[]
    for folder in ['src','types','proofs','spec','benchmarks','native_bench']:
        p=ROOT/folder
        if p.exists():sources.extend(f for f in p.rglob('*') if f.is_file() and f.suffix in ['.bend','.c','.h','.py','.go','.json','.mod','.sum','.sh'])
    sources.extend(ROOT.glob('*.bend'))
    for p in sources:
        require(hashes.get(str(p.relative_to(ROOT)))==digest(p),'missing/stale source '+str(p.relative_to(ROOT)))
    artifacts=r.get('artifacts',{});require(len(artifacts)>=3,'need raw logs and native executable artifacts')
    for name,h in artifacts.items():require(digest(within(name))==h,'stale artifact '+name)
    rows=r.get('benchmarks',[]);require(bool(rows),'no benchmarks')
    covered=set();seen=set()
    for row in rows:
        op=row.get('operation');require(isinstance(op,str) and op,'missing operation')
        workload=row.get('workload');require(isinstance(workload,str) and workload,'missing workload')
        key=(op,workload);require(key not in seen,'duplicate workload');seen.add(key);covered.add(op)
        require('size' in row and row.get('verified') is True,'missing correctness/size '+str(key))
        n=row.get('operations_per_sample');require(type(n) is int and n>0,'missing batch count')
        a=row.get('bend_ns',[]);b=row.get('reference_ns',[])
        require(len(a)==len(b) and len(a)>=C['minimum_samples'],'too few/unequal samples '+str(key))
        require(all(type(v) in [int,float] and math.isfinite(v) and v>0 for v in a+b),'invalid timings')
        ratio=statistics.median(a)/statistics.median(b)
        require(ratio<=C['max_ratio'],f'{key}: {ratio:.4f}x exceeds {C["max_ratio"]}x')
    require(set(C['required_operations'])<=covered,'missing operations: '+str(sorted(set(C['required_operations'])-covered)))
    print(f'PERFORMANCE GATE: {len(rows)} workloads / {len(covered)} operations within {C["max_ratio"]}x; semantic audit still mandatory')

if __name__=='__main__':
    runner=ROOT/C['runner'];require(runner.is_file(),'native benchmark runner not implemented')
    report=ROOT/C['report'];report.parent.mkdir(parents=True,exist_ok=True);report.unlink(missing_ok=True)
    subprocess.run([sys.executable,str(runner),'--report',str(report)],check=True,cwd=ROOT)
    require(report.is_file(),'runner produced no report');validate(json.loads(report.read_text()))

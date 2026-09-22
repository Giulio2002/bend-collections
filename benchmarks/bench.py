#!/usr/bin/env python3
"""Build once, then obtain a bounded, explicitly provisional quick rundown.
Quick mode samples the smallest workload for each operation, not every size.
Full release measurements remain available through full_sweep.py/run.py.
"""
import argparse,json,math,statistics,subprocess,time
from pathlib import Path
import run as bench
from workloads import TABLE
ROOT=bench.ROOT
MANIFEST=ROOT/'build/bench/build-manifest.json'

def fingerprints():
    paths=[]
    for directory in ['src','types','benchmarks/bend','benchmarks/native']:
        paths += [p for p in (ROOT/directory).rglob('*') if p.suffix in ['.bend','.c','.h']]
    return {str(p.relative_to(ROOT)):bench.sha(p) for p in sorted(paths)}

def build():
    started=time.monotonic();built=bench.build_all(sorted({r['structure'] for r in TABLE}))
    record={'source_sha256':fingerprints(),'compiler_sha256':bench.sha(bench.BEND),'binaries':{name:{'bend':bench.sha(b),'c':bench.sha(c)} for name,(b,c) in built.items()}}
    MANIFEST.write_text(json.dumps(record,indent=2)+'\n')
    print(f'Build complete in {time.monotonic()-started:.2f}s. Subsequent --quick runs reuse these binaries.',flush=True)

def verify_build():
    if not MANIFEST.exists():raise SystemExit('Missing build manifest. Run python3 benchmarks/bench.py --build first.')
    m=json.loads(MANIFEST.read_text())
    if m['source_sha256']!=fingerprints() or m['compiler_sha256']!=bench.sha(bench.BEND):raise SystemExit('Sources/compiler changed. Run --build before benchmarking.')
    for name,hashes in m['binaries'].items():
        for kind,path in [('bend',bench.BENDBIN/name),('c',bench.REFBIN/name)]:
            if not path.exists() or bench.sha(path)!=hashes[kind]:raise SystemExit('Missing/stale binary: '+str(path))

def execute(path,row,count,reps,is_bend,deadline):
    remaining=deadline-time.monotonic()
    if remaining<=0:raise TimeoutError('time budget exhausted')
    args=[str(path)]+(['--threads','1','--'] if is_bend else [])+list(map(str,[row['op'],row['size'],count,reps,row['seed'],0]))
    p=subprocess.run(args,capture_output=True,text=True,env=bench.ENV,timeout=remaining)
    if p.returncode:raise RuntimeError(p.stderr[-300:])
    match=bench.TIME_RE.search(p.stdout)
    if not match:raise RuntimeError('missing timing output')
    times=[int(x)*(1000000 if is_bend else 1) for x in match.groups()]
    checks=[s.strip() for s in p.stderr.splitlines() if s.strip().isdigit()]
    return times[0]-times[1],checks,{'stdout':p.stdout,'stderr':p.stderr,'elapsed_ns':times}

def quick(seconds,out):
    # Reserve final-report time within the requested wall-clock budget.
    started=time.monotonic();deadline=started+seconds-0.25
    verify_build()
    chosen={}
    for r in TABLE:
        if r['operation'] not in chosen or r['size']<chosen[r['operation']]['size']:chosen[r['operation']]=dict(r)
    rows=list(chosen.values());results=[];raw=[]
    for i,row in enumerate(rows):
        left=deadline-time.monotonic()
        result={k:row[k] for k in ['operation','workload','size','seed','method']}
        if left<=.025:
            result.update(status='NOT_MEASURED',reason='global 60-second budget exhausted');results.append(result);continue
        # Fair per-operation allowance prevents one slow row consuming the sweep.
        row_deadline=min(deadline,time.monotonic()+max(.05,left/(len(rows)-i)))
        count=min(row['count'],1000);reps=1
        if row['grow']=='count':count=min(row['count'],100000)
        else:count=min(count,max(1,row['cap']))
        try:
            for attempt in range(4):
                bd,bc,blog=execute(bench.BENDBIN/row['structure'],row,count,reps,True,row_deadline)
                cd,cc,clog=execute(bench.REFBIN/row['structure'],row,count,reps,False,row_deadline)
                raw.append({'operation':row['operation'],'attempt':attempt,'count':count,'reps':reps,'bend':blog,'c':clog})
                if not bc or bc!=cc:raise RuntimeError('checksum mismatch')
                result.update(verified=True,count=count,reps=reps,bend_delta_ns=bd,c_delta_ns=cd)
                # At least 3 Bend clock ticks; still a rough screen, not acceptance.
                if bd>=3000000 and cd>=10000:
                    b=bd/(count*reps);c=cd/(count*reps)
                    result.update(status='ESTIMATE',bend_ns=b,c_ns=c,ratio=b/c,above_target=b/c>2.5)
                    break
                if attempt<3:
                    factor=min(64,max(2,math.ceil(6000000/max(bd,100000))))
                    if row['grow']=='count':count*=factor
                    else:reps*=factor
                else:result.update(status='LOW_RESOLUTION',reason='batch difference below quick timing minimum; no ratio reported')
        except (subprocess.TimeoutExpired,TimeoutError):result.update(status='TIMEOUT',reason='per-operation quick budget exhausted')
        except Exception as exc:result.update(status='FAILED',reason=str(exc))
        results.append(result)
        ratio=f" {result['ratio']:.2f}x" if 'ratio' in result else ''
        print(f"[{i+1}/{len(rows)}] {row['operation']}: {result['status']}{ratio}",flush=True)
    report={'mode':'quick','acceptance':False,'budget_seconds':seconds,'seconds':round(time.monotonic()-started,3),'target_ratio':2.5,'scope':'Smallest nonempty workload per operation; single valid sample, at most three calibration retries','timing_note':'Bend clock has 1ms resolution; >=3ms batch differences are rough estimates. No full-suite acceptance is claimed.','expected_operations':len(rows),'results':results,'raw_samples':raw,'source_sha256':fingerprints()}
    out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(report,indent=2)+'\n')
    print(f"Quick report: {out} ({report['seconds']:.2f}s)",flush=True)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--build',action='store_true');ap.add_argument('--quick',action='store_true');ap.add_argument('--seconds',type=float,default=60);ap.add_argument('--report',type=Path,default=ROOT/'build/quick-bench/report.json');args=ap.parse_args()
    if not args.build and not args.quick:ap.error('choose --build and/or --quick')
    if args.seconds<1:ap.error('--seconds must be >=1')
    if args.build:build()
    if args.quick:quick(args.seconds,args.report)
if __name__=='__main__':main()

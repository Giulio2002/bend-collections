"""Full current-scope sweep, retaining build/runtime/measurement failures.
Uses the canonical calibration, six samples, C flags and checksum checks.
No concurrent timing workloads. Progress/evidence are saved after each row.
"""
import argparse, concurrent.futures, json, statistics, subprocess, threading, time, sys
from pathlib import Path
import run as bench
from workloads import TABLE, EXCLUDED_EMPTY_ROWS

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--report',required=True);ap.add_argument('--html')
    ap.add_argument('--jobs',type=int,default=1,help='rows measured in parallel (with --retry-failed)')
    ap.add_argument('--retry-failed',action='store_true',help='measure only the failed or missing rows of an existing --report (resumes an interrupted sweep)')
    args=ap.parse_args()
    if args.retry_failed: return retry(Path(args.report),args.jobs)
    sys.path.insert(0,str(bench.ROOT/'tools'))
    render = None
    if args.html:
        from render_full_benchmark import render
    out=Path(args.report).resolve();out.parent.mkdir(parents=True,exist_ok=True)
    started=time.time();initial_hashes=bench.source_hashes()
    report={'backend':'native-c','reference':bench.CONTRACT['reference'],
        'environment':bench.environment(),'scope':'All current nonempty collection workloads, including arena DLL and DLL iterators; TreeMap uses editable iterators, bulk folds removed',
        'max_ratio':bench.CONTRACT['max_ratio'],'expected_rows':len(TABLE),
        'excluded_empty_rows':EXCLUDED_EMPTY_ROWS,'source_sha256':initial_hashes,
        'benchmarks':[],'build_failures':{},'status':'running'}
    logs=[];built={}
    def save():
        report['seconds']=round(time.time()-started,1)
        temp=out.with_suffix('.tmp');temp.write_text(json.dumps(report,indent=1,sort_keys=True)+'\n');temp.replace(out)
        (out.parent/'samples.log').write_text('\n'.join(logs)+'\n')
        if args.html: render(report,args.html)
    save()
    for name in sorted({r['structure'] for r in TABLE}):
        try: built.update(bench.build_all([name]))
        except (SystemExit,Exception) as exc:
            report['build_failures'][name]=str(exc);print('BUILD FAILED',name,str(exc),flush=True)
        save()
    for index,row in enumerate(TABLE):
        base={'operation':row['operation'],'workload':row['workload'],'size':row['size'],'seed':row['seed']}
        if row['structure'] not in built:
            result={**base,'measurement':'build_failed','verified':False,'reason':report['build_failures'][row['structure']]}
        else:
            try:
                result=bench.measure(*built[row['structure']],row,logs)
                result['ratio']=statistics.median(result['bend_ns'])/statistics.median(result['reference_ns'])
                result['passes_speed']=result['verified'] and result['ratio']<=bench.CONTRACT['max_ratio']
            except (SystemExit,Exception) as exc:
                result={**base,'measurement':'failed','verified':False,'reason':str(exc)}
        report['benchmarks'].append(result)
        print(f"[{index+1}/{len(TABLE)}] {row['operation']} {row['workload']} " + (f"{result['ratio']:.3f}x {'PASS' if result['passes_speed'] else 'SLOW'}" if 'ratio' in result else f"FAILED {result.get('reason')}"),flush=True)
        save()
    report['status']='finished';report['source_unchanged']=all((bench.ROOT/p).is_file() and bench.sha(bench.ROOT/p)==h for p,h in initial_hashes.items())
    report['artifacts']={str(p.relative_to(bench.ROOT)):bench.sha(p) for pair in built.values() for p in pair}
    save()
    print('Finished:',out,flush=True)
def retry(path,jobs=1):
    """Re-measure the rows of a finished report that failed (a disturbed
    sample or calibration), replacing them in place; rows no longer in TABLE
    are dropped."""
    report=json.loads(path.read_text())
    rows={(r['operation'],r['workload']):r for r in TABLE}
    report['benchmarks']=[b for b in report['benchmarks'] if (b['operation'],b['workload']) in rows]
    have={(b['operation'],b['workload']) for b in report['benchmarks']}
    for r in TABLE:   # rows an interrupted sweep never reached
        if (r['operation'],r['workload']) not in have:
            report['benchmarks'].append({'operation':r['operation'],'workload':r['workload'],'measurement':'missing'})
    order={(r['operation'],r['workload']):n for n,r in enumerate(TABLE)}
    report['benchmarks'].sort(key=lambda b:order[(b['operation'],b['workload'])])
    todo=[i for i,b in enumerate(report['benchmarks']) if b.get('measurement')!='ok']
    print('measuring %d failed or missing rows' % len(todo),flush=True)
    built=bench.build_all(sorted({rows[(report['benchmarks'][i]['operation'],report['benchmarks'][i]['workload'])]['structure'] for i in todo}))
    logs=[];lock=threading.Lock();done=[0]
    def one(i):
        b=report['benchmarks'][i];row=rows[(b['operation'],b['workload'])]
        try:
            result=bench.measure(*built[row['structure']],row,logs)
            result['ratio']=statistics.median(result['bend_ns'])/statistics.median(result['reference_ns'])
            result['passes_speed']=result['verified'] and result['ratio']<=bench.CONTRACT['max_ratio']
        except (SystemExit,Exception) as exc:
            result={'operation':row['operation'],'workload':row['workload'],'size':row['size'],'seed':row['seed'],
                    'measurement':'failed','verified':False,'reason':str(exc)}
        with lock:
            report['benchmarks'][i]=result;done[0]+=1
            print(f"[retry {done[0]}/{len(todo)}] {row['operation']} {row['workload']} " + (f"{result['ratio']:.3f}x" if 'ratio' in result else f"FAILED {result.get('reason')}"),flush=True)
            path.write_text(json.dumps(report,indent=1,sort_keys=True)+'\n')
            (path.parent/'retry_samples.log').write_text('\n'.join(logs)+'\n')
    with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
        list(ex.map(one,todo))
    report['status']='finished';path.write_text(json.dumps(report,indent=1,sort_keys=True)+'\n')

if __name__=='__main__':main()

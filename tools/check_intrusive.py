#!/usr/bin/env python3
"""Reproduce the intrusive-list contribution gate with the chosen Bend binary."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
BUILD=ROOT/'build/intrusive-list'

def run(command, timeout=180):
    r=subprocess.run(command,cwd=ROOT,capture_output=True,text=True,timeout=timeout,
                     env={**os.environ,'BEND_NO_TELEMETRY':'1'})
    if r.returncode:
        raise RuntimeError(f'{command[0]} failed:\n{r.stdout[-4000:]}\n{r.stderr[-4000:]}')
    return r

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--bend',default=os.environ.get('BEND','bend'))
    p.add_argument('--cc',default='clang')
    a=p.parse_args()
    bend=shutil.which(a.bend) or str(Path(a.bend).resolve())
    cc=shutil.which(a.cc) or str(Path(a.cc).resolve())
    BUILD.mkdir(parents=True,exist_ok=True)
    run([sys.executable,'tools/generators/intrusive_list.py','--check'])
    checked=[]
    for f in ['main.bend', 'src/containers/intrusive_doubly_linked_list.bend',
              'src/containers/compat/intrusive_doubly_linked_list.bend',
              'proofs/containers/intrusive_doubly_linked_list/proof.bend',
              'tests/intrusive_doubly_linked_list/main.bend',
              'tests/intrusive_doubly_linked_list/example.bend',
              'tests/intrusive_doubly_linked_list/pooled_pulses.bend',
              'tests/intrusive_doubly_linked_list/scheduler.bend',
              'tests/intrusive_doubly_linked_list/affine.bend']:
        r=run([bend,f,'--check-only'])
        if (r.stdout+r.stderr).strip()!='All terms check.':
            raise RuntimeError(f'{f}: checker was not clean:\n{r.stdout}\n{r.stderr}')
        checked.append(f)
    prefix='tests/intrusive_doubly_linked_list/'
    examples = {'example': 'Group 0: 1 3 \nGroup 1: 2', 'affine': '6',
                'scheduler': 'Ready: 2 3 \nWaiting: 1 \nRender: 1 2 3 \nPayload sum: 600',
                'pooled_pulses': '3 pulses, 12 uses\nNodes created: 4 (all during prewarm)\nNodes available: 4\nPayload sum: 2430'}
    for source,name in [('main.bend','test'),('example.bend','example'),('affine.bend','affine'),
                        ('pooled_pulses.bend','pooled_pulses'),('scheduler.bend','scheduler')]:
        run([bend,prefix+source,'-o',str(BUILD/(name+'.c'))])
        run([cc,'-O3','-std=gnu11','-pthread',str(BUILD/(name+'.c')),'-lm','-o',str(BUILD/name)])
        run([bend,prefix+source,'-o',str(BUILD/(name+'.js'))])
        if name!='test':
            expected=examples[name]
            for cmd in [[str(BUILD/name)],['node',str(BUILD/(name+'.js'))]]:
                r=run(cmd)
                assert r.stdout.strip()==expected,(name,r.stdout)
    reports={}
    for script in ['check_intrusive_proofs.py','check_intrusive_list.py','check_intrusive_mutations.py','check_intrusive_allocations.py']:
        command=[sys.executable,'tools/'+script]
        if script!='check_intrusive_list.py':command+=['--bend',bend]
        if script=='check_intrusive_allocations.py':command+=['--cc',cc]
        r=run(command,300)
        reports[script]=json.loads(r.stdout)
        print(script+': '+r.stdout.strip(),flush=True)
    r=run([sys.executable, 'benchmarks/intrusive.py', '--bend', bend, '--cc', cc,
           '--check-only', '--report', str(BUILD/'workloads.json')], 300)
    reports['intrusive_workloads']=json.loads((BUILD/'workloads.json').read_text())
    print(r.stdout.strip(),flush=True)
    report={'compiler':run([bend,'version']).stdout.strip(),
            'compiler_sha256':hashlib.sha256(Path(bend).read_bytes()).hexdigest(),
            'clang':run([cc,'--version']).stdout.splitlines()[0],
            'checked':checked,'checks':reports,'passed':True}
    (BUILD/'gate.json').write_text(json.dumps(report,indent=2)+'\n')
    print('Intrusive-list gate passed.')

if __name__=='__main__':main()

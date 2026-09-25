#!/usr/bin/env python3
"""Require semantic regressions in the actual module to fail the trace oracle."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
from check_intrusive_list import Model

ROOT=Path(__file__).resolve().parents[1]
MODULE=Path('src/containers/internal/intrusive_list.bend')
MUTANTS=[
    ('head-not-updated', 'set_next(set_head(s, i, after), node, None{})', 'set_next(s, node, None{})'),
    ('successor-not-repaired', 'case Some{a}: set_prev(s, a, node)', 'case Some{a}: s'),
    ('prepend-not-published', '  set_head_nonempty(s, i, node)\n', '  s\n'),
    ('visit-twice', '(fn(s, c, v), Unit{})', '(fn(fn(s, c, v), c, v), Unit{})'),
    ('clear-head-too-early', 'next(set_head(s, i, None{}), node)', 'next(post_remove(set_head(s, i, None{}), c, node), node)'),
    ('pool-link-retained', '(set_next(s, node, None{}), (E.Pool{after, Nat.sub(count, 1n)}, node))', '(s, (E.Pool{after, Nat.sub(count, 1n)}, node))'),
]
TOKENS=['reset','p:0:3','p:0:2','p:0:1','foreach:0:0:3','r:0:2','r:0:1','p:1:2',
        'reset','p:0:3','p:0:2','p:0:1','clear_list:0:0:3',
        'reset','pool-new:0:0:3','pool-next']

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--bend',default='bend');a=p.parse_args()
    bend=shutil.which(a.bend) or str(Path(a.bend).resolve())
    source=(ROOT/MODULE).read_text();m=Model();expected=[m.step(t) for t in TOKENS]
    results=[]
    (ROOT/'build/intrusive-list').mkdir(parents=True,exist_ok=True)
    for name,old,new in MUTANTS:
        assert source.count(old)==1,(name,source.count(old))
        with tempfile.TemporaryDirectory(prefix='mutant-',dir=ROOT/'build/intrusive-list') as d:
            stage=Path(d)
            shutil.copytree(ROOT/'src/containers',stage/'src/containers')
            shutil.copytree(ROOT/'tests/intrusive_doubly_linked_list',stage/'tests/intrusive_doubly_linked_list')
            shutil.copytree(ROOT/'tests/support',stage/'tests/support')
            (stage/MODULE).write_text(source.replace(old,new))
            js=stage/'test.js'
            r=subprocess.run([bend,str(stage/'tests/intrusive_doubly_linked_list/main.bend'),'-o',str(js)],capture_output=True,text=True,timeout=60,env={**os.environ,'BEND_NO_TELEMETRY':'1'})
            # Ill-typed mutants do not establish oracle sensitivity.
            assert r.returncode==0,(name,r.stdout,r.stderr)
            r=subprocess.run(['node',str(js)]+TOKENS,capture_output=True,text=True,timeout=30)
            assert r.returncode==0,(name,r.stderr)
            assert r.stdout.splitlines()!=expected,('survived',name)
            results.append({'mutant':name,'caught_by':'state/trace oracle'})
    (ROOT/'build/intrusive-list/mutations.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps({'mutants_caught':len(results),'passed':True}))

if __name__=='__main__':main()

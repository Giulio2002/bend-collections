#!/usr/bin/env python3
"""Ensure fusion proofs reject wrong old-binding results, in isolated copies."""
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
BEND = json.loads((ROOT/'inventory/toolchain.json').read_text())['binary']
paths = ['src/balanced_search_tree.bend', 'types/balanced_search_tree.bend',
         'proofs/lib/logic.bend', 'proofs/balanced_search_tree/insert_fused.bend',
         'proofs/balanced_search_tree/remove_fused.bend']
results=[]
with tempfile.TemporaryDirectory(prefix='tree-fusion-mutations-') as directory:
    base=Path(directory)
    for name in paths:
        target=base/name;target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(ROOT/name,target)
    source=base/'src/balanced_search_tree.bend'; original=source.read_text()
    cases=[('insert_fused','(Node{R{}, Leaf{}, E.Entry{k, v}, Leaf{}}, None{})',
            '(Node{R{}, Leaf{}, E.Entry{k, v}, Leaf{}}, Some{v})'),
           ('remove_fused','(del_here(K, V, c, l, r), Some{E.val(K, V, e)})',
            '(del_here(K, V, c, l, r), None{})')]
    for name,old,new in cases:
        source.write_text(original)
        command=[BEND,str(base/f'proofs/balanced_search_tree/{name}.bend')]
        control=subprocess.run(command,text=True,capture_output=True,timeout=30)
        assert control.returncode==0 and 'All terms check' in control.stdout+control.stderr
        assert original.count(old)==1
        source.write_text(original.replace(old,new))
        mutant=subprocess.run(command,text=True,capture_output=True,timeout=30)
        output=mutant.stdout+mutant.stderr
        assert mutant.returncode!=0 and 'expected' in output and 'observed' in output,output
        results.append({'proof':name,'control_passed':True,'mutation_rejected':True,
                        'mutation':{'before':old,'after':new},'diagnostic':output})
report={'passed':True,'results':results}
(ROOT/'build/tree-opt/mutations.json').write_text(json.dumps(report,indent=2)+'\n')
print('Both controls pass; both incorrect old-binding mutations rejected.')

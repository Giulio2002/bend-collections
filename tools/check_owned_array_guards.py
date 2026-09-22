#!/usr/bin/env python3
"""Check affine rejection and ensure public move laws reject bad code."""
from pathlib import Path
import json,shutil,subprocess,tempfile
ROOT=Path(__file__).resolve().parents[1]
BEND=json.loads((ROOT/'inventory/toolchain.json').read_text())['binary']
results=[]
with tempfile.TemporaryDirectory(prefix='owned-array-') as directory:
    root=Path(directory)
    for name in ['src/dynamic_array.bend','src/pow2.bend','types/dynamic_array.bend','proofs/dynamic_array/owned.bend','proofs/dynamic_array/owned_instances.bend']:
        p=root/name;p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/name,p)
    source=root/'src/dynamic_array.bend';original=source.read_text()
    cmd=[BEND,str(root/'proofs/dynamic_array/owned_instances.bend')]
    control=subprocess.run(cmd,capture_output=True,text=True,timeout=30)
    assert control.returncode==0,control.stderr+control.stdout
    prefix,owned=original.split('# ---- owning elements (Type) ----')
    mutation=owned.replace('1n+len, Array.set(Maybe<&1, T>, arr','len, Array.set(Maybe<&1, T>, arr',1)
    assert mutation!=owned
    source.write_text(prefix+'# ---- owning elements (Type) ----'+mutation)
    bad=subprocess.run(cmd,capture_output=True,text=True,timeout=30)
    assert bad.returncode!=0 and ('expected' in bad.stdout+bad.stderr or 'observed' in bad.stdout+bad.stderr), (bad.returncode,bad.stdout,bad.stderr)
    results.append({'name':'push fails to increment length','rejected':True,'diagnostic':bad.stdout+bad.stderr})
    source.write_text(original)
    negative=root/'negative.bend'
    negative.write_text('import Base\nimport ./src/dynamic_array.bend as A\ndef duplicate(x: A.DynArray<Array<U32>>) -> A.DynArray<Array<U32>> & A.DynArray<Array<U32>>:\n  (x, x)\n')
    bad=subprocess.run([BEND,str(negative)],capture_output=True,text=True,timeout=30)
    assert bad.returncode!=0 and 'consumed more than once' in bad.stdout+bad.stderr
    results.append({'name':'copy owning array','rejected':True,'diagnostic':bad.stdout+bad.stderr})
    negative.write_text('import Base\nimport ./src/dynamic_array.bend as A\ndef duplicate(x: Array<U32>) -> Array<U32> & Array<U32>:\n  (x, x)\n')
    bad=subprocess.run([BEND,str(negative)],capture_output=True,text=True,timeout=30)
    assert bad.returncode!=0 and 'consumed more than once' in bad.stdout+bad.stderr
    results.append({'name':'copy owning element','rejected':True,'diagnostic':bad.stdout+bad.stderr})
report={'passed':True,'results':results}
(ROOT/'build/indexed-tree/owned-guards.json').write_text(json.dumps(report,indent=2)+'\n')
print('Proof mutation and both affine duplication guards rejected.')

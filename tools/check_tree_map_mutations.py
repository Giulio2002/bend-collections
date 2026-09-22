#!/usr/bin/env python3
"""Compile realistic mutations in isolated scratch copies; never edit production."""
import json, os, shutil, subprocess, tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
BEND=os.environ.get('BEND',str(Path.home()/'.bend/bin/bend'))
source=(ROOT/'src/balanced_search_tree.bend').read_text()
mutations=[
 ('red_root','set_red(~K, ~V, ~cmp, m1, r, False{})','set_red(~K, ~V, ~cmp, m1, r, True{})',True),
 ('replace_stored_key','put_replaced(~K, ~V, ~cmp, exchange(~K, ~V, ~cmp, m, 1n+i, Some{v}))','put_replaced(~K, ~V, ~cmp, exchange(~K, ~V, ~cmp, set_key(~K, ~V, ~cmp, m, 1n+i, k), 1n+i, Some{v}))',True),
 ('skip_after_cursor_remove','(Cursor{m, id, 0n, lower, upper, forward}, removed)','(Cursor{m, 0n, 0n, lower, upper, forward}, removed)',True),
]
report=[]
for name,old,new,proof_rejects in mutations:
 assert source.count(old)==1,(name,source.count(old))
 with tempfile.TemporaryDirectory(prefix='bend-tree-map-mutation-') as td:
  tmp=Path(td)
  for folder in ['src','types','tests/support','tests/tree_map']:
   shutil.copytree(ROOT/folder,tmp/folder)
  (tmp/'tools').mkdir();shutil.copy(ROOT/'tools/check_tree_map.py',tmp/'tools/check_tree_map.py')
  shutil.copy(ROOT/'TREE_MAP_COMPONENT_PROOF.bend',tmp/'TREE_MAP_COMPONENT_PROOF.bend')
  (tmp/'build/tree-map').mkdir(parents=True)
  mutated=source.replace(old,new)
  if name=='replace_stored_key':
   mutated=mutated.replace('case Tuple{m, Search{1n+i, p, on_left}}:\n      put_replaced', 'case Tuple{m, Search{1n+ +i, p, on_left}}:\n      put_replaced')
  (tmp/'src/balanced_search_tree.bend').write_text(mutated)
  built=subprocess.run([BEND,'tests/tree_map/main.bend','-o','build/tree-map/test'],cwd=tmp,text=True,capture_output=True,timeout=60)
  assert built.returncode==0,(name,'mutation must still compile',built.stdout,built.stderr)
  tested=subprocess.run(['python3','tools/check_tree_map.py','--seeds','3','--steps','100'],cwd=tmp,text=True,capture_output=True,timeout=60)
  assert tested.returncode!=0 and 'AssertionError' in tested.stderr,(name,tested.stdout,tested.stderr)
  proof=subprocess.run([BEND,'TREE_MAP_COMPONENT_PROOF.bend'],cwd=tmp,text=True,capture_output=True,timeout=60)
  if proof_rejects:assert proof.returncode!=0 and 'Error:' in proof.stdout+proof.stderr
  report.append({'mutation':name,'compiles':True,'differential_rejected':True,'component_proof_rejected':proof.returncode!=0,'test_failure':tested.stderr[-1800:],'proof_output':(proof.stdout+proof.stderr)[-1800:]})
  print(name,'rejected by differential tests; component proof rejects:',proof.returncode!=0,flush=True)
(ROOT/'build/tree-map/mutations.json').write_text(json.dumps({'mutations':report,'note':'These targeted component checks detect the three selected mutations, but do not establish correctness of arbitrary indexed-map or iterator traces.'},indent=2)+'\n')

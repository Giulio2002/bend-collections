#!/usr/bin/env python3
"""Reorder top-level Bend defs/types so every callee precedes its callers.
Blocks = a def/type/law line plus its indented body, with the comment lines
just above it; a law and its proving def (same name) stay together. Refuses to write unless the multiset of lines is unchanged."""
import re,sys
p=sys.argv[1]; src=open(p).read(); lines=src.split('\n')
head=[];blocks=[];cur=None;pend=[]
for ln in lines:
    if re.match(r'(def|type|law|@unsafe def) ',ln):
        cur={'lines':pend+[ln]}; pend=[]; blocks.append(cur)
    elif ln.startswith((' ','\t')) and cur is not None:
        cur['lines']+=pend+[ln]; pend=[]
    elif ln.startswith('#') or ln.strip()=='':
        pend.append(ln)
    elif cur is None:
        head.append(ln)
    else:
        raise SystemExit('unexpected top-level line: '+ln)
tail=pend
def name(b): return re.match(r'(?:@unsafe )?(?:def|type|law) (\w+)',[l for l in b['lines'] if re.match(r'(def|type|law|@unsafe)',l)][0]).group(1)
for b in blocks: b['name']=name(b)
# a law and the def that proves it (same name) travel together
merged=[]
for b in blocks:
    if merged and merged[-1]['name']==b['name']:
        merged[-1]['lines']+=b['lines']
    else:
        merged.append(b)
blocks=merged
names=[b['name'] for b in blocks]
ctor={}
for b in blocks:
    if b['lines'][[i for i,l in enumerate(b['lines']) if not l.startswith('#') and l.strip()][0]].startswith('type'):
        for l in b['lines']:
            m=re.match(r'\s+(\w+)\{',l)
            if m: ctor[m.group(1)]=b['name']
byname={b['name']:b for b in blocks}
deps={}
for b in blocks:
    body='\n'.join(l for l in b['lines'] if not l.lstrip().startswith('#'))
    toks=set(re.findall(r'(?<![.\w])\w+\b',body))
    d={t for t in toks if t in byname and t!=b['name']}|{ctor[t] for t in toks if t in ctor and ctor[t]!=b['name']}
    deps[b['name']]=d
out=[];state={}
def visit(n):
    if state.get(n)==2: return
    if state.get(n)==1: return
    state[n]=1
    for d in sorted(deps[n],key=names.index): visit(d)
    state[n]=2; out.append(n)
for n in names: visit(n)
res='\n'.join(head+sum([byname[n]['lines'] for n in out],[])+tail)
assert sorted(res.split('\n'))==sorted(lines), 'line multiset changed'
open(p,'w').write(res)
print('reordered',len(out),'blocks')

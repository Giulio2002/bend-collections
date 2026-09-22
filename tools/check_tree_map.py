#!/usr/bin/env python3
"""Differential observations plus independent whole-arena RB checks.

Native Bend executes every operation. Python never constructs its result.
Diagnostic serialization is test-only and excluded from performance timings.
"""
import argparse, json, random, subprocess, time
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser();p.add_argument('--seeds',type=int,default=100);p.add_argument('--steps',type=int,default=300);p.add_argument('--binary',type=Path,default=ROOT/'build/tree-map/test');p.add_argument('--report',type=Path,default=ROOT/'build/tree-map/tests.json');a=p.parse_args()

def validate_dump(text, model, key, peak):
    h,*slots=text.split(';');n,root,first,last,free=map(int,h.split(','))
    ns={i+1:s.split(',') for i,s in enumerate(slots)}
    assert len(ns)==peak, ('free slot not reused', len(ns), peak)
    live=set(); ordered=[]
    def walk(i,parent,lo=None,hi=None):
        if i==0:return 1
        assert i in ns and i not in live, ('cycle/bad link',i)
        live.add(i);s=ns[i];assert s[0]=='N',('live Free',i)
        color,l,r,p,k,v=map(int,s[1:]);assert p==parent,('parent',i,p,parent)
        kk=key(k);assert lo is None or lo<kk;assert hi is None or kk<hi
        if color:
            for c in (l,r):assert c==0 or ns[c][1]=='0',('red-red',i,c)
        lb=walk(l,i,lo,kk);ordered.append((k,v,i));rb=walk(r,i,kk,hi)
        assert lb==rb,('black height',i,lb,rb)
        return lb+(color==0)
    if root:assert ns[root][1]=='0'
    walk(root,0)
    assert len(live)==n==len(model),('size',n,len(live),len(model))
    expected=sorted(model.values(),key=lambda x:key(x[0]))
    assert [(k,v) for k,v,i in ordered]==expected,('contents',ordered,expected)
    assert first==(ordered[0][2] if ordered else 0)
    assert last==(ordered[-1][2] if ordered else 0)
    freed=set()
    while free:
        assert free in ns and free not in freed and free not in live
        freed.add(free);s=ns[free];assert s[0]=='F' and s[2]=='-',('free payload',free,s)
        free=int(s[1])
    assert live|freed==set(ns),('lost slots',set(ns)-live-freed)

checks=0;histories=0;start=time.monotonic()
for kind,key in [('ascending',lambda k:k),('reverse',lambda k:-k),('groups',lambda k:k//10)]:
  for seed in range(a.seeds):
    rng=random.Random(seed);ops=[]
    if seed==0:
        ops += [(0,k,k+100) for k in range(150)]
        ops += [(2,k,0) for k in range(0,150,2)]
        ops += [(0,k,k+200) for k in range(150,225)]
        ops += [(2,k,0) for k in reversed(range(225))]
    elif seed==1:
        ops += [(0,k,k+100) for k in reversed(range(150))]
        ops += [(12,0,0),(13,0,0)]*80
    if seed==2:
        ops += [(0,10,7),(21,10,9),(34,10,7),(35,0,8),(33,10,7),(33,10,8),(22,10,99),(23,10,55),(0,20,5),(29,20,6),(31,20,0),(30,20,0),(44,0,0)]
    ops += [(rng.choices(list(range(32))+list(range(33,51)),weights=[30,8,25,2,0.2,3,1,1,3,3,3,3,2,2,1,1,2,2,2,2,1,5,5,2,2,2,3,0.5,1,3,3,3,2,2,2]+[1]*15)[0],rng.randrange(150),rng.randrange(10000)) for _ in range(a.steps)]
    args=[]
    for op,k,v in ops:args += [f'{op}:{k}:{v}','99']
    r=subprocess.run([str(a.binary),kind]+args,capture_output=True,text=True,timeout=60)
    assert r.returncode==0,(kind,seed,r.stderr)
    lines=r.stdout.splitlines();assert lines.pop(0)=='start';assert len(lines)==2*len(ops),(len(lines),len(ops),r.stdout[:2000])
    m={};peak=0
    for i,(op,k,v) in enumerate(ops):
      kk=key(k);old=m.get(kk);expected='-'
      if op==0:
        expected=str(old[1]) if old else '-';m[kk]=(old[0] if old else k,v)
      elif op==1:expected=str(old[1]) if old else '-'
      elif op==2:
        expected=str(old[1]) if old else '-';m.pop(kk,None)
      elif op==3:expected=str(len(m))
      elif op==4:m.clear();expected='ok'
      elif op==5:expected=str(int(kk in m))
      elif op==20:expected=str(int(not m))
      elif op>=21:
        if op>=36:
          keys=sorted(x for x in m if x<key(50));hit=None
          if op in (36,37,38,39,40):
            mode={36:'le',37:'ge',38:'lt',39:'gt',40:'ge'}[op]
            cand=[x for x in keys if {'lt':x<kk,'le':x<=kk,'ge':x>=kk,'gt':x>kk}[mode]]
            if cand:hit=cand[-1] if mode in ('lt','le') else cand[0]
          elif op==41:hit=keys[0] if keys else None
          elif op==42:hit=keys[-1] if keys else None
          elif op==43:expected=str(len(keys))
          elif op==44:
            for x in keys:del m[x]
            expected='ok'
          elif op==45:expected=str(int(bool(m)))
          elif op==46:expected=str(int(kk in keys))
          elif op in (47,48):expected='items'+''.join(';'+str(m[x][op-47]) for x in sorted(m))
          elif op in (49,50):expected='entries'+''.join(f';{m[x][0]}={m[x][1]}' for x in sorted(m,reverse=op==50))
          if hit is not None:expected=f'{m[hit][0]}={m[hit][1]}'
        elif op in (21,22,23):
          expected=str(old[1]) if old else (str(v) if op==23 else '-')
          if op==21 and not old:m[kk]=(k,v)
          if op==22 and old:m[kk]=(old[0],v)
        elif op in (24,25,26,27,28):
          keys=sorted(m,reverse=op in (25,28))
          if op==26 and kk>key(v):expected='bounds'
          else:
            if op==26:keys=[x for x in keys if kk<=x<key(v)]
            expected='entries'+''.join(f';{m[x][0]}={m[x][1]}' for x in keys)
            if op==27:m.clear()
            if op==28:
              for x in keys:m[x]=(m[x][0],m[x][1]+1)
        elif op==29:
          if kk>=key(50):expected='range'
          else:
            expected=str(old[1]) if old else '-';m[kk]=(old[0] if old else k,v)
        elif op in (33,34):
          hit=old is not None and old[1]==v;expected=str(int(hit))
          if hit:
            if op==33:del m[kk]
            else:m[kk]=(old[0],v+1)
        elif op==35:expected=str(int(any(val==v for _,val in m.values())))
        elif op in (30,31):
          expected=str(old[1]) if old and kk>=key(50) else '-'
          if op==30 and kk>=key(50):m.pop(kk,None)
      else:
        keys=sorted(m);hit=None
        if op in (6,12,14):hit=keys[0] if keys else None
        elif op in (7,13,15):hit=keys[-1] if keys else None
        else:
          mode={8:'lt',9:'le',10:'ge',11:'gt',16:'lt',17:'le',18:'ge',19:'gt'}[op]
          cand=[x for x in keys if {'lt':x<kk,'le':x<=kk,'ge':x>=kk,'gt':x>kk}[mode]]
          if cand:hit=cand[-1] if mode in ('lt','le') else cand[0]
        if hit is not None:
          ek,ev=m[hit];expected=str(ek) if op>=14 else f'{ek}={ev}'
          if op in (12,13):del m[hit]
      if op==4:peak=0
      peak=max(peak,len(m))
      try:
        assert lines[2*i]==expected,('observation',lines[2*i],expected)
        validate_dump(lines[2*i+1],m,key,peak)
      except Exception as e:
        (ROOT/'build/tree-map/failure.json').write_text(json.dumps({'kind':kind,'seed':seed,'index':i,'ops':ops[:i+1],'actual':lines[2*i:2*i+2]},indent=2))
        raise AssertionError((kind,seed,i,ops[i],e)) from e
      checks+=1
    histories+=1
# Capacity rejection must preserve entries; the freed slot must accept a new key.
r=subprocess.run([str(a.binary),'ascending','32:1','0:1:10','0:2:20','0:3:30','2:1','0:3:30','3','99'],capture_output=True,text=True,check=True,timeout=30)
lines=r.stdout.splitlines();assert lines[:-1]==['start','ok','-','-','ERROR','10','-','2'],lines
validate_dump(lines[-1],{2:(2,20),3:(3,30)},lambda k:k,2)
report={'capacity_rejection_and_reuse':True,'passed':True,'histories':histories,'operations':checks,'seconds':time.monotonic()-start,'checks':['independent map oracle','ascending/reverse/equivalence-class comparators','stored key retained on replacement','black root','parent links','no red-red edges','equal black heights','strict order','cached size/endpoints','live/free partition','cleared free payloads','reused freed slots'],'api':'updates, navigation, polling, bidirectional iteration, cursor edits/removal, bounded backed views', 'scope':'finite differential testing; not a universal proof'}
a.report.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

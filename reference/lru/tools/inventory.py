"""Read-only inventory of exact upstream assertion sites and transitive helpers."""
import json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
HELPERS={
 'TestLRU':['testCache'], 'TestLRU_RemoveOldest':['testCacheRemoveOldest'],
 'TestLRU_AddWithExpire':['testCacheAddWithExpire'], 'TestLRU_AddWithRefresh':['testCacheAddWithRefresh'],
 'TestLRUMatch':['testCacheMatch'], 'TestLRUMetrics':['testMetrics'],
 'TestLRU_Values':['testCacheValues'], 'TestLRU_GetOldest':['testCacheGetOldest']}
# Exact retained assertion expressions, in original source-site order. None
# means an individually authorized callback-only assertion, never a test pass.
PORTS={
 'makeCache':['assert.doesNotThrow'], 'setupCache':[None],
 'testCache':['eq(c.Len(),32n)',None,'ok(found&&v===k+1n&&v===BigInt(i)+33n)','ok(!c.Get(i)[1])','ok(c.Get(i)[1])','ok(!c.Remove(64n))','ok(c.Remove(63n))','ok(c.Remove(32n))',None,'eq(c.Len(),30n)'],
 'TestLRU_Add':['ok(!c.Add(1n,2n))','ok(c.Add(3n,4n))'],
 'TestLRU_Purge':['ok(!c.Add(1n,2n))','ok(!c.Add(3n,4n))','ok(!c.Add(4n,5n))','eq(c.Len(),3n)','eq(c.Len(),0n)'],
 'TestLRU_Remove':['ok(c.Remove(1n))','ok(c.Remove(3n))',None,'eq(c.Len(),0n)'],
 'testCacheRemoveOldest':['ok(found)','eq(k,1n)','eq(v,2n)','ok(found)','eq(k,3n)','eq(v,4n)','ok(!c.RemoveOldest()[2])',None,'eq(c.Len(),0n)'],
 'testCacheAddWithExpire':['ok(c.Get(1n)[1])','ok(!c.Get(1n)[1])','ok(c.Get(3n)[1])','ok(!c.Get(3n)[1])','eq(c.Len(),0n)','eq(c.Len(),0n)','eq(c.Len(),1n)','eq(c.Len(),0n)','ok(c.Get(1n)[1])','ok(!c.Get(1n)[1])'],
 'testCacheAddWithRefresh':['ok(c.Get(1n)[1])','ok(c.GetAndRefresh(1n,0n)[1])','ok(c.GetAndRefresh(2n,0n)[1])'],
 'testCacheMatch':[None,'eq(c.Len(),BigInt(backup.size))','eq(keys.length,backup.size)','ok(backup.has(k))','ok(found)','eq(v,backup.get(k))','ok(found)','eq(actual,v)'],
 'testMetrics':['eq(m.Inserts,2n)','eq(m.Hits,1n)','eq(m.Misses,1n)','eq(m.Evictions,1n)','eq(m.Removals,1n)','eq(m.Collisions,0n)'],
 'testCacheValues':['eq(c.Values().sort((a,b)=>a<b?-1:a>b?1:0),want)'],
 'testCacheGetOldest':['ok(found)','eq(k,1n)','eq(v,2n)']}

def map_sites(function, sites, case, port):
 targets=PORTS.get(function,[])
 if len(targets)!=len(sites):raise RuntimeError('unmapped upstream assertion: '+function)
 if function=='makeCache':start=port.index('function make(');end=port.index('export const cases:')
 else:
  start=port.index('  '+case+'()');next_case=re.search(r'^  \w+\(\)',port[start+2:],re.M)
  end=start+2+next_case.start() if next_case else port.index('export function boundary')
 cursor=start;result=[]
 for site,target in zip(sites,targets):
  row={**site,'source_file':'vendor/go_freelru/lru_test.go'}
  if target is None:
   row.update(status='excluded',authorization='callback-exclusions.json',reason='callback argument/count assertion',retained_locations=[])
  else:
   at=port.find(target,cursor,end)
   if at<0:raise RuntimeError('missing retained assertion '+site['id']+': '+target)
   cursor=at+len(target)
   row.update(status='retained',retained_locations=[{'file':'tests/new/upstream.ts','line':port[:at].count('\n')+1,'expression':target}])
   if 'evictCounter' in site['source']:
    row['excluded_clauses']=[{'source':re.search(r'evictCounter != \d+',site['source'])[0],'authorization':'callback-exclusions.json','status':'excluded'}]
  result.append(row)
 return result

def inventory():
 text=(ROOT/'vendor/go_freelru/lru_test.go').read_text()
 starts=list(re.finditer(r'^func (\w+)\(',text,re.M)); funcs={}
 for i,m in enumerate(starts):
  src=text[m.start():starts[i+1].start() if i+1<len(starts) else len(text)]
  line=text[:m.start()].count('\n')+1
  sites=[]
  for site in re.finditer(r'\b(FatalIf|t\.Fatalf)\(',src):
   if src[max(0,site.start()-5):site.start()]=='func ':continue
   j=site.end(); depth=1;quote=None;escape=False
   while j<len(src) and depth:
    ch=src[j]
    if quote:
     if escape:escape=False
     elif ch=='\\':escape=True
     elif ch==quote:quote=None
    elif ch in '\"`':quote=ch
    elif ch=='(':depth+=1
    elif ch==')':depth-=1
    j+=1
   sites.append({'id':f'{m[1]}:{len(sites)+1}','line':line+src[:site.start()].count('\n'),'source':src[site.start():j]})
  funcs[m[1]]={'line':line,'assertions':sites,'source':src}
 port=(ROOT/'tests/new/upstream.ts').read_text()
 rows=[]
 for case in json.loads((ROOT/'tests.manifest.json').read_text()):
  names=[case['name'],'makeCache','setupCache','FatalIf']+HELPERS.get(case['name'],[])
  rows.append({'name':case['name'],'port':'tests/new/upstream.ts::cases.'+case['name'],
    'functions':{n:{**funcs[n],'assertions':map_sites(n,funcs[n]['assertions'],case['name'],port)} for n in names},'excluded_registration_sites':[{'file':'vendor/go_freelru/lru_test.go','line':funcs[n]['line']+funcs[n]['source'][:m.start()].count('\n'),'source':m[0],'authorization':'callback-exclusions.json','status':'excluded'} for n in names for m in re.finditer(r'cache.SetOnEvict\([^\n]*',funcs[n]['source'])],'mechanical_adaptations':['hash callback omitted','sleep replaced by injected millisecond clock','deterministic seeded random source for TestLRUMatch; uint64 underflow retained','callbacks excluded by callback-exclusions.json; all other clauses retained','TestLRUMatch backup uses an independent input-driven oldest-first list and finite map, never callback/implementation observations']})
 return rows
if __name__=='__main__':
 (ROOT/'tests/new/assertion-map.json').write_text(json.dumps(inventory(),indent=2)+'\n')

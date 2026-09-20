import assert from 'node:assert/strict';
import {LRU,uint64Codec,stringCodec,int64Codec} from '../../src/adapter.ts';
let checks=0;
function ok(b: unknown, message='assertion') { ++checks; assert.ok(b,message); }
function eq(a: unknown,b: unknown) { ++checks; assert.deepEqual(a,b); }
const ms=1000000n;
let now=1000n;
function make(cap: bigint) {
  let cache!: LRU<bigint,bigint>;
  ++checks;assert.doesNotThrow(()=>{cache=new LRU(cap,uint64Codec,()=>now,0n,0n);});
  return {cache};
}
export const cases: Record<string,()=>void> = {
  TestLRU() {
    const {cache:c}=make(32n);
    for(let i=0n;i<64n;++i)c.Add(i,i+1n);
    eq(c.Len(),32n);
    c.Keys().forEach((k,i)=>{const [v,found]=c.Get(k);ok(found&&v===k+1n&&v===BigInt(i)+33n);});
    for(let i=0n;i<32n;++i)ok(!c.Get(i)[1]);
    for(let i=32n;i<64n;++i)ok(c.Get(i)[1]);
    ok(!c.Remove(64n));ok(c.Remove(63n));ok(c.Remove(32n));eq(c.Len(),30n);
    c.CheckInvariants();
  },
  TestLRU_Add() {
    const {cache:c}=make(1n);
    ok(!c.Add(1n,2n));ok(c.Add(3n,4n));c.CheckInvariants();
  },
  TestLRU_Purge() {
    const {cache:c}=make(3n);
    ok(!c.Add(1n,2n));ok(!c.Add(3n,4n));ok(!c.Add(4n,5n));
    eq(c.Len(),3n);c.Purge();eq(c.Len(),0n);c.CheckInvariants();
  },
  TestLRU_Remove() {
    const {cache:c}=make(2n);c.Add(1n,2n);c.Add(3n,4n);
    ok(c.Remove(1n));ok(c.Remove(3n));eq(c.Len(),0n);c.CheckInvariants();
  },
  TestLRU_RemoveOldest() {
    const {cache:c}=make(2n);c.Add(1n,2n);c.Add(3n,4n);
    let [k,v,found]=c.RemoveOldest();ok(found);eq(k,1n);eq(v,2n);
    [k,v,found]=c.RemoveOldest();ok(found);eq(k,3n);eq(v,4n);
    ok(!c.RemoveOldest()[2]);eq(c.Len(),0n);c.CheckInvariants();
  },
  TestLRU_AddWithExpire() {
    const {cache:c}=make(2n);c.SetLifetime(100n*ms);c.Add(1n,2n);c.AddWithLifetime(3n,4n,200n*ms);
    ok(c.Get(1n)[1]);now+=101n;ok(!c.Get(1n)[1]);ok(c.Get(3n)[1]);now+=100n;ok(!c.Get(3n)[1]);eq(c.Len(),0n);
    c.Add(1n,2n);c.Purge();eq(c.Len(),0n);
    c.AddWithLifetime(1n,2n,100n*ms);c.PurgeExpired();eq(c.Len(),1n);now+=101n;c.PurgeExpired();eq(c.Len(),0n);
    c.SetLifetime(0n);c.AddWithLifetime(1n,2n,100n*ms);ok(c.Get(1n)[1]);now+=101n;ok(!c.Get(1n)[1]);c.CheckInvariants();
  },
  TestLRU_AddWithRefresh() {
    const {cache:c}=make(2n);c.AddWithLifetime(1n,2n,100n*ms);c.AddWithLifetime(2n,3n,100n*ms);
    ok(c.Get(1n)[1]);now+=101n;ok(c.GetAndRefresh(1n,0n)[1]);ok(c.GetAndRefresh(2n,0n)[1]);c.CheckInvariants();
  },
  TestLRUMatch() {
    const {cache:c}=make(2n);const backup=new Map<bigint,bigint>();
    const order:bigint[]=[]; // Input-driven reference recency, independent of cache outputs.
    let seed=0x12345678;
    for(let i=0n;i<100000n;++i) {
      if(!backup.has(i)&&backup.size===2)backup.delete(order.shift()!);
      backup.set(i,i);order.push(i);c.Add(i,i);
      seed=(Math.imul(seed,1664525)+1013904223)>>>0;
      const r=BigInt.asUintN(64,i-BigInt(seed%384));c.Remove(r);
      if(backup.delete(r))order.splice(order.indexOf(r),1);
      eq(c.Len(),BigInt(backup.size));const keys=c.Keys();eq(keys.length,backup.size);eq(keys,order);
      for(const k of keys){ok(backup.has(k));const [v,found]=c.Peek(k);ok(found);eq(v,backup.get(k));}
      for(const [k,v] of backup){const [actual,found]=c.Peek(k);ok(found);eq(actual,v);}
      c.CheckInvariants();
    }
  },
  TestLRUAdd() {const {cache:c}=make(1000n);for(let i=0n;i<1000n;++i)c.Add(i,0n);c.CheckInvariants();},
  TestLRUMetrics() {
    const {cache:c}=make(1n);c.Add(1n,2n);c.Add(3n,4n);c.Get(1n);c.Get(3n);c.Remove(3n);
    const m=c.Metrics();eq(m.Inserts,2n);eq(m.Hits,1n);eq(m.Misses,1n);eq(m.Evictions,1n);eq(m.Removals,1n);eq(m.Collisions,0n);
  },
  TestLRU_Values() {
    const {cache:c}=make(1000n);const want=[];
    for(let i=0n;i<1000n;++i){c.Add(i,i+1n);want.push(i+1n);}
    eq(c.Values().sort((a,b)=>a<b?-1:a>b?1:0),want);c.CheckInvariants();
  },
  TestLRU_GetOldest() {
    const {cache:c}=make(1000n);c.Add(1n,2n);c.Add(3n,4n);c.Add(5n,6n);
    const [k,v,found]=c.GetOldest();ok(found);eq(k,1n);eq(v,2n);c.CheckInvariants();
  }
};
export function boundary() {
  ok(!('SetOnEvict' in LRU.prototype));
  let reads=0;let t=10n;
  const c=new LRU(3n,stringCodec,()=>{++reads;return t;},'',0n);
  c.Add('',1n);c.Add('\0',2n);c.Add('a\0b',3n);eq(reads,0);eq(c.Keys(),['','\0','a\0b']);
  eq(c.Get('\0'),[2n,true]);eq(c.Keys(),['','a\0b','\0']);
  eq(c.RemoveOldest(),['',1n,true]);eq(c.RemoveOldest(),['a\0b',3n,true]);eq(c.RemoveOldest(),['\0',2n,true]);
  c.Purge();eq(c.Metrics().Removals,0n);
  c.AddWithLifetime('old',4n,1n);eq(reads,1);eq(c.Len(),1n);eq(c.GetOldest(),['old',0n,false]);eq(reads,2);
  c.AddWithLifetime('revive',5n,-1000001n);ok(c.GetAndRefresh('revive',0n)[1]);eq(c.Get('revive'),[5n,true]);
  c.Purge();c.Add('immortal',7n);c.AddWithLifetime('expired',8n,-1n);const before=reads;
  c.PurgeExpired();eq(reads,before);eq(c.Keys(),['immortal','expired']);eq(c.Len(),2n);
  eq(c.Get('expired'),[0n,false]);c.CheckInvariants();
  c.Purge();c.AddWithLifetime('replace',1n,-1n);
  ok(!c.Add('replace',9n));eq(c.Metrics().Inserts,2n);eq(c.Get('replace'),[9n,true]);
  const old=c.Metrics();eq(c.ResetMetrics(),old);eq(c.Metrics().Hits,0n);
  // Zero deadline sentinel, even when obtained from nonzero duration arithmetic.
  c.Purge();t=1n;c.AddWithLifetime('sentinel',1n,-1000000n);t=100n;ok(c.Get('sentinel')[1]);
  for(const [cap,size] of [[0n,0n],[2n,1n],[1n,0xffffffffn],[0x100000000n,0x100000000n]])
    assert.throws(()=>new LRU(cap,stringCodec,()=>0n,'',0n,size));
  const i=new LRU(3n,int64Codec,()=>0n,0n,0n);i.Add(-(1n<<63n),1n);i.Add((1n<<63n)-1n,2n);i.Add(0n,3n);
  eq(i.Keys(),[-(1n<<63n),(1n<<63n)-1n,0n]);i.CheckInvariants();
  assert.throws(()=>c.GetAndRefresh('sentinel',1n<<63n));
  assert.throws(()=>c.Add('\ud800',1n));
}
export function run(name: string) {
  now=1000n;checks=0;
  const fn = name==='boundary' ? boundary : cases[name];
  if(!fn)throw new Error('unsupported case '+name);
  fn();return {name,status:'passed',assertions:checks};
}
if(import.meta.main) {
  try {console.log(JSON.stringify(run(process.argv[2])));}
  catch(e){console.error(e);process.exit(1);}
}

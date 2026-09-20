import assert from 'node:assert/strict';
import {LRU,stringCodec} from '../../src/adapter.ts';
let assertions=0;
const eq=(a:unknown,b:unknown)=>{++assertions;assert.deepEqual(a,b);};
const marker=new Error('clock unavailable');
const raises=(f:()=>unknown)=>{++assertions;assert.throws(f,e=>e===marker);};
const ms=1000000n;

// Expected states follow input operations and the documented suspension point;
// neither expected states nor answers enter the Bend backend.
{
  const c=new LRU(2n,stringCodec,()=>{throw marker;},'',0n);
  c.Add('old',1n);c.Add('survivor',2n);
  raises(()=>c.AddWithLifetime('new',3n,ms));
  eq(c.Len(),1n);eq(c.Keys(),['survivor']);eq(c.Peek('new'),[0n,false]);
  eq(c.Metrics(),{Inserts:2n,Collisions:0n,Evictions:1n,Removals:0n,Hits:0n,Misses:0n});
  c.CheckInvariants();
}
{
  const c=new LRU(2n,stringCodec,()=>{throw marker;},'',0n);
  c.Add('old',1n);c.Add('newer',2n);
  raises(()=>c.AddWithLifetime('old',9n,ms));
  eq(c.Keys(),['old','newer']);eq(c.Peek('old'),[1n,true]);
  eq(c.Metrics(),{Inserts:2n,Collisions:0n,Evictions:0n,Removals:0n,Hits:0n,Misses:0n});
  raises(()=>c.GetAndRefresh('old',ms));
  eq(c.Keys(),['newer','old']);eq(c.Peek('old'),[1n,true]);
  eq(c.Metrics(),{Inserts:2n,Collisions:0n,Evictions:0n,Removals:0n,Hits:1n,Misses:0n});
  c.CheckInvariants();
}
for (const method of ['Get','Peek','Contains','GetOldest'] as const) {
  let fail=false;
  const c=new LRU(1n,stringCodec,()=>{if(fail)throw marker;return 0n;},'',0n);
  c.AddWithLifetime('finite',7n,ms);fail=true;
  const before=c.Metrics();
  raises(()=>method==='GetOldest'?c.GetOldest():c[method]('finite'));
  eq(c.Len(),1n);eq(c.Metrics(),before);c.CheckInvariants();
  fail=false;eq(c.Peek('finite'),[7n,true]);
}
for (const method of ['PurgeExpired','Keys','Values'] as const) {
  let phase='setup', reads=0;
  const c=new LRU(2n,stringCodec,()=>{
    if(phase==='setup')return 0n;
    if(phase==='failure' && ++reads===2)throw marker;
    return 1n;
  },'',0n);
  c.AddWithLifetime('first',1n,ms);c.AddWithLifetime('second',2n,ms);
  phase='failure';raises(()=>c[method]());
  eq(reads,2);eq(c.Len(),1n);
  eq(c.Metrics(),{Inserts:2n,Collisions:0n,Evictions:0n,Removals:1n,Hits:0n,Misses:0n});
  c.CheckInvariants();
  phase='recovery';eq(c.RemoveOldest(),['second',2n,true]);eq(c.Len(),0n);
}
{
  // Invalid samples are execution failures, too; eviction is not rolled back.
  const c=new LRU(1n,stringCodec,()=>1n<<63n,'',0n);
  c.Add('old',1n);
  ++assertions;assert.throws(()=>c.AddWithLifetime('new',2n,ms),RangeError);
  eq(c.Len(),0n);eq(c.Metrics().Evictions,1n);eq(c.Metrics().Inserts,1n);
  c.CheckInvariants();
}
console.log(JSON.stringify({name:'clock_failures',status:'passed',assertions}));

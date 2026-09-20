import {LRU,stringCodec,int64Codec,uint64Codec,int64} from '../../src/adapter.ts';
function record(value:any, allowed:readonly string[]) {
  if(value===null || typeof value!=='object' || Array.isArray(value))throw new Error('invalid transport object');
  for(const key of Object.keys(value))if(!allowed.includes(key))throw new Error('unsupported transport field '+key);
}
const input=await Bun.stdin.json();
record(input,['capacity','ops','seed_metrics','key_type']);
const keyType=input.key_type??'string';
if(!['string','int64','uint64'].includes(keyType))throw new Error('unsupported key type');
const codec:any=keyType==='string'?stringCodec:keyType==='int64'?int64Codec:uint64Codec;
const zeroKey:any=keyType==='string'?'':0n;
function userKey(k:any){
  if(keyType==='string')return k===undefined?'':k;
  if(k===undefined)return 0n;
  if(typeof k!=='string'||! /^(0|-?[1-9][0-9]*)$/.test(k))throw new Error('integer key decimal-string transport');
  return BigInt(k);
}
if(!input || !Array.isArray(input.ops) || !Number.isInteger(input.capacity))throw new Error('invalid trace');
if('callback_mode' in input || 'clock_mode' in input)throw new Error('unsupported callback or mutating-clock mode');
let now=0n,stride=0n,reads=0n;
const c=new LRU<any,bigint>(BigInt(input.capacity),codec,()=>BigInt.asIntN(64,now+(reads++)*stride),zeroKey,0n);
// Test-only counter fixture: bypassing billions of public calls, never results.
if(input.seed_metrics) {
  if(!Array.isArray(input.seed_metrics)||input.seed_metrics.length!==5)throw new Error('metric fixture');
  const names=['inserts','evictions','removals','hits','misses'];
  input.seed_metrics.forEach((s:any,i:number)=>{
    if(typeof s!=='string'||! /^(0|[1-9][0-9]*)$/.test(s))throw new Error('uint64 transport');
    const n=BigInt(s);if(n>=1n<<64n)throw new Error('uint64 range');
    (c as any).state.counts[names[i]]=uint64Codec.toBend(n);
  });
}
function i64(s:any,defaultValue='0') {
  if(s===undefined)s=defaultValue;
  if(typeof s!=='string'||! /^(0|-?[1-9][0-9]*)$/.test(s))throw new Error('int64 decimal-string transport');
  const n=BigInt(s);int64(n);return n;
}
const out=[];
for(const o of input.ops){
  record(o,['op','key','value','ns','now','stride']);
  if(typeof o.op!=='string')throw new Error('invalid operation name');
  codec.toBend(userKey(o.key));
  for(const field of ['value','ns','now','stride'])if(o[field]!==undefined)i64(o[field]);
  now=i64(o.now);stride=i64(o.stride);reads=0n;
  const key=userKey(o.key);let result:any=null;
  switch(o.op){
    case 'Add':result=c.Add(key,i64(o.value));break;
    case 'AddWithLifetime':result=c.AddWithLifetime(key,i64(o.value),i64(o.ns));break;
    case 'Get':result=c.Get(key);break;
    case 'Peek':result=c.Peek(key);break;
    case 'GetAndRefresh':result=c.GetAndRefresh(key,i64(o.ns));break;
    case 'Contains':result=c.Contains(key);break;
    case 'Remove':result=c.Remove(key);break;
    case 'RemoveOldest':result=c.RemoveOldest();break;
    case 'GetOldest':result=c.GetOldest();break;
    case 'Purge':c.Purge();break;
    case 'PurgeExpired':c.PurgeExpired();break;
    case 'Keys':result=c.Keys();break;
    case 'Values':result=c.Values();break;
    case 'Len':result=c.Len();break;
    case 'SetLifetime':c.SetLifetime(i64(o.ns));break;
    case 'Metrics':result=c.Metrics();break;
    case 'ResetMetrics':result=c.ResetMetrics();break;
    default:throw new Error('unsupported operation '+o.op);
  }
  c.CheckInvariants();out.push({result,metrics:c.Metrics(),len:c.Len(),reads});
}
console.log(JSON.stringify(out,(_,v)=>typeof v==='bigint'?v.toString():v));

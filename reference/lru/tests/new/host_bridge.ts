import assert from 'node:assert/strict';
import {uint64Codec,int64Codec,stringCodec,int64} from '../../src/adapter.ts';
const code=(c:any,k:any)=>c.encode(c.toBend(k));
// Translation validation of the host boundary against independent JS oracles:
// bigint -> decimal text -> Bend word (src/host.bend) -> codec string (least
// significant bit first) and back to bigint, int64 two's complement, and
// range rejection. The conversions are also proved (proofs/host_*.bend); this
// checks the JS runtime's String(bigint)/BigInt(text) and the marshalling.
let assertions=0;
const eq=(a:unknown,b:unknown)=>{++assertions;assert.deepEqual(a,b);};
const bits=(n:bigint)=>n.toString(2).padStart(64,'0').split('').reverse().join('');
let seed=0x243f6a8885a308d3n;
const next=()=>{seed=(seed*6364136223846793005n+1442695040888963407n)&((1n<<64n)-1n);return seed;};
const edges=[0n,1n,2n,0xffffffffn,0x100000000n,0x100000001n,(1n<<63n)-1n,1n<<63n,(1n<<64n)-2n,(1n<<64n)-1n];
const samples=[...edges];for(let i=0;i<2000;i++)samples.push(next());
const codes=new Map<string,bigint>();
for(const n of samples){
  eq(code(uint64Codec,n),bits(n));eq(uint64Codec.fromBend(uint64Codec.toBend(n)),n);
  const s=BigInt.asIntN(64,n);
  eq(code(int64Codec,s),bits(n));eq(int64Codec.fromBend(int64Codec.toBend(s)),s);
  eq(int64Codec.fromBend(int64(s).bits),s);
  eq(uint64Codec.fromBend(int64(s).bits),n);
  const prior=codes.get(code(uint64Codec,n));
  if(prior!==undefined)eq(prior,n);
  codes.set(code(uint64Codec,n),n);
}
for(const bad of [-1n,1n<<64n])assert.throws(()=>uint64Codec.toBend(bad),RangeError),++assertions;
for(const bad of [-(1n<<63n)-1n,1n<<63n])assert.throws(()=>int64Codec.toBend(bad),RangeError),++assertions;
for(const bad of [-(1n<<63n)-1n,1n<<63n,1 as any,'5' as any])assert.throws(()=>int64(bad),RangeError),++assertions;
for(const s of ['','a','\u0000','héllo','\u{1F600}']){eq(code(stringCodec,s),s);eq(stringCodec.fromBend(stringCodec.toBend(s)),s);}
assert.throws(()=>stringCodec.toBend('\udc00'),RangeError);++assertions;
console.log(JSON.stringify({name:'host_bridge',status:'passed',assertions}));

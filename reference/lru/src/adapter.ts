/** Executable host adapter. Every validation, conversion and cache decision
 *  is Bend code: src/host.bend (proved in proofs/host_*.bend) and the public
 *  machine src/public.bend. This file only
 *    - calls those Bend functions and passes their values back unchanged,
 *    - turns host integers into decimal text with the runtime's String(bigint)
 *      and reads Bend's decimal text back with BigInt(text),
 *    - calls the clock provider and catches its exception,
 *    - checks constructor tags.
 *  Run with Bend's Bun preload. */
import H from './host.bend';
import Codec from './codec.bend';

/** Decimal text of a host integer; anything else is not a numeral. */
function text(n: unknown): string {
  return typeof n === 'bigint' ? String(n) : '';
}
/** A Bend Result: its value, or its rejection as a RangeError. */
function take(r: any): any {
  if (r?.$ === 'Done') return r.value;
  if (r?.$ === 'Fail') throw new RangeError(r.error);
  throw new TypeError('invalid Bend result');
}
export function list(xs: any): any[] {
  const out = [];
  while (xs.$ === 'Con') { out.push(xs.head); xs = xs.tail; }
  if (xs.$ !== 'Nil') throw new TypeError('invalid Bend list');
  return out;
}
/** A key codec: the Bend reader of a user key, its reverse, and the proved
 *  Bend codec for that key type. The Bend machine only ever sees Bend keys
 *  and the Bend codec function. */
export interface KeyCodec<K> {
  toBend(key: K): any;
  fromBend(key: any): K;
  readonly encode: (key: any) => string;
}
/** uint64 keys are Bend Word(64n) keys under Codec.word64_encode. */
export const uint64Codec: KeyCodec<bigint> = {
  toBend(key) { return take(H.uint64_key(text(key))); },
  fromBend(key) { return BigInt(H.uint64_text(key)); },
  encode: Codec.word64_encode,
};
/** int64 keys are their two's-complement Bend Word(64n) under Codec.word64_encode. */
export const int64Codec: KeyCodec<bigint> = {
  toBend(key) { return take(H.int64_key(text(key))); },
  fromBend(key) { return BigInt(H.int64_text(key)); },
  encode: Codec.word64_encode,
};
/** String keys are Bend Strings of Unicode scalar values under Codec.string_encode. */
export const stringCodec: KeyCodec<string> = {
  toBend(key) {
    if (typeof key !== 'string') throw new TypeError('string key');
    return take(H.string_key(key));
  },
  fromBend(key) { return key; },
  encode: Codec.string_encode,
};
/** A signed 64-bit duration or instant as Bend's Int64. */
export function int64(n: unknown): any {
  return take(H.time(text(n)));
}
export class LRU<K, V> {
  private state: any;
  private zeroKey: any;
  constructor(capacity: bigint, private codec: KeyCodec<K>,
      private clock: () => bigint = () => BigInt(Date.now()),
      zeroKey: K, private zeroValue: V, size: bigint = capacity) {
    this.zeroKey = codec.toBend(zeroKey);
    this.state = take(H.create(text(capacity), text(size)));
  }
  /** One public command: H.begin, then one provider event per Ask through
   *  H.answer; Return/Raise carry the state to adopt. A thrown provider's
   *  original error propagates; an invalid sample raises a RangeError. */
  private run(request: any): any {
    let action = H.begin(this.codec.encode, this.zeroKey, this.zeroValue, this.state, request);
    let failure: unknown = undefined;
    while (action.$ === 'Ask') {
      let event;
      try { event = H.sample(text(this.clock())); }
      catch (error) { failure = error; event = H.thrown(); }
      action = H.answer(this.zeroValue, action.pending, event);
    }
    if (action.$ !== 'Return' && action.$ !== 'Raise') throw new TypeError('invalid Bend action');
    this.state = action.cache;
    if (action.$ === 'Return') return action.answer;
    throw failure ?? new RangeError(action.error.reason);
  }
  private answer(request: any, tag: string): any {
    const a = this.run(request);
    if (a?.$ !== tag) throw new TypeError('invalid Bend answer');
    return a;
  }
  private key(k: K): any { return this.codec.toBend(k); }
  Len() { return this.answer({$:'Len'},'Length').length as bigint; }
  SetLifetime(ns: bigint) { this.answer({$:'SetLifetime',nanoseconds:int64(ns)},'Empty'); }
  AddWithLifetime(k: K, v: V, ns: bigint): boolean {
    return this.answer({$:'AddWithLifetime',key:this.key(k),value:v,nanoseconds:int64(ns)},'Boolean').value;
  }
  Add(k: K, v: V): boolean { return this.answer({$:'Add',key:this.key(k),value:v},'Boolean').value; }
  Get(k: K): [V, boolean] { const a=this.answer({$:'Get',key:this.key(k)},'Value'); return [a.value,a.found]; }
  Peek(k: K): [V, boolean] { const a=this.answer({$:'Peek',key:this.key(k)},'Value'); return [a.value,a.found]; }
  Contains(k: K): boolean { return this.answer({$:'Contains',key:this.key(k)},'Boolean').value; }
  GetAndRefresh(k: K, ns: bigint): [V, boolean] {
    const a=this.answer({$:'GetAndRefresh',key:this.key(k),nanoseconds:int64(ns)},'Value'); return [a.value,a.found];
  }
  Remove(k: K): boolean { return this.answer({$:'Remove',key:this.key(k)},'Boolean').value; }
  RemoveOldest(): [K, V, boolean] { const a=this.answer({$:'RemoveOldest'},'Oldest'); return [this.codec.fromBend(a.key),a.value,a.found]; }
  GetOldest(): [K, V, boolean] { const a=this.answer({$:'GetOldest'},'Oldest'); return [this.codec.fromBend(a.key),a.value,a.found]; }
  PurgeExpired() { this.answer({$:'PurgeExpired'},'Empty'); }
  Keys(): K[] { return list(this.answer({$:'Keys'},'KeyList').keys).map(k=>this.codec.fromBend(k)); }
  Values(): V[] { return list(this.answer({$:'Values'},'ValueList').values); }
  Purge() { this.answer({$:'Purge'},'Empty'); }
  private counters(m: any) {
    const count = (w: any) => BigInt(H.uint64_text(w));
    return {Inserts:count(m.inserts), Collisions:0n, Evictions:count(m.evictions), Removals:count(m.removals), Hits:count(m.hits), Misses:count(m.misses)};
  }
  Metrics() { return this.counters(this.answer({$:'Metrics'},'Counters').metrics); }
  ResetMetrics() { return this.counters(this.answer({$:'ResetMetrics'},'Counters').metrics); }
  PrintStats() {
    const info = this.Diagnostics(); console.log(info); return info;
  }
  Diagnostics() {
    const d = this.answer({$:'Diagnostics'},'Storage');
    return {storage:'Base.Map crit-bit tree', leaves:d.leaves as bigint,
      recencyEntries:d.recency as bigint, capacity:d.capacity as bigint, collisions:'not applicable', metrics:this.counters(d.metrics)};
  }
  /** Test self-check: Bend's structural check, then each stored original
   *  key's code equals the recency list entry at the same position. */
  CheckInvariants() {
    const codes = list(H.keys(this.state)).map(k=>this.codec.encode(k));
    const order = list(this.state.order);
    if (!H.consistent(this.state) || codes.length !== order.length ||
        codes.some((code,i)=>code!==order[i])) throw new Error('map/recency invariant failed');
  }
}

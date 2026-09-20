#!/usr/bin/env python3
"""Strict Bend conformance runner. Expected outputs never enter either backend."""
import argparse,json,os,random,re,shutil,subprocess,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
BUN='/Users/monkeair/.bun/bin/bun'
MAIN='/Users/monkeair/.bend/current/bend2/main.ts'
GO='/opt/homebrew/bin/go'
ENV={**os.environ,'BEND_NO_TELEMETRY':'1','NO_COLOR':'1','GOCACHE':str(ROOT/'build/go-cache')}
def command(args,*,cwd=ROOT,payload=None,timeout=180):
 p=subprocess.run(args,cwd=cwd,input=payload,text=True,capture_output=True,env=ENV,timeout=timeout)
 if p.returncode:raise RuntimeError(f'{args}: exit {p.returncode}\n{p.stdout}\n{p.stderr}')
 return p.stdout

def backend(args,**kwargs):
 text=command(args,**kwargs)
 try:return json.loads(text)
 except (ValueError,TypeError) as e:raise RuntimeError('missing/malformed backend JSON: '+repr(text[:1000])) from e

def bun(script):return [BUN,'--preload',MAIN,str(script)]
def build_reference():
 dest=ROOT/'build/reference';dest.mkdir(parents=True,exist_ok=True)
 for name in ['lru.go','cache.go']:
  text=(ROOT/'vendor/go_freelru'/name).read_text().replace('package freelru','package main',1)
  if name=='lru.go':
   old='return time.Now().UnixMilli()'
   if text.count(old)!=1:raise RuntimeError('reference clock seam changed')
   text=text.replace(old,'return referenceNow()',1)
  (dest/name).write_text(text)
 shutil.copyfile(ROOT/'tools/reference_main.go',dest/'main.go')
 (dest/'go.mod').write_text('module local/reference\n\ngo 1.18\n')
 binary=dest/'reference'
 command([GO,'build','-o',str(binary),'.'],cwd=dest)
 return binary

def trace_payload(trace):
 # Numeric JSON tokens cannot survive JS JSON.parse at full width. Inputs and
 # outputs use canonical decimal strings; capacity alone is a bounded U32 token.
 trace={**trace,'ops':[{k:(str(v) if k in ('value','ns','now','stride') else v) for k,v in op.items()} for op in trace['ops']]}
 return json.dumps(trace,ensure_ascii=True)

def differential():
 binary=build_reference();rng=random.Random(583)
 names=['Add']*8+['AddWithLifetime']*5+['Get']*5+['Peek','Contains','Remove','GetAndRefresh','RemoveOldest','GetOldest','Keys','Values','PurgeExpired','Purge','SetLifetime','Metrics','ResetMetrics','Len']
 total=0
 for cap in [1,2,7,32]:
  ops=[]
  for i in range(1200):
   ops.append({'op':rng.choice(names),'key':rng.choice(['','\0','a\0b','😀']+[str(n) for n in range(20)]),
     'value':rng.randrange(-100,100),'ns':rng.choice([0,-1000001,-1000000,-999999,-1,1,999999,1000000,20000000]),
     'now':rng.randrange(-2,50),'stride':rng.choice([0,0,1])})
  payload=trace_payload({'capacity':cap,'ops':ops})
  expected=backend([str(binary)],payload=payload)
  actual=backend(bun(ROOT/'tests/new/trace.ts'),payload=payload)
  if not isinstance(actual,list) or len(actual)!=len(ops):raise RuntimeError('trace response length mismatch')
  if actual!=expected:
   first=next(i for i,(a,b) in enumerate(zip(actual,expected)) if a!=b)
   (ROOT/'build/differential-failure.json').write_text(json.dumps({'input':json.loads(payload),'index':first,'actual':actual[first],'expected':expected[first]},indent=2))
   raise AssertionError(f'differential mismatch capacity={cap} step={first}: {ops[first]} actual={actual[first]} expected={expected[first]}')
  total+=len(ops)
 # Integer keys through the adapter's int64/uint64 codecs (Bend Word(64n) keys),
 # including extremes, against the same pinned Go code at K=int64/uint64.
 pools={'int64':[-(1<<63),-(1<<63)+1,-1,0,1,(1<<63)-2,(1<<63)-1]+list(range(-12,12)),
        'uint64':[0,1,(1<<63)-1,1<<63,(1<<64)-2,(1<<64)-1]+list(range(24))}
 for key_type,pool in pools.items():
  for cap in [1,3,16]:
   ops=[]
   for i in range(800):
    ops.append({'op':rng.choice(names),'key':str(rng.choice(pool)),
      'value':rng.randrange(-100,100),'ns':rng.choice([0,-1000000,-1,1,999999,1000000,20000000]),
      'now':rng.randrange(-2,50),'stride':rng.choice([0,0,1])})
   compare_trace(binary,{'capacity':cap,'ops':ops,'key_type':key_type},'differential-'+key_type+'-'+str(cap))
   total+=len(ops)
 return {'status':'passed','operations':total,'seed':583,'capacities':[1,2,7,32],'integer_key_capacities':[1,3,16],'key_types':['string','int64','uint64'],
   'time_adapter':'only pinned now() return expression replaced; every clock read counted',
   'projection':'Collisions set to zero on reference output only: native storage adaptation'}

def compare_trace(binary,trace,label):
 payload=trace_payload(trace)
 expected=backend([str(binary)],payload=payload)
 actual=backend(bun(ROOT/'tests/new/trace.ts'),payload=payload)
 if not isinstance(actual,list) or len(actual)!=len(trace['ops']):raise AssertionError(label+': response shape')
 if actual!=expected:
  first=next(i for i,(a,b) in enumerate(zip(actual,expected)) if a!=b)
  (ROOT/'build'/('failure-'+label+'.json')).write_text(json.dumps({'trace':trace,'index':first,'actual':actual[first],'expected':expected[first]},indent=2))
  raise AssertionError(f'{label} step {first}: actual={actual[first]}, expected={expected[first]}')
 return len(actual)

def numeric_boundaries():
 binary=build_reference();lo=-(1<<63);hi=(1<<63)-1;total=0
 times=[lo,lo+1,-9223372036854,-1,0,1,9223372036854,hi-1,hi]
 lifetimes=[lo,lo+1,-2000001,-1000001,-1000000,-999999,-1,0,1,999999,1000000,1000001,hi-1,hi]
 ops=[]
 for now in times:
  for ns in lifetimes:
   ops += [{'op':'Purge'}, {'op':'AddWithLifetime','key':'wide','value':hi,'ns':ns,'now':now},
      {'op':'Len'}, {'op':'GetOldest','now':now}, {'op':'AddWithLifetime','key':'wide','value':lo,'ns':ns,'now':now},
      {'op':'GetAndRefresh','key':'wide','ns':ns,'now':now}, {'op':'Get','key':'wide','now':now},
      {'op':'PurgeExpired','now':hi}, {'op':'Keys','now':lo}]
 total+=compare_trace(binary,{'capacity':2,'ops':ops},'numeric-boundary')
 # White-box counter fixture only: both engines start from the same supplied
 # counters, and every subsequent decision is the actual implementation.
 ops=[{'op':'Add','key':'a','value':lo},{'op':'Get','key':'a'}, {'op':'Get','key':'missing'},
      {'op':'Add','key':'b','value':hi},{'op':'Remove','key':'b'}, {'op':'ResetMetrics'},{'op':'Metrics'}]
 total+=compare_trace(binary,{'capacity':1,'seed_metrics':[str((1<<64)-1)]*5,'ops':ops},'counter-wrap')
 return {'status':'passed','operations':total,'full_width_values':'canonical decimal strings',
   'coverage':'int64 min/max, signed submillisecond truncation, wrapping deadline addition, zero sentinel, all five uint64 counter wraps',
   'counter_fixture':'test-only initial counter seeding in both drivers; not a public cache operation'}

def assertion_inventory():
 import runpy
 generated=runpy.run_path(str(ROOT/'tools/inventory.py'))['inventory']()
 recorded=json.loads((ROOT/'tests/new/assertion-map.json').read_text())
 if generated!=recorded:raise AssertionError('stale or incomplete assertion inventory')
 sites={a['id']:a for row in generated for f in row['functions'].values() for a in f['assertions']}
 excluded=[a for a in sites.values() if a['status']=='excluded']
 mixed=[a for a in sites.values() if a.get('excluded_clauses')]
 return {'status':'passed','groups':len(generated),'retained_source_assertions':len(sites)-len(excluded),
         'excluded_source_assertions':[a['id'] for a in excluded],
         'partially_excluded_source_assertions':[a['id'] for a in mixed],
         'authorization':'callback-exclusions.json','excluded_counted_as_passes':False}

def sensitivity():
 dest=ROOT/'build/mutation';dest.mkdir(parents=True,exist_ok=True)
 for name in ['src','types','spec','proofs','tests/new']:
  shutil.copytree(ROOT/name,dest/name,dirs_exist_ok=True)
 for name in ['PROOF.bend','END_TO_END.bend']:shutil.copyfile(ROOT/name,dest/name)
 p=dest/'src/time.bend';original=p.read_text()
 if original.count('      le(d, now)')!=1:raise RuntimeError('expiry mutation target missing')
 p.write_text(original.replace('      le(d, now)','      False{}'))
 proc=subprocess.run(bun(dest/'tests/new/upstream.ts')+['boundary'],cwd=dest,text=True,capture_output=True,env=ENV,timeout=180)
 if proc.returncode==0 or 'AssertionError' not in proc.stderr:raise AssertionError('expiry mutant not rejected by assertion')
 p.write_text(original)
 p=dest/'src/codec.bend';original=p.read_text()
 if original.count("      '1'")!=1:raise RuntimeError('codec mutation target missing')
 p.write_text(original.replace("      '1'","      '0'"))
 proc=subprocess.run([BUN,MAIN,str(dest/'PROOF.bend')],cwd=dest,text=True,capture_output=True,env=ENV,timeout=180)
 if proc.returncode==0 or 'expected' not in proc.stdout+proc.stderr:raise AssertionError('codec mutant theorem not rejected')
 p.write_text(original)
 p=dest/'proofs/native_map.bend';original=p.read_text()
 old='  (pair, c) = r\n  c'
 if original.count(old)!=1:raise RuntimeError('comparison mutation target ambiguous')
 p.write_text(original.replace(old,'  (pair, c) = r\n  EQ{}'))
 try:
  proc=subprocess.run([BUN,MAIN,str(dest/'PROOF.bend')],cwd=dest,text=True,capture_output=True,env=ENV,timeout=180)
  if proc.returncode==0 or 'expected' not in proc.stdout+proc.stderr:raise AssertionError('comparison certificate mutant not rejected')
  (ROOT/'build/mutation-comparison.log').write_text(proc.stdout+proc.stderr)
 finally:p.write_text(original)
 p=dest/'src/cache.bend';original=p.read_text()
 old='m, code, Some{T.Item{key, value, deadline}})'
 if original.count(old)!=1:raise RuntimeError('store-value mutation target ambiguous')
 p.write_text(original.replace(old,'m, code, None{})'))
 try:
  proc=subprocess.run([BUN,MAIN,str(dest/'PROOF.bend')],cwd=dest,text=True,capture_output=True,env=ENV,timeout=180)
  if proc.returncode==0 or 'expected' not in proc.stdout+proc.stderr:raise AssertionError('actual store lookup theorem did not reject missing value')
  (ROOT/'build/mutation-store-value.log').write_text(proc.stdout+proc.stderr)
 finally:p.write_text(original)
 # Mutating the store to discard retained recency must fail its proof closure.
 # The first rejecting law is the existing store recency-uniqueness linkage.
 p=dest/'src/cache.bend';original=p.read_text()
 old='deadline}}), List.append(&2, String, without(order, code), Con{code, Nil{}})'
 new='deadline}}), Con{code, Nil{}}'
 if original.count(old)!=1:raise RuntimeError('store membership mutation target ambiguous')
 p.write_text(original.replace(old,new))
 try:
  proc=subprocess.run([BUN,MAIN,str(dest/'proofs/cache_store_membership.bend')],cwd=dest,text=True,capture_output=True,env=ENV,timeout=180)
  if proc.returncode==0 or 'recency_unique.store_preserves_unique_recency' not in proc.stdout+proc.stderr:raise AssertionError('store recency mutation was not rejected at the recorded theorem')
  (ROOT/'build/mutation-store-membership.log').write_text(proc.stdout+proc.stderr)
 finally:p.write_text(original)
 # This module imports only actual source/types, so its preparation law is
 # checked without unrelated recency or Map theorem dependencies.
 p=dest/'src/entry_ops.bend';original=p.read_text()
 old='refresh_prepare_found(K, V, c, code, C.lookup(K, V, c, code))'
 new='refresh_prepare_found(K, V, c, code, C.lookup(K, V, c, ""))'
 if original.count(old)!=1:raise RuntimeError('refresh lookup mutation target ambiguous')
 p.write_text(original.replace(old,new))
 try:
  proc=subprocess.run([BUN,MAIN,str(dest/'proofs/refresh_lookup.bend')],cwd=dest,text=True,capture_output=True,env=ENV,timeout=180)
  if proc.returncode==0 or 'Location: prepare' not in proc.stdout+proc.stderr:raise AssertionError('refresh preparation linkage did not reject wrong lookup code')
  (ROOT/'build/mutation-refresh-lookup.log').write_text(proc.stdout+proc.stderr)
 finally:p.write_text(original)
 # A missing-key refresh must retain positive capacity. Check the new joint
 # representation module directly and require its actual preparation branch.
 p=dest/'src/entry_ops.bend';original=p.read_text()
 old='C.Out{finish_miss(K, V, c, True{}), None{}, False{}, Nil{}}'
 new='C.Out{C.init(K, V, 0n), None{}, False{}, Nil{}}'
 if original.count(old)!=1:raise RuntimeError('refresh representation mutation target ambiguous')
 p.write_text(original.replace(old,new))
 try:
  proc=subprocess.run([BUN,MAIN,str(dest/'proofs/refresh_representation.bend')],cwd=dest,text=True,capture_output=True,env=ENV,timeout=180)
  if proc.returncode==0 or 'Location: found~' not in proc.stdout+proc.stderr or 'expected : {False{} == True{} : Bool}' not in proc.stdout+proc.stderr:raise AssertionError('refresh representation did not reject zero-capacity reset at preparation')
  (ROOT/'build/mutation-refresh-representation.log').write_text(proc.stdout+proc.stderr)
 finally:p.write_text(original)
 # Check new implementation-to-specification/representation links directly.
 for name,relative,old,new,proof,location in [
  ('full-capacity-spec','spec/operations.bend',
   'Nat.is_ge(List.length(&2, K, order), cap)', 'Nat.is_gt(List.length(&2, K, order), cap)',
   'proofs/full_add.bend','Location: full_add_head.model_head'),
  ('refresh-return-deadline-spec','spec/operations.bend',
   'Some{T.Item{k, v, deadline}}', 'Some{T.Item{k, v, olddeadline}}',
   'proofs/refresh_state.bend','Location: observation'),
  ('remove-count-spec','spec/cache.bend',
   'T.Counts{i, e, Word.inc(64n, r), h, m}', 'T.Counts{i, e, r, h, m}',
   'proofs/removal_state.bend','Location: normalized'),
  ('live-hit-count-spec','spec/operations.bend',
   'T.Counts{i, e, r, Word.inc(64n, h), m}', 'T.Counts{i, e, r, h, m}',
   'proofs/live_read_state.bend','Location: normalized'),
  ('absent-read-miss','spec/operations.bend',
   'S.Abstract{cap, bindings, order, life, T.Counts{i, e, r, h, Word.inc(64n, m)}, cb}',
   'S.Abstract{cap, bindings, order, life, T.Counts{i, e, r, h, m}, cb}',
   'proofs/absent_read.bend','Location: branch~'),
  ('signed-magnitude','src/wide.bend',
   'neg(unsigned_milliseconds(neg(w)))', 'neg(unsigned_milliseconds(w))',
   'proofs/signed_division.bend','Location: actual_negative'),
  ('deadline-zero-sentinel','spec/numeric.bend',
   '      T.I64{Word.zero(64n)}', '      now',
   'proofs/duration_refinement.bend','Location: choose'),
  ('division-quotient-bit','src/wide.bend',
   'Div{WCon{True{}, q}, U32.sub(r, 1000000)}', 'Div{WCon{False{}, q}, U32.sub(r, 1000000)}',
   'proofs/division_value.bend','Location: result_form'),
  ('division-remainder','src/wide.bend',
   'Div{WCon{True{}, q}, U32.sub(r, 1000000)}', 'Div{WCon{True{}, q}, r}',
   'proofs/division_invariant.bend','Location: result'),
  ('division-candidate','src/wide.bend',
   'U32.add(U32.mul(r, 2), bit_u32(b))', 'U32.add(U32.mul(r, 3), bit_u32(b))',
   'proofs/division_candidate.bend','Location: digit'),
  ('reset-observation-spec','spec/public_commands.bend',
   '  S.Abstract{cap, bindings, order, life, counts, cb} = s\n  Returned{S.Abstract{cap, bindings, order, life, T.zero_metrics(), cb}, Counters{counts}, events, 0n}',
   '  S.Abstract{cap, bindings, order, life, +counts, cb} = s\n  Returned{S.Abstract{cap, bindings, order, life, counts, cb}, Counters{counts}, events, 0n}',
   'proofs/configuration_observations.bend','Location: reset'),
  ('native-negation','src/wide.bend',
   '  Word.inc(64n, Word.not(64n, w))', '  Word.inc(64n, w)',
   'proofs/modular_negation.bend','Location: native_negation_refines'),
  ('core-refresh-representation','src/cache.bend',
   'read_live(K, V, State{cap, Map.set(&2, Maybe<&2, T.Entry<K, V>>, m, code, Some{entry}), order, life, counts, cb}',
   'read_live(K, V, State{0n, Map.set(&2, Maybe<&2, T.Entry<K, V>>, m, code, Some{entry}), order, life, counts, cb}',
   'proofs/core_refresh_representation.bend','Location: present~'),
  ('public-add-eviction-flag','src/public.bend',
   'C.store(K, V, c, code, key, value, deadline, evicted, Nil{}), Flag{})',
   'C.store(K, V, c, code, key, value, deadline, False{}, Nil{}), Flag{})',
   'proofs/public_add.bend','Location: lifetime'),
  ('public-expiry-counted-as-eviction','src/public.bend',
   'C.step_cache(K, V, C.remove_oldest(K, V, c, False{})), remaining, shape)',
   'C.step_cache(K, V, C.remove_oldest(K, V, c, True{})), remaining, shape)',
   'proofs/public_aggregate.bend','Location: walk_decide'),
  ('driver-drops-unused-events','src/driver.bend',
   'cache(K, V, outcome), zero_key, zero_value, remaining(K, V, outcome)))',
   'cache(K, V, outcome), zero_key, zero_value, Nil{}))',
   'proofs/public_trace.bend','Location: trace'),
  ('diagnostics-binding-list-spec','spec/public_commands.bend',
   'Storage{List.length(&2, T.Entry<K, V>, O.all_entries(~K, ~same, V, s)), List.length(&2, K, order)',
   'Storage{List.length(&2, T.Entry<K, V>, bindings), List.length(&2, K, order)',
   'proofs/spec_congruence.bend','Location: diagnostics_cong'),
  ('refresh-failure-drops-hit-spec','spec/effectful_operations.bend',
   'refresh_lifetime(~K, ~same, V, O.hit_state(~K, ~same, V, s, key, True{}), T.Item{key, value, deadline}',
   'refresh_lifetime(~K, ~same, V, s, T.Item{key, value, deadline}',
   'proofs/public_refresh.bend','Location: present'),
  ('purge-drops-capacity','src/public.bend',
   'C.State{cap, Map.new(&2, Maybe<&2, T.Entry<K, V>>), Nil{}, life, T.zero_metrics(), cb}',
   'C.State{0n, Map.new(&2, Maybe<&2, T.Entry<K, V>>), Nil{}, life, T.zero_metrics(), cb}',
   'proofs/public_safety.bend','Location: purge_ok'),
  ('integer-key-equality-sign','spec/keys.bend',
   '    case T.Positive{x} T.Negative{y}: False{}',
   '    case T.Positive{x} T.Negative{y}: True{}',
   'proofs/key_equality.bend','Location: integer_sound'),
  ('word64-key-equality-bit','spec/keys.bend',
   '    case True{} False{}: False{}',
   '    case True{} False{}: True{}',
   'proofs/key_equality.bend','Location: bit_sound'),
  ('host-halve-digit','src/host.bend',
   '    case Con{D7{}, t} False{}: prepend(D3{}, halve(t, True{}))',
   '    case Con{D7{}, t} False{}: prepend(D4{}, halve(t, True{}))',
   'proofs/host_binary.bend','Location: halve_value'),
  ('host-binary-carry','src/host.bend',
   '    case 1n+p: split(p, halve(ds, False{}), q => b => attach(b, p, binary(p, q)))',
   '    case 1n+p: split(p, halve(ds, True{}), q => b => attach(b, p, binary(p, q)))',
   'proofs/host_binary.bend','Location: binary_value'),
  ('host-leftover-check','src/host.bend',
   '    case Con{D0{}, t}: zeros(t)',
   '    case Con{D0{}, t}: True{}',
   'proofs/host_binary.bend','Location: zero_value'),
  ('host-int64-upper-bound','src/host.bend',
   '    case Done{+w}: fit(1n+n, msg, w, Bool.not(sign_bit(n, w)))',
   '    case Done{+w}: fit(1n+n, msg, w, True{})',
   'proofs/host_numeric.bend','Location: pos_zero'),
  ('host-sign-mapping','src/host.bend',
   '  fit(1n+n, msg, Word.not(1n+n, k), Bool.not(sign_bit(n, k)))',
   '  fit(1n+n, msg, k, Bool.not(sign_bit(n, k)))',
   'proofs/host_numeric.bend','Location: neg_value'),
  ('host-render-digit','src/host.bend',
   "    case D7{}: '7'",
   "    case D7{}: '1'",
   'proofs/host_render.bend','Location: char_value'),
  ('host-invalid-sample-accepted','src/host.bend',
   '    case Fail{e}: Clock.InvalidSample{e}',
   '    case Fail{e}: Clock.Sample{T.I64{Word.zero(64n)}}',
   'proofs/host_boundary.bend','Location: sample_lift'),
  ('host-loop-drops-event','src/host.bend',
   '  continued(K, V, D.advance(K, V, zero_value, pending, event))',
   '  continued(K, V, D.advance(K, V, zero_value, pending, Clock.ProviderException{"lost"}))',
   'proofs/host_loop.bend','Location: drives'),
  ('host-range-wraps','spec/host.bend',
   '  Nat.is_eq(N.unsigned(width, N.from_nat(width, v)), v)',
   '  Nat.is_eq(v, v)',
   'proofs/host_numeric.bend','Location: fits_bound'),
  ('modular-addition-spec','spec/numeric.bend',
   'T.I64{from_nat(64n, Nat.add(unsigned(64n, x), unsigned(64n, y)))}',
   'T.I64{from_nat(64n, Nat.sub(unsigned(64n, x), unsigned(64n, y)))}',
   'proofs/modular_addition.bend','Location: time_add_refines')]:
  p=dest/relative;original=p.read_text()
  if original.count(old)!=1:raise RuntimeError(name+' mutation target ambiguous')
  p.write_text(original.replace(old,new))
  try:
   proc=subprocess.run([BUN,MAIN,str(dest/proof)],cwd=dest,text=True,capture_output=True,env=ENV,timeout=180)
   if proc.returncode==0 or location not in proc.stdout+proc.stderr:raise AssertionError(name+' was not rejected at its implementation linkage: '+proc.stdout+proc.stderr)
   (ROOT/'build'/('mutation-'+name+'.log')).write_text(proc.stdout+proc.stderr)
  finally:p.write_text(original)
 theorem_mutants=[
  ('prepare-skips-eviction',dest/'src/protocol.bend',
   '    case True{}:\n      detach_oldest(K, V, c)', '    case True{}:\n      C.Out{c, None{}, False{}, Nil{}}'),
  ('entries-reversed',dest/'src/cache.bend',
   '    case Some{e}:\n      Con{e, rest}', '    case Some{e}:\n      List.append(&2, T.Entry<K, V>, rest, Con{e, Nil{}})'),
  ('store-duplicates-recency',dest/'src/cache.bend',
   'deadline}}), List.append(&2, String, without(order, code), Con{code, Nil{}})',
   'deadline}}), List.append(&2, String, order, Con{code, Nil{}})'),
  ('populated-allows-none',dest/'proofs/map_populated.bend',
   'case MLeaf{key, item}: Maybe.is_some(&2, V, item)', 'case MLeaf{key, item}: True{}'),
  ('abstraction-drops-binding',dest/'proofs/refinement.bend',
   '    case Some{entry}:\n      Con{entry, rest}', '    case Some{entry}:\n      rest'),
  ('native-store-put',dest/'src/cache.bend',
   'Map.set(&2, Maybe<&2, T.Entry<K, V>>, m, code, Some{T.Item{key, value, deadline}})',
   'Map.put(&2, Maybe<&2, T.Entry<K, V>>, m, code, Some{T.Item{key, value, deadline}})'),
  ('prefix-bit-omitted',dest/'proofs/invariants.bend',
   'Bool.not(Bool.xor(bit_value(Map.bit(a, p)), bit_value(Map.bit(b, p)))) && same_prefix(a, b, p)',
   'same_prefix(a, b, p)'),
  ('aggregate-failure-prefix',dest/'spec/cache.bend',
   'Fail{PrefixFailed{err, Con{entry, removed}, retained, times}}', 'Fail{PrefixFailed{err, removed, retained, times}}'),
  ('discriminator-order',dest/'proofs/invariants.bend',
   'Nat.is_lt(parent, p)', 'Nat.is_lt(p, parent)'),
  ('lookup-key',dest/'src/cache.bend',
   'None{}, m, code)', 'None{}, m, "")'),
  ('oldest-key',dest/'spec/public_oldest.bend',
   's, key)), key, zero_value, False{}, times}', 's, key)), "", zero_value, False{}, times}'),
  ('wide-addition',dest/'src/wide.bend',
   '  Word.add(64n, a, b)', '  Word.sub(64n, a, b)'),
  ('oldest-value',dest/'spec/public_oldest.bend',
   's, key)), key, zero_value, False{}, times}', 's, key)), key, value, False{}, times}'),
  ('routing-predicate',dest/'proofs/invariants.bend',
   'Bool.not(Bool.xor(bit_value(Map.bit(key, position)), side))','True{}'),
  ('core-deletion',dest/'src/cache.bend',
   'Map.del(&2, Maybe<&2, T.Entry<K, V>>, m, key)','m')]
 for name,path,old,new in theorem_mutants:
  original=path.read_text()
  if original.count(old)!=1:raise RuntimeError(name+' mutation target ambiguous')
  path.write_text(original.replace(old,new))
  try:
   proc=subprocess.run([BUN,MAIN,str(dest/'PROOF.bend')],cwd=dest,text=True,capture_output=True,env=ENV,timeout=180)
   if proc.returncode==0 or 'expected' not in proc.stdout+proc.stderr:raise AssertionError(name+' theorem mutant not rejected')
   (ROOT/'build'/('mutation-'+name+'.log')).write_text(proc.stdout+proc.stderr)
  finally:path.write_text(original)
 mutants=[
  ('recency',dest/'src/cache.bend',
   '      List.append(&2, String, without(order, code), Con{code, Nil{}})',
   '      order','boundary','AssertionError'),
  ('map-removal',dest/'src/cache.bend',
   'Map.del(&2, Maybe<&2, T.Entry<K, V>>, m, key)',
   'm','TestLRU_Remove','map/recency invariant failed'),
  ('removal-order',dest/'src/cache.bend',
   '      remove_encoded(K, V, c, k, evict)',
   '      remove_encoded(K, V, c, List.last.go(&2, String, rest, k), evict)','TestLRU_RemoveOldest','AssertionError')]
 for name,path,old,new,case,diagnostic in mutants:
  original=path.read_text()
  if original.count(old)!=1:raise RuntimeError(name+' mutation target ambiguous')
  path.write_text(original.replace(old,new))
  try:
   proc=subprocess.run(bun(dest/'tests/new/upstream.ts')+[case],cwd=dest,text=True,capture_output=True,env=ENV,timeout=180)
   if proc.returncode==0 or diagnostic not in proc.stderr:raise AssertionError(name+' mutant not rejected by semantic check: '+proc.stderr)
   (ROOT/'build'/('mutation-'+name+'.log')).write_text(proc.stdout+proc.stderr)
  finally:path.write_text(original)
 p=dest/'src/public.bend';original=p.read_text()
 old='    case True{}: C.remove_oldest(K, V, c, True{})'
 if original.count(old)!=1:raise RuntimeError('pre-clock counter mutation target ambiguous')
 p.write_text(original.replace(old,'    case True{}: C.remove_oldest(K, V, c, False{})'))
 try:
  proc=subprocess.run(bun(dest/'tests/new/clock_failures.ts'),cwd=dest,text=True,capture_output=True,env=ENV,timeout=180)
  if proc.returncode==0 or 'AssertionError' not in proc.stderr:raise AssertionError('pre-clock counter mutant not rejected: '+proc.stderr)
  (ROOT/'build/mutation-pre-clock-counter.log').write_text(proc.stdout+proc.stderr)
 finally:p.write_text(original)
 return {'status':'passed','mutants':['full-cache specification requires overflow instead of equality: actual full Add dispatch correspondence fails','refresh specification returns old deadline: actual refreshed observation correspondence fails','removal specification omits Removals increment: actual removal state correspondence fails','live read specification omits Hits increment: actual live state correspondence fails','absent read specification omits Misses increment: actual absent branch correspondence fails','negative duration divides unsigned bits: signed magnitude linkage fails','zero-duration specification returns clock sample: actual deadline correspondence fails','divider clears selected quotient bit: actual result conservation linkage fails','divider omits remainder subtraction: actual recursive bound theorem fails','divider triples prior remainder: actual digit recurrence theorem fails','reset specification retains counters: actual clear_metrics observation refinement fails','native negation omits complement: actual twos-complement theorem fails','core refresh resets capacity to zero: actual refresh representation theorem fails','independent addition specification changed to subtraction: actual Time.add refinement fails','refresh miss resets capacity to zero: full representation preparation theorem fails','refresh preparation queries wrong code: actual returned-state lookup law fails','store loses retained recency: existing recency-uniqueness linkage rejects changed implementation','full preparation skips eviction: existing protocol storage theorem fails','entry enumeration reverses recency: exact abstraction sequence theorem fails','store appends duplicate recency code: actual store uniqueness theorem fails','populated predicate permits stored None: native no-None preservation proof fails','abstraction discards present binding: actual abstraction retention theorem fails','native store uses put instead of set: actual store/lookup theorem fails','prefix predicate omits a bit: skipped-prefix rejection theorem fails','lost completed prefix on clock failure: specification law fails (not implementation refinement)','expired predicate forced false: boundary assertion fails','binary bit encoder collapses bits: round-trip theorem fails','comparison tag forced EQ: comparator preservation theorem fails','Get omits recency movement: order assertion fails','native Map deletion omitted: map/recency invariant fails','newest-first removal: RemoveOldest result assertion fails','store writes None: actual store/lookup theorem fails','routing predicate forced true: predicate-to-routing theorem fails','core deletion omitted: actual removal/lookup theorem fails','expired oldest returns stale value: public observation theorem fails','64-bit addition changed to subtraction: conservation theorem fails','expired oldest loses original key: public observation theorem fails','native lookup queries empty key: actual store/lookup linkage fails','reversed discriminator ordering: native deletion ordering proof fails','eviction miscounted before failed clock: actual public Bend machine state assertion fails','public Add reply ignores pre-clock eviction: public Add refinement fails','expiry walk counts removals as evictions: public aggregate refinement fails','driver drops unused provider events between requests: trace refinement fails','diagnostics count raw binding list: specification congruence fails','refresh failure specification drops committed hit: public refresh refinement fails','Purge resets capacity to zero: public reachability fails','Integer specification key equality identifies opposite signs: equality soundness proof fails','Word64 specification bit equality identifies distinct bits: equality soundness proof fails','host decimal halving table wrong digit: halving value proof fails','host binary conversion starts with a carry: binary reconstruction proof fails','host range check accepts nonzero leftover: zero-leftover proof fails','host int64 reader accepts values at or above 2^63: nonnegative range proof fails',"host int64 reader drops the two's-complement negation: negative mapping proof fails",'host decimal rendering emits a wrong digit: character value proof fails','host invalid clock sample treated as a sample: sample boundary proof fails','host step ignores the provider event: host loop equals D.drive proof fails','host range condition accepts every value (wrapping): fits-implies-bound proof fails']}

def transport_sensitivity():
 checks=[('missing output',[sys.executable,'-c','pass'],None,5),
   ('malformed output',[sys.executable,'-c','print("not json")'],None,5),
   ('backend failure',[sys.executable,'-c','print("{} ");raise SystemExit(7)'],None,5),
   ('timeout',[sys.executable,'-c','import time;time.sleep(2)'],None,0.05),
   ('unsupported operation',bun(ROOT/'tests/new/trace.ts'),json.dumps({'capacity':1,'ops':[{'op':'unsupported'}]}),30),
   ('unknown input field',bun(ROOT/'tests/new/trace.ts'),json.dumps({'capacity':1,'ops':[],'unexpected':True}),30),
   ('null operation',bun(ROOT/'tests/new/trace.ts'),json.dumps({'capacity':1,'ops':[None]}),30),
   ('unknown operation field',bun(ROOT/'tests/new/trace.ts'),json.dumps({'capacity':1,'ops':[{'op':'Len','unexpected':0}]}),30),
   ('numeric token loses exactness',bun(ROOT/'tests/new/trace.ts'),json.dumps({'capacity':1,'ops':[{'op':'Add','value':9007199254740993}]}),30),
   ('null string key',bun(ROOT/'tests/new/trace.ts'),json.dumps({'capacity':1,'ops':[{'op':'Get','key':None}]}),30),
   ('excluded callback registration',bun(ROOT/'tests/new/trace.ts'),json.dumps({'capacity':1,'ops':[{'op':'SetOnEvict','enabled':True}]}),30)]
 for name,args,payload,timeout in checks:
  try:backend(args,payload=payload,timeout=timeout)
  except (RuntimeError,subprocess.TimeoutExpired):continue
  raise AssertionError(name+' was accepted')
 return {'status':'passed','rejected':[x[0] for x in checks]}

REQUIRED_THEOREMS={
 'public_initialization':['Initial.new_with_size_refines'],
 'public_string_request':['PublicRelation.results(~String, ~SpecLookup.string_same, V, ActualDriver.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request), PublicSpec.execute('],
 'public_string_request_safe':['PublicSafety.outcome_ok(V, ActualDriver.execute('],
 'public_string_trace':['PublicTrace.created_rel(V, zero_key, zero_value, requests, events, C.new_with_size(String, V, capacity, size), S.new_with_size(String, V, capacity, size))'],
 'public_integer_trace':['PublicKeys.created_rel(~T.Integer, ~Codec.integer_encode, ~SpecKeys.integer_same, V, zero_key, zero_value, requests, events, C.new_with_size(T.Integer, V, capacity, size), S.new_with_size(T.Integer, V, capacity, size))'],
 'public_word64_trace':['PublicKeys.created_rel(~Word(64n), ~Codec.word64_encode, ~SpecKeys.word64_same, V, zero_key, zero_value, requests, events, C.new_with_size(Word(64n), V, capacity, size), S.new_with_size(Word(64n), V, capacity, size))'],
 'spec_integer_equality_sound':['{a == b : T.Integer}'],
 'spec_integer_equality_reflexive':['{SpecKeys.integer_equal(a, a) == True{} : Bool}'],
 'spec_word64_equality_sound':['{a == b : Word(64n)}'],
 'spec_word64_equality_reflexive':['{SpecKeys.bits_equal(64n, a, a) == True{} : Bool}'],
 'drive_finished':['ActualDriver.drive(K, V, zero_value, events, ActualPublic.Finished{c, answer}) == ActualDriver.Returned{c, answer, events, 0n}'],
 'drive_advance':['HostStep.continue(K, V, zero_value, ActualDriver.advance(K, V, zero_value, pending, event), tail)'],
 'host_fits_meaning':['{HostSpec.fits(n, v) == True{} : Bool}'],
 'host_fits_bound':['h: {HostSpec.fits(n, v) == True{} : Bool}) -> {Nat.is_lt(v, Nat.pow(2n, n)) == True{} : Bool}'],
 'host_uint64_key':['{Host.uint64_key(s) == HostNumeric.lift(64n, "uint64 key", HostSpec.unsigned_text(64n, s))'],
 'host_int64_key':['{Host.int64_key(s) == HostNumeric.lift(64n, "int64 key", HostSpec.int64_text(s))'],
 'host_uint64_text':['{HostSpec.natural(Host.uint64_text(w)) == Some{NumericSpec.unsigned(64n, w)}'],
 'host_int64_text':['{HostSpec.int64_text(Host.int64_text(w)) == Some{w}'],
 'host_uint64_roundtrip':['{Host.uint64_key(Host.uint64_text(w)) == Done{w}'],
 'host_int64_roundtrip':['{Host.int64_key(Host.int64_text(w)) == Done{w}'],
 'host_string_key':['{Host.string_key(s) == HostBoundary.accept(s, HostSpec.scalar(s))'],
 'host_time':['{Host.time(s) == HostBoundary.time_spec(HostSpec.int64_text(s))'],
 'host_sample':['{Host.sample(s) == HostBoundary.sample_spec(HostSpec.int64_text(s))'],
 'host_thrown':['{Host.thrown() == ProviderClock.ProviderException{'],
 'host_create':['{Host.create(K, V, capacity, size) == HostBoundary.create_spec(K, V, HostSpec.unsigned_text(32n, capacity), HostSpec.unsigned_text(32n, size))'],
 'host_loop_drive':['{HostLoop.loop(K, V, zero_value, events, Host.act(K, V, progress)) == ActualDriver.drive(K, V, zero_value, events, progress)'],
 'host_loop_string':['{HostLoop.loop(String, V, zero_value, events, Host.begin(String, V, Codec.string_encode, zero_key, zero_value, c, request)) == ActualDriver.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request)'],
 'host_loop_word64':['{HostLoop.loop(Word(64n), V, zero_value, events, Host.begin(Word(64n), V, Codec.word64_encode, zero_key, zero_value, c, request)) == ActualDriver.execute(~Word(64n), ~Codec.word64_encode, V, zero_key, zero_value, c, events, request)'],
 'actual_limb_encoding':['NativeWide.pack(low, high)'],
 'actual_limb_roundtrip':['NativeWide.unpack(NativeWide.pack(low, high)) == (low, high)'],
 'actual_limb_decoding':['LimbDecoding.value(NativeWide.unpack(word))']}
FORBIDDEN=re.compile(r'\baxiom\b|\bunsafe\b|\badmit\b|\bsorry\b|\?[A-Za-z_]')
# Every Bend host function the adapter calls, and the END_TO_END law that
# states its meaning. H.keys/H.consistent are test self-checks (CheckInvariants).
ADAPTER_COVERAGE={'uint64_key':'host_uint64_key','int64_key':'host_int64_key','uint64_text':'host_uint64_text',
 'int64_text':'host_int64_text','string_key':'host_string_key','time':'host_time','sample':'host_sample',
 'thrown':'host_thrown','create':'host_create','begin':'host_loop_string','answer':'host_loop_drive'}
ADAPTER_TEST_ONLY={'keys','consistent'}
TRUSTED_RESIDUE=['Bend 2.0.5 checker and primitive Base semantics; Bun/JS runtime, compiler and hardware',
 'JS runtime decimal text conversion of integers: String(bigint) into Bend and BigInt(text) out of Bend (compiled Bend Nat holds at most 2^48-1, so 64-bit values cannot cross as Nat); validated by tests/new/host_bridge.ts',
 'the clock provider call and catching its exception (src/adapter.ts run), identity passing of Bend values and constructor-tag checks']

def strip_ts(text):
 text=re.sub(r'/\*.*?\*/',' ',text,flags=re.S)
 text=re.sub(r'//[^\n]*',' ',text)
 return re.sub(r"'(?:\\.|[^'\\])*'|\"(?:\\.|[^\"\\])*\"",'""',text)

def adapter_residue(source):
 code=strip_ts(source)
 problems=[]
 for pattern,what in [(r'<<|>>','bit shift'),(r'asUintN|asIntN','BigInt width reduction'),(r'\bNumber\s*\(','Number conversion'),
   (r'\bMath\.','Math arithmetic'),(r'[*/%^~]','arithmetic operator'),(r'(?<![&])&(?![&])','bitwise and'),(r'(?<![|])\|(?![|])','bitwise or'),
   (r'[+-]','addition/subtraction or negation'),(r'\b(?!0n\b)\d+n\b','bigint literal other than 0n')]:
  if re.search(pattern,code):problems.append(what)
 for m in re.finditer(r'\bBigInt\s*\(([^()]*(?:\([^()]*\)[^()]*)*)\)',code):
  if not (m.group(1).startswith('H.') or m.group(1)=='Date.now()'):problems.append('BigInt conversion of '+m.group(1))
 for m in re.finditer(r'\bString\s*\(([^)]*)\)',code):
  if m.group(1)!='n':problems.append('String conversion of '+m.group(1))
 imports=re.findall(r'^import .*? from "(.*?)"|^import .*? from \'(.*?)\'',source,re.M)
 for pair in re.findall(r"^import [^\n]*? from ['\"](.*?)['\"]",source,re.M):
  if pair not in ('./host.bend','./codec.bend'):problems.append('import of '+pair)
 for name in set(re.findall(r'\bH\.(\w+)\s*\(',code)):
  if name not in ADAPTER_COVERAGE and name not in ADAPTER_TEST_ONLY:problems.append('uncovered Bend call H.'+name)
 check=code[code.index('CheckInvariants()'):] if 'CheckInvariants()' in code else ''
 for name in ADAPTER_TEST_ONLY:
  if re.search(r'\bH\.'+name+r'\s*\(',code.replace(check,'')):problems.append('test-only H.'+name+' used outside CheckInvariants')
 return problems

def full_scope(checks):
 for name in ['checker','sensitivity','differential','boundary','clock_failures','host_bridge']:
  if checks.get(name,{}).get('status')!='passed':raise AssertionError('prerequisite check failed: '+name)
 if 'import ./END_TO_END.bend' not in (ROOT/'PROOF.bend').read_text():raise AssertionError('PROOF.bend does not import END_TO_END.bend')
 end=(ROOT/'END_TO_END.bend').read_text()
 for name,parts in REQUIRED_THEOREMS.items():
  m=re.search(r'^(?:law '+name+r':\n(?:  .*\n)+)?def '+name+r'\b.*(?:\n  .*)*',end,re.M)
  if not m:raise AssertionError('missing END_TO_END theorem '+name)
  for part in parts:
   if part not in m.group(0):raise AssertionError(name+' statement changed: '+part)
 for law in set(ADAPTER_COVERAGE.values()):
  if law not in REQUIRED_THEOREMS:raise AssertionError('adapter coverage law not required: '+law)
 files=[p for d in ['src','spec','proofs','types'] for p in (ROOT/d).glob('*.bend')]+[ROOT/'END_TO_END.bend',ROOT/'PROOF.bend']
 for p in files:
  text=p.read_text();code='\n'.join(l.split('#')[0] for l in text.splitlines())
  if FORBIDDEN.search(code):raise AssertionError('forbidden proof escape in '+str(p.relative_to(ROOT)))
  defs=set(re.findall(r'^def ([\w.]+)',text,re.M))
  for law in re.findall(r'^law (\w+)',text,re.M):
   if law not in defs:raise AssertionError('law without proof: '+law)
  if p.parent.name=='spec':
   for line in text.splitlines():
    if line.startswith('import') and ('src/' in line or 'proofs/' in line):raise AssertionError('specification imports implementation/proof: '+str(p))
 adapter=(ROOT/'src/adapter.ts').read_text()
 problems=adapter_residue(adapter)
 if problems:raise AssertionError('adapter exceeds the trusted residue: '+'; '.join(sorted(set(problems))))
 # The residue check must reject reintroduced host arithmetic.
 probes={'asUintN':'const w = BigInt.asUintN(64, key);','shift':'const hi = key >> 32n;','mask':'const lo = Number(key & 0xffffffffn);',
  'add':'const next = key + 1n;','negate':'const neg = -key;','uncovered call':'H.halve(x, y);','import':"import W from './wide.bend';"}
 for name,line in probes.items():
  mutated=adapter.replace('export class LRU',line+'\nexport class LRU',1) if name!='import' else line+'\n'+adapter
  if not adapter_residue(mutated):raise AssertionError('residue gate accepted '+name)
 return {'status':'passed','theorems':sorted(REQUIRED_THEOREMS),'adapter_calls':ADAPTER_COVERAGE,
  'test_only_calls':sorted(ADAPTER_TEST_ONLY),'gate_probes_rejected':sorted(probes),'trusted':TRUSTED_RESIDUE}

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--report',required=True);args=parser.parse_args()
 report={'upstream_cases':[],'checks':{},'complete':False,'exclusions':{'authorization':'callback-exclusions.json','archive':'tests/new/callback-archive.json','counted_as_passes':False}}
 manifest=json.loads((ROOT/'tests.manifest.json').read_text());names=[r['name'] for r in manifest]
 if len(names)!=len(set(names)):raise RuntimeError('duplicate frozen manifest names')
 ROOT.joinpath('build').mkdir(exist_ok=True)
 for name in names:
  try:
   row=backend(bun(ROOT/'tests/new/upstream.ts')+[name],timeout=600)
   if not isinstance(row,dict) or row.get('name')!=name or row.get('status')!='passed' or not isinstance(row.get('assertions'),int):raise RuntimeError('invalid case result')
  except Exception as e:row={'name':name,'status':'failed','error':str(e)}
  report['upstream_cases'].append(row);print(name,row['status'],flush=True)
 for name,fn in [
  ('checker',lambda:{'status':'passed','output':command([BUN,MAIN,'PROOF.bend'])}),
  ('assertion_inventory',assertion_inventory),
  ('spec_templates',lambda:{'status':'passed','output':command([BUN,MAIN,'tests/new/spec_smoke.bend'])}),
  ('boundary',lambda:backend(bun(ROOT/'tests/new/upstream.ts')+['boundary'])),
  ('clock_failures',lambda:backend(bun(ROOT/'tests/new/clock_failures.ts'))),
  ('host_bridge',lambda:backend(bun(ROOT/'tests/new/host_bridge.ts'))),
  ('differential',differential),('numeric_boundaries',numeric_boundaries),('sensitivity',sensitivity),('transport_sensitivity',transport_sensitivity)]:
  try:report['checks'][name]=fn()
  except Exception as e:report['checks'][name]={'status':'failed','error':str(e)}
  print(name,report['checks'][name]['status'],flush=True)
 # Composition gate: the checker result alone establishes only what is written,
 # so require the complete set of composed END_TO_END statements, the PROOF
 # import, proof-closure hygiene, specification independence and the adapter
 # wiring to the proved machine. Fails unless every item holds.
 try:report['checks']['full_scope']=full_scope(report['checks'])
 except Exception as e:report['checks']['full_scope']={'status':'failed','error':str(e)}
 print('full_scope',report['checks']['full_scope']['status'],flush=True)
 report['complete']=all(r['status']=='passed' for r in report['upstream_cases']) and all(r['status']=='passed' for r in report['checks'].values())
 path=Path(args.report);path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(report,indent=2)+'\n')
 return 0 if report['complete'] else 1
if __name__=='__main__':sys.exit(main())

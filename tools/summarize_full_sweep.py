#!/usr/bin/env python3
"""Render all rows, per-structure coverage, failures and slowest results."""
import collections,json,statistics,sys
from pathlib import Path
root=Path(__file__).resolve().parents[1]
report=Path(sys.argv[1]) if len(sys.argv)>1 else root/'build/nonempty-full-sweep/report.json'
d=json.loads(report.read_text());rows=d['benchmarks'];limit=d['max_ratio']
def number(ns):
    return f'{ns/1e6:.3f} ms' if ns>=1e6 else f'{ns/1e3:.3f} µs' if ns>=1e3 else f'{ns:.3f} ns'
counts=collections.defaultdict(lambda:{'measured':0,'pass':0,'slow':0,'fail':0,'worst':None})
for r in rows:
    name=r['operation'].split('.')[0];c=counts[name]
    if r.get('measurement')!='ok' or not r.get('verified'):c['fail']+=1;continue
    c['measured']+=1;ratio=r['ratio'];c['pass' if ratio<=limit else 'slow']+=1
    if c['worst'] is None or c['worst']['ratio']<ratio:c['worst']=r
slow=sorted((r for r in rows if r.get('measurement')=='ok' and r.get('verified') and r['ratio']>limit),key=lambda r:r['ratio'],reverse=True)
failed=[r for r in rows if r.get('measurement')!='ok' or not r.get('verified')]
lines=[f"# Nonempty DSA sweep: {d['status']}", '',f"{len(rows)}/{d['expected_rows']} rows recorded. {len(d['excluded_empty_rows'])} empty timing rows excluded by user instruction. Threshold: {limit}x optimized C.",'', '| Structure | Passed | Slow | Failed | Worst measured ratio |','|---|---:|---:|---:|---|']
for name,c in sorted(counts.items()):
    w=c['worst'];worst=f"{w['ratio']:.3f}x — {w['operation'].split('.',1)[1]}/{w['workload']}" if w else '—'
    lines.append(f"| {name} | {c['pass']} | {c['slow']} | {c['fail']} | {worst} |")
lines+=['','## Every slow workload','','| Operation | Workload | Bend | C | Ratio |','|---|---|---:|---:|---:|']
for r in slow:lines.append(f"| {r['operation']} | {r['workload']} | {number(statistics.median(r['bend_ns']))} | {number(statistics.median(r['reference_ns']))} | {r['ratio']:.3f}x |")
lines+=['','## Failures','']
lines += [f"- {r['operation']}/{r['workload']}: {r.get('reason','checksum mismatch')}" for r in failed] or ['None.']
lines+=['','## All rows','','| Operation | Workload | Bend | C | Ratio | Status |','|---|---|---:|---:|---:|---|']
for r in rows:
    ok=r.get('measurement')=='ok' and r.get('verified')
    cells=[number(statistics.median(r[x])) for x in ['bend_ns','reference_ns']] if ok else ['—','—']
    ratio=f"{r['ratio']:.3f}x" if ok else '—';status=('PASS' if r['ratio']<=limit else 'SLOW') if ok else 'FAILED'
    lines.append(f"| {r['operation']} | {r['workload']} | {cells[0]} | {cells[1]} | {ratio} | {status} |")
(report.parent/'RUNDOWN.md').write_text('\n'.join(lines)+'\n')
print('\n'.join(lines[:6+len(counts)]));print('Total:',sum(c['pass'] for c in counts.values()),'pass,',len(slow),'slow,',len(failed),'failed')

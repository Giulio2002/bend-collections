#!/usr/bin/env python3
"""Render explicitly separate candidate and final LRU evidence."""
import html,json,statistics,sys
from pathlib import Path

def render(report,output,final=None):
 output=Path(output);output.parent.mkdir(parents=True,exist_ok=True)
 d=json.loads(Path(report).read_text()) if Path(report).exists() else {'status':'candidate screen not supplied','benchmarks':[]}
 rows=[]
 for r in d['benchmarks']:
  bn=statistics.median(r['bend_ns']) if r.get('bend_ns') else None
  cn=statistics.median(r['reference_ns']) if r.get('reference_ns') else None
  cols=[r['candidate'],r['operation'],r['workload'],f'{bn:.3f}' if bn else '—',f'{cn:.3f}' if cn else '—',f"{r['ratio']:.3f}×" if 'ratio' in r else 'FAILED',str(r.get('verified',False)),r.get('reason','')]
  rows.append('<tr>'+''.join('<td>'+html.escape(c)+'</td>' for c in cols)+'</tr>')
 page='''<!doctype html><meta charset="utf-8"><meta name="viewport" content="width=device-width"><meta http-equiv="refresh" content="30"><title>LRU optimization</title><style>body{font:16px system-ui;background:#111827;color:#e5e7eb;margin:32px}a{color:#93c5fd}td,th{padding:10px;border-bottom:1px solid #374151;text-align:left}table{border-collapse:collapse;width:100%}p{max-width:1100px;line-height:1.6}</style><h1>LRU optimization</h1>'''
 page+='<p>Status: <b>'+html.escape(d['status'])+'</b>. <a href="dsa-benchmarks.html">Frozen full DSA sweep</a>.</p>'
 page+='''<p>Candidate screening is separate from acceptance. Each candidate uses the same optimized C, public operations, inputs, six samples and timing thresholds. No FFI or generated-C modifications. The candidate screen covers selected medium workloads; it does not establish the 51-row target.</p><p>Before = original; native-zero = packed zero test and one lifetime decode; native-packed = signed packed expiry comparison; native-promote = fused DLL detach/append using the shared link-write primitive. All use Base.Map lookup. Both custom lookup experiments were rejected because they regressed add/get/peek. Changes are cumulative.</p><p>Proofs: universal local equivalence, plus the existing conditional operation-trace refinement for U32 and String pass. 2,208 native C/sanitizer differential cases pass. The laws reject three deliberate mutations. Existing trusted unsafe annotations remain; no new axioms or unsafe declarations were added. Whole-library formal verification remains incomplete.</p><p>Isolated-removal calibration had an invalid cap and could exhaust the cache. The rerun caps both sides identically at size/2. Invalid initial attempts remain failures. Metrics still use the legacy Word64 output representation, and deadline creation still performs the legacy nanosecond conversion: both remain performance costs.</p>'''
 page+='<table><thead><tr>'+''.join('<th>'+c+'</th>' for c in ['Candidate','Operation','Workload','Bend ns/op','C ns/op','Bend / C','Checksum verified','Failure'])+'</tr></thead><tbody>'+''.join(rows)+'</tbody></table>'
 if final and Path(final).exists():
  f=json.loads(Path(final).read_text());raw=output.with_name(output.stem+'-final.json');raw.write_text(json.dumps(f,indent=1)+'\n');page+='<p><a href="'+raw.name+'">Final rerun: raw samples, checksums, source and binary hashes</a></p>';page+='<h2>Selected implementation: all LRU workloads</h2><p>Status: '+html.escape(f.get('status','finished'))+'</p><table><tr><th>Operation</th><th>Workload</th><th>Bend ns/op</th><th>C ns/op</th><th>Ratio</th><th>Status</th></tr>'
  for r in f['benchmarks']:
   bn=statistics.median(r['bend_ns']) if r.get('bend_ns') else None;cn=statistics.median(r['reference_ns']) if r.get('reference_ns') else None;ratio=bn/cn if bn and cn else None
   cols=[r['operation'],r['workload'],f'{bn:.3f}' if bn else '—',f'{cn:.3f}' if cn else '—',f'{ratio:.3f}×' if ratio else '—',('PASS' if ratio<=2.5 else 'SLOW') if ratio and r.get('verified') else 'FAILED: '+r.get('reason','checksum')]
   page+='<tr>'+''.join('<td>'+html.escape(c)+'</td>' for c in cols)+'</tr>'
  page+='</table>'
 output.write_text(page);output.with_suffix('.json').write_text(json.dumps(d,indent=1)+'\n')
if __name__=='__main__':render(*sys.argv[1:])

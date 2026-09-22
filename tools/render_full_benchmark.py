#!/usr/bin/env python3
"""Render current full-sweep evidence, including pending and failed rows."""
import argparse, collections, datetime, html, json, statistics, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'benchmarks'))
from workloads import TABLE

def render(report, output):
 output=Path(output);output.parent.mkdir(parents=True,exist_ok=True)
 found={(r['operation'],r['size'],r['workload']):r for r in report['benchmarks']}
 groups=collections.defaultdict(lambda:collections.Counter());rows=[]
 def fmt(x):return '—' if x is None else f'{x:,.3f}'
 for w in TABLE:
  r=found.get((w['operation'],w['size'],w['workload']),{})
  ratio=r.get('ratio'); good=r.get('verified',False)
  state='pending' if not r else 'failed' if ratio is None or not good else 'pass' if ratio<=report['max_ratio'] else 'slow'
  groups[w['structure']][state]+=1
  bn=statistics.median(r['bend_ns']) if r.get('bend_ns') else None
  cn=statistics.median(r['reference_ns']) if r.get('reference_ns') else None
  reason=r.get('reason','checksum mismatch' if r and ratio is not None and not good else '')
  rows.append(f'<tr class="{state}"><td>{html.escape(w["operation"])}</td><td>{w["size"]:,}</td><td>{html.escape(w["workload"])}</td><td>{state}</td><td>{fmt(bn)}</td><td>{fmt(cn)}</td><td>{fmt(ratio)}{ "×" if ratio is not None else ""}</td><td>{html.escape(reason)}</td></tr>')
 totals=sum(groups.values(),collections.Counter());now=datetime.datetime.now().astimezone().isoformat(timespec='seconds')
 title=f'{len(found)}/{len(TABLE)} measured · {totals["pass"]} within target · {totals["slow"]} slow · {totals["failed"]} failed · {totals["pending"]} pending'
 summary=''.join(f'<tr><td>{html.escape(k)}</td>'+''.join(f'<td>{v[s]}</td>' for s in ['pass','slow','failed','pending'])+'</tr>' for k,v in sorted(groups.items()))
 builds=''.join(f'<li>{html.escape(k)}: {html.escape(v)}</li>' for k,v in report.get('build_failures',{}).items())
 page='''<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width"><meta http-equiv="refresh" content="30"><title>Bend collections — full benchmark</title><style>body{background:#111827;color:#e5e7eb;font:15px system-ui;margin:28px}a{color:#93c5fd}table{border-collapse:collapse;width:100%;margin:20px 0}td,th{padding:9px;border-bottom:1px solid #374151;text-align:left}th{background:#1f2937;position:sticky;top:0}.slow{color:#fca5a5}.pass{color:#86efac}.failed{color:#fcd34d}.pending{color:#9ca3af}p{max-width:1100px;line-height:1.6}input,select{padding:10px;background:#1f2937;color:white;border:1px solid #64748b}td:last-child{max-width:460px;overflow-wrap:anywhere}</style></head><body>'''
 page+=f'<h1>Bend collections — full benchmark</h1><p>Updated {now} · Run status: <b>{html.escape(report["status"])}</b> · elapsed {report.get("seconds",0)/60:.1f} minutes.</p><h2>{title}</h2>'
 page+='<p>The bulk fold API has been removed. TreeMap range and traversal use ordinary editable iterators again; the earlier iterator optimizations remain. This is a fresh full sweep, not a mixture of historical and new timings. The C references and workloads are unchanged. DSA auto-implementer remains stopped.</p><p>Target: Bend / optimized C ≤2.5× for each workload. Six samples per measured row, alternating timed-region order, calibrated batch lengths, checksum agreement and minimum timing deltas. Empty benchmarks remain excluded. A failed or pending row is not a pass. Restore-pair operations include the documented reinsertion/rebuild work on both sides. Other machine jobs may affect timings.</p>'
 page+='<p>Proof status: 16 indexed TreeMap component laws and three local traversal laws pass. The removed fold proofs no longer count. Full indexed TreeMap refinement and the whole-library proof gate remain unfinished.</p>'
 page+=f'<p><a href="{output.stem}.json">Raw samples, source hashes and environment</a></p>'
 if report.get('source_unchanged') is False:page+='<p class="failed">Source changed during measurement: results do not establish current-source acceptance.</p>'
 if builds:page+='<h2>Build failures</h2><ul>'+builds+'</ul>'
 page+='<h2>By collection</h2><table><thead><tr><th>Collection</th><th>Within target</th><th>Slow</th><th>Failed</th><th>Pending</th></tr></thead><tbody>'+summary+'</tbody></table>'
 page+='<h2>Every workload</h2><input id="query" placeholder="Filter collection / operation"><select id="state"><option value="">All statuses</option><option>slow</option><option>failed</option><option>pending</option><option>pass</option></select><table id="workloads"><thead><tr><th>Operation</th><th>Size</th><th>Workload</th><th>Status</th><th>Bend ns/op</th><th>C ns/op</th><th>Bend / C</th><th>Failure detail</th></tr></thead><tbody>'+''.join(rows)+'</tbody></table><script>function filter(){document.querySelectorAll("#workloads tbody tr").forEach(r=>r.hidden=(!r.textContent.toLowerCase().includes(query.value.toLowerCase())||(state.value&&r.className!==state.value)))}query.oninput=state.onchange=filter;</script></body></html>'
 for path,data in [(output,page),(output.with_suffix('.json'),json.dumps(report,indent=1)+'\n')]:
  temp=path.with_suffix(path.suffix+'.tmp');temp.write_text(data);temp.replace(path)
 assessment=output.parent.parent/'assessment.json'
 if assessment.exists():
  d=json.loads(assessment.read_text());v=d['projects']['dsa'];v.update(reviewed_at=now,performance_status=title,pace='Fresh full sweep: '+report['status'],implementation_missing='Optimize slow rows and resolve failed measurements; full formal verification remains open.',proof_status='TreeMap: 16 component and 3 traversal laws pass; no bulk-fold API/proofs. Full indexed refinement and whole-library proof gate incomplete.')
  temp=assessment.with_suffix('.tmp');temp.write_text(json.dumps(d,indent=2)+'\n');temp.replace(assessment)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('report',type=Path);p.add_argument('output',type=Path);a=p.parse_args();render(json.loads(a.report.read_text()),a.output)

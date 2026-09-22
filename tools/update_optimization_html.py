#!/usr/bin/env python3
"""Render the manual optimization report without touching other projects."""
import argparse,datetime,html,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser();p.add_argument('--before',type=Path,required=True);p.add_argument('--after',type=Path);p.add_argument('--iterator-report',type=Path);p.add_argument('--tree-report',type=Path);p.add_argument('--tree-map-report',type=Path);p.add_argument('--range-report',type=Path);p.add_argument('--fold-report',type=Path);p.add_argument('--ownership-report',type=Path);p.add_argument('--note',default='Optimization in progress');a=p.parse_args()
b=json.loads(a.before.read_text());c=json.loads(a.after.read_text()) if a.after else b
old={x['operation']:x for x in b['results']};rows=[]
for x in sorted(c['results'],key=lambda x:x['operation']):
 o=old.get(x['operation'],{});br=o.get('ratio');cr=x.get('ratio');color='bad' if cr and cr>2.5 else 'good' if cr else 'unknown'
 fmt=lambda n: '—' if n is None else f'{n:.2f}×'
 rows.append(f'<tr class="{color}"><td>{html.escape(x["operation"])}</td><td>{fmt(br)}</td><td>{fmt(cr)}</td><td>{html.escape(x["status"])}</td><td>{x.get("bend_ns",0):.2f}</td><td>{x.get("c_ns",0):.2f}</td><td>{html.escape(x.get("method",""))}</td></tr>')
now=datetime.datetime.now().astimezone().isoformat(timespec='seconds');slow=sum(x.get('ratio',0)>2.5 for x in c['results']);unknown=sum('ratio' not in x for x in c['results'])
page='''<!doctype html><meta charset="utf-8"><meta name="viewport" content="width=device-width"><title>Bend collections optimization</title><style>body{background:#111827;color:#e5e7eb;font:16px system-ui;margin:32px}a{color:#93c5fd}table{border-collapse:collapse;width:100%}td,th{padding:10px;text-align:left;border-bottom:1px solid #374151}.bad td:nth-child(3){color:#f87171}.good td:nth-child(3){color:#4ade80}.unknown{color:#fbbf24}th{position:sticky;top:0;background:#1f2937}p{max-width:1100px;line-height:1.5}input{padding:10px;margin:15px 0;width:350px}</style>'''
page+=f'<h1>Bend collections — manual optimization</h1><p>Updated {now}. DSA auto-implementer remains stopped.</p><p>{html.escape(a.note)}</p><p><b>{len(c["results"])} operations · {slow} above 2.5× · {unknown} unresolved timings · {c["seconds"]:.2f}s quick sweep</b></p><p>Ratios are Bend / optimized C. One smallest nonempty workload per operation. Quick estimates are noisy and are not full acceptance. No performance claim for unresolved rows. Get/pop/remove rows may include restoring insertion on both sides. C reference unchanged.</p><p>Implementation: stack, arena DLL, two-list queue/deque, array heap, red-black tree and remaining collections. No segment tree, union-find, graph, Fenwick, Trie or Counter. Queue facade tests: 24,000 operations passed; adapter gate passes. Full library proof gate remains incomplete.</p><input id="q" placeholder="Filter operations"><table><thead><tr><th>Operation</th><th>Before</th><th>Current</th><th>Status</th><th>Bend ns/op</th><th>C ns/op</th><th>Measurement</th></tr></thead><tbody>'+''.join(rows)+'</tbody></table><script>q.oninput=()=>document.querySelectorAll("tbody tr").forEach(r=>r.hidden=!r.textContent.toLowerCase().includes(q.value.toLowerCase()))</script>'
iterator_summary = ''
if a.iterator_report:
 ir=json.loads(a.iterator_report.read_text()); grouped={}
 for x in ir['results']:grouped.setdefault(x['operation'],{})[x['size']]=x
 passed=sum(bool(x.get('passed')) for x in ir['results'])
 iterator_summary=f'Iterator calibrated: {passed}/{ir["expected_rows"]} rows pass; acceptance={ir["acceptance"]}.'
 section=f'<h2>DLL iterator — calibrated Bend versus C</h2><p><b>{html.escape(iterator_summary)}</b> Six alternating samples per row; each Bend batch difference ≥50 ms. All three nonempty sizes. This gate covers iterators only.</p><p>Add/remove report the same restoring add + previous + remove workload with different seeds; first/last/finish include finish/recreate. Ratios are medians, Bend/C ≤2.5. C source unchanged. Component proofs and 32,429 differential operations pass; complete cursor-invariant and trace-refinement proofs remain unfinished.</p><table><thead><tr><th>Operation</th><th>64 elements</th><th>4,096 elements</th><th>65,536 elements</th><th>Worst ratio</th></tr></thead><tbody>'
 for op, sizes in grouped.items():
  worst=max((r.get('ratio',0) for r in sizes.values()),default=0)
  section+=f'<tr><td>{html.escape(op)}</td>'
  for size in [64,4096,65536]:
   r=sizes.get(size,{})
   if 'ratio' in r:
    color='#4ade80' if r.get('passed') else '#f87171'
    section+=f'<td style="color:{color}">{r["ratio"]:.3f}×<br><small>{r["median_bend_ns"]:.3f} / {r["median_c_ns"]:.3f} ns</small></td>'
   else:section+='<td>Pending or failed</td>'
  section+=f'<td>{worst:.3f}×</td></tr>'
 section+='</tbody></table><p><a href="dsa-iterator-performance.json">Full sample data and source hashes</a></p><h2>Whole collection quick screen</h2>'
 page=page.replace('<input id="q"',section+'<input id="q"')
groups={}
for x in c['results']:groups.setdefault(x['operation'].split('.')[0],[]).append(x)
summary='<h2>Overall collection status — quick screen</h2><table><thead><tr><th>Collection</th><th>Within 2.5×</th><th>Too slow</th><th>Unresolved</th></tr></thead><tbody>'
for name, results in groups.items():
 passed=sum('ratio' in x and x['ratio']<=2.5 for x in results)
 failed=sum(x.get('ratio',0)>2.5 for x in results)
 missing=sum('ratio' not in x for x in results)
 summary+=f'<tr><td>{html.escape(name)}</td><td>{passed}</td><td>{failed}</td><td>{missing}</td></tr>'
summary+='</tbody></table>'
page=page.replace('<input id="q"',summary+'<input id="q"')
if a.tree_report:
 tr=json.loads(a.tree_report.read_text())
 section='<h2>Red-black tree — calibrated update improvement</h2><p>One search per update now supplies both the new tree and old binding. Six samples per row with the unchanged C reference. Both fusion equivalence proofs and the complete red-black tree proof module pass; 11,109 differential/structural observations pass. These improvements do not establish the 2.5× performance target. Read-only operations remain the next bottleneck.</p><table><thead><tr><th>Operation / size</th><th>Before ns</th><th>After ns</th><th>C ns</th><th>Speedup</th><th>Bend/C</th></tr></thead><tbody>'
 for x in tr['results']:
  m=x['medians_ns'];color='#4ade80' if x['ratio']<=2.5 else '#f87171'
  section+=f'<tr><td>{html.escape(x["operation"])} / {x["size"]:,}</td><td>{m["before"]:.2f}</td><td>{m["after"]:.2f}</td><td>{m["c"]:.2f}</td><td>{x["speedup"]:.2f}×</td><td style="color:{color}">{x["ratio"]:.2f}×</td></tr>'
 section+='</tbody></table><p><a href="dsa-tree-performance.json">Before/after samples and source hashes</a></p>'
 page=page.replace('<input id="q"',section+'<input id="q"')
if a.ownership_report:
 own=json.loads(a.ownership_report.read_text())
 section='<h2>Dynamic arrays — owning Type support</h2>'
 for key in ['implementation','proof_status','performance_status','tree_status']:
  section+='<p>'+html.escape(own[key])+'</p>'
 section+=f'<p>Native nested-array tests: {own["tests"]["histories"]} histories / {own["tests"]["observations"]:,} observations passed.</p>'
 page=page.replace('<input id="q"',section+'<input id="q"')
if a.tree_map_report:
 tm=json.loads(a.tree_map_report.read_text()); tested=json.loads((ROOT/'build/tree-map/tests.json').read_text())
 good=sum(x.get('ratio',float('inf'))<=2.5 for x in tm['results']); bad=sum(x.get('ratio',0)>2.5 for x in tm['results']); unresolved=sum('ratio' not in x for x in tm['results'])
 section=f'<h2>Current indexed TreeMap — Data keys and values</h2><p>Production balanced-search-tree module replaced with dynamic-array storage, CLRS repair, comparator-based key identity, navigation, conditional updates, editable owning iterators, and backed range views. DSA worker remains stopped.</p><p><b>{tested["operations"]:,} operations / {tested["histories"]} histories passed</b>, with independent structural and free-slot checks after every operation. String keys with custom Data records pass. Capacity rejection/reuse passes.</p><p>Proof: 16 new component laws pass; existing dynamic-array and retained legacy-tree proof gates pass. Full indexed-tree refinement, rotation/deletion invariants and arbitrary iterator/view traces are <b>not yet proved</b>.</p><p>Performance: {good} rows within 2.5×, {bad} too slow, {unresolved} unresolved. Six alternating samples; unchanged optimized C reference. Both sides fold iteration/range outputs directly. Removal includes reinsertion. Source hashes and all samples below. Other jobs were running on this machine, so unresolved/noisy rows are not acceptance passes.</p><table><thead><tr><th>Operation</th><th>Size</th><th>Bend ns</th><th>C ns</th><th>Bend / C</th><th>Status</th></tr></thead><tbody>'
 for x in tm['results']:
  m=x.get('medians_ns',{}); ratio=x.get('ratio'); color='#4ade80' if ratio is not None and ratio<=2.5 else '#f87171'
  result='within target' if ratio is not None and ratio<=2.5 else 'too slow' if ratio is not None else 'unresolved'
  section+=f'<tr><td>{html.escape(x["operation"])}</td><td>{x["size"]:,}</td><td>{m.get("bend",0):.2f}</td><td>{m.get("c",0):.2f}</td><td style="color:{color}">{f"{ratio:.3f}×" if ratio is not None else "—"}</td><td title="{html.escape(x.get("error",""),quote=True)}">{result}</td></tr>'
 section+='</tbody></table><p><a href="dsa-tree-map-performance.json">Raw current TreeMap measurements</a> · <a href="dsa-tree-map-tests.json">Test evidence</a></p><h2>Historical whole-collection quick screen</h2><p>The rows below predate the TreeMap replacement. Use the current table above for tree measurements; previous whole-collection pass counts are not a current acceptance result.</p>'
 page=page.replace('<input id="q"',section+'<input id="q"')
if a.range_report:
 rr=json.loads(a.range_report.read_text())
 section='<h2>Latest TreeMap traversal optimization</h2><p>Unboxed ascent decisions and metadata-only successor walks. Same public cursor API and unchanged C reference. Six alternating samples with checksum agreement. 92,544 differential operations and 16 existing component laws pass; three additional local traversal laws pass. Full indexed-map proof remains open.</p><table><tr><th>Operation</th><th>Size</th><th>Before µs</th><th>After µs</th><th>C µs</th><th>Speedup</th><th>After / C</th></tr>'
 for r in rr['results']:
  m=r['medians_ns']
  section+=f'<tr><td>{html.escape(r["operation"])}</td><td>{r["size"]:,}</td><td>{m["before"]/1000:.3f}</td><td>{m["bend"]/1000:.3f}</td><td>{m["c"]/1000:.3f}</td><td>{r["speedup"]:.2f}×</td><td>{r["ratio"]:.2f}×</td></tr>'
 section+='</table><p>All six still exceed the 2.5× target. <a href="dsa-tree-range-performance.json">Raw samples and hashes</a>. The older sweep below predates this optimization; its range/iteration rows are superseded. Other operations have not been rebenchmarked.</p>'
 marker='<h2>Current indexed TreeMap'
 page=page.replace(marker,section+marker) if marker in page else page.replace('<input id="q"',section+'<input id="q"')
if a.fold_report:
 fr=json.loads(a.fold_report.read_text())
 section='<h2>Current public bulk folds</h2><p>fold/view_fold avoid per-entry editable cursor reconstruction and resolve the terminal node once. Unchanged optimized C workload; the old editable iterator remains available. Six new component laws pass; full fold refinement remains open.</p><table><tr><th>Operation</th><th>Size</th><th>Previous iterator µs</th><th>Bulk fold µs</th><th>C µs</th><th>Speedup</th><th>Fold / C</th></tr>'
 for r in fr['results']:
  m=r['medians_ns']
  section+=f'<tr><td>{html.escape(r["operation"])}</td><td>{r["size"]:,}</td><td>{m["before"]/1000:.3f}</td><td>{m["bend"]/1000:.3f}</td><td>{m["c"]/1000:.3f}</td><td>{r["speedup"]:.2f}×</td><td>{r["ratio"]:.2f}×</td></tr>'
 section+='</table><p><a href="dsa-tree-fold-performance.json">Raw fold comparison</a>. These results measure the new bulk API, not individual editable-iterator calls. Earlier tables below are historical. All six rows still exceed 2.5× C.</p>'
 page=page.replace('<h2>Latest TreeMap traversal optimization</h2>','<h2>Previous iterator optimization</h2>')
 marker='<h2>Previous iterator optimization</h2>' if a.range_report else '<h2>Current indexed TreeMap'
 page=page.replace(marker,section+marker)
out=ROOT/'build/optimization.html';out.write_text(page)
site=Path('/Users/monkeair/progress-dashboard/site');(site/'dsa-benchmarks.html').write_text(page);(site/'dsa-benchmarks.json').write_text(json.dumps(c))
if a.iterator_report:(site/'dsa-iterator-performance.json').write_text(json.dumps(ir,indent=2)+'\n')
if a.tree_report:(site/'dsa-tree-performance.json').write_text(json.dumps(tr,indent=2)+'\n')
p=site.parent/'assessment.json';d=json.loads(p.read_text());v=d['projects']['dsa'];v.update(scope='12 collections including LRU and queue facades; no segment tree/union-find/graph/Fenwick/Trie/Counter. 2.5× optimized C target.',implementation_done='Stack, arena DLL and LifoQueue/SimpleQueue/PriorityQueue added. Matching C benchmarks built.',implementation_missing='Optimize measured slow operations; owning-Type scope and complete proofs remain unfinished.',pace=a.note,performance_status=f'Quick provisional: {len(c["results"])} operations, {slow} above 2.5x, {unknown} unresolved; {c["seconds"]:.2f}s. Full gate not passed.',reviewed_at=now);p.write_text(json.dumps(d,indent=2)+'\n')
if iterator_summary:
 v['performance_status']+=' '+iterator_summary
 p.write_text(json.dumps(d,indent=2)+'\n')
print(out)

if a.tree_map_report:
 (site/'dsa-tree-map-performance.json').write_text(json.dumps(tm,indent=2)+'\n')
 (site/'dsa-tree-map-tests.json').write_text(json.dumps(tested,indent=2)+'\n')
 v.update(implementation_done='Indexed red-black TreeMap now replaces the recursive production tree. Data keys/values, comparator, navigation, conditional updates, owning cursors and bounded views. Other collections retained.',implementation_missing='TreeMap range/iteration speed and full indexed correctness proofs; remaining collection performance/proof work.',proof_status='16 TreeMap component laws pass. Existing Data-array and legacy-tree proof gates pass. Full indexed refinement/rotation/deletion/iterator/view proofs remain open.',performance_status=f'Current TreeMap: {good} within target, {bad} too slow, {unresolved} unresolved out of {len(tm["results"])} calibrated rows. Historical quick screen is not a current full-library gate.')
 p.write_text(json.dumps(d,indent=2)+'\n')

if a.range_report:
 (site/'dsa-tree-range-performance.json').write_text(json.dumps(rr,indent=2)+'\n')
 v['performance_status']='Latest traversal comparison: range 1.43–1.66× faster; iteration 1.29–1.55× faster. All six remain above 2.5× C. Other operations only have the older sweep.'
 v['proof_status']+=' Three local traversal laws also pass; these do not establish complete traversal equivalence.'
 p.write_text(json.dumps(d,indent=2)+'\n')

if a.fold_report:
 (site/'dsa-tree-fold-performance.json').write_text(json.dumps(fr,indent=2)+'\n')
 v['performance_status']='Public bulk folds: all six rows still exceed 2.5x C; see current table for measured improvement over editable iterators. Other operations were not rebenchmarked.'
 v['proof_status']+=' Six fold component laws pass; complete fold refinement remains open.'
 p.write_text(json.dumps(d,indent=2)+'\n')

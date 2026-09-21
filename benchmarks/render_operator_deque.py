"""Render the diagnostic without turning algorithm-mismatched rows into acceptance."""
import json,statistics
from pathlib import Path
root=Path(__file__).resolve().parents[1]
p=root/'benchmarks/evidence/operator-deque-20260922/report.json'
d=json.loads(p.read_text());lines=['# C DLL reference diagnostic, 2026-09-22','','Bend still uses the ring deque. C now uses a reusable indexed DLL. These are','diagnostic timings, NOT same-algorithm acceptance of the DLL migration.','','| Operation | Size class | Bend ns/op | C ns/op | Bend/C |','|---|---|---:|---:|---:|']
for r in d['rows']:
 if r['measurement']=='failed':lines.append(f"| {r['operation']} | {r['workload']} | unmeasurable | — | — |")
 else:lines.append(f"| {r['operation']} | {r['workload']} | {statistics.median(r['bend_ns']):.2f} | {statistics.median(r['reference_ns']):.2f} | {r['ratio']:.3f} |")
lines+=['','Original six-sample calibration, region ordering and checksum contract retained.','Failed measurements are not passes. Raw samples and source hashes accompany this table.','C correctness: ASan/UBSan, 200,000 model comparisons and 10 million constant-occupancy FIFO pairs passed.','Storage: 6,291,456-byte node capacity; optimized stress process peak RSS 4,587,520 bytes.','The operator snapshot still contains unfinished Bend DLL edits; no complete proof gate is claimed.']
(p.parent/'README.md').write_text('\n'.join(lines)+'\n')

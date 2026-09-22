# Benchmark scope change, 2026-09-22

Explicit user instruction: remove empty-list benchmarks for all structures, then run a full sweep and show the results.

- Exclude every timing row with initial size zero, across all structures, including the existing LRU workloads (104 rows).
- Retain empty-state runtime/oracle tests and formal obligations. This is a performance-scope change, not a correctness exemption.
- Preserve the remaining rows' seeds from the table before the empty filter. Keep operation selectors, counts, sizes, C algorithms, compiler flags, calibration, six samples and the 2.5x threshold.
- Full current sweep: 321 nonempty rows across 11 active new structures plus the reused LRU. The standalone DLL was already retired by the user.
- Include the previously supplemental LRU workloads, including explicitly labelled isolated and composite operations. Restoring-pair timings include both removal and restoration; they are not isolated removal costs.
- `benchmarks/full_sweep.py` preserves failed builds, checksum failures, timeouts and unmeasurable rows in its report and continues to the other rows. A failed row is never counted as a pass.

Run: `python3 benchmarks/full_sweep.py --report build/nonempty-full-sweep/report.json`.
Summary: `python3 tools/summarize_full_sweep.py`.

The old 60-row queue/deque report is historical evidence under the earlier scope. Its empty rows were not relabelled as passing. The current sweep remeasures every retained row.

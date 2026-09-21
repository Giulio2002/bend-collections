# Development triage, 2026-09-21

408 canonical workloads:243 within2.5xC,162 too slow,3 unmeasurable.
This is a failed full performance target, not acceptance. LRU is absent from
these canonical408rows and remains mandatory additional coverage.

The run overlapped SSZ benchmarking and other local work; use it to locate
bottlenecks, not as an isolated release benchmark. The source manifest is
collected at the end by the existing DSA harness; it is not the stronger
before/after build guard added to the SSZ harness. review.json records any
hash differences from this exported snapshot. Protected18reference/workload
files remained unchanged under the operator guard. No slowed C reference is
accepted. Native LRU proof construction is ongoing in this snapshot.

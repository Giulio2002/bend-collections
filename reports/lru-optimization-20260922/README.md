# LRU optimization evidence — 2026-09-22

Current native implementation: `src/lru/fast.bend`. Stock Bend 2.0.16, no FFI,
unchanged optimized C reference. The selected implementation keeps Base.Map,
compares packed signed timestamps, decodes lifetime once, and fuses recency
promotion using the DLL link-write primitive. Both custom lookups regressed
and were rejected.

- `final.json`: all 51 current LRU workload attempts: **6 pass, 30 slow, 15
  failed** against 2.5x. Six samples and the canonical timing minima; a new
  30-second per-row wall-time cap rejects unfinished measurements. Failed rows
  include noisy/nonpositive timing deltas, timeouts, and C arena exhaustion.
- `native-map-screen.json`: medium expiry 8,830 → 5,460 ns; lifetime setter
  2,632.5 → 1,680 ns. Ordinary read timings were noisy during unrelated SSZ
  proof activity; no precise speedup is claimed for them.
- `rejected-lookup-screen.json`: both custom lookup approaches were slower.
- `full-baseline-report.json`: frozen 357-row sweep before these LRU changes:
  **284 pass, 59 slow, 14 failed**. Original source unchanged during that run.
  The invalid isolated-removal cap is documented in the sidecar and corrected
  for the LRU rerun. This frozen report is not current LRU evidence.
- Native C plus ASan/UBSan differential test: **2,208 cases, zero mismatches**.
- Retained independent cache oracle: **24,000 operations, zero mismatches**.
- Universal local optimization equivalence and conditional U32/String operation
  traces pass. Three deliberate semantic mutants are rejected. No new unsafe
  declarations, axioms, or admitted holes. Existing trusted dependencies remain.

Raw logs, checksums, environment, source/binary hashes and candidate source text
are retained. Only proof EOF whitespace was normalized after timing; the exact
reversible byte changes are recorded in `post-measurement-proof-formatting.json`.
The runtime source hash still matches the measured implementation, and proof
gates are rerun after formatting.

This is a work-in-progress snapshot. LRU performance acceptance and whole-library
formal verification are **not complete**. Remaining large LRU costs include
legacy Word64 metrics output and deadline arithmetic, plus native Map lookup.

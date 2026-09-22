# Private work-in-progress snapshot

LRU now uses packed signed expiry checks, a single lifetime decode, and fused
recency promotion sharing the DLL link-write primitive. Native Base.Map remains;
both experimental custom lookups were measured slower and removed.

- Candidate medium expiry: 8.83 → 5.46 us; lifetime setting: 2.63 → 1.68 us.
- Final current LRU rerun: **6/51 pass 2.5x, 30 slow, 15 failed measurement**.
- Conditional operation-trace proofs for U32/String and local equivalence pass.
  Missing legacy proof dependencies were recovered as proof-only link/array
  lemmas. No retired collection runtime or new unsafe/axioms were introduced.
- 2,208 C/sanitizer cases and 24,000 retained-oracle operations pass; all three
  semantic mutants are rejected. Existing trust assumptions remain.
- Metrics Word64 output, deadline arithmetic and native Map lookup remain major
  costs. Whole-library proofs and performance acceptance are not complete.

The full frozen 357-row baseline before the LRU edits has 284 passes, 59 slow
rows and 14 failed measurements. It is archived separately from current LRU
results. See `reports/lru-optimization-20260922/` and
`docs/LRU_OPTIMIZATION.md` for exact sources, samples, failures and limitations.

TreeMap still uses the indexed red-black representation and ordinary editable
iterators. Bulk folds remain removed. Its prior 92,544 differential operations,
16 component laws and three traversal laws passed; full indexed refinement and
the whole-library proof gate remain unfinished.

Stock Bend 2.0.16; no FFI, compiler patch or generated-C modification. All C
references remain unchanged. DSA auto-implementer remains stopped.

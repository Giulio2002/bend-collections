# LRU optimization, September 22

The measured API is `src/lru/fast.bend`: native String-keyed Map lookup with
indexed doubly linked recency, recycled slots, lifetimes, and 64-bit metrics.
The retained reference API in `reference/lru` remains the independent oracle.
The optimized C reference, benchmark drivers, seeds, and timing thresholds
are unchanged. Stock Bend 2.0.16; no FFI or generated-C edits.

## Candidates and evidence

Candidates are measured separately before selection. Native Map storage is
preserved. The retained changes are native two-U32 signed expiry comparison, one lifetime
decoding per setter, and fused detach/append sharing the DLL link-write
primitive. Both custom Map lookup experiments were rejected: they made
add/get/peek roughly twice as slow. Base.Map lookup is retained.
Recency updates preserve the slot and payload; removing and reinserting a
public DLL node would unnecessarily change its handle.

`bend LRU_OPT_PROOF.bend` checks universal equivalence laws for the candidate
operations, including all 64-bit signed timestamp pairs and the zero immortal
sentinel. `bend proofs/lru_fast/inst_trace.bend` checks the existing conditional
operation-trace refinement for U32 and String payloads. The theorem's capacity,
representation and trace admissibility premises remain unchanged; this is not
a claim that arbitrary malformed caches satisfy the representation invariant.
Inherited unsafe annotations in Base and existing proofs remain part of the
trust assumptions. No unsafe declarations, axioms, or holes were added.

The baseline trace proof failed because it imported removed DLL/graph proof
files. `proofs/lru_fast/support` retains only the referenced link, array, and
arithmetic lemmas, with provenance in each file. It imports no retired
collection runtime. This repairs the dependency graph without restoring the
removed collection APIs.

The new trace gate passes. Native differential testing against optimized C
and ASan/UBSan C passed 2,208 cases. The current candidate also passed 24,000 retained-oracle operations and six
capacity boundary cases. An earlier candidate passed 1,800 interpreted
independent-spec operations; the redundant final interpreted rerun was stopped
to avoid contention with native timing and is not counted as a pass.
`python3 tools/lru_opt_mutations.py` requires the laws to reject an inverted lifetime flag,
disabled expiry, and disabled promotion; all three are rejected. These finite
tests complement the kernel checks and do not prove compiler correctness.

## Measurement limitations found

The isolated-removal calibration previously allowed `count == size` even
though region A performs `2 * count` removals. Such samples exhausted the
cache and measured misses. The cap is now `size // 2`, with a defensive check
in calibration. The initial full sweep retains its failed attempts; those
results are not acceptance evidence. Corrected rows must be rerun identically
on Bend and C. No reference algorithm was slowed or replaced.

The compatibility metrics API still builds a list of five `Word(64)` values.
Deadline creation still performs the legacy signed nanosecond conversion.
These are real remaining costs, not eliminated by optimizing Map lookup or
expiry comparison. A fixed 32-bit pattern expansion for pack/unpack passed its
local equivalence proof but failed stock native compilation (`arity over 255`)
and was rejected. It is not part of the shipped implementation.

## Candidate selection

In the second six-sample screen (medium workloads), original expiry cost
8,830 ns versus 5,460 ns for the selected native-promote candidate; lifetime
setting cost 2,632.5 ns versus 1,680 ns. These observed reductions are about
38% and 36%. Ordinary get/peek differences were noisy while an unrelated SSZ
proof briefly used several cores; no precise speedup is claimed for them.
The native-packed and native-promote expiry/C ratios were effectively equal
(582x and 586x); neither approaches the 2.5x target. The final 51-row rerun
is reported separately. Its 30-second row wall-time cap only fails unfinished
measurements; sample counts, timing minima and correctness checks are unchanged.

## Reproduce the current implementation

```sh
bend LRU_OPT_PROOF.bend
bend proofs/lru_fast/inst_trace.bend
python3 tools/lru_opt_mutations.py
python3 tools/lru_diff.py --quick
python3 benchmarks/lru_sweep.py --report build/lru-opt/final.json
```

The sweep rebuilds both binaries; the final report keeps failed
rows, source/binary hashes, timing samples, and checksums. The optional
`lru_candidates.py` experiment runner expects previously compiled candidate
binaries and is not the normal fresh-checkout benchmark command. Archived
candidate results do not certify the current source or whole-library acceptance.

## Final 51-row rerun

6 rows meet 2.5x C, 30 are slow, and 15 failed measurement. All rows remain in
`reports/lru-optimization-20260922/final.json`; failures are not acceptance
passes. The largest valid ratio is about 1,970x for medium metrics (14.34 us
Bend), followed by expiry and lifetime setting. The final medium expiry
measurement is 5.99 us; the before/after figures above are from the separate
candidate comparison. Final native differential testing passes 2,208 cases;
local equivalence, conditional U32/String traces and all three mutation checks
pass. Runtime and C reference hashes match the measured code.

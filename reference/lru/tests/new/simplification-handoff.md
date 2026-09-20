# Manual simplification handoff — 2026-09-19

> Historical (superseded in iteration 0022): the adapter now steps only via
> `D.advance`, and the composed public/trace/host laws are in END_TO_END.bend.
> See README.md and PROOF_STATUS.md for the current claims.

The LRU worker was stopped cleanly at cycle 21. All candidate files were copied
from the interrupted workspace before edits. The previous run, proof files,
session logs and frozen acceptance criteria remain available in the run archive.

## Changes and reasons

* The current `src/public.bend` machine already owned public cache decisions.
  Keep it. `src/adapter.ts` remains a small host boundary.
* Six shared entry helpers moved unchanged into `src/entry_ops.bend`.
  `src/protocol.bend` forwards its old entry points to these definitions.
  The public runtime now imports the six active helpers directly, without
  depending on the obsolete detach/count/aggregate phase machine. No previously
  checked proof was deleted or weakened. Core native Map/state representation
  and every independent specification remain unchanged.
* Three runtime mutation probes still targeted code removed by the previous
  worker's dispatcher migration. They now mutate actual native deletion,
  actual oldest removal, and the actual public pre-clock eviction counter.
  Two refresh proof mutations now target the extracted active implementation.
  Each still requires a specific semantic/proof failure, not an arbitrary exit.
* Existing public-read and public-Remove proofs were checked separately, then
  composed into `END_TO_END.public_string_get/peek/contains/remove`, importing
  their full dependency graph through PROOF. These statements connect the actual
  public start/drive machine to the independent typed command specification over
  all event lists, including clock failures. They retain represented String-cache
  premises; generic keys, reachable-state discharge, remaining operations,
  arbitrary traces and the TypeScript bridge are still unfinished.

## Do not repeat obsolete work

Signed duration arithmetic and core whole-operation proofs already exist.
The historical protocol is retained for proof reuse, not as a public completion
requirement. Do not remove callback metadata merely to reduce source size: that
would invalidate existing proofs while callbacks are already unreachable.
No new general-purpose map abstraction or replacement state machine is needed
without a specific remaining public obligation that cannot reuse current laws.

## Verification evidence

`build/simplification-validation.json` records the extraction-stage run: every
executable check passed, including all 12 upstream groups and 40 mutations;
full_scope correctly failed. Public-read and public-simple checked separately.
The final composed proof and frozen acceptance logs are recorded separately in
build; use their actual results, not this narrative, for current verification.
Do not claim full verification. Keep all remaining gates strict.

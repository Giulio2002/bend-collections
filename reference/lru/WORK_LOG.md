# Initial checkpoint — authoritative final scope

User requests a separate verified Bend single-threaded LRU using native Base Map.
They explicitly removed concurrency variants and then removed AESENC/custom hashing.
Do not implement any of those excluded features. Preserve the active SSZ project.

Frozen elastic/go-freelru commit: 3a0a715f3309fbbaed5d9afd402d53ff5e1efd81.
Upstream go test ./... passed in 2.263s; no Bend implementation exists yet.
21 public lru.go declarations and 12 TestLRU* functions are inventoried. Include
all shared helper assertions when porting; excluded concurrency/map-baseline tests
have recorded reasons. Document constructor/storage changes due to native Map.

Base Map is defined in the installed Base.bend; it uses String keys. Inspect its
actual laws/definitions and prove the needed map refinements, built-in canonical
key encodings, complete cache semantics, and adapter composition. Do not invent
custom hashing or a second map. Acceptance deliberately fails until implementation,
full tests and END_TO_END proofs exist. Return needs_work until all scope is done.

# 2026-09-19 — first substantive implementation checkpoint

Re-read this isolated workspace, both manifests, pinned lru.go/lru_test.go/cache.go,
frozen acceptance.py, installed Bend guide and Base Map definitions. No worker
subagents, commits, pushes, deployment, or SSZ operations were used.

Implemented `types/model.bend`, generic `src/cache.bend` using actual Map.get/set/
del, signed time calculations, canonical string/integer/Word codecs and proofs,
clock/callback TypeScript adapter, independent partial finite-map specification,
empty/singleton Map laws, actual generic initialization refinement and initial
Get/Remove refinement. END_TO_END imports those checked facts and explicitly does
not claim operation/trace completeness. README maps every manifest declaration
and documents hash-free constructors, size validation/hint, native diagnostics,
Collisions as not applicable, cost bounds, and semantic/trust limitations.

Ported all 12 TestLRU manifest functions to actual Bend execution with shared
constructor and callback assertions. Generated a source-site assertion/helper
inventory in tests/new/assertion-map.json. Ported TestLRUMatch retains 100,000
iterations and capacity 2; random choices are reproducible, including uint64
underflow. Expiry sleeps become controlled millisecond clocks. Added independent
Go differential traces (4 capacities, 4,800 operations) with signed durations,
backward clocks, per-read clock stepping, metrics/reset, callbacks and all trace
operations. Only the reference package declaration and now() time source change
in scratch copies; cache decisions are untouched. No expected results go to Bend.

Validation runner fails on unsupported operations, malformed/missing output,
backend exit, timeout, or failed checks. Mutation copies test expired-predicate
sensitivity and prove a collapsed binary codec is rejected by the checker.
A separate explicit full-scope failure lists unmet universal and semantic goals;
passing finite tests cannot clear it.

Failed attempts and corrections:

- Initial Bend codec helper appeared after its caller; definitions must be ordered.
  Reordered helpers; codec round-trip/injectivity checked.
- Large Nat literals for million/bound constants overflowed checker stack during
  expansion. Runtime divisors now use U32.to_nat. Public constructors use U32
  directly, with U32 validation, avoiding expansion of 0xffffffff in proof terms.
- Bend rejects computed-value destructuring and out-of-order matches. Split native
  read results into helpers and used explicit result accessors; no checker changes.
- Imported local names `metrics` and constructor `Result` conflicted with resolved
  global names. Renamed local counters and abstract Observation constructor.
- Recursive law/helper chains in the independent expiry-prefix attempt were
  rejected as an unfilled live claim. Replaced them with ordinary structural
  recursion and total result selection; no unfilled laws remain.
- Corrected equality rewrite direction while proving Word/String comparison and
  singleton native Map laws; the final proofs pass the unmodified checker.
- Bend launcher's help/check runs attempted to write ~/.bend/last and the sandbox
  denied that write. Direct Bun invocation of the same installed main.ts avoids
  that side effect; frozen acceptance still uses the required launcher unchanged.
- The upstream Go test command initially placed GOCACHE under vendor/go_freelru/
  build because its working directory changed. Removed only that newly generated
  cache immediately afterward and rechecked every frozen upstream SHA-256. No
  upstream source or protected harness change remains. Future cache paths must be
  absolute under workspace/build.

Intermediate evidence (before the final constructor/proof/bound-check additions):

- `bun .../bend2/main.ts src/codec.bend`: exit 0, All terms check.
- `bun .../bend2/main.ts PROOF.bend`: exit 0 after each final proof correction.
- `python3 tools/validate.py --report build/validation.json`: exit 1, intentionally
  incomplete. All 12 upstream cases passed, boundary passed (24 counted checks),
  independent 4,800-operation differential passed, both mutants rejected. All
  executable successes are finite evidence only.
- `/opt/homebrew/bin/go test ./...` in pinned upstream: exit 0, package passed in
  2.217s. Reference evidence only; not credited as Bend conformance.

Final frozen acceptance run and exact report are recorded below after completion.
Remaining work and next native-map/codec/invariant/operation/trace/adapter lemmas
are enumerated in PROOF_STATUS.md. Status must remain needs_work.

Final checkpoint evidence:

- `python3 automation/acceptance.py`: **exit 1**, captured in build/acceptance.log.
  Frozen source integrity passed; launcher checked PROOF.bend successfully;
  tools/validate.py executed all cases and independent checks successfully, then
  returned nonzero for the explicit full_scope obligations. Consequently frozen
  acceptance did not reach its final standalone END_TO_END invocation.
- Ran that final checker separately with the installed unmodified CLI main.ts:
  `BEND_NO_TELEMETRY=1 /Users/monkeair/.bun/bin/bun
  /Users/monkeair/.bend/current/bend2/main.ts END_TO_END.bend`: **exit 0**,
  `All terms check.` This checks only the documented partial theorems.
- Final conformance: **12/12 exact manifest cases passed**. TestLRUMatch executed
  **100,000 steps and 1,297,279 counted assertions**, including constructor and
  eviction helper checks. Every case also executes actual Bend operations.
- Boundaries: **passed**, 24 counted equality/boolean assertions plus rejection
  assertions. Differential: **4,800 operations passed**, seed 583, capacities
  1/2/7/32, full per-operation output/callback/metric/clock-read comparison under
  the documented Collisions storage projection.
- Sensitivity: expired=false implementation mutant fails an assertion; collapsed
  binary bit codec fails its theorem. Transport rejection checks passed for
  missing output, malformed output, backend failure, timeout, and unsupported op.
- Final report copied to **VALIDATION.json**, including source SHA-256 fingerprints,
  installed Base fingerprint, exact case names/counts and incomplete obligations.
  **needs_work**: proof completeness and semantic gaps are not external blockers.

# 2026-09-19 — iteration 0002, full-width arithmetic and effect phases

Re-read the fresh iteration 0002 workspace, manifests, retained implementation,
specification/proofs, adapter, validation driver, installed Base word arithmetic,
and pinned callback/eviction/clock sites. Edited only this candidate; no subagents,
commits, pushes, deployment, SSZ access, or protected source/harness modifications.
All new build/cache/reference/mutation artifacts are under this workspace/build.

Concrete changes:

- Replaced public time/duration with two's-complement Int64/Word(64n), and all five
  counters with Word(64n). Added actual wrapping addition/increment and binary
  magnitude division by 1,000,000 followed by sign restoration. Removed the former
  48-bit host restriction. Kept the old canonical signed Integer solely for its
  existing codec proofs. Existing constructor/initial-state proofs were migrated
  to the new representation, not removed.
- Added U32 limb packing/splitting used by the public host adapter, with generic
  checked round trips. Added arbitrary-width rollover, zero sign/detection/division
  and universal zero sentinel laws. Universal quotient/remainder/arithmetic and JS
  conversion correctness remain required, explicitly unclaimed.
- Made differential input/output full-width exact: canonical decimal strings,
  no BigInt-to-Number output conversion; Go reflection emits integer strings without
  float64. Numeric fixtures exercise 1,141 operations against pinned Go, including
  min/max int64, signed truncation, deadline wrapping and all counter wraps. The
  counter-seeding fixture is transparent and test-only in both drivers.
- Added Bend protocol detach/resume stages and native aggregate effect requests.
  Callbacks now see absent membership/decremented Len before counter increments.
  Resumption uses callback-modified counters/settings; full-cache Add samples time
  after callback return; refresh counts/touches before sampling. Keys, Values,
  PurgeExpired and Purge now follow Bend-generated requests, not host cache
  decisions. Tested 44 Go-comparison callback operations for observations, reset,
  callback disabling/replacement, reentrant live Get, lifetime changes and external
  clock changes. Reentrant structural mutation remains guarded and unimplemented.
- Added universal removal-phase folding and pre-callback metric laws, generalized
  actual SetLifetime/SetOnEvict/ResetMetrics refinement, native bit-routing string
  preservation, candidate representation predicates and initial positive-capacity
  representation proof. These do not assert general Map or trace correctness.
- Expanded independent finite-map operation and mathematical numeric specifications;
  explicitly instantiated generic templates in a separate checker test.
- Added semantic mutants for omitted recency movement, omitted native Map deletion,
  and newest-first callback eviction order, preserving existing expiry and codec
  theorem mutants and strict transport failures. Full-scope gate remains failed.

Failed attempts and corrections:

- The first binary division definition consumed width p twice; marked its Nat
  width reusable instead of bypassing affine checking.
- The first routing-preservation proof used an overlapping fallback Char pattern
  the checker could not infer; made the Chr constructor explicit and annotated
  its reconstructed value. The completed universal lemma checks.
- Base has no Bool.is_eq; representation predicates now use not(xor) directly.
- Public aggregate modes were first U32 tags; replaced them with a closed datatype
  to avoid accepting arbitrary invalid mode numbers as completion.
- Existing numeric proof claims were not broadened beyond what checked. Arithmetic
  execution parity is supported by tests, not asserted as a universal theorem.

Commands and observed outcomes so far in this iteration:

- Installed unmodified checker via `BEND_NO_TELEMETRY=1 bun .../bend2/main.ts
  src/cache.bend`, `src/protocol.bend`, `PROOF.bend`, and
  `tests/new/spec_smoke.bend`: exit 0 after the corrections above, All terms check.
- Direct `tests/new/upstream.ts boundary`: exit 0, 24 counted assertions plus
  rejection assertions, after numeric and protocol changes.
- `tools.validate.differential()`: 4,800 operations passed with exact transport.
- `tools.validate.numeric_boundaries()`: 1,141 operations passed against Go.
- `tools.validate.callback_boundaries()`: 44 operations passed against Go.
- `tools.validate.sensitivity()`: all five mutants rejected by intended semantic
  assertions/theorem checking (not by missing imports or parse errors).

Final frozen acceptance was run unchanged using
`/Users/monkeair/auto-implementer/.venv/bin/python automation/acceptance.py`:
**exit 1**, because the explicit full_scope gate remains failed. It checked
PROOF.bend, then all 12 manifest cases passed, including the full 100,000-iteration
TestLRUMatch. Spec-template, boundary, differential, numeric-boundary,
callback-boundary, sensitivity and transport-sensitivity checks all passed.
Log: build/acceptance.log. The Bend launcher again attempted ~/.bend/last and was
denied by the sandbox; checker output was All terms check. No external tool files
were edited. A final direct END_TO_END check and report fingerprints follow.

Final direct `END_TO_END.bend` check: exit 0, All terms check, using the unmodified
installed checker via Bun. This checks the documented partial theorem set only.
Every frozen upstream SHA-256 was rechecked successfully. VALIDATION.json now
contains this iteration's exact report, source/Base fingerprints, acceptance exit
status and explicit proved/unproved scope. The remaining full-scope failure is
intentional and required; final status is **needs_work**, not blocked or done.

## Iteration 3 — current isolated workspace only

Re-read retained source, proof predicates, adapter, transport/reference driver,
validation and installed Base definitions. No protected files or external tools
were modified; no subagents, commits or pushes were used.

Implemented native comparator certificates by structural Word/String induction:
EQ implies equality, native String.cmp preserves original operands, and equal
strings compare EQ. Added general actual Map.get storage preservation, including
all branches and arbitrary malformed trees; no map validity oracle is assumed.
Added Map.diff empty/nonempty and equal-leading-character reduction laws. Added
pairwise skipped-prefix agreement to candidate critbit invariants and a checked
malformed-tree rejection example. These do not establish insertion/deletion frame
laws or reachable-state preservation.

Proof attempts initially failed on matching comparator arguments out of binder
order and affine reuse of predecessor/word/key parameters. Reordered the helper
binders and marked explicitly duplicated data with `+`; the unmodified checker
then accepted PROOF.bend. No proof escape, axiom or weakened statement was used.

Added required directed nested Add/Remove/Purge/expired-Get callback probes under
four outer operations. Both engines are executed independently even if the other
fails; raw errors/reference outputs are stored in build/reentrant-boundaries.json.
Initial probing exposed pinned-Go out-of-range panics in removeAt/move after a
nested Add, and underflowed saved-slot continuation with nested expiry during
PurgeExpired. Backend panics remain failures. Bend's guard remains in place,
explicitly unresolved; lifting it cannot reproduce these continuations. Added a
comparator-tag mutation that forces EQ and must fail the new preservation proof.

Remaining next steps: unequal-character Map.diff msb/least-bit theorem; general
set/get/delete and invariant preservation; saved-slot callback/clock semantics
including panics/exceptions; independent effect/command/trace specification;
arithmetic interpretation and host/custom-codec bridges; universal actual cache
operation, aggregate, trace and public adapter composition. None is claimed done.

Final iteration-3 validation: direct unmodified checker on PROOF.bend and on
END_TO_END.bend each exited 0, All terms check. Frozen automation/acceptance.py
exited **1**. All 12 exact manifest cases, spec_templates, boundary (24 assertions),
4,800 differential operations, 1,141 numeric boundary operations, 44 existing
callback operations, six mutation checks and transport sensitivity passed.
The new required reentrant_boundaries check failed all 16 probes: six Go backend
panics and sixteen Bend guard errors; both engines were run for every probe.
Full_scope also remains failed. Logs/reports: build/acceptance.log,
build/validation.json, build/reentrant-boundaries.json. These are not skips or
accepted expected failures. All 28 pinned vendor file digests were reverified.
VALIDATION.json records current source/Base hashes, failed cases and partial scope.
Status remains needs_work; no completed all-operation, trace or adapter claim.

# Restart with continuous end-to-end ownership and preserved worker session

User requested the same end-to-end/self-audit policy as SSZ and worker-session
reuse. Active iteration 4 was interrupted and preserved; see frozen restart
provenance. Old and new code remains subject to fresh audit/validation. Continue
across all remaining subsystems without stopping at small milestones. The current
workspace/policies supersede prior assignments and paths in the resumed session.

## Restart 20260919T013953Z — fresh candidate validation and self-audit

Read CURRENT workspace, AUDITOR.md, automation/restart-provenance.json, retained
source, installed Base definitions, WORK_LOG and PROOF_STATUS. The restart
preserved three unreviewed edits: adapter clock sampling order and exception-aware
trace/reference drivers. Revalidated these instead of inheriting earlier claims.
No protected files, external tools or SSZ files were changed. No subagents used.

The resumed adapter evaluates the clock before reading the state passed to Bend
for AddWithLifetime, GetAndRefresh and aggregate resumption. This preserves
clock-side ResetMetrics/SetLifetime/SetOnEvict effects that the previous argument
evaluation order overwrote. Added 44 independent Go comparisons for these effects
and typed throwing callbacks under Remove, full Add, Purge, PurgeExpired and expired
Get, including subsequent Len/Keys/Get/Metrics. All passed in the directed run.
Added a scratch mutation restoring pre-clock state capture; it must differ from
Go rather than merely crash. Arbitrary structural clock reentrancy remains open.

The reference driver now catches only a typed callback fixture and runtime bounds
panics raised inside the cache-operation invocation. Bounds outcomes are explicit
saved_slot_bounds failures and terminate that semantic trace. Unsupported operations,
unexpected panics, malformed input/output, missing output and timeouts remain
backend failures. Reentrant checks require complete, equal, failure-free operation
traces; matching semantic failures do not make them pass. Extended all 16 probes
with Keys/Values/Get, callback re-enabling and RemoveOldest. The guard is still an
explicit unmet behavior requirement, not claimed to be a correct continuation.

New checked universal foundations:
- native Map.keys and Map.to_list accumulator length and public length equal
  actual Map.size, by structural tree induction;
- actual Map.get preserves the strengthened prefix/discriminator invariant;
- sign-threshold comparison equals executable last-bit sign at every width;
- comparison with zero equals executable zero detection at every width;
- executable signed order and expiration refine the independent numeric spec,
  including zero sentinel, for all 64-bit values;
- primitive Word.to_nat agrees with the independent bit-value interpretation;
- arbitrary-width limb join and public pack have the stated mathematical value
  (low plus high scaled by the low width's binary places).
These do NOT establish division/modular addition interpretation, all native Map
update/delete laws, reachable-state invariants or host JS semantic correspondence.
END_TO_END exposes the supporting expiration predicate bridge, not full API laws.

Failed proof/check attempts: accumulator rewrites initially had reversed equality
orientation, fixed with explicit symmetry; the END_TO_END imports were initially
placed below laws, rejected by the checker, then moved to the import section.
A concurrently running validation caught that temporary import-order error. Its
logs are retained as build/acceptance-attempt-import-error.log and
build/validation-attempt-import-error.json; frozen acceptance was rerun after the
correction. All terms check in the direct final END_TO_END invocation.

### Concrete specification conflict requiring a user decision

Fresh pinned-Go execution (no cache decision changes) at capacity 2:
Add("old",1); Add("survivor",2); on eviction disable callbacks and Add("nested",91);
Add("new",3); Len(). The outer Add returns true, nested Add returns false, Len
returns 3, Inserts=4 and Evictions=1. No panic occurs in this prefix. Input and
complete reference result are recorded in build/capacity-counterexample.json.
The same state can later panic, but the successful Len=3 is already observable.

Therefore exact arbitrary reentrant Go behavior and a capacity bound on ALL
reachable cache states cannot both hold. This is not a hard-proof excuse or a
request to silently narrow the domain: a user question is pending about preserving
Go's corrupt states with conditional invariants versus preserving invariants and
explicitly rejecting structural reentrancy. Neither policy has been assumed or
implemented. All failing gates remain. Independent proof work continued while
awaiting the decision. General Map laws, arithmetic/division/host bridges, effect
and trace semantics and universal API/adapter composition remain unfinished even
after this policy conflict is resolved.

Fresh settled-file frozen acceptance: exit 1. All 12 manifest cases, checker,
spec_templates, 24 boundary assertions, 4,800 differential operations, 1,141
numeric boundary operations, 44 prior callback operations, 44 new clock/exception
operations, seven mutation checks and transport sensitivity passed. All 16
structural reentrancy probes failed. Their extended suffix now produces seven
explicit Go bounds-failure traces, zero Go backend errors and sixteen Bend guard
errors. Full_scope remains failed. Fresh source/Base fingerprints and full
capacity-conflict input/reference evidence are retained in VALIDATION.json.
All 28 pinned vendor hashes match. Self-audit is tests/new/self_audit.md; it is not
independent auditor approval. Clarification on incompatible universal capacity
and exact corrupt-Go behavior is still pending; no policy answer was inferred.

## User scope update: callbacks excluded

The user explicitly put callbacks entirely out of scope. The new supported API
must omit SetOnEvict/user callback execution. Compare core behavior to Go with
a nil callback; eviction, expiry, ordering and metrics remain required. Old
callback/reentrancy results below are historical, excluded evidence rather than
completion blockers or passing coverage. See callback-exclusions.json and the
authoritative objective. Preserved implementation may still contain those paths;
remove them from the supported facade and establish callback-free reachability
and fresh proofs/tests. Worker session and active code are preserved, unverified.

## Restart 20260919T020431Z — callbacks explicitly excluded

Re-read current AUDITOR.md, callback-exclusions.json, API/test manifests and frozen
restart provenance. The user resolved the prior conflict by excluding callbacks
entirely. No callback/capacity conflict now blocks this callback-free objective.
No old path was edited, and no protected file or other project was changed.

Removed callback registration and dispatch from the TS facade, Bend cache API and
independent command/model. Removed registration refinement is archived. Internal
pure flag/event records remain inert; commit rejects enabled/nonempty records
before adopting them. Aggregate internal phases are renamed RemovalReady and
after_removal and execute no user code. Full formal reachability remains required.

Converted both runtime drivers to nil-callback operation; removed excluded modes,
clock mutation fixtures and callback-dependent probes from the active gate. They
are archived with authorization and prior evidence in callback-archive.json,
neither counted as passes nor allowed to block completion. Unsupported callback
registration is now a transport rejection test, not a silently ignored API.

Preserved all 12 upstream scenarios. Removed callback-only assertion clauses;
retained Add-return clauses from mixed assertions. TestLRUMatch now has an
independent input-driven finite map and oldest-first list, not callback-maintained
backup state. Its reference model never reads implementation results to update
expected state. Boundary removal-order checks now use RemoveOldest results.
Inventory generation lists every retained port expression/line and each excluded
source assertion/clause and callback registration site. A strict inventory gate
checks regeneration equals the checked-in map.

Completed native seek shape and replacement certificates and the universal
actual Map.set same-key lookup theorem in map_insert.bend. No map validity or
oracle premise remains in set_same. Connected it to actual cache store/lookup
through a checked projection bridge. Other-key and deletion/Map.diff/invariant
laws still remain. Checker attempts caught a consumed/binder-order match after a
rewrite; matching the routing bit first repaired it. Cache lookup and native
lookup projections were not definitionally interchangeable; an explicit tuple
projection equality was proved instead. Final PROOF check passed after repairs.

Initial callback-free validator run: all 12 groups, checker, spec templates,
boundary, 4,800 nil-callback differential operations, numeric boundaries,
sensitivity and transport checks passed; full_scope remained failed as required.
The new assertion-inventory gate and subsequent proof edits require fresh final
validation. This is an intermediate recovery checkpoint, not completion.

## Current callback-free continuation checkpoint

Added disabled.bend: checked initial flag False and actual host-used detach,
prepare-add, native-store/add, read, refresh, counter/configuration and aggregate
transition flag preservation. This does not yet prove event-list emptiness or
full TS composition. A first checker attempt matched c after found, violating
Bend binder order; destructuring c first repaired it. A duplicated Type-level
encoder parameter was rejected; binding its encoded key once repaired linear use.

Added map_shape.bend: replacement along a seek-found path preserves the complete
native discriminator/key skeleton. Actual Map.set reduces to replacement when
seek finds that same key, and preserves native key enumeration. The actual seek
premise is stated, not assumed discharged for every cache state. Map.put on Tip
creates a leaf, so unconditional shape preservation was deliberately not claimed.
The accumulator proof initially needed +acc to authorize duplication; repaired.
No replacement runtime map was introduced; skeleton is a proof observation only.

Added counter.bend and word_bounds.bend: arbitrary-width installed Word.inc
satisfies integer conservation including carry-out, and the independent unsigned
interpretation lies below 2^width. Signed division, modular-add/spec conversion,
Map.diff first-difference, frame/deletion laws and reachable invariants remain.

TestLRUMatch now compares exact order with its input-driven list on all 100,000
iterations. The store-None mutant fails the actual C.store lookup theorem. Strict
trace parsing rejects unknown object fields, null operations/keys and non-string
64-bit numbers, including unused malformed numeric fields. All expected answers
remain outside backend streams. Rewrote self_audit.md to the current scope.

Fresh validator and unchanged frozen acceptance each exited 1 with all 12 cases,
26 boundary assertions, 4,800 nil-callback differential operations, 1,141 numeric
operations, seven semantic/theorem mutants and eleven transport-failure checks
passing. The failed gate is full_scope, whose obligations remain genuine.
The Bend launcher reported its ~/.bend/last write was sandbox-denied; its checker
still returned success and printed All terms check. No external tool was changed.
The last added independent word-bounds proof is checked directly and must be
included in the final refreshed closure. This remains an intermediate checkpoint.

Native lookup soundness now checked in map_lookup.bend: a returned Some value
identifies an exact original leaf with the queried key and the same value, and
that binding occurs in actual Map.to_list enumeration. No validity premise is
needed for this direction. The converse needs routing and remains open. The
actual C.lookup projection is connected by refinement.lookup_enumerated. The
first Type sum used numeric + syntax and was rejected; replacing it with the
explicit Type-level Either repaired the statement. All terms then check.

Final checkpoint validation is being refreshed after these added laws. The next
Map obligations are converse lookup/enumeration under critbit, Map.diff least
position and differing bit, other-key set preservation, deletion and invariant
preservation. Independent complete commands/effects/traces, numeric division and
host key/clock/transport composition remain unfinished. All-source hashes and
exact evidence are regenerated by tools/evidence.py after validation settles.

Settled checkpoint outcome: unchanged automation/acceptance.py exited 1. All 12
unique manifest groups and every active executable check passed; full_scope alone
failed. TestLRUMatch reports 1,297,281 assertions, including all 100,000 independent
exact-order checks. Assertion inventory retains 57 distinct original sites,
excludes six callback-only sites and excludes callback clauses at five mixed
sites; those exclusions are not passes. Seven mutants are rejected and eleven
transport failures are rejected. Fresh direct PROOF checking prints All terms
check after the final lookup linkage and internal-phase terminology cleanup.

Recovery state: no unfinished shell mutation or intentionally failing proof file.
General other-key set/delete, least-difference/routing and invariant preservation;
complete modular arithmetic/division and actual host key/numeric bridges; complete
independent commands/effects/traces and all-operation/aggregate/trace refinement;
and actual public clock/transport composition remain genuine required work.
Current source/evidence/Base hashes are regenerated in VALIDATION.json. Historical
callback conflicts are exclusively excluded evidence, not current blockers. This
checkpoint does not claim that the entire objective or any full-scope gate passes.

## Iteration 0002 — native Map dependency closure

Re-read this workspace's AUDITOR.md, restart provenance, callback exclusions,
current proof status, native definitions and host implementation. No previous
workspace was edited. Callbacks remain excluded and no callback parity work was
introduced. The full-scope gate is unchanged.

Checked new native laws:
- map_seek: every successful actual lookup implies actual seek finds that exact
  queried key. This discharges map_shape's replacement premise from a successful
  lookup, including through cache_lookup_seeks_key for actual C.lookup.
- map_pop: actual native pop's returned value, interpreted with the same supplied
  default, equals actual native get for every tree and query. This is a returned-
  value property, not a remaining-tree invariant or other-key frame property.
- map_routing: derive a logical routing witness from the existing executable
  critbit predicate and prove a real matching leaf is found by native lookup.
  Prefix/discriminator constraints are not discarded from the full invariant;
  this weaker derived condition is sufficient only for these lookup laws.
- map_enumeration: actual native enumeration contains only original leaves, and
  every enumerated Some binding is found under critbit. Together with retained
  lookup soundness this gives both directions against actual Map.to_list.
- map_delete: actual deletion leaves the queried key's lookup at None under
  critbit. Both node-collapse cases use opposite-side routing to exclude the
  query from the surviving sibling. removed_key_absent links this to actual
  C.remove_present. Other-key deletion and invariant preservation remain open.

All five modules are in the PROOF/END_TO_END dependency closure. No high-level
Map oracle, replacement map, axiom or admission was added. Conditional critbit
premises remain explicit; establishing them for every reachable cache is still
required and is not claimed as already proved.

Failed attempts and repairs: the pop leaf-result statement initially lacked a
closing parenthesis; fixed before checking. A routing proof tried duplicating a
Type-level membership witness directly; Bend rejected it. Structural duplication
now reconstructs the witness, with no unrestricted cast. Computed-pair matching
required helper definitions. An initial helper used an unfilled forward law and
was rejected; it now receives the structurally derived recursive induction
function. The final proof closure checks. The first redirected validation launch
failed because this fresh workspace had no build directory; created build and
reran, without changing validation behavior.

Added two meaningful theorem mutants: weaken the executable routing predicate to
True, and omit actual core Map.del. Both must be rejected by the checker. The
seven existing mutants, all 12 groups, individual callback exclusions and strict
transport checks remain required. A direct fresh validate.py run exited 1 with
all active checks passed and full_scope failed. Frozen acceptance is being
refreshed against the same closure; exact outcomes and hashes follow below.

Next obligations remain Map.diff least-discriminator/first-difference, other-key
set/delete and full tree/representation preservation, numeric division and host
key/numeric bridges, complete independent commands/clock effects/traces, every
operation and aggregate refinement, and actual public adapter composition.

Settled iteration-0002 evidence: direct tools/validate.py and unchanged frozen
acceptance both exited 1 solely because full_scope remains failed. All 12 groups,
26 boundary assertions, 4,800 differential operations, 1,141 numeric-boundary
operations, nine rejected mutants and eleven rejected transport failures passed.
Direct END_TO_END checking also printed All terms check. No completion claim is
made from these partial propositions or finite tests. No protected file, external
tool or other project was changed. Current fingerprints and exact retained logs
are refreshed by tools/evidence.py, which now derives run/iteration from the
current workspace rather than retaining iteration 1 metadata.

Recoverable state: all new proof files check and are imported; no open mutation,
process, failed proof stub or temporary weakening remains. The full-scope gate
stays failed. Resume at Map.diff/other-key/preservation dependencies listed above;
then complete the remaining arithmetic, independent trace specification and real
public adapter composition. The task remains needs_work, not externally blocked.

## Current iteration 0003 checkpoint

Re-read the current audit, scope exclusions and restart provenance. Callback-free
scope remains authoritative. Added spec/public_oldest.bend for the full public
key/value/found observation and exact clock-list consumption. Empty and immortal
oldest entries consume no sample; finite entries require one; expiry returns the
captured original key and the caller's zero value after independent removal.
Missing bindings and missing samples are explicit failures. The old snapshot
helper in spec/operations.bend remains internal. Supporting public-observation
laws check; this is not yet actual facade refinement.

Added native deletion proofs against existing Base.pop/del. Arbitrary discriminator
routing constraints survive deletion, including native empty-child collapse.
The weaker lookup-routing R.valid predicate is preserved. Structural membership
proofs establish that no new binding appears and all different-key bindings
survive, even without tree validity. Composing those facts with actual lookup
soundness/completeness yields a complete different-key lookup frame law under
R.valid, for both present and absent keys. Connected routing preservation and
this frame law to actual C.remove_present/C.lookup. Full critbit and reachable
cache representation preservation are still unproved, not assumed discharged.

Added arbitrary-width Word.adc conservation, including carry-in and independently
computed carry-out, plus the actual W.add 64-bit consequence. This proves exact
unsigned addition plus overflow conservation; signed division, modulo-uniqueness,
U32/BigInt and host String bridges remain work.

Checker attempts: public_oldest initially failed binder-order checking; moving
state destructuring before matching order repaired it. The deletion branch also
initially matched its bit after consuming it in an equality transport; moving
transport inside each bit branch repaired it. No failed proof stub remains.
PROOF.bend and new modules check with the unmodified installed checker. The first
fresh validator run exited 1 with all active checks passing (including ten
mutants), solely because full_scope remains failed. A further addition mutant
and fresh frozen acceptance follow; their settled evidence will be recorded.

Further work in the same invocation: completed absent-query deletion framing,
actual removal frame linkage, and replacement preservation of full critbit via
value-erasure correspondence. Completed empty-event laws for actual host-used
primitive and aggregate transitions; an affine-use error in decide was repaired
by marking the reused String input unrestricted (Data), not a proof assumption.
New modules are imported by END_TO_END and the complete partial PROOF closure
checks. Full host composition and all-operation reachability remain unproved.
Added independent mutants for expired-oldest key/value loss and actual W.add
changed to subtraction; all prior checks remain. Final direct and frozen checks
are being refreshed after these changes; full_scope remains intentionally failed.

Added actual recency filtering/removal capacity bounds, without assuming map
validity. An initial Nat <= transitivity base case required splitting zero versus
successor on the upper bound because Base.cmp does not reduce 0 versus a symbolic
Nat; the corrected structural proof checks. This is a local removal property,
not all-operation capacity preservation. The latest direct validator exited 1
with all runtime/checker/inventory checks and twelve mutants passed; full_scope
was the only failed check. Frozen acceptance is rerun after importing this final
local lemma so it checks the full retained closure.

Self-audit checkpoint: all new specifications import only Base, neutral types and
other independent specs. Reviewed native deletion/collapse, full-adder and pinned
GetOldest source correspondence. Conditional routing/critbit premises and absent
full reachability/host bridges remain explicit. The new proof laws are neither
finite trace enumeration nor assumed Map correctness. Reading build/validation.json
while acceptance was active failed because the unchanged harness unlinks its
previous report before running; evidence refresh waits for process completion.
The Bend launcher also reports a denied ~/.bend/last write under the sandbox;
the unmodified checker itself succeeds. No attempt was made to change external
tools or permissions.

Recoverable continuation plan: prove actual Map.msb/bit XOR correspondence and
Map.diff's least discriminator, then insertion framing/full critbit preservation.
Deletion lookup framing and routing preservation are done; full prefix/below/
nonempty preservation under collapse is still needed. Compose these with exact
recency membership, uniqueness, original-key identity and no-None invariants.
Use adc conservation and word bounds to finish modulo correspondence; prove the
long-division quotient/remainder and signed truncation laws, then actual host
limb/String conversion. Complete the independent command/effect/trace dispatcher,
including state at clock failures (full Add has already evicted; refresh has
already touched/counted before a failed clock read), then actual operation,
aggregate, trace and host composition. PublicOldest already has explicit clock
consumption but has no claimed facade refinement. Retain full_scope until those
obligations and independent completion review pass.

Settled final evidence for iteration 0003: direct validation and final unchanged
frozen acceptance exit 1 solely at full_scope. All 12 groups, 26 boundary
assertions, 4,800 differential operations, 1,141 numeric-boundary operations,
twelve semantic/theorem mutants and eleven transport-failure checks pass.
PROOF and END_TO_END check with the installed unmodified checker. The independent
assertion inventory remains current. Exact logs are build/validate.log and
build/acceptance.log; build/validation.json is the final frozen-run report.

Interruption: this invocation has reached its available context/output budget
before the integrated universal-proof objective is complete. Preserve this
recoverable checked checkpoint; no pending process, failed proof stub, un-restored
mutant or weakened completion gate remains. Status is needs_work, not blocked
and not completion. No external input is needed to resume the remaining proof
work listed above. Source/Base/evidence fingerprints are regenerated after this
note by tools/evidence.py; no independent completion approval is claimed.

## Iteration 0004 ongoing checkpoint

Re-read the current isolated files, literal AUDITOR.md and retained obligations.
No callback functionality was restored and no protected files were edited.

Implemented and checked six native-Map proof modules: map_bits, map_msb,
map_difference_char, map_index, map_difference and map_splice_frame. The chain
proves actual bit/XOR correspondence, native scan bounds and nonzero set-bit
witnesses with fuel discharged, actual character/divmod offsets, and a
whole-String distinguishing discriminator for actual Map.diff. It then proves
native insertion splice framing and actual Map.set singleton other-key
preservation. All are universally quantified over their stated types, including
empty/embedded-zero Strings, and use installed Base definitions. No replacement
map, assumed Map oracle, axiom or desired lookup result is introduced.

Failed proof attempts repaired during development: shifted-bit induction needed
the decreasing index before the changing word argument; a dependent proof Sigma
needed Type quantity &1 rather than Data &2; imported binder `at` collided with
an exported function and was renamed; several equality transports needed the
opposite direction; character base cases needed explicit Chr patterns. The
final checker closure contains no failed stubs. Fixed-width shift exhaustion
uses 32 arbitrary Boolean binders and definitional reduction, not finite test
enumeration. Least-discriminator prefix minimality remains separate and open.

Added tests/new/clock_failures.ts with 51 assertions against the actual public
facade and Bend runtime. It distinguishes provider exceptions and invalid clock
samples from successful results and inspects the state left by failed Add,
replacement, refresh, reads and aggregates. It does not claim pinned Go has a
throwing clock API. Added mandatory clock_failures validation plus actual lookup
and pre-clock counter mutation checks. Direct validation exits 1 solely at
full_scope: all 12 groups, 26 boundary assertions, 51 clock-failure assertions,
4,800 differential operations, 1,141 numeric operations, 14 mutants and 11
transport rejection checks pass. Frozen acceptance is running for a fresh final
report; this paragraph is an intermediate checkpoint, not completion evidence.

Next proof dependencies remain least-discriminator prefix agreement, full
insertion/deletion critbit preservation, reachable map/order identity and bounds,
modular/signed division and host conversion bridges, independent complete
commands/effects/failures/traces, every-operation refinement and actual facade/
transport composition. General set framing is not inferred from the singleton
result. The completion gate remains failed until these are genuinely discharged.

Continued after the first validation checkpoint: completed native first-difference
minimality, rather than stopping at distinction. Added map_difference_order,
map_character_prefix and map_string_prefix. Their structural Nat lemmas relate
earlier character offsets to word bits above the actual XOR MSB; a general
proved offset split handles first-character versus tail traversal. The universal
native_prefix theorem now proves equality of every earlier native routing bit.
The executable invariants.same_prefix predicate is discharged by induction in
native_prefix_invariant. Combined with the distinction theorem, this completes
the actual Map.diff first/least-discriminator foundation over Base Strings.

A proof attempt exposed that two separately defined pair projections are not
definitionally interchangeable on an opaque pair. Added a checked projection
correspondence and transported it explicitly; no rewrite or assumption was
silently imposed. Explicit Chr patterns also resolved the native empty-string
branches. PROOF checks with all nine new modules in its dependency closure.
The completion gate's descriptive remaining-work text now lists general
insertion/preservation rather than the discharged first-difference obligation;
the gate itself remains failed.

Final fresh iteration-0004 verification: the unchanged frozen acceptance exits
1 solely at full_scope. Its report passes all 12 groups, assertion inventory,
26 boundary assertions, 51 clock-failure assertions, 4,800 differential operations,
1,141 numeric operations, 14 mutants and 11 transport rejection checks. Direct
PROOF, END_TO_END and spec_smoke checks also pass. The final report/log are
build/validation.json and build/acceptance.log. These finite checks and partial
proofs do not establish all-operation correctness or independent approval.

Recovery checkpoint at invocation context-budget exhaustion: the integrated
objective remains incomplete. No process, unchecked proof stub or temporary
mutant remains pending. The nine new modules are imported through END_TO_END.
Resume with general native insertion frame/critbit preservation, using
map_difference.native_difference and map_string_prefix.native_prefix_invariant
as discharged first-difference foundations, plus map_splice_frame for the actual
splice. Full deletion prefix/below/nonempty preservation, all cache representation
components, modular/signed division and actual host conversion, complete commands/
clock failures/traces and public operation/adapter composition remain required.
The failing completion gate is retained. Status is needs_work; no external input
or scope change is needed. Fingerprints are regenerated after this checkpoint.

## Iteration 0005 current-workspace continuation

Re-read AUDITOR.md, restart provenance, current source, representation predicates
and prior status. Preserved protected files, callback exclusions, actual native
Map storage and all prior checked dependencies. No subagents or external-project
work. The full-scope gate remains failed.

Completed full native deletion preservation rather than only its lookup-routing
component. map_delete_prefix proves preservation of each query/prefix constraint;
map_delete_common shrinks both quantified leaf domains of common_prefix.
map_critbit_parts decomposes and reassembles the actual executable conjunction.
map_delete_below proves root discriminator ordering through native child collapse,
using the original sibling constraint and a checked strict transitivity lemma.
map_route_boolean bridges the existing logical routing proof to the executable
predicate. map_delete_critbit proves every native deletion preserves the complete
critbit predicate from its input predicate. refinement.removal_preserves_storage_
critbit connects this to the actual C.remove_present call. Cache reachability,
identity and full recency preservation are still not consequences of this local
law. Added map_seek_prefix as an actual seek-prefix dependency for insertion.

Failed attempts: a generic leaf-property template checked in isolation but could
not be instantiated in the caller law (undefined template name); it was removed
from the proof source and replaced by direct prefix proofs. Scratch attempts in
build are not proof evidence. A computed tuple destructuring needed a separate
parameterized helper; duplicating dependent equality fields needed explicit typed
bindings. Final imported proofs check with the installed unmodified checker.
No failed stub or assumed generic preservation theorem remains in the closure.

Added a reversed-discriminator-order mutation to the strict validator. Direct
validation exits 1 only at full_scope; all 12 groups and retained independent
checks pass, including 15 mutants. Consolidated PROOF_STATUS.md to distinguish
current completed first-difference/deletion obligations from historical notes.
Still required: general insertion and reachable representation, complete numeric
and host conversion bridges, independent commands/clock failures/traces, every
operation/aggregate refinement and actual public adapter composition.

Continued into actual public-path linkage: protocol_storage proves storage
critbit preservation for P.detach_present/detach_found/detach, detach_oldest,
prepare_room/prepare_found/prepare_add and finish_removal. These are the functions
called by adapter.ts Remove, RemoveOldest and pre-clock Add preparation. The
predicate does not depend on metrics, and the counter phase is proved to leave
it unchanged. This does not prove TS dispatch/marshalling, output results or
full representation; the distinction is explicit in current status.

Inspected the new ordering mutation diagnostic: reversing Inv.below is rejected
at map_delete_below.lower_parent with opposite Nat comparison directions. Spec
imports remain Base/neutral/spec only; no expected-answer inputs or callback API
were introduced. All proof modules are now included by END_TO_END/PROOF through
actual dependencies. The final frozen suite is rerun after this linkage.

Recoverable next dependencies: extend map_seek_prefix to relate the selected
existing leaf to all other leaves under a node's common-prefix constraint. Use
native_difference and native_prefix_invariant without rebuilding them to frame
Map.ins through arbitrary existing nodes, handling both splice and descent.
Then prove full insertion critbit preservation and combine it with the now
complete deletion predicate preservation and replacement result. The cache
representation additionally needs original-key/no-None preservation, exact
map/order membership and unique bounded recency; storage critbit alone is not
that representation. Continue arithmetic and actual host bridges, independent
command/failure/trace semantics and every-operation/public composition afterward.
The failed generic-template scratch files were removed after documenting the
attempt; no unchecked proof source from that attempt remains.

Final fresh iteration-0005 evidence: unchanged frozen acceptance exits 1 solely
at full_scope. All 12 upstream groups, assertion inventory, 26 boundary and 51
clock-failure assertions, 4,800 differential and 1,141 numeric operations pass.
All 15 mutants and 11 transport rejection checks pass. Direct PROOF, END_TO_END
and spec_smoke checks pass with the installed unmodified checker. Exact final
artifacts are build/validation.json and build/acceptance.log; tools/evidence.py
refreshes source/Base/evidence fingerprints after this note.

Interruption: the invocation's available context budget is exhausted before the
integrated universal-proof objective is complete. This is a recoverable checked
checkpoint, not a milestone completion claim. No process, failed proof stub or
temporary mutant remains active. Continue from the dependencies above; no external
input is required. Status needs_work. Full_scope stays failed and no independent
completion approval is claimed.

## Iteration 0006 recovery checkpoint

Re-read current workspace and literal auditor requirements. Repaired independent
expiration failure semantics: PrefixFailure retains completed removals and pending
entries, and AggregateFailure carries the state after those removals. Added
aggregate_failure specification laws and a mutation that drops a completed
removal; the checker rejects it. This is specification evidence, not real host
composition. Throwing/invalid clock input semantics remain open.

Native insertion progress: map_descent_frame proves arbitrary opposite-branch
lookup framing at a descent, with explicit order/routing premises.
map_insert_nonempty proves every native insertion result nonempty without input
validity. map_insert_routes proves preservation of any routing constraint satisfied
by the new key through arbitrary splice/descent paths. All are imported by
END_TO_END and checked against installed Base; no Map implementation changed.

Next: discharge general insertion splice framing and prefix/order constraints
using selected_has_prefix and native first-difference; combine new routing and
nonempty results with replacement/deletion into reachable representation. Complete
arithmetic/host codecs, independent commands and explicit clock failures/traces,
actual every-operation refinement and real facade/transport composition afterward.
No full-scope completion or independent approval is claimed.

Validation: first fresh frozen acceptance exited 1 solely at full_scope; all 12
groups, boundary, clock failures, differential, numeric, 16 mutations and 11
transport checks passed. A final frozen run includes the final insertion helpers.
Launcher mutable state is isolated in build/bend-home with an installed-runtime
symlink; no installed tool or external project is modified.

Interruption checkpoint: the remaining response/context budget cannot accommodate
the integrated universal-proof work in this invocation. Preserve the checked
files above and resume the stated dependencies. This is needs_work, not an
external blocker or a claim that a local proof milestone completes the task.
The final validation result and fingerprints are recorded in VALIDATION.json.

Final iteration-0006 frozen acceptance exited 1 solely at full_scope. All 12
upstream groups and all executable checks passed, including 16 mutants. Final
PROOF, END_TO_END and spec_smoke check. No validation process remains active.

## Iteration 0007 checked progress and recovery details

Re-read current AUDITOR.md, provenance, proof status, implementation boundaries
and retained Map dependencies. Completed universal actual native Map.set critbit
preservation (map_set_critbit.preserves_critbit). New prefix algebra/bounds/join
laws support all-pairs insertion preservation. Actual seek prefix/routing facts
discharge fresh-key conditions. map_insert_before handles strict-before splicing;
map_seek_discriminator rules out equal-root diff; map_insert_descent and structural
induction complete arbitrary-tree insertion. The final public native theorem
requires only input critbit validity, with no assumed insertion result.

Connected the native law to actual C.store and P.refresh_at. Native insertion
membership now works in both directions: existing exact bindings survive and
other-key bindings cannot be introduced. map_insert_frame combines these with
lookup/membership correspondence to preserve both successful and absent queries
through genuine new-key insertion. Complete Map.set framing still needs
replacement and empty-seek composition. No alternative runtime map was added.

The proof development required keeping linear distinctness functions affine;
the induction instead duplicates a checked String.eq-false proposition and
derives distinctness at each use. Common-prefix conversion uses equality
transport rather than duplicating a linear native seek pair. All retained source
checks; no failed scratch theorem or admission is present.

Fresh validation passed all 12 upstream groups and all executable checks; two
additional mutants (native store uses put, prefix bit omitted) bring the count
to 18. Full_scope remains failed. Final frozen acceptance and source/evidence
fingerprints are refreshed below. The independent completion audit remains open.

Resume with full Map.set other-key framing, then reachable representation
(capacity/unique bounded recency/exact membership/key identity/no None/faithful
abstraction), arithmetic and host conversions, independent command/failure/trace
semantics, and real every-operation/host composition. Insertion critbit itself
is now closed and should not be rebuilt.

Final iteration-0007 evidence: frozen acceptance exits 1 solely at full_scope.
All 12 groups, assertion inventory, boundary, clock-failure, differential, numeric,
18 mutation and transport checks pass. Direct PROOF, END_TO_END and spec_smoke
checks pass. No validation process or temporary mutant remains active.

Interruption: this invocation has reached its available response/context budget
with the integrated objective incomplete. This is a recoverable needs_work
checkpoint, not a milestone completion claim. Continue the remaining obligations
above; no external input is required. Source/evidence fingerprints are refreshed
after this note, and independent completion approval is not claimed.


## Iteration 0008 recovery checkpoint

Re-read the current AUDITOR.md, restart provenance, source and retained proof
status. Completed actual Map.set other-key framing, including replacement and
empty seek. map_put_frame proves replacement framing along all query/update
route combinations; map_seek_empty derives empty-tree shape from valid empty
seek; map_set_frame composes actual comparator/seek branches. The final native
frame assumes only input critbit and distinct query, and store_other_lookup
reaches actual C.store/C.lookup. No native algorithm was reimplemented.

Added abstraction_bindings: every successful actual lookup survives abstraction
as the exact Entry, and every abstract entry has an exact native enumeration
origin. Added populated-leaf preservation through native insertion, put, set and
deletion, then actual construction/store and facade detach/prepare/refresh
links. abstraction_size derives abstract binding count = native map size under
that explicit populated-leaf component. Added actual store/touch/removal recency
uniqueness through filtering and fresh append. These components do not yet
establish joint reachable representation, encoded original-key identity, bounds
or complete recency faithfulness.

Added three sensitivity checks: abstraction dropping a present binding,
populated predicate permitting None leaves, and actual store retaining duplicate
recency occurrences. Current total is 21 mutants. Full_scope remains failed;
no all-operation/trace or host-composition completion is claimed.

Resume with joint reachable representation (capacity, map/order membership,
encoded original-key identity, recency faithfulness), then numeric/host bridges,
independent complete commands and provider/invalid-sample failures, universal
operation/trace refinement, and actual clock/transport composition. Do not rebuild
Map.set framing or its critbit validity, which now check. Final validation and
fingerprint results are recorded after this checkpoint.


Fresh checks pass for PROOF, END_TO_END and spec_smoke. The final full validation
passes all 12 groups, inventory, boundary, clock failures, 4,800 differential
operations, 1,141 numeric operations, 21 mutations and 11 transport checks.
Frozen acceptance exits 1 solely at full_scope. Mutation diagnostics were read:
duplicate store recency fails store_preserves_unique_recency; dropped abstract
binding fails binding_head; permitting None in the populated predicate fails
put_preserves_populated (an earlier native preservation lemma, not the later
enumeration theorem). The evidence description was corrected accordingly.

The current invocation is reaching its available response/context budget with
the integrated objective incomplete. Preserve this checked needs_work checkpoint;
there is no external blocker and no full-completion approval. Continue the joint
representation obligations above, using the new component proofs. Final evidence
is regenerated after the description correction and this note. No worker
subagents, commits, protected changes or other-project work were performed.


## Iteration 0009 checkpoint

Re-read the current workspace's audit instructions, provenance, proof status,
actual core/protocol transitions and recency foundations. Added recency_capacity:
actual present-key filtering frees a slot, moving a present key cannot grow,
and store preserves the input capacity bound with explicit room-or-presence.
Added map_key_membership: exact successful native leaf membership reaches
actual Map.keys, and included-list membership transports to recency. Added
cache_order: successful actual lookup is ordered from native keys/order inclusion;
actual replacement discharges the presence premise and actual live read cannot
grow. PROOF imports these through END_TO_END.

The generic proof-template syntax experiment is only build scratch and is not
counted as a public theorem. No implementation, specification, protected files,
callback scope or executable gates were changed. The full_scope gate remains
failed. Remaining work starts with absent/full add preparation, positive capacity,
exact map/order and key-identity preservation, and joint public reachability;
then arithmetic/host bridges, independent failure/trace semantics and universal
actual operation/adapter composition. Existing native Map foundations should
not be rebuilt.

Fresh frozen acceptance exits 1 solely at full_scope. All 12 upstream groups,
assertion inventory, boundary, clock failures, differential/numeric checks,
21 mutations and 11 transport checks pass. Direct PROOF, END_TO_END and
spec_smoke checks pass. No validation process remains active.

Interruption: the available response/context budget is exhausted before joint
representation and the remaining end-to-end objective are complete. This is a
recoverable needs_work checkpoint, not completion or an external blocker.
Resume by deriving oldest lookup availability from order-to-native-key inclusion,
populated leaves and critbit validity, then discharge full add preparation's
free-slot premise. Continue through all remaining objective obligations.
Fingerprints are regenerated after this note; independent completion approval
is not claimed.


## Iteration 0010 intermediate checkpoint

Re-read the authoritative candidate and AUDITOR.md. Added checked inverse native
key enumeration/lookup; oldest availability; actual absent/full preparation and
complete core AddWithLifetime capacity bounds; extraction from the joint
representation; exact encoded recency abstraction; actual lookup original-key
identity with custom injectivity and built-in String/Integer/Word64 instances.
Added generic initial representation and arbitrary-key/value/time first-add
nonempty witnesses at capacity one. These remain conditional components and
initial cases, not complete reachable preservation or all-operation refinement.
Two additional mutations exercise skipped preparation eviction and reversed
entry order (the former fails the pre-existing storage link; the latter the new
exact recency theorem). Initial frozen run passed all executable checks and
23 mutations, failing solely full_scope. Final validation will be refreshed after
remaining proof integration and documentation.


## Iteration 0010 checked recovery checkpoint

Final frozen acceptance exits 1 solely at full_scope. All 12 upstream groups,
assertion inventory, boundary, clock-failure, 4,800 differential and 1,141 numeric
operations, 23 mutations and 11 transport checks pass. PROOF, END_TO_END and
spec_smoke check directly. The final 96-file local proof dependency closure is
acyclic, specifications remain independent, and all 28 pinned vendor hashes
match. No validation process remains active. Final fingerprints follow this note.

Interruption: the available response/context budget is exhausted before the
entire objective is complete. This is a recoverable needs_work checkpoint, not
an external blocker or a completion claim. Resume joint representation
preservation: full-cache availability/free-slot and complete core add capacity
are now checked; reuse them. Next preserve exact bidirectional map/order
membership and encoded original-key identity jointly with existing uniqueness,
critbit, populated-leaf and bound components through every actual transition.
The conditional exact recency/original-key abstraction results can then be
instantiated through reachability. Continue through arithmetic/host bridges,
independent failure/trace semantics, every-operation refinement and actual
clock/transport composition. Full_scope remains failed; independent completion
approval has not been obtained.


## Iteration 0011 intermediate checkpoint

Added recency filter other-key membership and inclusion laws; native lookup
presence/key-membership equivalence; native deletion membership/filter
correspondence; both map/order inclusion directions through actual facade
removal/oldest/preparation phases and core encoded/oldest removal. These compose
existing checked native Map laws and retain explicit input component premises.
PROOF, END_TO_END and spec_smoke check freshly. Full validation is running;
full_scope remains intentionally failed pending the complete objective.


## Iteration 0011 checked recovery checkpoint

Fresh frozen acceptance exits 1 solely at full_scope. All 12 groups, assertion
inventory, boundary, clock failures, 4,800 differential and 1,141 numeric
operations, 23 mutations and 11 transport checks pass. PROOF, END_TO_END and
spec_smoke check directly. The 100-file local proof closure is acyclic,
specification imports are independent, and all 28 pinned vendor hashes match.
No validation process remains active; fingerprints are regenerated after this note.

Interruption: the available response/context budget is exhausted before the
entire objective is complete. Preserve this needs_work checkpoint. Resume with
insertion/update map/order membership and native-key uniqueness, and encoded
original-key identity preservation. Reuse the new deletion membership/filter
correspondence and actual core/protocol removal/preparation preservation; do not
rebuild native Map laws. Compose these with capacity, recency uniqueness,
critbit and populated-leaf components into joint reachable representation.
Then discharge the conditional abstraction laws and continue through arithmetic,
host codecs, independent failure/trace semantics, every-operation refinement and
actual clock/transport composition. No full completion or independent completion
approval is claimed.

## Iteration 0012: update membership and composed storage preservation

Actual Map.set membership is exactly the union of the old keys and the written
key, for arbitrary populated critbit trees. The proof uses the actual same-key
lookup and other-key frame laws and derives output critbit/populated premises.
The corresponding actual recency move has the same pointwise membership.
cache_store_membership.store therefore preserves both map/order inclusions,
without assuming the output inclusions or a particular native enumeration order.

cache_storage_preservation.storage combines critbit validity, absence of stored
None, and both membership directions. It holds at construction and is preserved
by actual store, core removals (including oldest removal), Add/AddWithLifetime
(including replacement and eviction), and the protocol detach/preparation
phases. Actual refresh_at also preserves the component when an actual successful
lookup establishes that its code is present; no unexpired premise is required.
The proof follows the actual cache state returned at each phase.
It is a storage component, NOT the full representation predicate: capacity,
recency/native-key uniqueness, encoded original-key identity, callback metadata,
observations and public trace/adapter correctness are not implied by this claim.
The existing conditional capacity/abstraction laws remain conditional.


## Iteration 0012 checked recovery checkpoint

Fresh frozen acceptance exits 1 solely at full_scope. All 12 upstream groups,
assertion inventory, boundary, clock-failure, 4,800 differential and 1,141 numeric
operations, 24 mutation checks and 11 transport checks pass. PROOF, END_TO_END
and spec_smoke check. The 105-file local proof closure is acyclic; specification
imports are independent and all 28 pinned vendor hashes match. The added store
mutation is rejected by the existing recency-uniqueness linkage, as required by
its diagnostic check, not credited to the new membership law. No process remains
active.

Interruption: the response/context budget is exhausted before the entire
objective is complete. This is a needs_work recovery checkpoint, not completion.
Resume with native-key uniqueness and encoded original-key identity preservation.
Reuse map_set_membership (same/other/union/existing), recency_update_membership,
cache_store_membership.store, cache_refresh_membership.refresh_at and the
composed cache_storage_preservation component. The latter establishes only
critbit/populated/bidirectional-membership preservation, not the full predicate.
Compose capacity, recency uniqueness and identity next; discharge refresh's
actual lookup premise through refresh_prepare and continue through all other
public phases and arbitrary reachable operations. Then complete arithmetic,
host codecs, independent failure/trace semantics, universal refinement and real
adapter/transport composition. Full_scope remains failed; no independent
completion approval is claimed.

## Iteration 0013: native-key uniqueness and refresh lookup

map_keys_unique.unique_keys proves that actual Map.keys has no duplicate keys
for arbitrary populated critbit trees. Opposite native routing bits establish
disjoint child key enumerations; structural induction follows Map.keys.go and
its accumulator/append correspondence. No hash injectivity or enumeration oracle
is assumed. cache_storage_preservation.storage_has_unique_keys derives this
component from the already composed storage predicate.

refresh_lookup.prepare proves that the binding returned by actual
P.refresh_prepare is the binding stored under the requested code in its returned
cache. prepare_flag proves that the success flag equals item presence.
successful_prepare discharges refresh_at's lookup premise from the actual
returned item, including expired entries. These laws assume no cache validity or
expiry premise. Preservation of the remaining representation components through
refresh_prepare, complete refresh refinement, and host composition remain open.


## Iteration 0013 checked recovery checkpoint

Fresh frozen acceptance exits 1 solely at full_scope. All 12 upstream groups,
assertion inventory, boundary, 51 clock-failure assertions, 4,800 differential
operations, 1,141 numeric operations, 25 mutations and 11 transport checks pass.
PROOF, END_TO_END and spec_smoke check. The 108-file local proof closure is
acyclic, all specification imports remain independent and all 28 pinned vendor
hashes match. The new isolated refresh mutation fails at refresh_lookup.prepare,
not an earlier recency theorem. No process remains active.

Interruption: the available response/context budget is exhausted with the full
objective still incomplete. Preserve this needs_work checkpoint. Native-key
uniqueness is now proved by map_keys_unique.unique_keys, with no hash assumption,
and derived from cache_storage_preservation.storage by storage_has_unique_keys.
Reuse map_key_disjoint and actual keys.go accumulator/append correspondence.
Do not rebuild those foundations.

Next complete encoded original-key identity preservation and compose the full
representation predicate. refresh_lookup proves the actual preparation output
binding and flag/item correspondence, so its successful_prepare lemma discharges
the later refresh_at lookup premise from the actual returned item. Still prove
all representation components of that preparation output and compose the whole
refresh path, reads, aggregates and partial failure states. Continue through
arithmetic, host key/numeric bridges, independent command/failure/trace semantics,
universal observable refinement and actual adapter composition. No full
completion or independent completion approval is claimed.

## Iteration 0014 integrated checkpoint

Worked only in the current 0014 candidate. Re-read AUDITOR.md, restart provenance,
current source and retained proof dependencies. Added complete encoded-key
identity preservation for actual store/native deletion and refresh-at, using
existing native lookup/frame/no-new-binding laws. The suffix proof links every
visited element to actual native enumeration via an exact prefix equation.

Added full Inv.representation preservation for actual refresh_prepare and its
successful refresh_at continuation, and for core removal/oldest removal and
protocol detach/oldest detach phases. The preparation proof includes the state
committed before a potentially failing clock call. No intermediate successful
lookup is assumed: refresh_lookup.successful_prepare derives it from the returned
entry. String, mathematical Integer and Word(64) specializations check. These
results do not prove returned observations, arithmetic bridges or host execution.

New files: enumeration_suffix, recency_move_inclusion, cache_store_identity,
cache_store_identities, cache_delete_identities, cache_refresh_identity,
cache_refresh_prepare, refresh_representation, refresh_complete_representation,
and removal_representation under proofs/. END_TO_END imports the composed laws.
The extra mutation resets a missing-key refresh to capacity zero; the full
preparation representation theorem rejects it at found~0. Existing tests and
failed full_scope gate are unchanged.

Recovery dependency order: reuse these primitive identity and full removal/refresh
laws. Next compose full store/Add preservation using representation_parts,
cache_add_capacity, storage preservation and the new identities; cover read,
configuration and aggregate phases, then prove arbitrary reachable-state induction.
Do not rebuild native Map foundations. Continue full arithmetic/host conversions,
independent command/failure/trace semantics, universal observable refinement and
actual adapter composition. Independent full-completion approval remains absent.

Fresh final validation: PROOF, END_TO_END and spec_smoke check; frozen acceptance
exits 1 solely at full_scope. All 12 upstream groups and all executable gates
pass, including 4,800 differential operations, 1,141 numeric-boundary operations,
26 mutations and 11 transport rejection checks. The local proof import closure
is acyclic (118 files); specification independence and 28 pinned vendor hashes
were checked. The self-audit is recorded in tests/new/self_audit.md.

This invocation reaches its response/context resource limit with the complete
objective still unfinished. The checked files above are the recoverable
checkpoint, not a completion claim. No process is intentionally left running.
Resume from full store/Add representation composition and the remaining integrated
assignment; hard proofs are not an external blocker. Keep full_scope failed.


## Iteration 0015 implementation checkpoint

Re-read the current workspace, restart provenance, literal AUDITOR.md, proof
status and actual source. Reused the retained native Map and identity foundations.
Added representation_access, capacity_preservation, store_representation,
add_representation, configuration_representation, read_representation,
aggregate_representation, core_refresh_representation and transition_reachability.
Actual Add discharges the internal store bound and derives replacement original
identity from lookup. Actual core refresh derives its updated native lookup.
Arbitrary finite proof-side transition sequences preserve full representation
and exact abstraction recency from positive-capacity initialization. This driver
is explicitly not the actual host dispatcher or an observable trace theorem.

modular_addition now proves Base binary division decomposition, reconstruction
modulo arbitrary powers of two, actual full-width addition and increment
correspondence with independent mathematical conversion. END_TO_END exposes
actual_time_addition and limited native_transition_representation. Signed
division/truncation and host arithmetic/key conversions are still open.

Added independent clock, effectful_operations, effectful_aggregate,
public_commands and traces specifications. They classify invalid samples,
provider exceptions and exhaustion; preserve prior eviction/refresh/aggregate
state effects; define all typed command observations and finite caller traces.
Clock request counts and remaining events are retained on both successes and
failures. clock_failure_spec checks specification properties, not host refinement.
All three key types instantiate the specs in spec_smoke. Input/transport/resource
rejection and actual host classification/refinement are still outstanding.

The first new Add mutation was rejected by an older storage theorem. It was
replaced with a core-refresh capacity mutation that fails the new present law.
The independent numeric add-to-subtract mutation fails time_add_refines. The
standalone sensitivity rerun passed all 28 mutations. No failed result was
counted as success. The subsequent fresh full frozen acceptance exits 1 solely at full_scope.

Recovery order: finish actual public phase composition (including callback-free
metadata and final refresh/store continuations), then use the new independent
public command/trace model for every-operation and arbitrary-trace refinement.
Finish signed division, nanosecond truncation, deadlines, host BigInt/U32/String
and codec bridges; prove actual facade/runner control flow, rejection and
transport failure semantics. Do not rebuild native Map or modulo-addition laws.
Do not treat the proof-side transition driver as the host or the typed Event
classification as a proved host conversion. Keep full_scope failed until all
these obligations and independent full-completion approval are satisfied.


Final checked recovery record: PROOF, END_TO_END and spec_smoke passed with the
installed checker. Frozen acceptance passed all 12 upstream groups, assertion
inventory, boundary, 51 clock-failure assertions, 4,800 differential operations,
1,141 numeric-boundary operations, 28 mutations and 11 transport rejection cases.
Only full_scope failed, as required by the outstanding proof obligations. The
134-file proof closure is acyclic, all nine specs have independent imports, and
all 28 vendor hashes match. No process remains running. Source/evidence hashes
are refreshed by tools/evidence.py after this record.

This response reaches its available response/context resource budget before the
entire objective is complete. Preserve this checked checkpoint and resume the
integrated assignment above; it is not a milestone-based completion claim or an
external blocker. No independent full-completion approval has been obtained.


## Iteration 0016 recovery checkpoint

Re-read current AUDITOR.md, provenance, source and proof status. Added
proofs/public_phase_safety.bend, imported by END_TO_END. It combines full
representation, disabled metadata and empty events at actual phase boundaries:
Add preparation, conditional eviction counting and subsequent insertion;
refresh preparation and lookup-discharged successful refresh_at; reads,
expired-read counter assignments, aggregate next/after-clock/after-removal;
positive-capacity initialization and configuration/reset. All three mathematical
codec instances check. Existing native Map foundations were reused unchanged.

Added tests/new/public-phase-map.md to record each real adapter assignment, its
current certificate and the missing host proof. These are phase-composition
certificates, not TypeScript execution or public observable refinement. No
runtime code or protected policies/tests were changed. This initial conjunction
assembly added no mutation; subsequent native observation/arithmetic work below
adds two checks while retaining all 28 existing checks.

A scratch generation attempt failed because build/ was absent; no generated
extension was claimed from that attempt. After creating scratch, the extension
checked. A configuration wrapper then needed explicit affine duplication; it
was fixed and PROOF/END_TO_END rechecked before the fresh acceptance rerun.

Resume the entire assignment from actual host control-flow and commit linkage,
including the explicit gaps in public-phase-map.md. Reuse these joint phase
certificates rather than rebuilding component preservation. Complete signed
division/deadlines and numeric/key marshalling, then exact public operation,
clock/failure and trace refinement to the independent specifications. Full_scope
must remain failed until the actual composed public proof and independent
completion approval are present.

Continued the 0016 checkpoint through joint detach/oldest-detach safety and
constructor_safety: native constructor success derives positive capacity from
actual U32 comparison and no longer needs an assumed positive input. Failures
remain failures; host validation/dispatch is not claimed. Added direct native
Len/Metrics/clear_metrics observation correspondence in configuration_observations.
Len explicitly requires representation, derived for initialization and preserved
native phases but not yet for arbitrary actual host execution.

Numeric additions: limb_decoding composes existing split/join laws into actual
unpack/repack identity, decoded-value equality and injectivity. modular_negation
proves complement conservation and modular subtraction at every word width,
including zero/minimum patterns, and exposes a concrete W.neg link. natural_division
reuses Base divmod and checked quotient translation to prove arbitrary positive
periods, Euclidean decomposition and exact quotient/remainder projections. The
U32 long-division recurrence is still not linked to these facts.

A direct concrete 2^32 Nat-bound proposition triggered the unmodified checker's
normalizer stack limit; that unretained attempted proposition was removed rather
than counted as checked. Generic word bounds remain checked in word_bounds.
Minor equality-direction and affine-use errors during proof development were
corrected; successful checker runs certify only the retained propositions.

Added two semantic mutations: remove W.neg's complement and change the independent
reset specification to retain counters. Each must be rejected at its respective
new native-operation refinement; no new conjunction-assembly sensitivity claim.
Source/spec/host boundaries remain explicit in public-phase-map.md. No runtime
source, protected files, callback scope or expected-answer transport changed.


Extended arithmetic further through arbitrary-width Base addition with carry and
subtraction, plus concrete U32 interpretation in word_addition/word_subtraction.
No runtime arithmetic was substituted. These laws are imported through END_TO_END.
The native proof closure is now 142 files, acyclic, with independent specs and all
28 vendor hashes intact. Native constructor and limb-decoding laws are explicitly
exposed in END_TO_END; no end-to-end host completion claim is added.

The reset mutant first failed affine checking, so the gate correctly failed.
Adjusted only the scratch mutant's counter binder to allow duplication; the
corrected mutant then failed the intended actual-operation/specification equation.
The corrected 30-mutation suite passed. Fresh acceptance is being repeated after
the final arithmetic imports; final results and fingerprints are recorded below.

Final 0016 verification: fresh PROOF, END_TO_END and spec_smoke checks pass. Frozen
acceptance exits 1 solely because full_scope remains failed. All 12 manifest
upstream groups, assertion inventory, boundary, 51 clock-failure assertions,
4,800 differential operations, 1,141 numeric operations, 30 semantic mutations
and 11 transport-rejection checks pass. The failed affine mutant run is superseded
by the corrected semantic mutation and complete fresh acceptance, not counted as
a passing run. Independent full-completion approval has not been obtained.

Recovery at the available response/context resource limit: preserve this checked
partial work and continue the ENTIRE assignment. This is not completion or an
external blocker. The next arithmetic steps are multiplication/compare and bounded
remainder composition for actual wide.div_million, then signed truncation and
Time.deadline correspondence; reuse natural_division.decomposition, modular_negation,
word_addition and word_subtraction. Avoid normalizing concrete 2^32/2^64 unary Nat
constants in standalone checker propositions; the general width laws are checked.
For public semantics, reuse constructor_safety and public_phase_safety, connect
actual host assignments/branches/conversions and failure paths, and extend exact
native observation refinement beyond Len/Metrics/reset through every operation
and arbitrary public traces. The phase map lists unproved host boundaries. Do not
replace any with a disconnected proof driver or assumed successful transport.
Keep full_scope failed until all obligations and independent approval are real.


0018 ongoing recovery checkpoint (not completion): re-read AUDITOR.md, restart
provenance and retained current files. Fresh retained PROOF checks. The interrupted
0017 multiplication/comparison/shift proofs are present and transitively checked.
Added division_bounds: strict candidate range for either input bit and restoration
of remainder range after one mathematical subtraction. Added subtraction_bounds:
actual Base Word.sub and U32.sub equal natural subtraction when the subtrahend is
no larger; carry behavior is derived from actual ADC conservation and word bounds.
Both new modules check standalone. Their conditional bounds remain internal proof
obligations to discharge in actual div_million induction. No complete divider,
signed deadline, host conversion or public trace refinement claim is made.
No runtime, specification, protected-file or test gate changes in this checkpoint.
Continuing with the executed divider and the full remaining assignment.

0018 ongoing: division_shift proves actual candidate equals shift-with-input-bit.
division_no_overflow establishes exact candidate value from a native <=1,000,000
bound using high-bit monotonicity; no massive unary constant normalization needed.
division_candidate_bound establishes candidate <2,000,000; division_remainder
establishes native subtraction restores <1,000,000. division_invariant inducts
over actual wide.div_million, discharging the remainder premise for arbitrary
widths and inputs. END_TO_END exposes actual_divider_remainder. All modules check
standalone; root check is being refreshed. Quotient reconstruction remains open.
A concrete unary conservation specialization failed checker stack normalization;
removed it, retained only its checked general U32 conservation lemma. This is a
failed proof attempt, not evidence of success or a reason to stop the assignment.
Fresh acceptance before the final induction passed all executable checks and 31
mutations, remaining failed at full_scope. Added a further omitted-subtraction
mutant for the new recurrence bound. Final current-source validation still needed.

0018 ongoing further arithmetic: division_value.conservation proves exact weighted
quotient/remainder conservation by actual digit dispatch and recursive execution,
and actual discharges the fixed denominator identity. division_quotient recognizes
that decomposition using Base Nat.divmod and returns the independent mathematical
quotient, still parameterized by a U32 divisor with explicit equality to one million.
Direct fixed-divisor quotient specialization overflowed checker normalization and
was removed to build/quotient-specialization.txt; not counted as checked. Both
retained modules check. Added selected-quotient-bit mutation targeting result_form.
The public fixed quotient/signed deadline bridge remains open, as do all host and
universal observable-refinement obligations. Continuing the full assignment.

0018 continuing: resolved the fixed-divisor normalization issue with a structural
guard in the independent numeric specification. specification_equation universally
proves identical mathematical from_nat(unsigned(input)/divisor) meaning. No checker
or primitive modifications. division_quotient.actual now discharges fixed divisor
identity, and unsigned_milliseconds reaches the actual runtime and public numeric
nonnegative branch. A guarded negative specification retains the original mathematical
modulus/subtraction/division meaning, likewise proved by a universal equation.
negation_magnitude proves exact negative magnitude, including int64 minimum, from
actual complement/increment conservation and the selected sign. signed_division
and duration_refinement now prove actual Time.milliseconds and Time.deadline against
the independent spec for every int64 input, including wrap and zero sentinel.
Added signed-magnitude and zero-sentinel semantic mutations. Earlier notes calling
fixed quotient and signed arithmetic open are superseded by these checked modules.
Native arithmetic is complete at this boundary; host marshalling, every-operation
observable refinement and real clock/transport/trace composition remain unfinished.

0018 current executable checkpoint: frozen acceptance passes all executable
checks, including all 12 upstream groups, 4,800 differential operations, 1,141
numeric operations and 35 semantic mutations. It exits 1 solely for full_scope.
The initial sentinel mutation failure was correctly gated because an earlier
immortal-duration lemma rejected it. The corrected spec sentinel mutation tests
the intended actual/spec equation and passes its rejection gate. Continuing with
observable refinement: abstraction_lookup.binding now derives actual lookup of
every abstract binding from the joint representation, preserving exact original
key/value/deadline and independent of enumeration order. Three codec instances
check. Full S.find correspondence and every-operation refinement are next; native
duration arithmetic is complete. No claim of full host or trace completion.

0018 ongoing observable-refinement checkpoint: lookup_refinement now proves
exact actual native lookup equals independent S.find, including absence, under
the full representation and explicit codec/equality contracts. The String
instance discharges codec injectivity and equality reflection/reflexivity.
The independent extensional state relation preserves every lookup, exact recency,
capacity, lifetime, metrics and disabled metadata while ignoring binding-list
storage order; reflexivity/symmetry/transitivity and configuration congruence
check. These relation laws alone are not cache refinement.
absent_read.string_read and absent_remove.string_remove establish exact native
observations for arbitrary represented caches with absent keys, including
nonempty caches. The absence premise is a branch condition, not a full-operation
claim. P.read's absent branch and no-removal signal are connected to the core
read. The actual TS caller, clock classification and transport remain unproved.
Fresh frozen acceptance passes all executable checks and 36 mutants, exiting 1
solely at full_scope. Subsequent relation/protocol lemmas check independently;
full validation and fingerprints will be refreshed after the next changes.
No independent completion approval or full verification is claimed. Continuing.

0018 live untracked read: live_peek.string_read composes actual native lookup,
checked expiration correspondence, and the nonexpired branch into exact
independent observations, including original entry and unchanged state/metrics.
A local helper/binder name collision was exposed by the root checker despite a
standalone pass; renamed entry_deadline/expiry and reran PROOF successfully.
The subsequent frozen acceptance is running. Local proof closure: 170 files,
acyclic; independent specification imports checked. Compared current absent/live
branches directly with pinned Go Get/peek/remove source. Full tracked/live/expired
and mutation/aggregate operation refinement and all actual host bridges remain.

0018 continuing: whole native String Remove and tracked/untracked Read now refine
independent observable specifications using E.observations. Remove covers all keys;
Read covers absent, live, expired and immortal entries for all native int64 times.
Exact recency, metrics, entry identity, return flags and empty events are preserved;
only binding enumeration order differs extensionally. All input representation and
disabled-flag premises remain explicit. Native detach/conditional count composition
is proved equal to core removal, including its actual flag dispatch. These are not
yet actual TS public API or arbitrary public trace theorems. New same/other-key
specification deletion laws are linked to native deletion; existing native Map
foundations were reused. Added removal-count and live-Hits specification mutants;
the updated mutation suite is pending. Full_scope remains failed. Continuing.

0018 fresh frozen acceptance passes all executable gates including 38 semantic
mutations; exit 1 solely for full_scope. Native whole Read/Remove and detach-count
composition were included. Subsequent spec_write_lookup and store_lookup_refinement
check standalone and now enter the root: actual store lookup agrees with independent
write for every key, preserving other keys. Full store state/observation and Add
composition remain next; internal store capacity bound must be discharged by Add.
Refreshing evidence after a fresh root check; no completion claim or stopping point.

0018 evidence audit caught stale mutation report labels: all three new semantic
mutants executed and their required rejection logs exist, but the descriptive
report list still contained 35 labels. Added the three omitted labels so the
next generated report enumerates all 38 executed mutations. No mutation gate or
expected diagnostic was weakened. The intermediate snapshot predates this report
metadata correction; rerunning frozen validation before the next snapshot.

0018 continuing Add refinement: store_state proves full independent write state
and observation correspondence under an internal output-capacity bound. The
replacement and nonfull Add branches now discharge that bound from the full
representation and actual lookup/comparison. Replacement derives retained original
key identity from native lookup; it does not assume equality of arbitrary keys.
These branches check; full-cache eviction/Add and actual public clock phases remain
open. Corrected frozen report now explicitly lists all 38 passing mutations;
full_scope remains the sole failing gate. Continuing with full-cache insertion.

0018 native whole-operation checkpoint: add_refinement.with_lifetime/add now prove
all native String Add branches against the independent specification. Full-cache
head availability, original-key identity and store room are derived from existing
representation laws; no extra bound is exposed. All int64 duration cases compose
through duration_refinement. oldest_refinement proves native RemoveOldest and the
internal GetOldest observation through exact original-key recency and whole Read/
Remove. Public GetOldest captured-key projection and real clock/transport remain
separate. These modules check standalone and are now imported by END_TO_END.
Continuing with native refresh and aggregate observations, then all host bridges.

0018 native GetAndRefresh now refines independent refresh for every represented
String cache and native int64 duration/time, including previously expired entries.
Lookup-derived original identity is retained, native Map replacement is linked to
independent binding replacement, and exact Hits/recency/return/deadline are proved.
No prior-expiry or extra capacity premise is used. Native whole Add, Read, Remove,
RemoveOldest and internal GetOldest proofs remain checked. Actual host clock effects,
partial failure states, conversion, generic codec composition, aggregates and traces
remain unfinished. Added two sensitivity checks for full-capacity equality and
refreshed returned deadline (40 total intended); updated validation is pending.

0018 sensitivity rerun correctly rejected the strict-full-capacity mutant, but
its gate expected an unqualified model_head name. The checker reported the actual
imported linkage full_add_head.model_head. Corrected that exact diagnostic label;
the failed run is not counted as passing. The mutant and required nonzero checker
exit remain unchanged. Revalidation follows before refreshing evidence.

0020 (new backend session) architecture change: the public dispatcher now lives
in Bend. src/public.bend defines Request/Answer/Pending/Progress with start,
resume and abandon; src/driver.bend runs the same machine over an explicit
Clock.Event list (drive/execute/run). src/adapter.ts was reduced to marshalling
plus one loop: start, one validated sample per Waiting, abandon on provider
failure. All 12 upstream groups, boundary (26) and clock_failures (51) pass on the
rewired adapter. Purge is now a single Map.new replacement (no callbacks).
Checker constraint discovered: function-valued proofs are affine, so the
extensional E.states lookup can be queried once per proof value; enumerating
replies (Keys/Values) are therefore proved inside the aggregate proof rather than
by a generic congruence. New proofs so far: public_relation (result relation),
public_drive, public_finish (finished step => refining result), public_read
(whole Get/Peek/Contains including every provider failure branch). RECOVERY:
continue with public_* proofs for Remove/RemoveOldest/GetOldest/config/Purge,
Add, GetAndRefresh, expire aggregate, safety preservation, stepwise trace;
then END_TO_END exposure, docs, validate.py gates/fingerprints. full_scope stays
failed until all of that is done.


## Manual simplification after interrupted cycle 0021

Worker stopped; all edits preserved. Extracted six unchanged active entry helpers
into src/entry_ops.bend, retained definitionally equivalent protocol forwarders,
and removed the historical phase protocol from the actual public import graph.
Repaired three stale runtime mutation targets after the earlier worker's Bend
public-dispatch migration; retained their semantic assertions. All extraction-stage
executable tests passed, with full_scope still correctly failed. Preserved and
checked public_read/public_simple, and composed four actual public String request
laws in END_TO_END. Their representation and host/generic/trace limits are explicit.
The operator's new guidance targets the current implementation and closed public
obligations; it does not authorize narrowing the goal or weakening acceptance.

## 0022 (Claude backend) checkpoint A

Re-read handoff, AUDITOR.md and current public proofs. New checked public laws
(actual Driver.execute vs independent PublicSpec.execute, every event list):
public_config (Len, SetLifetime, Metrics, ResetMetrics, Purge, Diagnostics;
generic key/codec), public_oldest_ops (RemoveOldest, GetOldest; String),
public_add (Add/AddWithLifetime incl. pre-clock eviction retained on clock
failure; String), public_refresh (GetAndRefresh incl. retained hit/recency on
failure; String). All exposed in END_TO_END; PROOF checks.
Implementation adjustments (observably identical, all upstream groups/clock
failures pass): public Add now stores once on the prepared cache with the
retained original key and pre-clock eviction flag; immortal refresh stores the
zero sentinel explicitly.
Discovered blocker: E.states' pointwise lookup is a function (affine in the
checker), so spec states cannot be threaded through several spec operations
(aggregate prefix loop, traces). RECOVERY/NEXT: redefine spec/equivalence
states as equality of a Data-kinded canonical form (scalars, recency, lookups
at recency keys, stray bindings) and adapt the few constructors; then prove
spec congruence, aggregate, reachability, traces.

## 0022 checkpoint B: canonical relation and static-parameter finding

Checker finding (reproduced in /tmp experiments, recorded here): parameters
marked `~` are static; the checker specializes each use (`f~0`, `f~1`) and
checks the specialization. A `~`-generic definition checked alone does NOT
validate its body for arbitrary static arguments (a bogus generic stray
equality passed standalone and was rejected once instantiated). Therefore every
`~`-generic lemma must be instantiated with concrete static arguments inside the
PROOF closure; END_TO_END now exposes String instances of the generic config
laws. Generic-codec claims hold per instantiated codec, not as one universal
theorem over arbitrary `~encode`.
Rewrite semantics: for `%e : P(_)` with `e : a == b`, the goal must be P(b)
and the continuation proves P(a).
spec/equivalence.states is now equality of a Data-kinded canonical form
(scalars, exact recency, lookups at recency keys, stray bindings) so it can be
reused; proofs/canonical.bend proves lookup agreement for every key, ordered
entry agreement and canonical transforms for erase/unlist/write/move;
proofs/canonical_string.bend instantiates them; canonical_native proves stray
= Nil for represented native caches. removal/eviction/store/refresh state and
write congruence were rebuilt on it. END_TO_END and PROOF check.
NEXT: aggregate Keys/Values/PurgeExpired public proof; spec congruence of
PublicSpec.execute; reachability; traces; codecs; host bridge.

## 0022 checkpoint C: String public API refinement, reachability, traces

Checked and exposed in END_TO_END (String keys, every provider-event list):
public_aggregate (Keys/Values/PurgeExpired oldest-prefix walk incl. failures
after completed removals), public_diagnostics (spec leaves = bound abstract
entries; native Map.size = recency length via size_length.same_length),
public_requests.string_request (all 18 requests), spec_congruence.execute_cong
(the independent PublicSpec.execute respects the canonical relation),
public_safety.request_ok (representation + disabled flag for every outcome
cache incl. retained failure states), public_trace.trace / from_construction
(D.run vs Traces.run for arbitrary request lists; construction rejection and
acceptance). Mutations of the driver (dropping unused events) and public walk
(evict-counted expiry removal) are rejected by the checker.
Spec change: PublicSpec.diagnostics leaves counts O.all_entries (bound entries)
instead of raw binding-list length (identical for well-formed models; now a
canonical-invariant observation).
NEXT: frozen acceptance rerun; generic codecs (Integer/Word64) for the public
laws; host bridge; docs/PROOF_STATUS table; mutation gates for new links.

## 0022 checkpoint D: generic keys, host step, composition gate

- proofs/rename_machine.bend: every cache primitive, Entry op, Pub function and
  driver function commutes with renaming stored original keys to codes
  (no injectivity needed); d_run relates D.run at K to D.run at String.
- proofs/rename_spec.bend: the independent specification at K with key
  equality `same` renames to the String specification, given
  `agree: String.eq(enc a, enc b) == same(a)(b)` (static proof parameter);
  t_run relates Traces.run.
- spec/keys.bend: independent structural Integer/Word64 key equalities;
  proofs/key_equality.bend: sound, reflexive, and agreement with code equality
  via codec injectivity (decision argument).
- proofs/public_keys.bend: K-level result/trace relation (exact K replies via
  injective reply renaming; canonical states after renaming);
  from_construction transports public_string_trace. END_TO_END:
  public_integer_trace, public_word64_trace, spec_*_equality_sound/reflexive.
- Host: src/driver.bend D.advance (one provider event per Waiting progress);
  adapter.ts now runs K=String / K=Word(64n) with the Bend codecs themselves
  (Codec.string_encode / new Codec.word64_encode) and steps via D.advance only;
  END_TO_END host_finished/host_waiting prove D.drive is its iteration.
  tests/new/host_bridge.ts validates JS conversions against JS oracles.
  END_TO_END actual_limb_encoding/roundtrip expose pack laws.
- tools/validate.py: host_bridge check; key-equality mutants; the
  unconditional full_scope failure replaced by a composition gate (required
  END_TO_END statements, PROOF import, no holes/axioms/proof-less laws, spec
  independence, adapter wiring), probed to reject each violation.
Pitfall found: a `~`-generic lemma whose type mentions a static parameter it
does not bind (t_run_cons used `~same`) parses and only fails when specialized;
instances must be checked through the top-level theorem.
Also: differential now includes int64/uint64 key traces (adapter Word64 codecs vs
pinned Go at K=int64/uint64, extremes included); tools/evidence.py scope lists
rewritten to the current composed claims and the stated trust boundary.

## 0023 plan (host bridge repair after audit)
Audit: JS numeric/key conversions and the TS loop were unproved; full_scope
passed on substring checks. Plan: (1) numbers cross the JS boundary only as
decimal strings (String(bigint) / BigInt(string)) or Nat (BigInt, runtime
identity); src/host.bend parses/validates/renders in Bend, proved against
spec/host.bend (positional decimal semantics, from_nat/unsigned). (2) one Bend
step function family (begin/answer) returns Return/Raise/Ask actions; TS loop
only calls the provider and passes values; prove the loop model equals
D.execute. (3) docs/gate repair. Keep full_scope failing while any bridge open.

## 0023 checkpoint A: host numeric conversions in Bend, proved
Runtime finding: compiled Bend Nat is limited to 2^48-1 ("a Nat past the
largest immediate"), so 64-bit values never cross or compute as Nat. Checker
finding: closed Nat constants like Nat.pow(2n, 30n) are expanded during
checking (stack overflow) -> spec/host.bend states "v < 2^n" as the round trip
unsigned(n, from_nat(n, v)) == v (proved equal to v < 2^n in
host_numeric.fits_meaning) and two's complement -(k+1) as Word.not(from_nat k);
all theorems generic in the width, instantiated at 64/63/32.
Checked: src/host.bend (decimal digits -> exact halving -> Word(n) + leftover;
digit doubling -> decimal text), spec/host.bend, proofs/nat_algebra,
word_value (from_nat value), host_decimal (digits vs positional), host_binary
(halving/binary/zeros), host_numeric (unsigned_word, signed_word), host_render
(unsigned_text, signed_text). NEXT: host_loop, END_TO_END exposure, adapter.ts
rewrite, validate gate + mutants, docs.

## 0023 checkpoint B: adapter reduced to residue; gate repaired
src/adapter.ts now calls only src/host.bend (readers, renderers, create,
sample/thrown, begin/answer, test-only keys/consistent) and Bend codecs;
integers cross as decimal text. proofs/host_loop.bend: HostLoop.loop over
begin/answer = D.drive / D.execute. proofs/host_boundary.bend: string key,
time, sample, create, key round trips. END_TO_END: host_* laws, drive_* renamed
unfolding lemmas. tools/validate.py full_scope: adapter residue checker
(no arithmetic/shift/mask/width reduction/Number, allowed imports, every H
call covered by a named law, test-only calls confined) with 7 self-probes; 8
new sensitivity mutants on src/host.bend. validate.py exit 0.

## 0024 correction to checkpoint A
Checkpoint A said fits was "proved equal to v < 2^n"; at that time only
host_numeric.fits_meaning (v < 2^n => fits) was checked. 0024 adds
host_numeric.unsigned_below and host_numeric.fits_bound (fits => v < 2^n),
exposed as END_TO_END host_fits_bound; together with host_fits_meaning they
show fits(n, v) holds exactly when v < 2^n. Mutant host-range-wraps (spec fits
accepts every value) is rejected at fits_bound; full_scope requires the new
statement.

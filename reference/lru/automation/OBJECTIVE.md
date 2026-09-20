# Fully verified single-threaded LRU using Bend's native Map

Implement a standalone Bend LRU library with the complete SINGLE-THREADED
observable cache behavior of elastic/go-freelru with callbacks disabled. Upstream is pinned in
vendor/go_freelru at 3a0a715f3309fbbaed5d9afd402d53ff5e1efd81.

LATEST USER REQUIREMENTS OVERRIDE EARLIER IDEAS: use Bend's native Base Map type
for key lookup. NO AESENC, NO custom hashing, NO custom hash table. Exclude
SyncedLRU, ShardedLRU, locks, parallel adapters and concurrency proofs. Keep the
separate SSZ auto implementer running; never change its run or files.

LATEST SCOPE UPDATE: callbacks are entirely OUT OF SCOPE for now. Do not implement,
prove or pursue callback parity, callback adapters, reentrancy, or callback-driven
clock/state mutation. The supported and verified public API has no SetOnEvict or
other way to install/execute user callbacks. If retained code exposes those APIs,
remove them from the supported facade and make callback execution unreachable
from in-scope operations. Archive old probes/observations as excluded evidence;
do not count them as passes or allow their unresolved results to block completion.
Do not add a silently ignored/no-op callback registration API. Compare against Go
with a nil eviction callback. Callback-free eviction/removal/expiry, recency and
metrics remain fully in scope; do not remove those semantics or proofs.

Implement all single-threaded public operations inventoried in api.manifest.json:
construction/validation, Len, Add/AddWithLifetime, Get/GetAndRefresh, Peek,
Contains, Remove, RemoveOldest, GetOldest, Keys, Values, Purge, PurgeExpired,
SetLifetime, Metrics/ResetMetrics and diagnostics. Preserve upstream
observable value, return, recency, lifetime/expiry, and metric behavior.
Read source when comments disagree. Include replacement, full/empty caches,
absent keys, capacity one, expiration boundary/rounding, refresh of expired keys,
and metrics reset. Do not silently redesign behavior.

Intentional API/storage adaptations: native Map replaces upstream hash buckets.
Expose constructors without required hash callbacks. NewWithSize compatibility
may preserve capacity/size input validation, with size documented as a nonbinding
upstream storage hint, since Base Map owns storage. Do not recreate bucket sizing,
hash callbacks or collision machinery. Document these adaptations in an API map;
port the observable upstream assertions with only those mechanical adaptations.
Diagnostics must accurately describe actual native-map storage rather than invent
Go bucket statistics. No claim of Go GC, allocation, speed or O(1) parity without
evidence; report costs of the actual Bend map and recency representation honestly.

Base Map uses String keys. Support usable generic key/value APIs via an explicit
injective canonical key encoding, with built-in string and integer codecs and
proved encode/decode/equality correspondence. Never collapse distinct user keys
or assume the hash is injective. String keys must preserve the full chosen String
semantics, including empty strings and embedded zero characters. Custom key
codecs may require a stated injectivity contract; built-in codecs must discharge
it. Preserve original keys for key iteration. Use the actual Base
Map APIs for lookup/update/removal; do not implement a second map underneath.
Recency metadata must remain bounded by capacity and reflect exact LRU order.

Model time explicitly for deterministic arbitrary traces and supply a usable
clock adapter with documented units and assumptions. Match pinned expiration
arithmetic, rounding and boundary semantics. Do not turn resource failures,
invalid transport, missing output or timeout into successful cache operations.
Provide a usable clock/transport adapter and prove its connection to actual
cache operations; do not label an unproved host bridge end-to-end verified.

Formal verification: build independent spec/*.bend describing an abstract finite
map, exact recency order, expiration, metrics and operation traces. Independent
specs must not import implementation/proofs or define correctness as whatever the
implementation returns. Shared neutral datatypes are allowed. Prove construction,
every public operation and arbitrary finite trace refine that model, preserving
capacity, uniqueness, recency/map consistency, key identity and all representation
invariants. Discharge public input bounds and premises. Prove the Base Map laws
needed by the actual cache against its implementation; do not merely assume
lookup/set/delete work because it is the native type. Trust the unmodified Bend
checker and primitive Base semantics, not unproved high-level map algorithms.
Avoid reimplementing Map: establish lemmas about its existing definitions.

Expose universally quantified actual-API initialization, operation and trace
correctness and public adapter composition in END_TO_END.bend, imported by
PROOF.bend. No holes, unsafe proof escapes, axioms, finite test enumeration passed
as universal proof, circular/self-equality specifications, opaque map oracles,
unproved numeric/key/adapter bridges or resource-bound premises disguised as
protocol correctness. Explain source/spec correspondence and trust boundaries.
Compiler/runtime/hardware correctness are separate from the mathematical
functional claim. No cryptographic algorithm or proof is part of this project.

Testing: port ALL single-threaded TestLRU* functions in tests.manifest.json,
including every in-scope shared helper/assertion, to actual Bend execution.
Only callback installation/invocation/event/count/reentrancy assertions are now
explicitly excluded. Preserve the containing test scenarios and ALL remaining
cache/return/order/expiry/metric assertions. Enumerate each removed assertion in
the test mapping with the user-authorized callback exclusion; never mark excluded
assertions as passing. All 12 test groups remain required in the report. Keep an explicit
case/assertion map; the Go suite alone is not Bend conformance. Excluded concurrency
and map-baseline tests are listed in excluded-tests.json. Add independent
stateful differential traces against pinned Go, controlling time where needed
with a transparent reference adapter that does not change cache decisions.
Exercise capacity/input bounds, long histories, eviction/replacement, expiration,
all metrics, integer/string key encoding and map/recency consistency.
Expected results must never be sent to the Bend implementation backend.
Build tools/validate.py --report PATH with JSON upstream_cases:[{name:<exact
manifest name>,status:"passed"|"failed"}], plus differential/boundary evidence.
Exit nonzero until every case and independent check passes. Unsupported or missing
operations fail; no skips or expected-output substitution. Add mutation checks
that demonstrate meaningful theorem/test sensitivity without weakening gates.

This run continues the preserved implementation and interrupted candidate from
an earlier LRU run; read automation/restart-provenance.json, WORK_LOG.md and
PROOF_STATUS.md. The worker resumes its existing session ID, but the CURRENT
workspace, objective and policy are authoritative. Earlier assignment stop points
and previous workspace paths are stale. Re-read current files and establish fresh
validation; preserved unreviewed edits are not certified by this restart.

Work continuously toward the ENTIRE remaining end-to-end objective. Do not stop
at a lemma, method, subsystem or passing test group. Continue through general
native Map laws, numeric/key correctness, cache invariants, every operation,
arbitrary trace refinement, and all real clock/transport adapters until
the full public implementation and composed proof satisfy every frozen criterion.
Maintain intermediate checkpoints and WORK_LOG notes without ending the worker
invocation. No total cycle or agent-time cap. If an actual process/context/resource
interruption forces a return, report needs_work with a recoverable checkpoint.
Hard proofs are work to continue, not an external blocker. Preserve sound work.

Read the literal AUDITOR.md provided in your workspace and perform those checks
yourself before proposing completion: normative/Go correspondence, nonvacuous
propositions, actual implementation linkage, dependency closure, all premises,
rejection/failure semantics, exact tests and absence of expected-output leakage.
Fix defects and repeat appropriate checks. The orchestrator must independently
perform the same substantive checks; the separate auditor remains a mandatory
additional gate. Never trade soundness for apparent progress. No local proof or
finite test milestone establishes full completion; all criteria and gates must
pass with a full universal proof and independent approval.

Work only in the isolated candidate. No worker subagents, commits, pushes,
deployment, changes to protected files, tools/credentials outside the workspace,
or other projects. build/ is scratch. Bend 2.0.5 is /Users/monkeair/.bend/bin/bend;
Bun is /Users/monkeair/.bun/bin/bun with preload
/Users/monkeair/.bend/current/bend2/main.ts; Go is /opt/homebrew/bin/go.

```toml
name = "Verified single-threaded Bend LRU using native Map"
project = ".."
codex = "/Users/monkeair/.local/bin/codex"
max_iterations = 0
agent_timeout = 0
orchestrator_timeout = 0
validation_timeout = 43200
editable = ["src/*", "spec/*", "proofs/*", "types/*", "*.bend", "tools/*", "tests/new/*", "README.md", "WORK_LOG.md", "PROOF_STATUS.md", "VALIDATION.json", "go.mod", "go.sum", "package.json"]
protected = ["vendor/*", "automation/*", "api.manifest.json", "tests.manifest.json", "excluded-tests.json", "callback-exclusions.json", "upstream.lock.json"]
ignore = ["build", "build/*", "*.pyc"]
validation = [["/Users/monkeair/auto-implementer/.venv/bin/python", "automation/acceptance.py"]]

[criteria]
api = "All callback-free single-threaded FreeLRU observable behaviors implemented using native Map, with explicit no-hash constructor/storage adaptations."
map_keys = "Actual Base Map lookup/set/removal laws and built-in key encoding injectivity proved; no custom hash/map or opaque map oracle."
refinement = "Universal actual initialization, operation and arbitrary trace refinement; capacity, recency, time and metrics fully covered within the callback-free public API."
conformance = "Every inventoried single-threaded upstream test executes against Bend; independent differential, boundary and mutation checks pass."
composition = "Complete nonvacuous END_TO_END laws imported by PROOF, all public invariants and actual adapter bridges discharged."
engineering = "Usable generic native-map API, bounded recency metadata, exact observable semantics, reproducible evidence and honest cost/trust documentation."
```

# Self-audit against literal AUDITOR.md (not independent approval)

## Iteration 0023 self-audit (current; older sections below are historical)

Audit findings from 0022 and their repair:
- Unproved JS numeric/key conversions (high). The adapter no longer does any
  integer arithmetic. It passes `String(bigint)` text to `src/host.bend` and
  reads Bend's decimal text back with `BigInt`. Parsing, range checks, sign
  mapping, the word split and rendering are Bend code proved against
  spec/host.bend (host_uint64_key, host_int64_key, host_*_text,
  host_*_roundtrip, host_time, host_sample, host_create, host_string_key).
  Two findings forced this design:
  - A compiled Bend Nat above 2^48-1 aborts at runtime, so 64-bit values
    cannot cross as Nat. Decimal text is the minimal runtime-identity form.
  - The checker expands closed big constants, so spec/host.bend states the
    ranges without 2^63/2^64 as the round-trip condition fits(n, v).
    host_fits_meaning (v < 2^n implies fits) and host_fits_bound (fits
    implies v < 2^n; added in 0024) together show fits(n, v) holds exactly
    when v < 2^n.
- Host loop overclaimed (high/medium). The loop now calls only the step
  functions H.begin/H.answer. Its model HostLoop.loop is proved equal to
  D.drive/D.execute over the provider's events (host_loop_*). The
  host_finished/host_waiting lemmas are renamed drive_finished/drive_advance
  and described as driver unfolding lemmas. The README, the END_TO_END header,
  host_step.bend and PROOF_STATUS were corrected.
- Substring gate (medium). full_scope now checks the adapter's code for the
  trusted residue only: no arithmetic, shift, mask, width reduction or Number
  conversion; only host.bend/codec.bend imports; every Bend call covered by an
  END_TO_END law. It self-tests seven injected violations. Eight new mutants
  hit the Bend conversions and the host step, each rejected at its intended
  lemma with a type error.

Checked against AUDITOR.md:
- Nonvacuous statements. Every host law states exact acceptance with the
  specified word, and rejection (Fail) otherwise. Rendering laws state exact
  read-back.
- Actual linkage. The laws are about the functions the adapter calls. The
  loop law equals the D.execute of the trace theorems.
- No substring stands in for a proof. The gate's statement checks only confirm
  that the proved statements are still present. The proofs are the checker's.
- Rejection vs execution failure:
  - Range and format rejections are Fail values thrown as RangeError.
  - An invalid clock sample is an InvalidSample event, i.e. an execution
    failure with the retained state.
  - A provider exception propagates the original error.
- Spec independence: spec/host.bend imports only spec/numeric.bend.
- No holes, axioms or laws without proofs (gate).
- Remaining trust, stated honestly: the checker and runtime (including
  String/BigInt text conversion), the provider call and exception capture,
  and identity passing in the 8-line TS loop.


## Iteration 0022 final self-audit (current; older sections below are historical)

- Normative correspondence: the public machine keeps pinned decisions (Len never
  expires; GetAndRefresh revives; replacement counts an insert and keeps the
  stored key; full Add evicts before the clock read; GetOldest keeps the
  expired oldest key; Keys/Values/PurgeExpired remove only the expired oldest
  prefix; Purge empties and zeroes metrics). The Go differential, all 12 ported
  groups and boundary checks pass.
- Nonvacuous propositions: public_string_trace/public_integer_trace/
  public_word64_trace relate exact replies (K-typed), errors, unused events and
  request counts per request plus canonical final states; construction rejection
  must equal the spec error. The relations are Empty on class mismatch.
- Implementation linkage: theorems quantify over the actual D.run/D.execute of
  src/public.bend with the actual Base Map; mutation checks (tools/validate.py)
  of src/public.bend, src/driver.bend, spec/*.bend and spec/keys.bend are
  rejected at named proof locations.
- Dependency closure: PROOF.bend imports END_TO_END.bend; no holes, axioms or
  law without proof (validated by the full_scope gate); spec/ imports no src/ or
  proofs/. Generic lemmas are instantiated inside the closure (String, Integer,
  Word64).
- Premises: representation/disabled premises of per-request laws are discharged
  for every reachable state (request_safe; traces start at construction).
  Codec premises (inj, agree) are discharged for all built-in codecs.
- Failure semantics: provider exceptions, invalid samples and (modelled)
  exhaustion stop with the specified retained state and error; the adapter
  rethrows the original error after adopting D.advance's state.
- Tests: expected results never reach the Bend backend (reference adapter, JS
  oracles). Callback assertions are individually excluded, not counted.
- Trust boundary (stated, not claimed verified): JS marshalling and the loop
  body in src/adapter.ts, Bun runtime, Bend checker and Base primitives.


Current scope is callback-free, as authorized by callback-exclusions.json. The
old reentrancy/capacity conflict and probes are archived in callback-archive.json;
they are neither successful coverage nor remaining completion requirements.

- Normative correspondence: nil-callback removal, full insertion, replacement,
  refresh and oldest-prefix expiry retain pinned source decisions. Len never
  expires; GetAndRefresh revives; replacement counts as insertion; GetOldest keeps
  the expired oldest key; Purge resets counts after removals. Diagnostics identify
  native storage, not Go buckets. Collisions is an explicit storage adaptation.
- Public linkage: no SetOnEvict, stored host callback or callback dispatch remains
  in adapter.ts or supported transport. Commit rejects enabled/nonempty legacy
  metadata before adoption. Internal removal phases run no user code. Disabled
  flag laws cover actual primitive transformations and aggregate transitions;
  this is not yet a complete host reachability/composition proof.
- Native proof closure: map_insert.set_same quantifies arbitrary actual native
  trees, keys, defaults and values. Its seek shape and replacement certificates
  discharge routing/comparison premises against Base. No desired lookup result
  is assumed by the public law. Initial projections connect it to C.store and
  C.lookup. Lookup soundness additionally connects actual returned values to exact original
  leaves and native enumeration, then to C.lookup. The converse now derives its
  routing premise from the existing critbit predicate. Successful lookup
  establishes the seek-found premise for replacement; native pop agrees with
  get on its returned value, and same-key deletion under critbit is linked to
  actual C.remove_present. General native insertion, first-difference and deletion foundations are now
  checked (see current PROOF_STATUS); full reachable representation remains. Mutants target both the routing predicate
  and actual core deletion, alongside the retained store-None linkage mutant.
- Proposition meaning: no claim that checking these partial laws proves all
  cache operations. Numeric sign/zero/order/packing proofs are not complete
  modular addition/division or host BigInt/String correspondence. Exact increment
  conservation with carry and unsigned-width bounds are now checked universally. Invariants
  remain partly proved candidates. END_TO_END lacks complete operation and trace
  laws; full_scope remains a failure.
- Independence: spec modules import only Base, neutral types and other specs.
  Legacy inactive event fields do not install executable functions. Complete
  commands, clock effects and finite-trace semantics remain to be finished.
- Assertion coverage: every original assertion site is retained with an exact
  port expression/location, individually excluded, or split into retained and
  authorized excluded clauses. All 12 groups still execute. TestLRUMatch's model
  advances from inputs, never cache output; the added order assertion checks its
  independent recency list on every iteration. Exclusions are not marked passed.
- Expected-answer isolation: Go and Bend receive operations and clock inputs,
  never expected observations. Comparison takes place in Python. Seeded counters
  are identical input state fixtures for wrapping checks, not expected results.
- Negative semantics: unsupported operations, callback registration, malformed or
  missing output, backend failure and timeout fail. No matching process failures
  are accepted as cache results. No callback/panic fixture is in the active gate.
- Remaining work: joint reachable representation, arithmetic and host bridges, complete
  independent trace specification, all-operation invariants/refinement and real
  host/transport composition. No completion or independent approval is proposed.

Iteration 0003 review: read pinned GetOldest (lru.go:561) and native Base pop/del
and full-adder definitions directly. Public GetOldest must capture its key before
Peek removes an expired entry; the new independent public observation does so.
Its supporting laws are labeled as specification properties, not runtime bridge
proofs. The missing-clock and invalid-binding branches are failures. Empty and
immortal branches retain all clock samples.

Inspected deletion membership proofs: all other bindings survive and no new
binding can appear, including child collapse; these propositions concern actual
Base.pop/del. Lookup framing additionally uses the explicit R.valid premise and
proves its preservation by deletion. Actual C.remove_present is linked through
its Map.del call and projection equality. Full critbit and cache reachability
are still not inferred from that weaker premise. Replacement critbit preservation
is independent of values and discharges seek-found from actual successful lookup.

The addition theorem concerns executed Word.adc/W.add and an independent unsigned
interpretation; overflow conservation is explicit. Its carry is computed from
input bits, not supplied as a correctness assumption. Bit case analysis is the
inductive Boolean base step, not finite enumeration substituted for arbitrary
word correctness. Signed division and host marshalling remain open.

Empty-event laws use actual protocol definitions, preserving the distinction
between callback-disabled local steps and proved host composition. The latter is
still missing. Specifications retain only neutral/Base/spec imports. New proofs
use no axioms/admissions or replacement Map. Added semantic mutants change the
public expired key/value and actual 64-bit addition; strict existing checks and
all twelve groups remain required. Completion is neither claimed nor proposed.


Final local bound audit: recency_bounds proves actual C.without length monotonicity
and actual core removal's capacity bound from its input bound. It does not claim
that insertion or arbitrary traces preserve the complete representation. No
Nat bound is substituted for actual transport/resource success. The final
checker closure imports this module, the full-adder laws, deletion and replacement
proofs, public-oldest specification properties and empty-event prerequisites.

Iteration 0004: inspected the bit/msb/diff proofs against installed native Base.
The scan's fuel premise is discharged for all U32; its nonzero premise is derived
from unequal actual comparisons. Whole-String distinction uses actual divmod,
character presence bits and recursive offsets. It proves distinction, not prefix
minimality. Splice framing is linked to actual Map.ins.splice; singleton framing
uses actual Map.set, comparator identity and the proved discriminator. Full
insertion preservation and reachable-cache invariants are not claimed.

Clock-failure tests execute adapter.ts with actual Bend modules. Expected state
is asserted by the host test and never supplied to backend operations. Provider
exceptions preserve identity; invalid samples fail with RangeError. The tests
inspect partial state and counter timing rather than accepting generic process
failures. The new counter mutant is rejected by these assertions. The lookup
mutant changes actual C.lookup and is rejected by the existing implementation
linkage proof. These checks are not universal host/transport verification.

Later iteration-0004 continuation supersedes the earlier prefix limitation:
actual native prefix minimality is now proved and connected to the executable
same_prefix predicate. Each earlier offset is quantified, not enumerated. The
Nat offset split has a proof of either its first-character bound or exact tail
offset; it is not an assumed routing certificate. Character bit arithmetic uses
actual native MSB and bit definitions. Distinction plus this prefix law establishes
first difference, but not preservation of arbitrary existing insertion paths.
The remaining public proof obligations and full_scope failure are unchanged.

Iteration 0005: inspected full native deletion preservation against actual
Base.pop/del, including collapsing an empty child. Prefix constraints are proved
directly on the executable all-pairs predicate; ordering uses original sibling
bounds and proved transitivity. Routing is converted from the existing logical
certificate back to the executable Boolean predicate. Nonempty children and
recursive validity are discharged by cases on the actual child result, not
assumed for the output. The storage predicate is linked to actual C.remove_present.
Input validity remains explicit, and no reachability theorem is claimed.

A generic template attempt was not accepted as proof evidence merely because its
isolated module checked; caller instantiation failed and direct proofs replaced
it. Actual seek-prefix preservation has explicit prefix and successful-result
premises; it supplies a dependency, not a completed insertion theorem. The new
mutation reverses the executable discriminator ordering and must be rejected by
the checked native ordering proof. General insertion, numeric/host bridges and
operation/trace composition remain open; full_scope is unchanged as a failure.

Public-path check: adapter.ts invokes P.detach for Remove, P.detach_oldest for
RemoveOldest and P.prepare_add before insertion clock sampling. protocol_storage
now quantifies those actual functions and proves their storage critbit result
from input validity; finish_removal leaves that predicate unchanged. This is a
real local implementation connection, but does not establish dispatch, marshalling,
results, full reachable representation or arbitrary host traces. Completion
approval is neither requested nor claimed from these supporting laws.

## Iteration 0006 review

The independent expiration specification previously discarded all completed
removals on exhausted clock input. PrefixFailure now retains that prefix and the
pending entries; AggregateFailure carries remove_entries applied to the original
state, including removal metrics. The added laws are specification properties,
not claims that TypeScript failures refine this result. Explicit throwing/invalid
clock inputs, command traces and host composition remain open. The new mutation
drops one completed removal during failure propagation and must fail checking.

map_descent_frame reaches actual Base Map.ins and Map.ins.deep. Its opposite-branch
lookup frame quantifies arbitrary trees and queries; its ordering and routing
premises remain explicit. It does not establish general insertion or reachable
representation preservation. No source/runtime facade or callback scope changed.

Insertion routing preservation now additionally checks for arbitrary trees when
the inserted key satisfies the existing constraint. Native insertion nonemptiness
has no validity premise. Neither supplies the missing prefix/order proof or
reachable cache invariant. The aggregate failure mutation was freshly rejected at
failed_prefix_keeps_completed_removal. All full-scope gates remain unchanged.

## Iteration 0007 substantive self-review

Native Map.set critbit preservation now covers all branches against Base.
The proof follows actual seek, derives the new-key prefix and opposite routing
from native difference, rules out equality with the followed root, and performs
structural induction for descent. Replacement uses actual put skeleton laws.
No child validity, output routing or successful transport is assumed as a public
conclusion. Input critbit is still explicit; full reachable cache representation
is not claimed. Core store and host-used refresh_at are linked to the theorem.

New-key insertion framing covers arbitrary valid trees and present/absent queries
using exact structural leaf membership in both directions. Its premises describe
actual seek and unequal comparison; full Map.set framing still needs replacement
and empty-seek composition. All new proof dependencies enter PROOF through
END_TO_END. Specs remain independent of implementation/proofs. Runtime and Go
source are unchanged. All 12 groups and individual callback exclusions remain
required, with independent answers outside backend inputs. Clock/transport errors
remain failures, and existing partial-state tests remain required.

Two additional mutants are rejected: using native put in actual C.store fails
store_lookup, and removing a prefix bit fails skipped_prefix_rejected. The latter
is predicate sensitivity, not a new claim of complete operation refinement.
Actual adapter composition, legal host bridges, full representation and trace
refinement remain open; checker success does not close those obligations.


## Iteration 0008 self-audit (not independent approval)

The new Map.set frame reaches installed Base.set, seek, comparison, ins and put.
The input premises are exactly a critbit-valid tree and a distinct query. The
replacement lemma is stronger locally: Map.put needs only a selected leaf and
a query distinct from that leaf, with no critbit premise. Its four branch cases
cover equal and opposite update/query routes. The empty-seek lemma derives a
contradiction from nonempty valid children, rather than assuming the entire tree
empty. The actual store link uses C.store and C.lookup, including the real
lookup result projection. All laws are universally quantified, not examples.

The new abstraction laws reach refinement.abstract and its bindings function.
Every successful actual lookup survives with its complete Entry; every abstract
binding has an exact native enumeration origin. This proves neither preservation
of encoded identity nor full recency faithfulness. Full representation reachability
remains an open obligation. The new mutation drops Some entries in binding_cons
and must fail the retention theorem, demonstrating sensitivity of that link.

Inspected the current independent-spec import boundary, actual native Base
branches, pinned GetOldest/PurgeExpired behavior, and differential payload
construction. Expected outputs remain separate from inputs sent to Bend.
Neither API domains, callback exclusions, source assertions nor transport failure
handling were weakened. Earlier sections describe historical milestones; the
current open work is listed in PROOF_STATUS.md. No full-completion approval is
claimed, and full_scope remains failed.

The populated-leaf component has now been proved through actual native set and
deletion, including child collapse, and linked to construction, store and
facade-used detach/prepare/refresh phases. It is a structural Boolean predicate,
not an opaque map oracle. The abstraction-size theorem derives exact cardinality
from this explicit component via actual Map.to_list and the retained native
size law. A mutation accepting None leaves is rejected at put_preserves_populated.
This establishes sensitivity of that native preservation proof, not a claim
that the first rejection occurs in the abstraction cardinality theorem.
Full reachability must still establish the component jointly with bounded
unique recency, map/order agreement and encoded original-key identity.

Recency filtering, fresh append and their composition prove unique output for
actual store/touch/removal. The equality reversal needed for append is derived
from the native String comparator; no injective hash or equality oracle is used.
The store mutation retains the old recency occurrence before appending and must
fail store_preserves_unique_recency. This is actual implementation linkage,
while joint public reachability remains open; later iterations establish conditional boundedness and membership components.


## Iteration 0009 self-audit (partial, not independent approval)

Read AUDITOR.md and retained source/status. New recency-capacity laws recurse on
actual C.without and native List.append. present_frees_slot assumes only actual
Boolean membership, not uniqueness or the desired output bound. The store bound
has an explicit room-or-presence premise, which is not disguised as reachability.
Native key membership is derived from actual successful lookup's structural
leaf witness and actual Map.keys accumulator traversal. keys_in_order is the
existing representation component, not an assumed output property. Replacement
and live-read links use actual C.add_found and C.read_live. Their original-key,
metric and complete operation refinement is not claimed by these bound laws.

The remaining gap is joint preservation, including absent/full preparation,
encoded identity, exact membership and recency abstraction. Independent specs,
public domains, callback exclusions, expected-answer isolation and strict
transport failures are unchanged. All new proof dependencies use checked Base
and prior proofs; no axioms, admissions, alternate map or expected-output paths
were introduced. Full_scope remains failed.


## Iteration 0010 self-audit (partial, not independent approval)

Re-read literal AUDITOR.md, restart provenance, current core/protocol/facade and
retained proof status. New inverse key enumeration partitions actual Map.keys.go
between native leaves and its accumulator; populated leaves rule out None and
checked critbit routing yields actual lookup. The oldest-removal and add bounds
use this availability, positive capacity, and existing input membership/bounds.
They do not assume eviction succeeds or that an output bound already holds.

Exact abstraction recency is sequence equality after encoding original keys.
It reaches C.entries_go, C.lookup_result, native get/enumeration, keys_of and
refinement.abstract. Identity is derived from the existing identities predicate;
built-in injectivity comes from codec inverses. Unary Integer and Word(64) are
separate mathematical instances; actual host BigInt conversion is still unproved.
Generic initialization and arbitrary-key/value/time first insertion at capacity
one witness nonempty joint states, not an arbitrary-trace induction. Full joint
preservation remains the next obligation, including membership and identity.

The new reversed-entry mutation is rejected at abstraction_recency.head_step.
Skipping eviction in prepare_room is rejected earlier at cache_populated's
existing protocol preservation link; it is not described as a new capacity-law
failure. All prior mutation checks remain required. Source/spec independence,
acyclic dependencies, nil-callback Go comparison and expected-answer isolation
were inspected. No runtime behavior, protected source, public domains, callback
exclusions or rejection/failure semantics changed. Resource/transport errors
remain failures. The full_scope gate remains failed and independent completion
approval is not claimed.

Final checks: PROOF, END_TO_END and spec_smoke passed directly; the 96-file
local proof closure is acyclic and all 28 pinned vendor fingerprints match.
Frozen acceptance exits 1 solely at full_scope; all 12 upstream groups and
executable checks pass, including 23 mutations and 11 transport failures.
These are partial functional/proof results, not independent completion approval.


## Iteration 0011 self-audit (partial, not independent approval)

Re-read AUDITOR.md, provenance, current source and status. The new membership
proofs use actual C.without, native Map.get/keys/del and already checked native
routing/deletion laws. Boolean lookup presence is proved in both present and
absent cases; populated leaves are needed because a native None leaf is still
an enumerated key. Deletion's universal membership equation includes deletion
of an absent code and arbitrary other queries. It does not claim enumeration
sequence equality. Filtering both lists preserves inclusion by structural
induction; this supplies both directions for actual removal and preparation.

Actual P.detach and P.prepare_add miss/full branches are checked, not replaced
by a successful-removal premise. Core removal links have the same table/order
changes and retain their existing metrics logic. Compared pinned Go Remove and
RemoveOldest: neither checks expiration, and successful removal increments
Removals. New membership laws do not claim metric or return-value refinement.
No runtime/source behavior or independent specifications were changed. Joint
reachable preservation, unique native keys, encoded-identity preservation,
insertion/update membership was subsequently checked in iteration 0012; remaining public composition stays open.
The existing frozen gates and 23 mutation checks are retained without weakening.

Fresh final evidence: PROOF, END_TO_END and template smoke check; frozen
acceptance fails only full_scope while all 12 groups and executable checks,
including 23 mutations and 11 transport rejections, pass. The 100-file local
proof closure is acyclic, spec imports independent and 28 vendor hashes match.
These are partial results; joint reachability and full composition are unproved.


Iteration 0012 self-audit: re-read literal AUDITOR.md and restart provenance.
New update membership quantifies arbitrary Base Strings, values and populated
critbit trees; it includes absent and present queries. The same-key and other-key
cases reach actual Map.set/get/keys, not a replacement map. Recency correspondence
uses actual without/append. Mutual-inclusion transfer is proved by structural
list induction. The store theorem reaches the actual C.store table/order fields.

The composed storage predicate deliberately excludes capacity, uniqueness,
identity, callbacks, observations and trace semantics. Construction and core
Add/removal/protocol preparation establish preservation of its stated components.
No theorem assumes these output components. No public refinement or actual host
composition is inferred. The fresh mutation targets C.store retaining only the new recency code.
Checking cache_store_membership includes its dependencies: the first rejection
is the existing recency_unique.store_preserves_unique_recency proof, not the new
membership law. The gate requires that diagnostic and the evidence names it
accurately. This is implementation sensitivity, not isolated sensitivity for
the new membership proposition.

Rechecked input/expected separation in tools/validate.py: both backends receive
the same input payload, with comparison only afterwards. Pinned GetOldest captures
the key before peek; PurgeExpired checks the oldest element for a bounded loop;
ResetMetrics returns the previous counters. New proofs do not alter any of those
decisions or claim to establish them. Full_scope remains failed and independent
full-completion approval remains outstanding.

Refresh membership additionally follows actual lookup to an enumerated native
leaf, establishing prior key membership. The replacement membership theorem then
shows every native key is unchanged while the protocol keeps recency unchanged.
There is no expiry premise: expired refresh is included. This proves the local
refresh_at phase under its actual-lookup premise; it does not establish that the
host always supplies the right entry or that clock failures refine a trace spec.


Iteration 0013 self-audit: re-read AUDITOR.md, current source, proof status and
restart provenance. The uniqueness proof follows actual native keys.go, using
its accumulator/append law. Child disjointness comes from actual native routing:
a key present on both sides would have both discriminator bits. Populated
premises are explicit and extracted from the storage component; no uniqueness
conclusion is assumed. The tree induction uses only strictly smaller children.

Refresh lookup preservation follows actual read_live and finish_miss state
fields. The output item correspondence is not a claim that refresh preserves
all representation components or that the host is verified. The new mutation
changes only refresh_prepare's lookup argument to the empty key; checking
refresh_lookup directly fails at its prepare law. This module imports source
and neutral types only, avoiding rejection by unrelated recency theorems.

Independent specs remain unmodified. No expected outputs enter the Bend backend,
no callback assertions are reinstated, and the failed full_scope gate remains.
Native-key uniqueness is now derived; encoded identity preservation, complete
joint reachability, numeric/host bridges and universal observable refinement are
still open. No full-completion approval is claimed.

Iteration 0014 self-audit: read the literal AUDITOR.md and current restart
provenance. Compared the new refresh preservation statements with actual
src/protocol.bend, src/cache.bend and the facade's GetAndRefresh assignments.
Pinned Go getAndRefresh uses findKeyNoExpire, moves recency and increments Hits
before assigning expire(lifetime). The new laws make no unexpired-entry premise.
The preparation state is committed before the adapter's clock call, as documented;
its representation survives either successful sampling or an exception, but no
formal host exception/transport composition is claimed.

Store identity is proved first for every successful lookup, using actual
store_lookup/store_other_lookup. The enumeration proof inducts over an actual
output suffix while carrying an exact prefix/output equation. Critbit validity
is preserved by the existing native set law; populated output is derived from
input identity and native populated preservation. Thus the proof cannot silently
omit any enumerated binding or accept a None leaf. The fresh code/encode equation
is explicit; refresh derives it from the original lookup. Deletion identity uses
native no_new_binding and needs no validity premise. None of these facts assumes
injectivity of hashes or rebuilds the native map.

Full removal and refresh preservation reassemble the unchanged Inv.representation
predicate. Native-key uniqueness is derived from output storage. Capacity and
unique recency use existing actual-operation bounds; membership movement follows
the real touch_order. The successful refresh theorem derives intermediate lookup
from the returned item, and preparation separately covers the failure state.
Input representation remains explicit: arbitrary public reachability and complete
observable refinement are not established. Existing initialization and nonempty
capacity-one witnesses demonstrate that this predicate is inhabited.

Fresh dependency inspection found an acyclic 118-file local closure of PROOF.
Specification imports remain independent; all 28 pinned vendor hashes match.
No implementation, codec, transport, specification or assertion-map semantics were
changed. The sole new test gate is an additional mutation: resetting a refresh
miss to capacity zero must fail the new full representation proof at found~0.
Expected answers remain outside backend payloads; callback exclusions and all 12
manifest groups are retained. Full_scope remains failed. This is a worker
self-audit, not independent completion approval.


## Iteration 0015 substantive self-audit

This remains a self-audit, not independent approval. Read literal AUDITOR.md and
pinned Go Add/refresh/GetOldest/PurgeExpired/metrics definitions again. No public
callback API, Map replacement, harness policy or upstream file was changed.

- Representation linkage: store_representation composes the prior identity,
  storage and unique-recency laws. Its explicit internal output-length premise
  is discharged in actual Add via Parts.add_bounded. Replacement identity comes
  from actual lookup. Read uses actual expired/live branches; refresh proves
  actual native updated lookup before moving recency. Config and aggregate laws
  preserve the full predicate through actual returned states, including pending
  clocks/removals. Existing full removal/refresh foundations are reused.
- Nonvacuity/premises: initialized_run starts from any 1+n capacity and any finite
  list of the enumerated actual transitions. It assumes no output invariant,
  resource bound, successful transport or assumed native-map law. Built-in
  String/Integer/Word64 instances check. The proof-side driver is NOT the host
  dispatcher; it does not prove public observable traces or all host assignments.
  Exact recency abstraction premises are discharged for this closure only.
- Arithmetic: binary_division follows installed Nat.divmod.go using the checked
  quotient translation. Reconstruction quantifies arbitrary widths, words and
  multiples; carry conservation yields actual W.add/Time.add and Word.inc
  correspondence with independent from_nat. Signed division and host numeric
  conversions remain absent, so no complete deadline/adapter claim is made.
- Independent specifications: all nine spec files import only Base, spec files
  and neutral types. Typed commands explicitly cover every Command constructor.
  Clock failures preserve pre-request Add eviction or refresh recency/Hits;
  expired-prefix failure preserves completed removals. GetOldest projection
  keeps its captured key and returns zero value on an expired miss. Empty,
  immortal and absent-key branches avoid consuming provider events. Reset
  returns old metrics while zeroing new ones. Trace results preserve failures;
  continuation represents a caller catching an error. No host conversion or
  resource rejection is inferred from the typed sample classifications.
- Closure: the local PROOF import closure is acyclic, with 134 files. Direct
  PROOF, END_TO_END and all-three-key spec template checks passed. No high-level
  Map oracle, unsafe escape, assumed conclusion or circular spec was introduced.
- Sensitivity: direct core-refresh zero-capacity and independent add-to-subtract
  mutants fail at present~ and time_add_refines respectively. The initially
  tried Add mutant failed an older storage theorem and is excluded from the new
  sensitivity claims. Existing runtime/theorem mutation gates remain required.
- Coverage/isolation: no assertion map, callback exclusion, pinned reference or
  backend payload generation was changed. New specs execute only as checker
  templates; they are not substituted for Go expected answers or Bend outputs.
  Runtime checks remain independent. All 28 pinned vendor hashes matched.

Open: full public reachability/disabled-event composition, legal-domain and host
numeric/key bridges, signed division/deadlines, actual operation/aggregate/trace
refinement, untyped failure semantics and actual TypeScript/transport composition.
The full_scope gate remains failed and independent completion approval is absent.

Fresh final frozen acceptance: all 12 groups and executable checks pass, including
4,800 differential operations, 1,141 numeric operations, 28 mutation cases and
11 transport failures. It exits 1 solely at full_scope. This confirms the limited
checkpoint and does not waive any remaining refinement or independent audit gate.


## Iteration 0016 substantive self-audit

Re-read literal AUDITOR.md, current source and prior recovery records. The new
public_phase_safety module does not replace the specification or native Map.
It combines previously checked representation, flag-preservation and empty-event
facts for the same actual returned state. Actual Add preparation/counting/final
insertion are composed; successful refresh obtains its lookup through
Lookup.successful_prepare from the actual returned item. Read and aggregate
certificates distinguish intermediate caches and removal-ready event lists.
Initialization and configuration instances discharge their joint facts directly.

The input joint predicate is explicit and inhabited by positive-capacity
initialization. No assumed final invariant, time sample, resource bound or
successful transport premise is introduced. The successful-refresh returned-item
premise is a branch condition, not an assertion of the desired final state.
Generic templates are instantiated for all three retained mathematical codecs.

The TypeScript host was inspected assignment by assignment; the mapping is in
public-phase-map.md. That document explicitly records outstanding commit/tag,
input conversion, branch, loop, return and resource-failure bridges. Neither the
map nor the new certificates are claimed to prove actual host execution or full
public reachability. Callback behavior remains excluded; only disabled metadata
and empty event preservation are composed. No supported runtime code, upstream
assertion map, exclusion policy, backend input generation or reference was changed.

Fresh PROOF and END_TO_END checks pass. The proof closure is acyclic (135 files),
specification imports remain independent, and all 28 pinned vendor hashes match.
The initial configuration wrapper needed affine duplication annotations; that
checker rejection was fixed before the fresh acceptance rerun. Existing mutation
gates are retained; no new sensitivity claim is made for tuple assembly.

Remaining obligations are unchanged in kind: actual public reachability and
observable operation/trace refinement, signed division/deadlines, host key/numeric
bridges, actual untyped rejection and clock/transport composition. The full_scope
gate remains mandatory and independent completion approval remains absent.


### Extended 0016 native boundary and arithmetic audit

The final native proof closure has 142 acyclic files. Rechecked independent spec
imports and all 28 vendor fingerprints. Constructor success safety derives
positivity from the actual U32 zero comparison; its Fail branch asserts no cache
success. Existing constructor/refinement laws and executable validation retain
rejection behavior. The new predicate alone is not advertised as total constructor
correctness or a host validation proof.

Native metrics/reset observations directly mention C.metrics and C.clear_metrics
and compare to independent Public.metrics/reset. Their equations preserve the
entire abstract state and old counters, with unused events unchanged and zero
requests for these pure boundary calls. They are not a host request-count proof.
The Len equation derives abstract sequence length from faithful recency under the
explicit representation premise. That premise is not yet discharged for every
actual public host trace. Joint detach certificates now cover both removal forms.

Inspected limb-decoding reconstruction/value/injectivity against actual W.unpack,
W.limbs and existing split/join laws. Inspected complement conservation, modulo
negation, generic addition/carry/subtraction and U32 interpretation against actual
Base.adc/inc/not and the native wrappers. Base divmod decomposition follows its
countdown recursion, with a nonnegative remainder below the positive divisor.
These lemmas do not assume division correctness, but also do not yet prove the
actual U32 duration-divider recurrence or host BigInt/String conversions.

The new reset mutant initially failed affine usage before its semantic theorem;
that run was correctly rejected by the sensitivity gate. Corrected the mutant's
binding to permit duplication, leaving the real specification untouched. The
corrected mutation fails at configuration_observations.reset. The native negation
mutant fails at native_negation_refines. All 28 older mutants remain required.
No source assertion, callback exclusion, expected-answer isolation, reference
adapter, transport rejection or full_scope gate was weakened. Actual host
composition, signed division and universal observable refinement remain open.


Re-read pinned NewWithSize, Len, Metrics and ResetMetrics source for the new
boundary laws. The order of constructor checks is unchanged, with only the
explicit no-hash/native-storage adaptation. Reset returns pre-reset counters and
clears the stored counters, while Len performs no expiration. The new equations
match these callback-free observations. README now distinguishes proved native
phase preservation from the still-unproved public host reachability.

Final fresh frozen acceptance exits 1 only for full_scope. All 12 upstream groups,
assertion inventory, spec templates, boundary, clock failures, differential,
numeric boundaries, 30 mutations and transport sensitivity pass. PROOF,
END_TO_END and spec_smoke separately check. This self-audit is not the mandatory
independent auditor's approval and does not waive the remaining objective.


## 0018 ongoing self-audit

Re-read literal AUDITOR.md and pinned duration code. Actual wide.div_million
processes high bits first, doubles the partial remainder, adds one input bit,
conditionally subtracts one million, and emits that quotient bit. Inspected each
new link against those definitions: Base comparison/multiplication/ADC/shifts,
word bounds, actual digit selection, recursive remainder invariant and weighted
quotient/remainder conservation. The fixed divisor equality is discharged, not
assumed as a public input. Base Nat.divmod decomposition then identifies quotient.
The independent spec's structural guards have universal equations to the original
mathematical quotient formulas; specs import no implementation or proof code.
The checker itself and Base primitives remain unmodified. Failed direct unary
normalization attempts were removed, not counted as proofs.

Signed magnitude uses a proved sign-implies-nonzero fact and actual carry
conservation; int64 minimum is included. Modular negation of a zero quotient is
covered, as are wrapping addition and the deadline zero sentinel. Universal
Time.milliseconds and Time.deadline equations have no input-range premises.
These are native bit-pattern results, not a claim about host BigInt marshalling,
provider outcomes, transport or full public traces. Those remain required.

The new deadline mutant initially failed an earlier immortal-duration equation,
so its expected-location gate correctly failed. Changed the scratch mutation to
the independent zero-sentinel specification; it now rejects at duration_refinement
choose, testing the intended actual/specification link. Fresh frozen acceptance
then passed all executable checks and 35 semantic mutations, with full_scope still
failed. No assertion exclusions, expected-answer inputs, transport failure checks
or protected files were altered.

AbstractionLookup.binding derives actual lookup from abstract binding origin,
native enumeration lookup and encoded identity; it extracts all component
premises from representation. String, Integer and Word64 instances check. It is
a binding correspondence lemma, not complete S.find or public operation refinement.
Independent full-completion auditor approval remains outstanding.

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

0018 additional audit: live_peek.string_read reaches actual C.read_encoded through
lookup_refinement and Numeric.expiration_refines. Its represented-state, found
entry and nonexpired premises are branch conditions, not a full public API claim.
Root import exposed a helper/binder naming collision; renamed it and the root
checker passes. Directly inspected pinned Go Get/peek/remove: absent Get increments
Misses, untracked reads do not, absent Remove preserves metrics. Independent
specifications retain no src/proofs imports; the 170-file root closure is acyclic.
Actual TS readTime, encode calls, commit checks and return conversion still require
proof, and the current branch laws do not discharge those obligations.

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

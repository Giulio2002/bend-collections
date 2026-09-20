# Proof status — current callback-free scope

Status: the composed obligations below are checked in PROOF.bend. The
full_scope gate in tools/validate.py checks the required END_TO_END statements,
proof hygiene, specification independence, and that src/adapter.ts contains
only the stated trusted residue: no arithmetic, and only Bend calls that an
END_TO_END law covers. Independent audit approval is still required. Older
sections and WORK_LOG.md notes are historical. Callbacks remain excluded by
callback-exclusions.json.

Iteration 0023: the audit found unproved JS numeric/key conversions and an
overstated host-loop claim. Both are repaired:
- The conversions are now Bend code (src/host.bend), proved against
  spec/host.bend.
- The adapter loop calls only the H.begin/H.answer step functions. Their
  iteration in the Bend model HostLoop.loop is proved equal to
  D.drive/D.execute (proofs/host_loop.bend); the 8-line TS loop matches that
  model by inspection (trusted).
- drive_finished/drive_advance (formerly host_finished/host_waiting) are
  described as driver unfolding lemmas.

The remaining trust (README.md) is the JS runtime's decimal text conversion,
the provider call and exception capture, identity passing in the TS loop (which
matches HostLoop.loop by inspection) and constructor-tag checks.

Iteration 0024: the range condition is now proved in both directions
(host_fits_meaning and host_fits_bound), so fits(n, v) holds exactly when
v < 2^n.


## Public obligation table (current)

| Obligation | Actual executed entry | Independent specification | Checked theorem (END_TO_END) | Premises / boundary |
|---|---|---|---|---|
| Construction / NewWithSize | `C.new_with_size` | `S.new_with_size` | `public_initialization`, `native_constructor_state_safety`, rejection branch of every `public_*_trace` | host text via `host_create` (uint32 range, then the actual validation) |
| Add / AddWithLifetime | `Pub.start` then `D.drive` (prepare, AddWait, store) | `PublicSpec.execute` (`effectful_operations.add*`) | `public_string_add*`, `public_string_request`, traces | represented + disabled state (discharged for reachable states) |
| Get / Peek / Contains | `Pub.read` | `effectful_operations.read` | `public_string_request`, traces | as above |
| GetAndRefresh | `Pub.refresh` | `effectful_operations.refresh` | `public_string_get_and_refresh`, traces | as above |
| Remove / RemoveOldest / GetOldest | `C.remove`, `C.remove_oldest`, `Pub.get_oldest` | `S.remove`, `O.remove_oldest`, `PublicSpec.oldest` | `public_string_remove*`, `public_string_get_oldest`, traces | as above |
| Keys / Values / PurgeExpired | `Pub.expire` walk | `effectful_aggregate.purge_expired` | `public_string_keys/values/purge_expired`, traces | as above |
| Purge / Len / SetLifetime / Metrics / ResetMetrics / Diagnostics | `Pub.start` | `PublicSpec.execute` | `public_string_*`, traces | Diagnostics: native `Map.size` = entry count (`size_length`) |
| Every request | `D.execute` | `PublicSpec.execute` | `public_string_request` | represented + disabled |
| Reachability | `D.execute` outcome cache (returned, or retained on failure) | representation + disabled flag | `public_string_request_safe` | — |
| Arbitrary finite traces (String) | `D.run` (caller continues after failures) | `Traces.run` | `public_string_trace` | construction inputs only |
| Generic keys | `D.run` at K with codec enc | `Traces.run` at K with key equality same | `PublicKeys.from_construction` (contracts `inj`, `agree`) | instantiated below |
| Integer keys (`T.Integer`, unary codec) | as above | `Keys.integer_same` | `public_integer_trace`, `spec_integer_equality_sound/reflexive` | none |
| Word64 keys (adapter uint64/int64) | as above | `Keys.word64_same` | `public_word64_trace`, `spec_word64_equality_sound/reflexive` | none |
| Host step functions | `src/adapter.ts` loop over `H.begin`/`H.answer` (`src/host.bend`) | `D.drive`/`D.execute` | `host_loop_drive`, `host_loop_string`, `host_loop_word64` (loop model = driver over the provider's events); `drive_finished`/`drive_advance` are driver unfolding lemmas only | trusted residue: provider call, exception capture, the 8-line loop passing values unchanged |
| Host integers and keys | `H.uint64_key`, `H.int64_key`, `H.time`, `H.sample`, `H.create`, `H.uint64_text`, `H.int64_text` | `spec/host.bend` (positional decimal, round-trip range, two's complement) + `spec/numeric.bend` | `host_uint64_key`, `host_int64_key`, `host_unsigned_word`, `host_signed_word`, `host_uint64_text`, `host_int64_text`, `host_*_roundtrip`, `host_time`, `host_sample`, `host_create`, `host_fits_meaning` + `host_fits_bound` (together: fits(n, v) exactly when v < 2^n) | trusted: JS runtime `String(bigint)`/`BigInt(text)` (Bend Nat cannot hold 64-bit values: limit 2^48-1) |
| Host strings | `H.string_key` | `spec/host.bend` `scalar` | `host_string_key` | JS strings reach Bend unchanged (runtime) |

How the non-String theorems are obtained: `proofs/rename_map.bend` proves that
renaming the original keys stored in Map values (never the Map keys) commutes
with every Base Map operation used. `proofs/rename_machine.bend` lifts this to
every cache, public-machine and driver function (`d_run`).
`proofs/rename_spec.bend` does the same for the specification (`t_run`), under
`agree`. `proofs/public_keys.bend` transports `public_string_trace` along both.
Reply renaming is injective (from codec injectivity), so K-level replies are
compared exactly.

Relation used: `spec/equivalence.states` is equality of a canonical form
(scalars, exact recency, lookups at recency keys, stray bindings);
`proofs/canonical.bend` proves it implies agreement of `S.find` for every key
and of ordered entries. `spec_congruence.execute_cong` proves the independent
semantics respects it (needed to thread spec states through traces).
Checker facts relied on: static `~` parameters are checked per instantiation,
so generic lemmas count only through their String/Integer/Word64 instances in
the PROOF closure.

## Iterations 0017–0018: executed divider range and primitive arithmetic

Fresh checks in 0018 validate the retained interrupted multiplication, comparison
and shift foundations. Word multiplication is related to the independent modulo
interpretation through its actual Base.mul.go recurrence and derived carry excess.
Word/U32 comparison, addition and subtraction interpretation laws are checked.
subtraction_bounds derives exact natural subtraction under the input ordering;
its carry is established from actual ADC conservation and universal word bounds.

The actual wide.digit candidate is linked to shift-with-incoming-bit and has exact
mathematical value whenever its native remainder is at most one million. The proof
uses native high-bit comparison to discharge overflow without expanding large unary
constants. division_candidate_bound and division_remainder prove concrete native
candidate and subtraction bounds. division_invariant.bounded then inducts over the
actual wide.div_million definition: every returned remainder is strictly less than
one million, for every word width and input, with no reachable-range premise.
END_TO_END.actual_divider_remainder exposes that universal implementation law.

division_value additionally proves quotient-times-divisor plus remainder equals
the input interpretation for every actual divider execution, discharging the fixed
divisor identity. division_quotient recognizes that decomposition through Base
Nat.divmod and proves the actual fixed-divisor quotient. The initial direct unary
specialization hit the checker stack limit. The equivalent independent specification
now matches the input word before interpreting its magnitude; a universal equation
proves it is still from_nat(unsigned(input) / divisor). This avoids eager expansion
without changing the checker, primitive semantics or arithmetic meaning.

negation_magnitude discharges complement/increment overflow from negative input
signs, including the signed minimum. signed_division proves magnitude division
followed by modular negation, and duration_refinement proves Time.milliseconds and
Time.deadline equal the independent mathematical definitions for all native int64
bit patterns. No input bounds, resource bounds or successful host conversion are
assumed. END_TO_END exposes actual_duration_conversion and actual_deadline_arithmetic,
including signed truncation, wrapped addition and zero-sentinel behavior.

Host BigInt/U32/String conversion, real clock/transport composition, all-operation
observable refinement and arbitrary public traces remain open. New mutation gates
target candidate multiplication, remainder subtraction, quotient-bit selection,
signed magnitude and zero sentinel. They augment the retained 30 mutations.
Full_scope remains failed. Historical descriptions below concern the earlier
checkpoint and do not supersede these current arithmetic claims.

## Iteration 0016: joint safety at public phase boundaries

public_phase_safety composes full representation, disabled legacy metadata and
empty emitted event lists for actual Add preparation/counting/insertion, refresh
preparation and successful continuation, protocol reads, expired-read removal
and miss counting, detach/oldest detach, aggregate transitions, initialization and configuration/reset
phases. Existing native Map and representation foundations are reused.

The composed Add theorem starts with joint input safety, proves preparation,
conditionally counts the eviction through existing P.finish_detached, then proves
actual insertion from that intermediate cache. Refresh derives its required
lookup from the actual preparation result. It does not assume a final safe state.
Intermediate states have separate certificates, including states retained before
a later failed clock request. String, Integer and Word64 instances check.

This is still a collection of mathematical phase-composition laws, not a formal
TypeScript execution proof. The actual host's conditional branches, commit checks,
state assignments, sample conversions, resource failures and returned observations
remain to be connected. tests/new/public-phase-map.md maps each assignment to its
present theorem and outstanding bridge. No claim of complete public reachability is made. Full_scope remains
failed. No independent mutation coverage is claimed for conjunction assembly.
The existing 28 mutation cases are retained; two additional checks target actual
negation and the native reset observation link.

constructor_safety derives native constructor success safety from the actual U32
zero comparison for every capacity/size pair; it does not assume positive capacity.
Fail remains Fail, and host BigInt conversion is not covered. configuration_observations
links actual Metrics and clear_metrics results to the independent typed public
observations; Len agrees with abstract length under representation, with the
conditional premise stated explicitly. These are native boundaries, not TS proofs.

limb_decoding proves unpack/repack identity, exact mathematical decoded value and
decoder injectivity for every native 64-bit word. modular_negation proves arbitrary
width complement conservation and two's-complement modulo subtraction, plus a
concrete link to W.neg. natural_division establishes Euclidean decomposition and
quotient/remainder projection against existing Base Nat.divmod for any positive
divisor. It does not yet connect the U32 binary-long-division implementation to
that decomposition. word_addition and word_subtraction prove arbitrary-width
modulo arithmetic for actual Base ripple operations, including carry, and concrete
U32 addition/subtraction interpretation. Multiplication and remainder-bound
composition are still needed for the actual duration divider. Signed duration
division and host conversions remain open.

## Iteration 0015: transition closure, modular arithmetic and clock specifications

Full representation now survives actual core Add/AddWithLifetime, tracked and
untracked reads, GetOldest, core GetAndRefresh, configuration/metric changes,
Add preparation and aggregate protocol phases. store_representation keeps an
internal output-length premise; add_representation discharges it from the input
representation using the existing capacity theorem. Replacement derives the
retained original key's encoding from the actual lookup, rather than assuming it.
core_refresh_representation proves the native update lookup before the live read.

transition_reachability proves preservation and exact abstraction recency for
arbitrary finite lists of its actual core/protocol transitions, initialized at
any positive capacity. String, Integer and Word64 specializations check. The
proof-side transition driver is explicitly NOT the TypeScript dispatcher and
NOT an independent observable specification. Its closure includes intermediate
preparation/read/removal/aggregate states, but does not prove actual host control
flow, returned values, errors, callback-disabled composition or transport.
The separately checked successful protocol refresh law still requires composition
with the actual host. Full public reachability/refinement remains unfinished.

modular_addition proves actual Time.add equals independent spec/numeric.add,
including wraparound, for arbitrary Int64 operands. It proves Base Nat.divmod's
binary decomposition and reconstructs any word after adding any multiple of
2^width. Existing carry conservation then yields exact addition and increment
modulo correspondence. This does not finish signed division, nanosecond
truncation, deadlines or BigInt/U32/String host bridges.

Independent clock.bend distinguishes valid samples, invalid samples, provider
exceptions and exhausted streams. effectful_operations models Add, refresh and
read outcomes; effectful_aggregate preserves completed removals after later
clock failures. public_commands gives every typed S.Command an explicit public
result; traces gives arbitrary finite caller sequences, including continuing
after a caught failure. States, request counts and unused provider events are
retained. GetOldest retains its captured key on an expired miss. All three key
types instantiate the specifications through spec_smoke. clock_failure_spec
checks failure-state propagation and captured-key properties. These are
specification properties, not implementation/host refinement. Rejection of
untyped transport, conversion errors and resource failures still needs formal
composition; no successful-transport premise has been introduced.

Two new mutants target actual core refresh capacity and the independent addition
specification. They fail directly at core_refresh_representation.present and
modular_addition.time_add_refines. A discarded initial Add probe failed an older
storage law; it is not reported as new-proof sensitivity. Full_scope stays failed.

## Historical checkpoints (current scope above overrides old open-obligation notes)

## Iteration 0014: encoded identity and joint removal/refresh preservation

cache_store_identity proves pointwise identity after actual C.store using native
set_same and other-key framing. cache_store_identities then proves the complete
Inv.identities predicate for its actual native enumeration. The structural
suffix induction maintains an exact prefix/enumeration equation; populated-leaf
preservation excludes None. Input critbit validity, input identities and the new
code = encode(key) equation remain explicit. No injectivity is assumed by this
identity direction; custom-codec injectivity is still needed for key equality.

cache_delete_identities preserves the complete predicate through actual Map.del,
C.remove_present and P.detach_present. Every remaining enumerated binding is
restored to an original binding by the checked no_new_binding law. This identity
preservation does not need a critbit premise. String, mathematical Integer and
Word(64) specializations instantiate the generic proofs.

refresh_representation preserves the existing full Inv.representation predicate
through actual P.refresh_prepare, on both hit and miss. The hit branch derives
recency membership from actual lookup and composes bounded unique recency with
both inclusion directions. The unchanged table retains all original identities.
This intermediate state is the one committed before requesting a clock sample.
cache_refresh_prepare separately composes storage preservation and discharges
the final phase's lookup premise from the returned item.

cache_refresh_identity derives the code/key equation from the prepared binding
and reuses store identity preservation for the new deadline. The composed
refresh_complete_representation theorem preserves the full predicate through
actual preparation followed by refresh_at, conditioned on that actual returned
item being Some. It assumes no expiry, capacity-space or intermediate-lookup
premise. It does not prove clock effects, host dispatch or returned observations.

removal_representation composes the existing capacity, unique recency, storage
and new identity laws into full representation preservation through core
remove_present/remove_found/remove_encoded/oldest_remove/remove_oldest and
protocol detach_present/detach_found/detach/detach_first/detach_oldest. No lookup
success premise is required. These are universally quantified preservation laws,
not full observable refinement or arbitrary public reachability.

The new mutation replaces a refresh miss with a zero-capacity cache. Checking
refresh_representation directly rejects it at found~0 with False == True as
the required result. This establishes sensitivity of the new actual preparation
link. All earlier mutation gates remain required. Full Add/read/aggregate
representation composition, arbitrary reachability, numeric/host bridges and
universal operation/trace/adapter refinement remain unfinished.

## Earlier checked foundations

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
expiry premise. The iteration 0014 laws above now preserve the full representation through
refresh preparation and completion. Observable refresh refinement and host
composition remain open.

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
recency uniqueness, encoded original-key identity, callback metadata,
observations and public trace/adapter correctness are not implied by this claim.
The existing conditional capacity/abstraction laws remain conditional.

## Checked native Map foundation

- Actual native Word/Char/String comparator equality and operand preservation;
  native bit traversal preserves the queried String and agrees with structural
  bit selection and XOR.
- Actual Map.diff first-difference and least-discriminator correctness for all
  distinct Base Strings. Every earlier native routing bit agrees. The existing
  executable same_prefix predicate is discharged, including empty strings and
  embedded zeros. Native MSB fuel, character offsets and divmod stride premises
  are proved, not assumed. This is a Base String claim, not host conversion.
- Actual Map.get preserves its storage tree; native enumeration lengths equal
  native size. Successful lookup names an exact stored/enumerated key and value.
  Converse enumeration/lookup requires the explicit critbit premise. Successful
  lookup discharges the seek-found premise for replacement.
- Actual Map.set same-key lookup holds for arbitrary trees and values without a
  validity premise. Actual C.store/C.lookup is linked to this theorem. Successful
  replacement preserves native shape, keys and the full critbit predicate.
- Native insertion preserves arbitrary existing routing constraints when the
  inserted key satisfies them, through both splice and descent. This theorem
  assumes no critbit validity, and its fresh-key premise is now discharged in
  the full insertion-validity proof.
- Native Map.ins always returns a nonempty tree, without an input-validity
  premise; this supplies the changed-child nonempty obligation for insertion.
- Native insertion descent preserves arbitrary lookups through the opposite
  branch, with explicit discriminator-order and routing premises. These remain local
  lookup-frame lemmas, now composed into the full Map.set frame below.
- Insertion-splice framing is checked, with its discriminator premise discharged
  by Map.diff. Actual singleton_set_other preserves the original value after
  inserting a distinct key. General new-key insertion framing now checks as described below.
- Native pop returned-value agreement, same-key deletion and other-key deletion
  frame laws are checked. Lookup frame laws use the explicit routing/critbit
  premises, with links to actual C.remove_present.
- **Full native deletion critbit preservation is now checked.**
  map_delete_prefix/common prove preservation of each prefix constraint and both
  domains of the all-pairs prefix relation. map_delete_below proves discriminator
  ordering through actual child collapse; map_route_boolean composes the existing
  routing theorem back into the executable predicate. map_delete_critbit combines
  these with nonempty children and recursive validity. The new
  refinement.removal_preserves_storage_critbit links the result to actual core
  removal. protocol_storage additionally covers the actual facade-used detach,
  detach_oldest, prepare_add and finish_removal phases. Its input critbit premise remains explicit; general reachable-state
  preservation is not inferred from it.
- map_seek_prefix proves that an actual seek result satisfies the existing leaf
  prefix constraints. It does not assume a desired seek result or membership
  oracle. It is composed into the full insertion-validity proof.

- **Full native Map.set critbit preservation now checks.** Prefix algebra,
  bounds, joins and insertion preservation handle the all-pairs relation.
  Actual seek inherits routing and prefix constraints; native diff cannot equal
  the root followed by seek. Strict-before splicing and recursive descent derive
  every local obligation from input validity. Replacement uses checked native
  skeleton preservation. Empty seek yields a valid leaf. The final theorem has
  only the input critbit premise, and is linked to actual C.store and P.refresh_at.
- Native Map.ins retains all exact old key/value leaves. Combined with insertion
  validity and membership/lookup correspondence, successful old lookups survive
  insertion at the actual seek-selected discriminator. Structural inverse membership also proves absence preservation at other keys.
  map_insert_frame composes these into general new-key insertion framing with
  actual seek/diff premises. The complete Map.set frame now discharges these
  premises through the actual comparator and seek branches. Replacement uses
  a generic Map.put frame; valid empty seek is proved to imply an empty tree.
  The final theorem assumes only input critbit and a distinct query, and is
  linked to actual C.store/C.lookup.

- Native insertion, replacement, set and deletion preserve the explicit
  populated-leaf predicate (no stored None). Construction establishes it; actual
  store, facade detach/room-preparation/removal-count and refresh phases preserve
  it. These component laws do not yet compose into all-public-operation reachability.

- Actual recency filtering preserves uniqueness and removes every occurrence of
  its target. Appending a fresh code preserves uniqueness; composing these proves
  uniqueness for actual store and touch_order, as well as core removal. These
  do not yet establish capacity bounds or exact map/order membership.

- Present-key recency filtering frees at least one slot without a uniqueness
  premise. Moving a present key cannot grow recency; inserting with a free slot
  preserves the bound. These reach actual C.store with explicit room-or-presence.
- Actual successful cache lookup implies recency membership under the existing
  native-key/order inclusion component. This discharges replacement's presence
  premise and proves actual live read cannot grow recency.
- Native Map.keys membership now yields an exact populated leaf and successful
  lookup under populated/critbit input components. Order-to-keys inclusion then
  derives oldest lookup availability. Actual P.prepare_add on absent keys frees
  a slot using positive capacity and the input bound; it does not assume the
  eviction lookup succeeds. Actual C.add_with_lifetime preserves the capacity
  bound through both absent/full insertion and replacement.
- representation_parts extracts these premises from the existing joint
  representation predicate, including no stored None derived from native
  enumeration and identities. Generic initialization and the first actual add
  to capacity one establish the full predicate for arbitrary keys/values/times.
  Joint preservation across arbitrary operations and traces remains open.

- Native Map.keys membership and actual lookup presence are now equivalent
  under populated/critbit input components, including absent keys. Native
  deletion's key membership equals filtering the original native key list for
  every queried String. This composes existing deletion/frame/validity laws;
  no new map implementation or assumed enumeration oracle is introduced.
- Both map/order inclusion directions are preserved by actual detach_present,
  detach, detach_oldest, prepare_add and their intermediate protocol phases,
  and by core remove_present/remove_encoded/remove_oldest. These statements
  retain input membership, populated leaves and critbit validity premises.
  Store/update membership is checked, and native-key uniqueness is derived
  from populated critbit storage. Encoded identity is now preserved through store, deletion and refresh;
  composition across all operations and full joint reachability remain open.

## Other checked claims and boundaries

- Actual abstraction retains every successful lookup as the exact original
  entry (key, value and deadline). Conversely every abstract binding originates
  in native enumeration. These laws quantify arbitrary cache states; they do
  do not by themselves prove recency preservation or reachability. Under the explicit
  populated-leaf component, actual abstract binding count equals actual native
  map size: enumeration and abstraction cannot drop a stored leaf.

- Exact recency abstraction now checks: encoding the original keys of the
  abstract recency sequence yields precisely the native order list, not merely
  equal size or set membership. Listed-identity laws retain each original key;
  successful actual lookup at encode(key) returns that original key under the
  explicit encoder injectivity contract. Built-in String, unary Integer and
  Word(64) instances discharge this contract using checked codec laws.
  These results extract their premises from representation or explicit input
  components; they do not establish joint reachability or the host BigInt bridge.

- Expiration-prefix failures now carry completed removals, pending entries and
  unused samples. Aggregate failures carry the state after those removals,
  preserving their metric effects. Checked specification laws cover prefix
  propagation and state recovery. This covers exhausted sample lists; explicit
  provider exceptions and real adapter refinement remain open.

- Mathematical String, unary Integer and fixed-width Word codecs have round-trip,
  equality and injectivity laws. Actual Unicode-scalar/BigInt marshalling and
  custom-codec public composition remain unproved.
- Constructor rejection, actual initialization, empty Get/Remove, SetLifetime and
  ResetMetrics have limited refinement laws against independent finite-map state.
- Initial representation checks; actual recency filtering does not grow metadata,
  and removal preserves its input capacity bound. The complete reachable
  representation (positive capacity, unique bounded recency, exact map/order
  membership, original-key identity and no stored None) is not yet preserved by
  every operation. Reachable abstraction faithfulness therefore remains open.
- Numeric support includes zero/sign/sentinel and expiration predicates,
  mathematical limb packing, unsigned word bounds, arbitrary-width increment
  conservation and Word.adc carry conservation linked to actual W.add. Complete
  modular arithmetic, signed division/remainder/truncation, deadlines and actual
  host conversion correspondence remain open.
- Disabled flag and empty legacy events are proved for host-used core/protocol
  transitions. There is no callback installation or execution in the facade.
  These local laws do not prove public host reachability or adapter composition.
- The independent public GetOldest observation includes the original key on
  expired miss, zero value, consumed/unused clock samples and missing-clock
  failure. Its current laws are specification properties, not facade refinement.

## Executable coverage and unfinished closure

All 12 upstream groups and individually mapped callback exclusions remain
required. Expected answers stay outside backend inputs. Differential and numeric
checks use nil-callback pinned Go with explicit time. Clock-failure tests inspect
actual partial eviction/counter, refresh and aggregate state; they are not a
formal host theorem or a claim that Go exposes throwing clocks. Transport errors,
missing/malformed output, backend failures and timeouts remain failures.

Current required proof work:

1. Connect the proved core/protocol representation closure to actual public
   control flow and every state assignment, including successful refresh
   continuation, callback-disabled and empty-event composition. The proof-side
   transition list is not the actual host driver.
2. Complete signed division, nanosecond truncation, deadlines and actual host
   numeric/String/key bridges and custom-codec contracts. Modulo addition and
   increment now refine the independent conversion.
3. Prove all-operation and aggregate observable refinement to the new independent
   typed command/failure/trace specifications. Specify and connect untyped input
   rejection, marshalling and resource/transport failures; typed Clock.Event
   classifications alone do not prove host validation.
4. Prove arbitrary actual public traces and TypeScript facade/transport
   composition, discharging legal public bounds and all reachable-state premises.
   No successful-transport or resource-bound correctness assumption is permitted.
5. Fresh complete frozen acceptance and independent completion approval.

END_TO_END imports the checked dependencies; PROOF imports END_TO_END. Its public
laws expose constructor/initialization, SetLifetime, expiration, exact actual
time addition and proof-side transition representation. It does not yet expose universal all-operation, trace or
actual host-composition correctness. The failed full_scope gate is mandatory.

## Fresh 0016 validation

PROOF, END_TO_END and spec_smoke check. All 12 upstream groups and all executable
checks pass, including 4,800 differential operations, 1,141 numeric operations,
30 semantic mutations and 11 transport rejections. Frozen acceptance exits 1
solely at full_scope. The proof dependency closure is acyclic (142 files), specs
remain independent, and all 28 pinned vendor hashes match. See VALIDATION.json
for the current reproducible fingerprints. Independent completion approval is
still absent; the objective remains needs_work.

0018 observable refinement extension (partial): exact native lookup now equals
independent S.find under the full representation; String equality and codec
contracts are discharged. Independent extensional state equality preserves
all lookups and exact recency/configuration/metrics, and its equivalence and
configuration laws check. Actual absent reads (tracked and untracked), absent
Remove, and present nonexpired untracked reads refine their independent native
observations in arbitrary represented String caches. The native P.read absent
branch agrees with core read and emits a false removal signal. These are branch
proofs, not full every-operation/public-host/trace correctness. Representation
and branch premises remain explicit; full_scope remains failed.

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

0018 continuing Add refinement: store_state proves full independent write state
and observation correspondence under an internal output-capacity bound. The
replacement and nonfull Add branches now discharge that bound from the full
representation and actual lookup/comparison. Replacement derives retained original
key identity from native lookup; it does not assume equality of arbitrary keys.
These branches check; full-cache eviction/Add and actual public clock phases remain
open. Corrected frozen report now explicitly lists all 38 passing mutations;
full_scope remains the sole failing gate. Continuing with full-cache insertion.

0018 native GetAndRefresh now refines independent refresh for every represented
String cache and native int64 duration/time, including previously expired entries.
Lookup-derived original identity is retained, native Map replacement is linked to
independent binding replacement, and exact Hits/recency/return/deadline are proved.
No prior-expiry or extra capacity premise is used. Native whole Add, Read, Remove,
RemoveOldest and internal GetOldest proofs remain checked. Actual host clock effects,
partial failure states, conversion, generic codec composition, aggregates and traces
remain unfinished. Added two sensitivity checks for full-capacity equality and
refreshed returned deadline (40 total intended); updated validation is pending.


## Manual simplification — current public path

Actual public behavior is src/public.bend, interpreted by src/driver.bend and
called by src/adapter.ts. src/entry_ops.bend is its shared entry helper module;
the historical protocol is not a public runtime dependency. No existing checked
proof was removed. END_TO_END now exposes public_string_get, public_string_peek,
public_string_contains and public_string_remove against the independent public
command model with exact provider-event/error observations, under represented
callback-disabled String-cache premises. This does not discharge generic codecs,
reachable-state premises, the remaining operations, arbitrary traces or the real
TypeScript marshalling/clock/transport bridge. Full_scope remains failed.

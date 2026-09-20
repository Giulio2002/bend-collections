import ./proofs/remove_refinement.bend as RemoveRefinement
import ./proofs/ordered_entries.bend as OrderedEntries
import ./proofs/recency_head_removal.bend as RecencyHeadRemoval
import ./spec/equivalence.bend as Equivalence
import ./proofs/spec_lookup.bend as SpecLookup
import ./proofs/refresh_refinement.bend as RefreshRefinement
import ./proofs/add_refinement.bend as AddRefinement
import ./proofs/oldest_refinement.bend as OldestRefinement
import ./proofs/nonfull_add.bend as NonfullAdd
import ./proofs/replacement_refinement.bend as ReplacementRefinement
import ./proofs/store_lookup_refinement.bend as StoreLookupRefinement
import ./proofs/read_refinement.bend as ReadRefinement
import ./proofs/protocol_remove_refinement.bend as ProtocolRemoveRefinement
import ./proofs/live_read_state.bend as LiveReadState
import ./proofs/live_peek.bend as LivePeek
import ./proofs/absent_remove.bend as AbsentRemove
import ./proofs/absent_read.bend as AbsentRead
import ./proofs/extensional_states.bend as ExtensionalStates
import ./proofs/lookup_refinement.bend as LookupRefinement
import ./proofs/abstraction_lookup.bend as AbstractionLookup
import ./proofs/duration_refinement.bend as DurationRefinement
import ./proofs/division_value.bend as DivisionValue
import ./proofs/division_quotient.bend as DivisionQuotient
import ./proofs/division_invariant.bend as DivisionInvariant
import ./proofs/division_no_overflow.bend as DivisionNoOverflow
import ./proofs/division_bounds.bend as DivisionBounds
import ./proofs/subtraction_bounds.bend as SubtractionBounds
import Base
import ./proofs/division_candidate.bend as DivisionCandidate
import ./proofs/multiplication_bounds.bend as MultiplicationBounds
import ./proofs/word_comparison.bend as WordComparison
import ./proofs/word_addition.bend as WordAddition
import ./proofs/word_subtraction.bend as WordSubtraction
import ./proofs/configuration_observations.bend as ConfigurationObservations
import ./proofs/constructor_safety.bend as ConstructorSafety
import ./proofs/natural_division.bend as NaturalDivision
import ./src/wide.bend as NativeWide
import ./proofs/limb_decoding.bend as LimbDecoding
import ./proofs/modular_negation.bend as ModularNegation
import ./proofs/public_phase_safety.bend as PublicPhaseSafety
import ./proofs/clock_failure_spec.bend as ClockFailureSpecification
import ./proofs/transition_reachability.bend as Reachability
import ./proofs/modular_addition.bend as ModularAddition
import ./proofs/add_representation.bend as AddRepresentation
import ./proofs/read_representation.bend as ReadRepresentation
import ./proofs/aggregate_representation.bend as AggregateRepresentation
import ./proofs/removal_representation.bend as RemovalRepresentation
import ./proofs/refresh_complete_representation.bend as RefreshCompleteRepresentation
import ./proofs/cache_store_identities.bend as StoreIdentities
import ./proofs/cache_delete_identities.bend as DeleteIdentities
import ./proofs/refresh_representation.bend as RefreshRepresentation
import ./proofs/cache_refresh_prepare.bend as RefreshPrepare
import ./proofs/refresh_lookup.bend as RefreshLookup
import ./proofs/cache_storage_preservation.bend as StoragePreservation
import ./proofs/cache_store_membership.bend as StoreMembership
import ./proofs/cache_delete_membership.bend as DeleteMembership
import ./proofs/representation_nonempty.bend as NonemptyRepresentation
import ./proofs/cache_key_identity.bend as KeyIdentity
import ./proofs/representation_parts.bend as RepresentationParts
import ./proofs/abstraction_recency.bend as RecencyFaithfulness
import ./proofs/cache_add_capacity.bend as AddCapacity
import ./proofs/cache_prepare_capacity.bend as PrepareCapacity
import ./proofs/cache_oldest_available.bend as OldestAvailable
import ./proofs/map_key_lookup.bend as KeyLookup
import ./proofs/cache_order.bend as CacheOrder
import ./proofs/recency_unique.bend as RecencyUnique
import ./proofs/abstraction_size.bend as AbstractionSize
import ./proofs/cache_populated.bend as CachePopulated
import ./proofs/abstraction_bindings.bend as AbstractionBindings
import ./proofs/map_set_frame.bend as SetFrame
import ./proofs/map_insert_frame.bend as InsertFrame
import ./proofs/map_insert_membership.bend as InsertMembership
import ./proofs/map_set_critbit.bend as SetCritbit
import ./proofs/map_insert_routes.bend as InsertRoutes
import ./proofs/map_insert_nonempty.bend as InsertNonempty
import ./proofs/map_descent_frame.bend as DescentFrame
import ./proofs/aggregate_failure.bend as AggregateFailure
import ./proofs/protocol_storage.bend as ProtocolStorage
import ./proofs/map_seek_prefix.bend as SeekPrefix
import ./proofs/map_delete_common.bend as DeleteCommon
import ./proofs/map_difference.bend as NativeDifference
import ./proofs/map_splice_frame.bend as NativeSpliceFrame
import ./proofs/map_string_prefix.bend as NativeStringPrefix
import ./proofs/recency_bounds.bend as RecencyBounds
import ./proofs/empty_events.bend as EmptyEvents
import ./proofs/map_shape_invariants.bend as ShapeInvariants
import ./proofs/addition.bend as Addition
import ./proofs/map_delete_frame.bend as DeleteFrame
import ./proofs/map_delete_routes.bend as DeleteRoutes
import ./proofs/public_oldest.bend as PublicOldest
import ./proofs/disabled.bend as Disabled
import ./proofs/map_insert.bend as MapInsert
import ./proofs/map_shape.bend as MapShape
import ./proofs/map_seek.bend as MapSeek
import ./proofs/map_pop.bend as MapPop
import ./proofs/map_enumeration.bend as MapEnumeration
import ./proofs/map_delete.bend as MapDelete
import ./src/time.bend as Time
import ./spec/numeric.bend as NumericSpec
import ./types/model.bend as T
import ./proofs/protocol.bend as Phases
import ./spec/operations.bend as Operations
import ./proofs/invariants.bend as Invariants
import ./src/protocol.bend as Protocol
import ./proofs/numeric.bend as Numeric
import ./proofs/counter.bend as Counter
import ./proofs/word_bounds.bend as WordBounds
import ./spec/cache.bend as S
import ./src/cache.bend as C
import ./proofs/refinement.bend as Initial
import ./proofs/native_map.bend as Native
import ./src/codec.bend as Codec
import ./src/public.bend as ActualPublic
import ./src/driver.bend as ActualDriver
import ./spec/clock.bend as ProviderClock
import ./spec/public_commands.bend as PublicSpec
import ./proofs/public_relation.bend as PublicRelation
import ./proofs/public_read.bend as PublicRead
import ./proofs/public_simple.bend as PublicSimple
import ./proofs/public_config.bend as PublicConfig
import ./proofs/public_oldest_ops.bend as PublicOldestOps
import ./proofs/public_add.bend as PublicAdd
import ./proofs/public_refresh.bend as PublicRefresh
import ./proofs/public_aggregate.bend as PublicAggregate
import ./proofs/public_diagnostics.bend as PublicDiagnostics
import ./proofs/public_requests.bend as PublicRequests
import ./proofs/public_safety.bend as PublicSafety
import ./proofs/public_trace.bend as PublicTrace
import ./spec/traces.bend as SpecTraces
import ./spec/keys.bend as SpecKeys
import ./proofs/key_equality.bend as KeyEquality
import ./proofs/public_keys.bend as PublicKeys
import ./proofs/host_step.bend as HostStep
import ./src/host.bend as Host
import ./spec/host.bend as HostSpec
import ./proofs/host_numeric.bend as HostNumeric
import ./proofs/host_render.bend as HostRender
import ./proofs/host_boundary.bend as HostBoundary
import ./proofs/host_loop.bend as HostLoop
# Actual-API correctness, universally quantified. Construction, every public
# request, reachability and arbitrary traces from construction are exposed for
# String keys (public_string_*), and arbitrary traces for Integer and Word64
# keys (public_integer_trace, public_word64_trace). The host boundary
# (src/host.bend, the only Bend code src/adapter.ts calls besides codecs) is
# proved at the end: every numeric/key/text conversion against spec/host.bend,
# and the adapter's step functions H.begin/H.answer, iterated over the
# provider's events, equal D.execute (host_loop_*). README.md states the
# remaining trusted residue (JS String/BigInt text conversion, the provider
# call and its exception, identity passing of values in the TS loop).

# Constructor error branches are actual public API facts.
law zero_capacity_rejected:
  for -K: Data
  for -V: Data
  {C.new(K, V, 0) == Fail{"capacity must be positive"} : Result<&2, &2, String, C.Cache<K, V>>}

def zero_capacity_rejected(K, V):
  {==}

# Publicly exposed initial refinement against the independent finite-map model.
law public_initialization:
  for -K: Data
  for -V: Data
  for +capacity: U32
  for +size: U32
  {Initial.abstract_created(K, V, C.new_with_size(K, V, capacity, size)) == S.new_with_size(K, V, capacity, size) : Result<&2, &2, String, S.Model<K, V>>}
def public_initialization(K, V, capacity, size):
  Initial.new_with_size_refines(K, V, capacity, size)

# Universal actual configuration-operation refinements (early native laws).
law public_set_lifetime:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for ns: T.Int64
  {Initial.abstract(K, V, C.set_lifetime(K, V, c, ns)) == S.set_lifetime(K, V, Initial.abstract(K, V, c), ns) : S.Model<K, V>}
def public_set_lifetime(K, V, c, ns):
  Initial.set_lifetime_refines(K, V, c, ns)

# Supporting public time predicate bridge, not an all-operation theorem.
law public_expiration_predicate:
  for deadline: T.Int64
  for now: T.Int64
  {Time.expired(deadline, now) == NumericSpec.expired(deadline, now) : Bool}
def public_expiration_predicate(deadline, now):
  Numeric.expiration_refines(deadline, now)

# Exact modular arithmetic for the actual deadline adder (signed duration
# division is below; limb conversions are actual_limb_*).
law actual_time_addition:
  for a: T.Int64
  for b: T.Int64
  {Time.add(a, b) == NumericSpec.add(a, b) : T.Int64}
def actual_time_addition(a, b):
  ModularAddition.time_add_refines(a, b)

# Representation closure over actual native transitions. This is not claimed
# as observable trace refinement or a theorem about the TypeScript dispatcher.
law native_transition_representation:
  for -V: Data
  for n: Nat
  for ops: List<&2, Reachability.Transition<String, V>>
  {Invariants.representation(~String, ~Codec.string_encode, V, Reachability.run(~String, ~Codec.string_encode, V, ops, C.init(String, V, 1n+n))) == True{} : Bool}
def native_transition_representation(V, n, ops):
  Reachability.string_initialized_run(V, n, ops)

# Native 64-bit limb conversion (src/wide.bend pack/unpack). Packing two U32
# limbs denotes low + 2^32 * high and unpacking is its inverse.
def actual_limb_encoding(low: U32, high: U32) -> {NumericSpec.unsigned(64n, NativeWide.pack(low, high)) == Nat.add(U32.to_nat(low), NumericSpec.scale_binary(32n, U32.to_nat(high))) : Nat}:
  Numeric.pack_interpretation(low, high)

def actual_limb_roundtrip(low: U32, high: U32) -> {NativeWide.unpack(NativeWide.pack(low, high)) == (low, high) : U32 & U32}:
  Numeric.pack_roundtrip(low, high)

law actual_limb_decoding:
  for word: Word(64n)
  {LimbDecoding.value(NativeWide.unpack(word)) == NumericSpec.unsigned(64n, word) : Nat}
def actual_limb_decoding(word):
  LimbDecoding.decoded_value(word)

# Joint safety of native constructor success; rejected inputs remain Fail.
# Host BigInt validation/conversion is outside this theorem.
law native_constructor_state_safety:
  for -V: Data
  for capacity: U32
  for size: U32
  ConstructorSafety.safe_result(~String, ~Codec.string_encode, V, C.new_with_size(String, V, capacity, size))
def native_constructor_state_safety(V, capacity, size):
  ConstructorSafety.string_new(V, capacity, size)

# Actual binary divider remainder invariant, for every width and bit pattern.
def actual_divider_remainder(+n: Nat, word: Word(n)) -> {U32.is_lt(DivisionInvariant.remainder(n, NativeWide.div_million(n, word)), 1000000) == True{} : Bool}:
  DivisionInvariant.bounded(n, word)

# Mathematical reconstruction of actual quotient and remainder; fixed native
# denominator identity is discharged inside DivisionValue.actual.
def actual_divider_value(+n: Nat, word: Word(n)) -> {DivisionValue.value(n, NativeWide.div_million(n, word), 1000000) == NumericSpec.unsigned(n, word) : Nat}:
  DivisionValue.actual(n, word)

# Full native arithmetic correspondence; host conversions are separate.
def actual_duration_conversion(ns: T.Int64) -> {Time.milliseconds(ns) == NumericSpec.milliseconds(ns) : T.Int64}:
  DurationRefinement.milliseconds(ns)

def actual_deadline_arithmetic(now: T.Int64, ns: T.Int64) -> {Time.deadline(now, ns) == NumericSpec.deadline(now, ns) : T.Int64}:
  DurationRefinement.deadline(now, ns)

# Conditional whole native operation laws on represented states. Their premises
# are discharged for every reachable public state by public_string_request_safe
# and the trace theorems below.
def native_string_add_with_lifetime(-V: Data, c: C.Cache<String, V>, key: String, value: V, ns: T.Int64, now: T.Int64, valid: {Invariants.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> Equivalence.observations(~String, ~SpecLookup.string_same, V, Initial.observe(String, V, C.add_with_lifetime(String, V, Codec.string_encode, c, key, value, ns, now)), Operations.add_with_lifetime(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c), key, value, ns, now)):
  AddRefinement.with_lifetime(V, c, key, value, ns, now, valid, disabled)

def native_string_read(-V: Data, c: C.Cache<String, V>, key: String, now: T.Int64, tracked: Bool, valid: {Invariants.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> Equivalence.observations(~String, ~SpecLookup.string_same, V, Initial.observe(String, V, C.read_encoded(String, V, c, key, now, tracked)), Operations.read(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c), key, now, tracked)):
  ReadRefinement.operation(V, c, key, now, tracked, valid, disabled)

def native_string_remove(-V: Data, c: C.Cache<String, V>, key: String, valid: {Invariants.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> Equivalence.observations(~String, ~SpecLookup.string_same, V, Initial.observe(String, V, C.remove(String, V, Codec.string_encode, c, key)), S.remove(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c), key)):
  RemoveRefinement.operation(V, c, key, valid, disabled)

def native_string_refresh(-V: Data, c: C.Cache<String, V>, key: String, ns: T.Int64, now: T.Int64, valid: {Invariants.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> Equivalence.observations(~String, ~SpecLookup.string_same, V, Initial.observe(String, V, C.get_and_refresh(String, V, Codec.string_encode, c, key, ns, now)), Operations.refresh(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c), key, ns, now)):
  RefreshRefinement.operation(V, c, key, ns, now, valid)

def native_string_remove_oldest(-V: Data, c: C.Cache<String, V>, valid: {Invariants.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> Equivalence.observations(~String, ~SpecLookup.string_same, V, Initial.observe(String, V, C.remove_oldest(String, V, c, False{})), Operations.remove_oldest(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c))):
  OldestRefinement.remove_oldest(V, c, valid, disabled)

def native_string_get_oldest(-V: Data, c: C.Cache<String, V>, now: T.Int64, valid: {Invariants.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> Equivalence.observations(~String, ~SpecLookup.string_same, V, Initial.observe(String, V, C.get_oldest(String, V, c, now)), Operations.get_oldest(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c), now)):
  OldestRefinement.get_oldest(V, c, now, valid, disabled)

# Actual public start/drive paths per request. These quantify over every
# provider-event list, including failure/exhaustion, from any represented
# String-cache state; reachability and traces follow below.

def public_string_get(-V: Data, zero_key: String, zero_value: V, c: C.Cache<String, V>, key: String, events: List<&2, ProviderClock.Event>, valid: {Invariants.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> PublicRelation.results(~String, ~SpecLookup.string_same, V, ActualDriver.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, ActualPublic.Get{key}), PublicSpec.execute(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c), zero_key, zero_value, events, S.Get{key})):
  PublicRead.read(V, zero_key, zero_value, c, key, True{}, ActualPublic.ValueOnly{}, events, valid, disabled, {==})

def public_string_peek(-V: Data, zero_key: String, zero_value: V, c: C.Cache<String, V>, key: String, events: List<&2, ProviderClock.Event>, valid: {Invariants.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> PublicRelation.results(~String, ~SpecLookup.string_same, V, ActualDriver.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, ActualPublic.Peek{key}), PublicSpec.execute(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c), zero_key, zero_value, events, S.Peek{key})):
  PublicRead.read(V, zero_key, zero_value, c, key, False{}, ActualPublic.ValueOnly{}, events, valid, disabled, {==})

def public_string_contains(-V: Data, zero_key: String, zero_value: V, c: C.Cache<String, V>, key: String, events: List<&2, ProviderClock.Event>, valid: {Invariants.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> PublicRelation.results(~String, ~SpecLookup.string_same, V, ActualDriver.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, ActualPublic.Contains{key}), PublicSpec.execute(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c), zero_key, zero_value, events, S.Contains{key})):
  PublicRead.read(V, zero_key, zero_value, c, key, False{}, ActualPublic.Flag{}, events, valid, disabled, {==})

def public_string_remove(-V: Data, zero_key: String, zero_value: V, c: C.Cache<String, V>, key: String, events: List<&2, ProviderClock.Event>, valid: {Invariants.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> PublicRelation.results(~String, ~SpecLookup.string_same, V, ActualDriver.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, ActualPublic.Remove{key}), PublicSpec.execute(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c), zero_key, zero_value, events, S.Remove{key})):
  PublicSimple.remove(V, zero_key, zero_value, c, key, events, valid, disabled)

# Remaining public requests through the same actual start/drive machine,
# instantiated for String keys (static codec parameters are checked per use).
def public_string_len(-V: Data, zero_key: String, zero_value: V, c: C.Cache<String, V>, events: List<&2, ProviderClock.Event>, valid: {Invariants.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> PublicRelation.results(~String, ~SpecLookup.string_same, V, ActualDriver.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, ActualPublic.Len{}), PublicSpec.execute(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c), zero_key, zero_value, events, S.Len{})):
  PublicConfig.len(~String, ~Codec.string_encode, ~SpecLookup.string_same, V, zero_key, zero_value, c, events, valid)

def public_string_set_lifetime(-V: Data, zero_key: String, zero_value: V, c: C.Cache<String, V>, ns: T.Int64, events: List<&2, ProviderClock.Event>) -> PublicRelation.results(~String, ~SpecLookup.string_same, V, ActualDriver.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, ActualPublic.SetLifetime{ns}), PublicSpec.execute(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c), zero_key, zero_value, events, S.SetLifetime{ns})):
  PublicConfig.set_lifetime(~String, ~Codec.string_encode, ~SpecLookup.string_same, V, zero_key, zero_value, c, ns, events)

def public_string_metrics(-V: Data, zero_key: String, zero_value: V, c: C.Cache<String, V>, events: List<&2, ProviderClock.Event>) -> PublicRelation.results(~String, ~SpecLookup.string_same, V, ActualDriver.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, ActualPublic.Metrics{}), PublicSpec.execute(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c), zero_key, zero_value, events, S.Metrics{})):
  PublicConfig.metrics(~String, ~Codec.string_encode, ~SpecLookup.string_same, V, zero_key, zero_value, c, events)

def public_string_reset_metrics(-V: Data, zero_key: String, zero_value: V, c: C.Cache<String, V>, events: List<&2, ProviderClock.Event>) -> PublicRelation.results(~String, ~SpecLookup.string_same, V, ActualDriver.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, ActualPublic.ResetMetrics{}), PublicSpec.execute(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c), zero_key, zero_value, events, S.ResetMetrics{})):
  PublicConfig.reset_metrics(~String, ~Codec.string_encode, ~SpecLookup.string_same, V, zero_key, zero_value, c, events)

def public_string_purge(-V: Data, zero_key: String, zero_value: V, c: C.Cache<String, V>, events: List<&2, ProviderClock.Event>) -> PublicRelation.results(~String, ~SpecLookup.string_same, V, ActualDriver.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, ActualPublic.Purge{}), PublicSpec.execute(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c), zero_key, zero_value, events, S.Purge{})):
  PublicConfig.purge(~String, ~Codec.string_encode, ~SpecLookup.string_same, V, zero_key, zero_value, c, events)

def public_string_diagnostics(-V: Data, zero_key: String, zero_value: V, c: C.Cache<String, V>, events: List<&2, ProviderClock.Event>, valid: {Invariants.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> PublicRelation.results(~String, ~SpecLookup.string_same, V, ActualDriver.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, ActualPublic.Diagnostics{}), PublicSpec.execute(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c), zero_key, zero_value, events, S.Diagnostics{})):
  PublicDiagnostics.string_diagnostics(V, zero_key, zero_value, c, events, valid)

def public_string_remove_oldest(-V: Data, zero_key: String, zero_value: V, c: C.Cache<String, V>, events: List<&2, ProviderClock.Event>, valid: {Invariants.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> PublicRelation.results(~String, ~SpecLookup.string_same, V, ActualDriver.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, ActualPublic.RemoveOldest{}), PublicSpec.execute(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c), zero_key, zero_value, events, S.RemoveOldest{})):
  PublicOldestOps.string_remove_oldest(V, zero_key, zero_value, c, events, valid, disabled)

def public_string_get_oldest(-V: Data, zero_key: String, zero_value: V, c: C.Cache<String, V>, events: List<&2, ProviderClock.Event>, valid: {Invariants.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> PublicRelation.results(~String, ~SpecLookup.string_same, V, ActualDriver.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, ActualPublic.GetOldest{}), PublicSpec.execute(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c), zero_key, zero_value, events, S.GetOldest{})):
  PublicOldestOps.string_get_oldest(V, zero_key, zero_value, c, events, valid, disabled)

def public_string_add(-V: Data, zero_key: String, zero_value: V, c: C.Cache<String, V>, key: String, value: V, events: List<&2, ProviderClock.Event>, valid: {Invariants.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> PublicRelation.results(~String, ~SpecLookup.string_same, V, ActualDriver.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, ActualPublic.Add{key, value}), PublicSpec.execute(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c), zero_key, zero_value, events, S.Add{key, value})):
  PublicAdd.add(V, zero_key, zero_value, c, key, value, events, valid, disabled)

def public_string_add_with_lifetime(-V: Data, zero_key: String, zero_value: V, c: C.Cache<String, V>, key: String, value: V, ns: T.Int64, events: List<&2, ProviderClock.Event>, valid: {Invariants.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> PublicRelation.results(~String, ~SpecLookup.string_same, V, ActualDriver.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, ActualPublic.AddWithLifetime{key, value, ns}), PublicSpec.execute(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c), zero_key, zero_value, events, S.AddWithLifetime{key, value, ns})):
  PublicAdd.with_lifetime(V, zero_key, zero_value, c, key, value, ns, events, valid, disabled)

def public_string_get_and_refresh(-V: Data, zero_key: String, zero_value: V, c: C.Cache<String, V>, key: String, ns: T.Int64, events: List<&2, ProviderClock.Event>, valid: {Invariants.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> PublicRelation.results(~String, ~SpecLookup.string_same, V, ActualDriver.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, ActualPublic.GetAndRefresh{key, ns}), PublicSpec.execute(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c), zero_key, zero_value, events, S.GetAndRefresh{key, ns})):
  PublicRefresh.string_refresh(V, zero_key, zero_value, c, key, ns, events, valid)

# Oldest-prefix expiry walk (Keys, Values, PurgeExpired): one request per inspected
# finite oldest entry; completed removals survive later provider failures.
def public_string_keys(-V: Data, zero_key: String, zero_value: V, c: C.Cache<String, V>, events: List<&2, ProviderClock.Event>, valid: {Invariants.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> PublicRelation.results(~String, ~SpecLookup.string_same, V, ActualDriver.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, ActualPublic.Keys{}), PublicSpec.execute(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c), zero_key, zero_value, events, S.Keys{})):
  PublicAggregate.string_keys(V, zero_key, zero_value, c, events, valid)

def public_string_values(-V: Data, zero_key: String, zero_value: V, c: C.Cache<String, V>, events: List<&2, ProviderClock.Event>, valid: {Invariants.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> PublicRelation.results(~String, ~SpecLookup.string_same, V, ActualDriver.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, ActualPublic.Values{}), PublicSpec.execute(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c), zero_key, zero_value, events, S.Values{})):
  PublicAggregate.string_values(V, zero_key, zero_value, c, events, valid)

def public_string_purge_expired(-V: Data, zero_key: String, zero_value: V, c: C.Cache<String, V>, events: List<&2, ProviderClock.Event>, valid: {Invariants.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> PublicRelation.results(~String, ~SpecLookup.string_same, V, ActualDriver.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, ActualPublic.PurgeExpired{}), PublicSpec.execute(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c), zero_key, zero_value, events, S.PurgeExpired{})):
  PublicAggregate.string_purge_expired(V, zero_key, zero_value, c, events, valid)

# Every public request (String keys) through the actual start/drive machine,
# for every provider-event list, against the independent typed semantics.
def public_string_request(-V: Data, zero_key: String, zero_value: V, c: C.Cache<String, V>, events: List<&2, ProviderClock.Event>, request: ActualPublic.Request<String, V>, valid: {Invariants.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> PublicRelation.results(~String, ~SpecLookup.string_same, V, ActualDriver.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request), PublicSpec.execute(~String, ~SpecLookup.string_same, V, Initial.abstract(String, V, c), zero_key, zero_value, events, PublicRelation.command(String, V, request))):
  PublicRequests.string_request(V, zero_key, zero_value, c, events, request, valid, disabled)

# Reachability: the cache after every request (returned, or retained after a
# provider exception, invalid sample or exhausted event list) keeps the full
# representation invariant and disabled legacy callback metadata.
def public_string_request_safe(-V: Data, zero_key: String, zero_value: V, c: C.Cache<String, V>, events: List<&2, ProviderClock.Event>, request: ActualPublic.Request<String, V>, valid: {Invariants.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> PublicSafety.outcome_ok(V, ActualDriver.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request)):
  PublicSafety.request_ok(V, zero_key, zero_value, c, events, valid, disabled, request)

# Arbitrary finite traces from actual construction: every capacity/size input,
# every request list and every provider-event list. Rejected construction gives
# the independent error; accepted construction yields a trace whose every
# outcome, final state, unused events and request count refine Traces.run.
def public_string_trace(-V: Data, zero_key: String, zero_value: V, capacity: U32, size: U32, requests: List<&2, ActualPublic.Request<String, V>>, events: List<&2, ProviderClock.Event>) -> PublicTrace.created_rel(V, zero_key, zero_value, requests, events, C.new_with_size(String, V, capacity, size), S.new_with_size(String, V, capacity, size)):
  PublicTrace.from_construction(V, zero_key, zero_value, capacity, size, requests, events)

# Built-in non-String keys. The specification's structural key equalities
# decide equality (sound and reflexive), independently of any codec.
def spec_integer_equality_sound(a: T.Integer, b: T.Integer, e: {SpecKeys.integer_equal(a, b) == True{} : Bool}) -> {a == b : T.Integer}:
  KeyEquality.integer_sound(a, b, e)

def spec_integer_equality_reflexive(a: T.Integer) -> {SpecKeys.integer_equal(a, a) == True{} : Bool}:
  KeyEquality.integer_reflexive(a)

def spec_word64_equality_sound(a: Word(64n), b: Word(64n), e: {SpecKeys.bits_equal(64n, a, b) == True{} : Bool}) -> {a == b : Word(64n)}:
  KeyEquality.bits_sound(64n, a, b, e)

def spec_word64_equality_reflexive(a: Word(64n)) -> {SpecKeys.bits_equal(64n, a, a) == True{} : Bool}:
  KeyEquality.bits_reflexive(64n, a)

# Arbitrary finite traces from construction for Integer and Word64 keys, through
# the same start/drive machine instantiated at the key type with its injective
# codec. Every outcome's reply (including keys in Oldest/KeyList replies),
# error, unused events and request count equal the independent K-keyed
# specification's exactly; states are related canonically after renaming keys
# to their codes. Obtained by transporting public_string_trace along the proved
# machine and specification key renamings (rename_machine/rename_spec.bend).
def public_integer_trace(-V: Data, +zero_key: T.Integer, +zero_value: V, +capacity: U32, +size: U32, +requests: List<&2, ActualPublic.Request<T.Integer, V>>, +events: List<&2, ProviderClock.Event>) -> PublicKeys.created_rel(~T.Integer, ~Codec.integer_encode, ~SpecKeys.integer_same, V, zero_key, zero_value, requests, events, C.new_with_size(T.Integer, V, capacity, size), S.new_with_size(T.Integer, V, capacity, size)):
  PublicKeys.from_construction(~T.Integer, ~Codec.integer_encode, ~SpecKeys.integer_same, ~KeyEquality.integer_agree, ~Codec.integer_injective, V, zero_key, zero_value, capacity, size, requests, events)

def public_word64_trace(-V: Data, +zero_key: Word(64n), +zero_value: V, +capacity: U32, +size: U32, +requests: List<&2, ActualPublic.Request<Word(64n), V>>, +events: List<&2, ProviderClock.Event>) -> PublicKeys.created_rel(~Word(64n), ~Codec.word64_encode, ~SpecKeys.word64_same, V, zero_key, zero_value, requests, events, C.new_with_size(Word(64n), V, capacity, size), S.new_with_size(Word(64n), V, capacity, size)):
  PublicKeys.from_construction(~Word(64n), ~Codec.word64_encode, ~SpecKeys.word64_same, ~KeyEquality.word64_agree, ~Codec.word64_injective, V, zero_key, zero_value, capacity, size, requests, events)

# D.drive unfolding lemmas: a Finished progress returns without consuming
# events, and a Waiting progress consumes exactly one event through
# D.advance. (These are facts about the Bend driver, not about src/adapter.ts;
# the adapter's loop is covered by host_loop_* below.)
def drive_finished(-K: Data, -V: Data, +zero_value: V, events: List<&2, ProviderClock.Event>, c: C.Cache<K, V>, answer: ActualPublic.Answer<K, V>) -> {ActualDriver.drive(K, V, zero_value, events, ActualPublic.Finished{c, answer}) == ActualDriver.Returned{c, answer, events, 0n} : ActualDriver.Outcome<K, V>}:
  HostStep.finished(K, V, zero_value, events, c, answer)

def drive_advance(-K: Data, -V: Data, +zero_value: V, event: ProviderClock.Event, tail: List<&2, ProviderClock.Event>, pending: ActualPublic.Pending<K, V>) -> {ActualDriver.drive(K, V, zero_value, Con{event, tail}, ActualPublic.Waiting{pending}) == HostStep.continue(K, V, zero_value, ActualDriver.advance(K, V, zero_value, pending, event), tail) : ActualDriver.Outcome<K, V>}:
  HostStep.waiting(K, V, zero_value, event, tail, pending)

# ---------------------------------------------------------------------------
# Host boundary. src/adapter.ts passes integers as decimal text and strings
# unchanged, and calls only these Bend functions (plus the Bend codecs).

# The host specification's range condition fits(n, v) (the n-bit round trip)
# holds exactly when v < 2^n: host_fits_meaning gives v < 2^n => fits, and
# host_fits_bound gives fits => v < 2^n, so out-of-range numerals are rejected,
# never wrapped.
def host_fits_meaning(+n: Nat, +v: Nat, h: {Nat.is_lt(v, Nat.pow(2n, n)) == True{} : Bool}) -> {HostSpec.fits(n, v) == True{} : Bool}:
  HostNumeric.fits_meaning(n, v, h)

def host_fits_bound(+n: Nat, +v: Nat, h: {HostSpec.fits(n, v) == True{} : Bool}) -> {Nat.is_lt(v, Nat.pow(2n, n)) == True{} : Bool}:
  HostNumeric.fits_bound(n, v, h)

# uint64 keys: exactly the natural numerals below 2^64, as their word.
def host_uint64_key(+s: String) -> {Host.uint64_key(s) == HostNumeric.lift(64n, "uint64 key", HostSpec.unsigned_text(64n, s)) : Result<&2, &2, String, Word(64n)>}:
  HostNumeric.unsigned_word(64n, "uint64 key", s)

# int64 keys: exactly the integer numerals in [-2^63, 2^63), two's complement.
def host_int64_key(+s: String) -> {Host.int64_key(s) == HostNumeric.lift(64n, "int64 key", HostSpec.int64_text(s)) : Result<&2, &2, String, Word(64n)>}:
  HostNumeric.signed_word(63n, "int64 key", s)

# Signed reader for every width (int64 is n = 63).
def host_signed_word(+n: Nat, +msg: String, +s: String) -> {Host.signed_word(n, msg, s) == HostNumeric.lift(1n+n, msg, HostSpec.signed_text(n, s)) : Result<&2, &2, String, Word(1n+n)>}:
  HostNumeric.signed_word(n, msg, s)

# Unsigned reader for every width (uint64 is 64, construction inputs 32).
def host_unsigned_word(+n: Nat, msg: String, +s: String) -> {Host.unsigned_word(n, msg, s) == HostNumeric.lift(n, msg, HostSpec.unsigned_text(n, s)) : Result<&2, &2, String, Word(n)>}:
  HostNumeric.unsigned_word(n, msg, s)

# Counters and uint64 keys returned as text read as the word's unsigned value.
def host_uint64_text(+w: Word(64n)) -> {HostSpec.natural(Host.uint64_text(w)) == Some{NumericSpec.unsigned(64n, w)} : Maybe<&2, Nat>}:
  HostRender.unsigned_text(64n, w)

# int64 keys returned as text read as exactly the same two's-complement word.
def host_int64_text(+w: Word(64n)) -> {HostSpec.int64_text(Host.int64_text(w)) == Some{w} : Maybe<&2, Word(64n)>}:
  HostRender.signed_text(63n, w)

def host_uint64_roundtrip(+w: Word(64n)) -> {Host.uint64_key(Host.uint64_text(w)) == Done{w} : Result<&2, &2, String, Word(64n)>}:
  HostBoundary.uint64_roundtrip(w)

def host_int64_roundtrip(+w: Word(64n)) -> {Host.int64_key(Host.int64_text(w)) == Done{w} : Result<&2, &2, String, Word(64n)>}:
  HostBoundary.int64_roundtrip(w)

# String keys: exactly the Unicode scalar strings, unchanged.
def host_string_key(+s: String) -> {Host.string_key(s) == HostBoundary.accept(s, HostSpec.scalar(s)) : Result<&2, &2, String, String>}:
  HostBoundary.string_key(s)

# Durations: signed int64 text, rejected with "int64 value" otherwise.
def host_time(+s: String) -> {Host.time(s) == HostBoundary.time_spec(HostSpec.int64_text(s)) : Result<&2, &2, String, T.Int64>}:
  HostBoundary.time(s)

# Clock samples: an in-range int64 is a Sample, anything else InvalidSample.
def host_sample(+s: String) -> {Host.sample(s) == HostBoundary.sample_spec(HostSpec.int64_text(s)) : ProviderClock.Event}:
  HostBoundary.sample(s)

# Construction: uint32 capacity/size text, then the actual validation.
def host_create(-K: Data, -V: Data, +capacity: String, +size: String) -> {Host.create(K, V, capacity, size) == HostBoundary.create_spec(K, V, HostSpec.unsigned_text(32n, capacity), HostSpec.unsigned_text(32n, size)) : Result<&2, &2, String, C.Cache<K, V>>}:
  HostBoundary.create(K, V, capacity, size)

# The adapter's loop: H.begin, then H.answer once per Ask with the provider's
# event, adopting Return/Raise. Over any event sequence it is D.drive ...
def host_loop_drive(-K: Data, -V: Data, +zero_value: V, events: List<&2, ProviderClock.Event>, progress: ActualPublic.Progress<K, V>) -> {HostLoop.loop(K, V, zero_value, events, Host.act(K, V, progress)) == ActualDriver.drive(K, V, zero_value, events, progress) : ActualDriver.Outcome<K, V>}:
  HostLoop.drives(K, V, zero_value, events, progress)

# ... and a request is D.execute, the machine of the trace theorems above.
def host_loop_string(-V: Data, zero_key: String, +zero_value: V, +c: C.Cache<String, V>, events: List<&2, ProviderClock.Event>, request: ActualPublic.Request<String, V>) -> {HostLoop.loop(String, V, zero_value, events, Host.begin(String, V, Codec.string_encode, zero_key, zero_value, c, request)) == ActualDriver.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request) : ActualDriver.Outcome<String, V>}:
  HostLoop.executes(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request)

def host_loop_word64(-V: Data, zero_key: Word(64n), +zero_value: V, +c: C.Cache<Word(64n), V>, events: List<&2, ProviderClock.Event>, request: ActualPublic.Request<Word(64n), V>) -> {HostLoop.loop(Word(64n), V, zero_value, events, Host.begin(Word(64n), V, Codec.word64_encode, zero_key, zero_value, c, request)) == ActualDriver.execute(~Word(64n), ~Codec.word64_encode, V, zero_key, zero_value, c, events, request) : ActualDriver.Outcome<Word(64n), V>}:
  HostLoop.executes(~Word(64n), ~Codec.word64_encode, V, zero_key, zero_value, c, events, request)

# A throwing provider is the provider-exception event (its original error is
# rethrown by the adapter after adopting the Raise state).
def host_thrown() -> {Host.thrown() == ProviderClock.ProviderException{"clock provider threw"} : ProviderClock.Event}:
  {==}

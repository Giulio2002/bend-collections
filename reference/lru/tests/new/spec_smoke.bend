import Base
import ../../spec/traces.bend as Traces
import ../../spec/public_commands.bend as PublicCommands
import ../../spec/effectful_aggregate.bend as EffectfulAggregate
import ../../spec/effectful_operations.bend as Effectful
import ../../spec/clock.bend as Clock
import ../../proofs/representation_parts.bend as Parts
import ../../proofs/abstraction_recency.bend as Recency
import ../../src/cache.bend as C
import ../../proofs/refinement.bend as F
import ../../proofs/cache_populated.bend as Pop
import ../../proofs/cache_oldest_available.bend as Oldest
import ../../spec/public_oldest.bend as PublicOldest
import ../../spec/cache.bend as S
import ../../spec/operations.bend as O
import ../../types/model.bend as T
import ../../proofs/abstraction_identity.bend as Identity
import ../../proofs/invariants.bend as Inv
import ../../proofs/map_lookup.bend as Lookup

# Instantiate templates so their live affine/termination obligations are checked.
def same(a: String) -> String -> Bool:
  b => String.eq(a, b)

def smoke() -> S.Observation<String, Nat>:
  O.add(~String, ~same, Nat, S.initial(String, Nat, 2n), "k", 7n, T.I64{Word.zero(64n)})

def smoke_read(s: S.Model<String, Nat>, now: T.Int64) -> S.Observation<String, Nat>:
  O.read(~String, ~same, Nat, s, "k", now, True{})

def smoke_refresh(s: S.Model<String, Nat>, ns: T.Int64, now: T.Int64) -> S.Observation<String, Nat>:
  O.refresh(~String, ~same, Nat, s, "k", ns, now)

def smoke_oldest(s: S.Model<String, Nat>, now: T.Int64) -> S.Observation<String, Nat>:
  O.get_oldest(~String, ~same, Nat, s, now)

def smoke_remove_oldest(s: S.Model<String, Nat>) -> S.Observation<String, Nat>:
  O.remove_oldest(~String, ~same, Nat, s)

def smoke_purge(s: S.Model<String, Nat>) -> O.AggregateResult<String, Nat>:
  O.purge(~String, ~same, Nat, s)

def smoke_expire(s: S.Model<String, Nat>, times: List<&2, T.Int64>) -> Result<&2, &2, O.AggregateFailure<String, Nat>, O.AggregateResult<String, Nat>>:
  O.purge_expired(~String, ~same, Nat, s, times)

def smoke_public_oldest(s: S.Model<String, Nat>, times: List<&2, T.Int64>) -> Result<&2, &2, String, PublicOldest.Reply<String, Nat>>:
  PublicOldest.get_oldest(~String, ~same, Nat, s, "", 0n, times)


def smoke_identity(-V: Data, xs: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<String, V>>>>, code: String, entry: T.Entry<String, V>, valid: {Inv.identities(~String, ~Inv.string_identity, V, xs) == True{} : Bool}, member: Lookup.listed(T.Entry<String, V>, xs, code, entry)) -> {code == Identity.entry_code(~String, ~Inv.string_identity, V, entry) : String}:
  Identity.listed_identity(~String, ~Inv.string_identity, V, xs, code, entry, valid, member)

def smoke_recency(-V: Data, c: C.Cache<String, V>, valid: {F.storage_critbit(String, V, c) == True{} : Bool}, populated: {Pop.storage_populated(String, V, c) == True{} : Bool}, identities: {Recency.cache_identities(~String, ~Inv.string_identity, V, c) == True{} : Bool}, included: {Oldest.order_in_keys(String, V, c) == True{} : Bool}) -> {Recency.encode_keys(~String, ~Inv.string_identity, Recency.model_order(String, V, F.abstract(String, V, c))) == Recency.native_order(String, V, c) : List<&2, String>}:
  Recency.faithful(~String, ~Inv.string_identity, V, c, valid, populated, identities, included)

def smoke_joint_add(-V: Data, c: C.Cache<String, V>, key: String, value: V, ns: T.Int64, now: T.Int64, valid: {Inv.representation(~String, ~Inv.string_identity, V, c) == True{} : Bool}) -> {Nat.is_le(C.len(String, V, C.step_cache(String, V, C.add_with_lifetime(String, V, Inv.string_identity, c, key, value, ns, now))), C.capacity(String, V, c)) == True{} : Bool}:
  Parts.add_bounded(~String, ~Inv.string_identity, V, c, key, value, ns, now, valid)

def smoke_joint_recency(-V: Data, c: C.Cache<String, V>, valid: {Inv.representation(~String, ~Inv.string_identity, V, c) == True{} : Bool}) -> {Recency.encode_keys(~String, ~Inv.string_identity, Recency.model_order(String, V, F.abstract(String, V, c))) == Recency.native_order(String, V, c) : List<&2, String>}:
  Parts.recency_faithful(~String, ~Inv.string_identity, V, c, valid)

def effectful_add(s: S.Model<String, Nat>, key: String, value: Nat, ns: T.Int64, events: List<&2, Clock.Event>) -> Effectful.Outcome<String, Nat>:
  Effectful.add_with_lifetime(~String, ~same, Nat, s, key, value, ns, events)

def effectful_default_add(s: S.Model<String, Nat>, key: String, value: Nat, events: List<&2, Clock.Event>) -> Effectful.Outcome<String, Nat>:
  Effectful.add(~String, ~same, Nat, s, key, value, events)

def effectful_refresh(s: S.Model<String, Nat>, key: String, ns: T.Int64, events: List<&2, Clock.Event>) -> Effectful.Outcome<String, Nat>:
  Effectful.refresh(~String, ~same, Nat, s, key, ns, events)

def effectful_purge_expired(s: S.Model<String, Nat>, events: List<&2, Clock.Event>) -> Effectful.Outcome<String, Nat>:
  EffectfulAggregate.purge_expired(~String, ~same, Nat, s, events)

def effectful_read(s: S.Model<String, Nat>, key: String, tracked: Bool, events: List<&2, Clock.Event>) -> Effectful.Outcome<String, Nat>:
  Effectful.read(~String, ~same, Nat, s, key, tracked, events)

def public_command(s: S.Model<String, Nat>, events: List<&2, Clock.Event>, command: S.Command<String, Nat>) -> PublicCommands.Result<String, Nat>:
  PublicCommands.execute(~String, ~same, Nat, s, "", 0n, events, command)

def public_trace(s: S.Model<String, Nat>, events: List<&2, Clock.Event>, commands: List<&2, S.Command<String, Nat>>) -> Traces.Trace<String, Nat>:
  Traces.run(~String, ~same, Nat, commands, s, "", 0n, events)

def integer_equal(a: T.Integer, b: T.Integer) -> Bool:
  match a b:
    case T.Positive{x} T.Positive{y}: Nat.is_eq(x, y)
    case T.Negative{x} T.Negative{y}: Nat.is_eq(x, y)
    case x y: False{}

def integer_same(a: T.Integer) -> T.Integer -> Bool:
  b => integer_equal(a, b)

def word64_same(a: Word(64n)) -> Word(64n) -> Bool:
  b => Cmp.is_eq(Word.cmp(64n, a, b))

def integer_public_trace(s: S.Model<T.Integer, Nat>, events: List<&2, Clock.Event>, commands: List<&2, S.Command<T.Integer, Nat>>) -> Traces.Trace<T.Integer, Nat>:
  Traces.run(~T.Integer, ~integer_same, Nat, commands, s, T.Positive{0n}, 0n, events)

def word64_public_trace(s: S.Model<Word(64n), Nat>, events: List<&2, Clock.Event>, commands: List<&2, S.Command<Word(64n), Nat>>) -> Traces.Trace<Word(64n), Nat>:
  Traces.run(~Word(64n), ~word64_same, Nat, commands, s, Word.zero(64n), 0n, events)

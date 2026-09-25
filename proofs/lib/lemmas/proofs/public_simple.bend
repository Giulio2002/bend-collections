import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../src/public.bend as Pub
import ../src/driver.bend as D
import ../spec/cache.bend as S
import ../spec/clock.bend as Clock
import ../spec/operations.bend as O
import ../spec/public_commands.bend as PC
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./disabled.bend as Disabled
import ./spec_lookup.bend as Lookup
import ./public_relation.bend as R
import ./public_finish.bend as Finish
import ./extensional_states.bend as Ext
import ./remove_refinement.bend as Remove

# Whole public Remove through the actual start/drive machine, every event list.
def remove(-V: Data, zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +key: String, +events: List<&2, Clock.ClockEvent>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> R.results(~String, ~Lookup.string_same, V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, Pub.Remove{key}), PC.execute(~String, ~Lookup.string_same, V, F.abstract(String, V, c), zero_key, zero_value, events, R.command(String, V, Pub.Remove{key}))):
  %Equal.sym(D.Outcome<String, V>, D.drive(String, V, zero_value, events, Pub.finish_step(String, V, zero_value, C.remove(String, V, Codec.string_encode, c, key), Pub.Flag{})), Finish.returned(V, zero_value, C.remove(String, V, Codec.string_encode, c, key), Pub.Flag{}, events, 0n), Finish.drive_step(V, zero_value, C.remove(String, V, Codec.string_encode, c, key), Pub.Flag{}, events)) : R.results(~String, ~Lookup.string_same, V, _, PC.observation(~String, ~Lookup.string_same, V, zero_key, zero_value, PC.Flag{}, S.remove(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key), events, 0n))
  Finish.finished(V, zero_key, zero_value, C.remove(String, V, Codec.string_encode, c, key), Pub.Flag{}, S.remove(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key), events, 0n, {==}, Remove.operation(V, c, key, valid, disabled))

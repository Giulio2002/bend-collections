import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../src/public.bend as Pub
import ../src/driver.bend as D
import ../spec/cache.bend as S
import ../spec/clock.bend as Clock
import ../spec/public_commands.bend as PC
import ../spec/traces.bend as Traces
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./disabled.bend as Disabled
import ./spec_lookup.bend as Lookup
import ./public_relation.bend as R
import ./public_requests.bend as Requests
import ./public_safety.bend as Safety
import ./spec_congruence.bend as Congruence
import ./extensional_states.bend as Ext
import ./constructor_safety.bend as ConstructorSafety

# Arbitrary finite public traces: the actual driver threads its own caches and
# provider events through every request (callers may continue after a failed
# request); the independent trace threads its own models. They stay related.

def commands(-V: Data, requests: List<&2, Pub.Request<String, V>>) -> List<&2, S.Command<String, V>>:
  match requests:
    case Nil{}: Nil{}
    case Con{request, tail}: Con{R.command(String, V, request), commands(V, tail)}

def outcomes(-V: Data, actual: List<&2, D.Outcome<String, V>>, expected: List<&2, PC.Result<String, V>>) -> Type:
  match actual expected:
    case Nil{} Nil{}: Unit
    case Con{o, os} Con{r, rs}: R.results(~String, ~Lookup.string_same, V, o, r) & outcomes(V, os, rs)
    case Nil{} Con{r, rs}: Empty
    case Con{o, os} Nil{}: Empty

# Final state related, same unused provider events, same total request count,
# and every per-request outcome related to its independent result.
def traces(-V: Data, actual: D.Trace<String, V>, expected: Traces.Trace<String, V>) -> Type:
  match actual expected:
    case D.Ran{c, ea, os, na} Traces.Finished{s, eb, rs, nb}:
      E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, c), s) & {ea == eb : List<&2, Clock.Event>} & {na == nb : Nat} & outcomes(V, os, rs)

def result_state(-V: Data, o: D.Outcome<String, V>, r: PC.Result<String, V>, related: R.results(~String, ~Lookup.string_same, V, o, r)) -> E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, D.cache(String, V, o)), Traces.state(String, V, r)):
  match o r:
    case D.Returned{c, a, e, n} PC.Returned{s, x, f, m}:
      (st, rp, ev, ct) = related
      st
    case D.Failed{c, a, e, n} PC.Failed{s, x, f, m}:
      (st, er, ev, ct) = related
      st
    case D.Returned{c, a, e, n} PC.Failed{s, x, f, m}: Empty.absurd(E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, c), s), related)
    case D.Failed{c, a, e, n} PC.Returned{s, x, f, m}: Empty.absurd(E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, c), s), related)

def result_remaining(-V: Data, o: D.Outcome<String, V>, r: PC.Result<String, V>, related: R.results(~String, ~Lookup.string_same, V, o, r)) -> {D.remaining(String, V, o) == Traces.remaining(String, V, r) : List<&2, Clock.Event>}:
  match o r:
    case D.Returned{c, a, e, n} PC.Returned{s, x, f, m}:
      (st, rp, ev, ct) = related
      ev
    case D.Failed{c, a, e, n} PC.Failed{s, x, f, m}:
      (st, er, ev, ct) = related
      ev
    case D.Returned{c, a, e, n} PC.Failed{s, x, f, m}: Empty.absurd({e == f : List<&2, Clock.Event>}, related)
    case D.Failed{c, a, e, n} PC.Returned{s, x, f, m}: Empty.absurd({e == f : List<&2, Clock.Event>}, related)

def result_requests(-V: Data, o: D.Outcome<String, V>, r: PC.Result<String, V>, related: R.results(~String, ~Lookup.string_same, V, o, r)) -> {D.requests(String, V, o) == Traces.requests(String, V, r) : Nat}:
  match o r:
    case D.Returned{c, a, e, n} PC.Returned{s, x, f, m}:
      (st, rp, ev, ct) = related
      ct
    case D.Failed{c, a, e, n} PC.Failed{s, x, f, m}:
      (st, er, ev, ct) = related
      ct
    case D.Returned{c, a, e, n} PC.Failed{s, x, f, m}: Empty.absurd({n == m : Nat}, related)
    case D.Failed{c, a, e, n} PC.Returned{s, x, f, m}: Empty.absurd({n == m : Nat}, related)

def prepend_related(-V: Data, +o: D.Outcome<String, V>, +r: PC.Result<String, V>, step: R.results(~String, ~Lookup.string_same, V, o, r), requests: {D.requests(String, V, o) == Traces.requests(String, V, r) : Nat}, actual: D.Trace<String, V>, expected: Traces.Trace<String, V>, rest: traces(V, actual, expected)) -> traces(V, D.prepend(String, V, o, actual), Traces.prepend(String, V, r, expected)):
  D.Ran{+c, +ea, os, +na} = actual
  Traces.Finished{+s, +eb, rs, +nb} = expected
  (st, ev, ct, later) = rest
  (st, ev, Equal.trans(Nat, Nat.add(D.requests(String, V, o), na), Nat.add(Traces.requests(String, V, r), na), Nat.add(Traces.requests(String, V, r), nb), Equal.cong(Nat, Nat, x => Nat.add(x, na), D.requests(String, V, o), Traces.requests(String, V, r), requests), Equal.cong(Nat, Nat, y => Nat.add(Traces.requests(String, V, r), y), na, nb, ct)), (step, later))

def ok_valid(-V: Data, c: C.Cache<String, V>, safe: Safety.ok(V, c)) -> {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}:
  (valid, disabled) = safe
  valid

def ok_disabled(-V: Data, c: C.Cache<String, V>, safe: Safety.ok(V, c)) -> {Disabled.flag(String, V, c) == False{} : Bool}:
  (valid, disabled) = safe
  disabled

# One request against any related independent model.
def step_results(-V: Data, +zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +s: S.Model<String, V>, +events: List<&2, Clock.Event>, +request: Pub.Request<String, V>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}, +related: E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, c), s)) -> R.results(~String, ~Lookup.string_same, V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request), PC.execute(~String, ~Lookup.string_same, V, s, zero_key, zero_value, events, R.command(String, V, request))):
  Congruence.compose(V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request), PC.execute(~String, ~Lookup.string_same, V, F.abstract(String, V, c), zero_key, zero_value, events, R.command(String, V, request)), PC.execute(~String, ~Lookup.string_same, V, s, zero_key, zero_value, events, R.command(String, V, request)), Requests.string_request(V, zero_key, zero_value, c, events, request, valid, disabled), Congruence.execute_cong(V, zero_key, zero_value, F.abstract(String, V, c), s, events, related, R.command(String, V, request)))

# Every finite request list, every provider-event list, from any safe cache and
# any related independent model.
def trace(-V: Data, +zero_key: String, +zero_value: V, requests: List<&2, Pub.Request<String, V>>, +c: C.Cache<String, V>, +s: S.Model<String, V>, +events: List<&2, Clock.Event>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}, +related: E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, c), s)) -> traces(V, D.run(~String, ~Codec.string_encode, V, requests, c, zero_key, zero_value, events), Traces.run(~String, ~Lookup.string_same, V, commands(V, requests), s, zero_key, zero_value, events)):
  match requests:
    case Nil{}: (related, {==}, {==}, Unit{})
    case Con{+request, +tail}:
      %result_remaining(V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request), PC.execute(~String, ~Lookup.string_same, V, s, zero_key, zero_value, events, R.command(String, V, request)), step_results(V, zero_key, zero_value, c, s, events, request, valid, disabled, related)) : traces(V, D.prepend(String, V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request), D.run(~String, ~Codec.string_encode, V, tail, D.cache(String, V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request)), zero_key, zero_value, D.remaining(String, V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request)))), Traces.prepend(String, V, PC.execute(~String, ~Lookup.string_same, V, s, zero_key, zero_value, events, R.command(String, V, request)), Traces.run(~String, ~Lookup.string_same, V, commands(V, tail), Traces.state(String, V, PC.execute(~String, ~Lookup.string_same, V, s, zero_key, zero_value, events, R.command(String, V, request))), zero_key, zero_value, _)))
      prepend_related(V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request), PC.execute(~String, ~Lookup.string_same, V, s, zero_key, zero_value, events, R.command(String, V, request)), step_results(V, zero_key, zero_value, c, s, events, request, valid, disabled, related), result_requests(V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request), PC.execute(~String, ~Lookup.string_same, V, s, zero_key, zero_value, events, R.command(String, V, request)), step_results(V, zero_key, zero_value, c, s, events, request, valid, disabled, related)), D.run(~String, ~Codec.string_encode, V, tail, D.cache(String, V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request)), zero_key, zero_value, D.remaining(String, V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request))), Traces.run(~String, ~Lookup.string_same, V, commands(V, tail), Traces.state(String, V, PC.execute(~String, ~Lookup.string_same, V, s, zero_key, zero_value, events, R.command(String, V, request))), zero_key, zero_value, D.remaining(String, V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request))), trace(V, zero_key, zero_value, tail, D.cache(String, V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request)), Traces.state(String, V, PC.execute(~String, ~Lookup.string_same, V, s, zero_key, zero_value, events, R.command(String, V, request))), D.remaining(String, V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request)), ok_valid(V, D.cache(String, V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request)), Safety.request_ok(V, zero_key, zero_value, c, events, valid, disabled, request)), ok_disabled(V, D.cache(String, V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request)), Safety.request_ok(V, zero_key, zero_value, c, events, valid, disabled, request)), result_state(V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request), PC.execute(~String, ~Lookup.string_same, V, s, zero_key, zero_value, events, R.command(String, V, request)), step_results(V, zero_key, zero_value, c, s, events, request, valid, disabled, related))))

# From actual construction: rejected inputs give the same error; accepted
# inputs start a trace related to the independent initial model.
def created_rel(-V: Data, +zero_key: String, +zero_value: V, +requests: List<&2, Pub.Request<String, V>>, +events: List<&2, Clock.Event>, actual: Result<&2, &2, String, C.Cache<String, V>>, expected: Result<&2, &2, String, S.Model<String, V>>) -> Type:
  match actual expected:
    case Fail{ea} Fail{eb}: {ea == eb : String}
    case Done{c} Done{s}: traces(V, D.run(~String, ~Codec.string_encode, V, requests, c, zero_key, zero_value, events), Traces.run(~String, ~Lookup.string_same, V, commands(V, requests), s, zero_key, zero_value, events))
    case Fail{ea} Done{s}: Empty
    case Done{c} Fail{eb}: Empty

def created(-V: Data, +zero_key: String, +zero_value: V, +requests: List<&2, Pub.Request<String, V>>, +events: List<&2, Clock.Event>, result: Result<&2, &2, String, C.Cache<String, V>>, safe: ConstructorSafety.safe_result(~String, ~Codec.string_encode, V, result)) -> created_rel(V, zero_key, zero_value, requests, events, result, F.abstract_created(String, V, result)):
  match result:
    case Fail{error}: {==}
    case Done{+c}:
      (+valid, +disabled) = safe
      trace(V, zero_key, zero_value, requests, c, F.abstract(String, V, c), events, valid, disabled, Ext.string_reflexive(V, F.abstract(String, V, c)))

def from_construction(-V: Data, +zero_key: String, +zero_value: V, +capacity: U32, +size: U32, +requests: List<&2, Pub.Request<String, V>>, +events: List<&2, Clock.Event>) -> created_rel(V, zero_key, zero_value, requests, events, C.new_with_size(String, V, capacity, size), S.new_with_size(String, V, capacity, size)):
  %F.new_with_size_refines(String, V, capacity, size) : created_rel(V, zero_key, zero_value, requests, events, C.new_with_size(String, V, capacity, size), _)
  created(V, zero_key, zero_value, requests, events, C.new_with_size(String, V, capacity, size), ConstructorSafety.string_new(V, capacity, size))

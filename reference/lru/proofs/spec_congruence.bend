import Base
import ../src/cache.bend as C
import ../src/driver.bend as D
import ../spec/cache.bend as S
import ../spec/clock.bend as Clock
import ../spec/numeric.bend as N
import ../spec/operations.bend as O
import ../spec/effectful_operations.bend as Eff
import ../spec/effectful_aggregate.bend as A
import ../spec/public_commands.bend as PC
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./refinement.bend as F
import ./spec_lookup.bend as Lookup
import ./public_relation.bend as R
import ./extensional_states.bend as Ext
import ./canonical.bend as Can
import ./canonical_string.bend as CS
import ./canonical_remove.bend as CR
import ./write_congruence.bend as Write

# The independent public semantics is invariant under the canonical relation:
# related models give equal replies/errors/events/counts and related states.
# This is a property of the specification alone (String keys).

def sres(-V: Data, a: PC.Result<String, V>, b: PC.Result<String, V>) -> Type:
  match a b:
    case PC.Returned{sa, ra, ea, na} PC.Returned{sb, rb, eb, nb}:
      E.states(~String, ~Lookup.string_same, V, sa, sb) & {ra == rb : PC.Reply<String, V>} & {ea == eb : List<&2, Clock.Event>} & {na == nb : Nat}
    case PC.Failed{sa, xa, ea, na} PC.Failed{sb, xb, eb, nb}:
      E.states(~String, ~Lookup.string_same, V, sa, sb) & {xa == xb : Clock.Error} & {ea == eb : List<&2, Clock.Event>} & {na == nb : Nat}
    case PC.Returned{sa, ra, ea, na} PC.Failed{sb, xb, eb, nb}: Empty
    case PC.Failed{sa, xa, ea, na} PC.Returned{sb, rb, eb, nb}: Empty

def eres(-V: Data, a: Eff.Outcome<String, V>, b: Eff.Outcome<String, V>) -> Type:
  match a b:
    case Eff.Returned{oa, ea, na} Eff.Returned{ob, eb, nb}:
      E.observations(~String, ~Lookup.string_same, V, oa, ob) & {ea == eb : List<&2, Clock.Event>} & {na == nb : Nat}
    case Eff.Failed{sa, xa, ea, na} Eff.Failed{sb, xb, eb, nb}:
      E.states(~String, ~Lookup.string_same, V, sa, sb) & {xa == xb : Clock.Error} & {ea == eb : List<&2, Clock.Event>} & {na == nb : Nat}
    case Eff.Returned{oa, ea, na} Eff.Failed{sb, xb, eb, nb}: Empty
    case Eff.Failed{sa, xa, ea, na} Eff.Returned{ob, eb, nb}: Empty

# Composition: actual-versus-spec results followed by spec congruence.
def compose(-V: Data, actual: D.Outcome<String, V>, x: PC.Result<String, V>, y: PC.Result<String, V>, first: R.results(~String, ~Lookup.string_same, V, actual, x), second: sres(V, x, y)) -> R.results(~String, ~Lookup.string_same, V, actual, y):
  match actual x y:
    case D.Returned{c, answer, events, count} PC.Returned{sx, rx, ex, nx} PC.Returned{sy, ry, ey, ny}:
      (st1, rp1, ev1, ct1) = first
      (st2, rp2, ev2, ct2) = second
      (Ext.string_transitive(V, F.abstract(String, V, c), sx, sy, st1, st2), Equal.trans(PC.Reply<String, V>, R.reply(String, V, answer), rx, ry, rp1, rp2), Equal.trans(List<&2, Clock.Event>, events, ex, ey, ev1, ev2), Equal.trans(Nat, count, nx, ny, ct1, ct2))
    case D.Failed{c, error, events, count} PC.Failed{sx, xx, ex, nx} PC.Failed{sy, xy, ey, ny}:
      (st1, er1, ev1, ct1) = first
      (st2, er2, ev2, ct2) = second
      (Ext.string_transitive(V, F.abstract(String, V, c), sx, sy, st1, st2), Equal.trans(Clock.Error, error, xx, xy, er1, er2), Equal.trans(List<&2, Clock.Event>, events, ex, ey, ev1, ev2), Equal.trans(Nat, count, nx, ny, ct1, ct2))
    case D.Returned{c, answer, events, count} PC.Returned{sx, rx, ex, nx} PC.Failed{sy, xy, ey, ny}: Empty.absurd(R.results(~String, ~Lookup.string_same, V, D.Returned{c, answer, events, count}, PC.Failed{sy, xy, ey, ny}), second)
    case D.Returned{c, answer, events, count} PC.Failed{sx, xx, ex, nx} y: Empty.absurd(R.results(~String, ~Lookup.string_same, V, D.Returned{c, answer, events, count}, y), first)
    case D.Failed{c, error, events, count} PC.Failed{sx, xx, ex, nx} PC.Returned{sy, ry, ey, ny}: Empty.absurd(R.results(~String, ~Lookup.string_same, V, D.Failed{c, error, events, count}, PC.Returned{sy, ry, ey, ny}), second)
    case D.Failed{c, error, events, count} PC.Returned{sx, rx, ex, nx} y: Empty.absurd(R.results(~String, ~Lookup.string_same, V, D.Failed{c, error, events, count}, y), first)

def project_cong(-V: Data, +zero_key: String, +zero_value: V, +sa: S.Model<String, V>, +sb: S.Model<String, V>, +item: Maybe<&2, T.Entry<String, V>>, +present: Bool, +related: E.states(~String, ~Lookup.string_same, V, sa, sb), kind: PC.Projection<String>) -> {PC.project(~String, ~Lookup.string_same, V, sa, zero_key, zero_value, item, present, kind) == PC.project(~String, ~Lookup.string_same, V, sb, zero_key, zero_value, item, present, kind) : PC.Reply<String, V>}:
  match kind:
    case PC.Flag{}: {==}
    case PC.ValueOnly{}: {==}
    case PC.RemovedOldest{}: {==}
    case PC.CapturedOldest{k}: {==}
    case PC.Nothing{}: {==}
    case PC.Keys{}: Equal.cong(List<&2, T.Entry<String, V>>, PC.Reply<String, V>, xs => PC.KeyList{O.entry_keys(String, V, xs)}, O.all_entries(~String, ~Lookup.string_same, V, sa), O.all_entries(~String, ~Lookup.string_same, V, sb), CS.entries_agreement(V, sa, sb, related))
    case PC.Values{}: Equal.cong(List<&2, T.Entry<String, V>>, PC.Reply<String, V>, xs => PC.ValueList{O.entry_values(String, V, xs)}, O.all_entries(~String, ~Lookup.string_same, V, sa), O.all_entries(~String, ~Lookup.string_same, V, sb), CS.entries_agreement(V, sa, sb, related))

def observation_cong(-V: Data, +zero_key: String, +zero_value: V, +kind: PC.Projection<String>, a: S.Observation<String, V>, b: S.Observation<String, V>, +events: List<&2, Clock.Event>, +count: Nat, related: E.observations(~String, ~Lookup.string_same, V, a, b)) -> sres(V, PC.observation(~String, ~Lookup.string_same, V, zero_key, zero_value, kind, a, events, count), PC.observation(~String, ~Lookup.string_same, V, zero_key, zero_value, kind, b, events, count)):
  S.Observed{+sa, +ia, +fa, ea} = a
  S.Observed{+sb, +ib, +fb, eb} = b
  (+st, +it, +fl, ev) = related
  %it : sres(V, PC.Returned{sa, PC.project(~String, ~Lookup.string_same, V, sa, zero_key, zero_value, ia, fa, kind), events, count}, PC.Returned{sb, PC.project(~String, ~Lookup.string_same, V, sb, zero_key, zero_value, _, fb, kind), events, count})
  %fl : sres(V, PC.Returned{sa, PC.project(~String, ~Lookup.string_same, V, sa, zero_key, zero_value, ia, fa, kind), events, count}, PC.Returned{sb, PC.project(~String, ~Lookup.string_same, V, sb, zero_key, zero_value, ia, _, kind), events, count})
  (st, project_cong(V, zero_key, zero_value, sa, sb, ia, fa, st, kind), {==}, {==})

def effect_cong(-V: Data, +zero_key: String, +zero_value: V, +kind: PC.Projection<String>, a: Eff.Outcome<String, V>, b: Eff.Outcome<String, V>, related: eres(V, a, b)) -> sres(V, PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, kind, a), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, kind, b)):
  match a b:
    case Eff.Returned{oa, +ea, +na} Eff.Returned{ob, eb, nb}:
      (obs, ev, ct) = related
      %ev : sres(V, PC.observation(~String, ~Lookup.string_same, V, zero_key, zero_value, kind, oa, ea, na), PC.observation(~String, ~Lookup.string_same, V, zero_key, zero_value, kind, ob, _, nb))
      %ct : sres(V, PC.observation(~String, ~Lookup.string_same, V, zero_key, zero_value, kind, oa, ea, na), PC.observation(~String, ~Lookup.string_same, V, zero_key, zero_value, kind, ob, ea, _))
      observation_cong(V, zero_key, zero_value, kind, oa, ob, ea, na, obs)
    case Eff.Failed{sa, xa, ea, na} Eff.Failed{sb, xb, eb, nb}: related
    case Eff.Returned{oa, ea, na} Eff.Failed{sb, xb, eb, nb}: Empty.absurd(sres(V, PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, kind, Eff.Returned{oa, ea, na}), PC.Failed{sb, xb, eb, nb}), related)
    case Eff.Failed{sa, xa, ea, na} Eff.Returned{ob, eb, nb}: Empty.absurd(sres(V, PC.Failed{sa, xa, ea, na}, PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, kind, Eff.Returned{ob, eb, nb})), related)

# ---------------------------------------------------------------------------
# Canonical projections.
def cap_of(-V: Data, c: E.Canonical<String, V>) -> Nat:
  E.Canon{cap, o, l, m, f, xs, x} = c
  cap

def order_of(-V: Data, c: E.Canonical<String, V>) -> List<&2, String>:
  E.Canon{cap, o, l, m, f, xs, x} = c
  o

def life_of(-V: Data, c: E.Canonical<String, V>) -> T.Int64:
  E.Canon{cap, o, l, m, f, xs, x} = c
  l

def cb_of(-V: Data, c: E.Canonical<String, V>) -> Bool:
  E.Canon{cap, o, l, m, f, xs, x} = c
  f

def c_hit(-V: Data, c: E.Canonical<String, V>) -> E.Canonical<String, V>:
  E.Canon{cap, o, l, T.Counts{i, e, r, h, m}, f, xs, x} = c
  E.Canon{cap, o, l, T.Counts{i, e, r, Word.inc(64n, h), m}, f, xs, x}

def c_evict(-V: Data, c: E.Canonical<String, V>) -> E.Canonical<String, V>:
  E.Canon{cap, o, l, T.Counts{i, e, r, h, m}, f, xs, x} = c
  E.Canon{cap, o, l, T.Counts{i, Word.inc(64n, e), r, h, m}, f, xs, x}

def c_miss(-V: Data, c: E.Canonical<String, V>) -> E.Canonical<String, V>:
  E.Canon{cap, o, l, T.Counts{i, e, r, h, m}, f, xs, x} = c
  E.Canon{cap, o, l, T.Counts{i, e, r, h, Word.inc(64n, m)}, f, xs, x}

def c_purged(-V: Data, c: E.Canonical<String, V>) -> E.Canonical<String, V>:
  E.Canon{cap, o, l, m, f, xs, x} = c
  E.Canon{cap, Nil{}, l, T.zero_metrics(), f, Nil{}, Nil{}}

def find_cong(-V: Data, +s: S.Model<String, V>, +t: S.Model<String, V>, +related: E.states(~String, ~Lookup.string_same, V, s, t), +k: String) -> {S.find(~String, ~Lookup.string_same, V, Can.bindings(String, V, s), k) == S.find(~String, ~Lookup.string_same, V, Can.bindings(String, V, t), k) : Maybe<&2, T.Entry<String, V>>}:
  CS.lookup_agreement(V, s, t, related, k)

# Remove: full observation congruence (item, flag, inert metadata, state).
def remove_found_obs(-V: Data, +sc: Nat, +sb: List<&2, T.Entry<String, V>>, +so: List<&2, String>, +sl: T.Int64, +si: Word(64n), +se: Word(64n), +sr: Word(64n), +sh: Word(64n), +sm: Word(64n), +sf: Bool, +tc: Nat, +tb: List<&2, T.Entry<String, V>>, +to: List<&2, String>, +tl: T.Int64, +ti: Word(64n), +te: Word(64n), +tr: Word(64n), +th: Word(64n), +tm: Word(64n), +tf: Bool, +k: String, +related: E.states(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, T.Counts{si, se, sr, sh, sm}, sf}, S.Abstract{tc, tb, to, tl, T.Counts{ti, te, tr, th, tm}, tf}), found: Maybe<&2, T.Entry<String, V>>) -> E.observations(~String, ~Lookup.string_same, V, S.remove_decision(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, T.Counts{si, se, sr, sh, sm}, sf}, k, found), S.remove_decision(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, T.Counts{ti, te, tr, th, tm}, tf}, k, found)):
  match found:
    case None{}: (related, {==}, {==}, {==})
    case Some{+entry}:
      +states = Equal.trans(E.Canonical<String, V>, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, S.erase(~String, ~Lookup.string_same, V, sb, k), S.unlist(~String, ~Lookup.string_same, so, k), sl, T.Counts{si, se, Word.inc(64n, sr), sh, sm}, sf}), Can.c_drop(~String, ~Lookup.string_same, V, Can.c_removed(String, V, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, T.Counts{si, se, sr, sh, sm}, sf})), k), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, S.erase(~String, ~Lookup.string_same, V, tb, k), S.unlist(~String, ~Lookup.string_same, to, k), tl, T.Counts{ti, te, Word.inc(64n, tr), th, tm}, tf}), CS.drop_transform(V, sc, sb, so, sl, T.Counts{si, se, Word.inc(64n, sr), sh, sm}, sf, k), Equal.trans(E.Canonical<String, V>, Can.c_drop(~String, ~Lookup.string_same, V, Can.c_removed(String, V, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, T.Counts{si, se, sr, sh, sm}, sf})), k), Can.c_drop(~String, ~Lookup.string_same, V, Can.c_removed(String, V, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, T.Counts{ti, te, tr, th, tm}, tf})), k), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, S.erase(~String, ~Lookup.string_same, V, tb, k), S.unlist(~String, ~Lookup.string_same, to, k), tl, T.Counts{ti, te, Word.inc(64n, tr), th, tm}, tf}), Equal.cong(E.Canonical<String, V>, E.Canonical<String, V>, c => Can.c_drop(~String, ~Lookup.string_same, V, Can.c_removed(String, V, c), k), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, T.Counts{si, se, sr, sh, sm}, sf}), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, T.Counts{ti, te, tr, th, tm}, tf}), related), Equal.sym(E.Canonical<String, V>, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, S.erase(~String, ~Lookup.string_same, V, tb, k), S.unlist(~String, ~Lookup.string_same, to, k), tl, T.Counts{ti, te, Word.inc(64n, tr), th, tm}, tf}), Can.c_drop(~String, ~Lookup.string_same, V, Can.c_removed(String, V, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, T.Counts{ti, te, tr, th, tm}, tf})), k), CS.drop_transform(V, tc, tb, to, tl, T.Counts{ti, te, Word.inc(64n, tr), th, tm}, tf, k))))
      +cbs = Equal.cong(E.Canonical<String, V>, Bool, c => cb_of(V, c), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, T.Counts{si, se, sr, sh, sm}, sf}), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, T.Counts{ti, te, tr, th, tm}, tf}), related)
      (states, {==}, {==}, Equal.cong(Bool, List<&2, T.Event<String, V>>, f => S.callbacks(String, V, Con{entry, Nil{}}, f), sf, tf, cbs))

def remove_obs(-V: Data, s: S.Model<String, V>, t: S.Model<String, V>, +k: String, +related: E.states(~String, ~Lookup.string_same, V, s, t)) -> E.observations(~String, ~Lookup.string_same, V, S.remove(~String, ~Lookup.string_same, V, s, k), S.remove(~String, ~Lookup.string_same, V, t, k)):
  S.Abstract{+sc, +sb, +so, +sl, T.Counts{+si, +se, +sr, +sh, +sm}, +sf} = s
  S.Abstract{+tc, +tb, +to, +tl, T.Counts{+ti, +te, +tr, +th, +tm}, +tf} = t
  %find_cong(V, S.Abstract{sc, sb, so, sl, T.Counts{si, se, sr, sh, sm}, sf}, S.Abstract{tc, tb, to, tl, T.Counts{ti, te, tr, th, tm}, tf}, related, k) : E.observations(~String, ~Lookup.string_same, V, S.remove_decision(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, T.Counts{si, se, sr, sh, sm}, sf}, k, S.find(~String, ~Lookup.string_same, V, sb, k)), S.remove_decision(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, T.Counts{ti, te, tr, th, tm}, tf}, k, _))
  remove_found_obs(V, sc, sb, so, sl, si, se, sr, sh, sm, sf, tc, tb, to, tl, ti, te, tr, th, tm, tf, k, related, S.find(~String, ~Lookup.string_same, V, sb, k))

# Recency move (tracked hit).
def hit_cong(-V: Data, s: S.Model<String, V>, t: S.Model<String, V>, +k: String, +tracked: Bool, +related: E.states(~String, ~Lookup.string_same, V, s, t)) -> E.states(~String, ~Lookup.string_same, V, O.hit_state(~String, ~Lookup.string_same, V, s, k, tracked), O.hit_state(~String, ~Lookup.string_same, V, t, k, tracked)):
  S.Abstract{+sc, +sb, +so, +sl, T.Counts{+si, +se, +sr, +sh, +sm}, +sf} = s
  S.Abstract{+tc, +tb, +to, +tl, T.Counts{+ti, +te, +tr, +th, +tm}, +tf} = t
  match tracked:
    case False{}: related
    case True{}: Equal.trans(E.Canonical<String, V>, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, Can.moved(~String, ~Lookup.string_same, so, k), sl, T.Counts{si, se, sr, Word.inc(64n, sh), sm}, sf}), Can.c_move(~String, ~Lookup.string_same, V, c_hit(V, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, T.Counts{si, se, sr, sh, sm}, sf})), k), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, Can.moved(~String, ~Lookup.string_same, to, k), tl, T.Counts{ti, te, tr, Word.inc(64n, th), tm}, tf}), CS.move_transform(V, sc, sb, so, sl, T.Counts{si, se, sr, Word.inc(64n, sh), sm}, sf, k), Equal.trans(E.Canonical<String, V>, Can.c_move(~String, ~Lookup.string_same, V, c_hit(V, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, T.Counts{si, se, sr, sh, sm}, sf})), k), Can.c_move(~String, ~Lookup.string_same, V, c_hit(V, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, T.Counts{ti, te, tr, th, tm}, tf})), k), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, Can.moved(~String, ~Lookup.string_same, to, k), tl, T.Counts{ti, te, tr, Word.inc(64n, th), tm}, tf}), Equal.cong(E.Canonical<String, V>, E.Canonical<String, V>, c => Can.c_move(~String, ~Lookup.string_same, V, c_hit(V, c), k), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, T.Counts{si, se, sr, sh, sm}, sf}), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, T.Counts{ti, te, tr, th, tm}, tf}), related), Equal.sym(E.Canonical<String, V>, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, Can.moved(~String, ~Lookup.string_same, to, k), tl, T.Counts{ti, te, tr, Word.inc(64n, th), tm}, tf}), Can.c_move(~String, ~Lookup.string_same, V, c_hit(V, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, T.Counts{ti, te, tr, th, tm}, tf})), k), CS.move_transform(V, tc, tb, to, tl, T.Counts{ti, te, tr, Word.inc(64n, th), tm}, tf, k))))

# Refresh after the hit: the rebinding written with the new deadline.
def refreshed_cong(-V: Data, s: S.Model<String, V>, t: S.Model<String, V>, +k: String, +v: V, +d: T.Int64, +deadline: T.Int64, +related: E.states(~String, ~Lookup.string_same, V, s, t)) -> E.observations(~String, ~Lookup.string_same, V, Eff.refresh_deadline(~String, ~Lookup.string_same, V, O.hit_state(~String, ~Lookup.string_same, V, s, k, True{}), T.Item{k, v, d}, deadline), Eff.refresh_deadline(~String, ~Lookup.string_same, V, O.hit_state(~String, ~Lookup.string_same, V, t, k, True{}), T.Item{k, v, d}, deadline)):
  S.Abstract{+sc, +sb, +so, +sl, T.Counts{+si, +se, +sr, +sh, +sm}, +sf} = s
  S.Abstract{+tc, +tb, +to, +tl, T.Counts{+ti, +te, +tr, +th, +tm}, +tf} = t
  (Equal.trans(E.Canonical<String, V>, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, Con{T.Item{k, v, deadline}, S.erase(~String, ~Lookup.string_same, V, sb, k)}, Can.moved(~String, ~Lookup.string_same, so, k), sl, T.Counts{si, se, sr, Word.inc(64n, sh), sm}, sf}), Can.c_write(~String, ~Lookup.string_same, V, c_hit(V, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, T.Counts{si, se, sr, sh, sm}, sf})), k, v, deadline), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, Con{T.Item{k, v, deadline}, S.erase(~String, ~Lookup.string_same, V, tb, k)}, Can.moved(~String, ~Lookup.string_same, to, k), tl, T.Counts{ti, te, tr, Word.inc(64n, th), tm}, tf}), CS.write_transform(V, sc, sb, so, sl, T.Counts{si, se, sr, Word.inc(64n, sh), sm}, sf, k, v, deadline), Equal.trans(E.Canonical<String, V>, Can.c_write(~String, ~Lookup.string_same, V, c_hit(V, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, T.Counts{si, se, sr, sh, sm}, sf})), k, v, deadline), Can.c_write(~String, ~Lookup.string_same, V, c_hit(V, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, T.Counts{ti, te, tr, th, tm}, tf})), k, v, deadline), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, Con{T.Item{k, v, deadline}, S.erase(~String, ~Lookup.string_same, V, tb, k)}, Can.moved(~String, ~Lookup.string_same, to, k), tl, T.Counts{ti, te, tr, Word.inc(64n, th), tm}, tf}), Equal.cong(E.Canonical<String, V>, E.Canonical<String, V>, c => Can.c_write(~String, ~Lookup.string_same, V, c_hit(V, c), k, v, deadline), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, T.Counts{si, se, sr, sh, sm}, sf}), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, T.Counts{ti, te, tr, th, tm}, tf}), related), Equal.sym(E.Canonical<String, V>, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, Con{T.Item{k, v, deadline}, S.erase(~String, ~Lookup.string_same, V, tb, k)}, Can.moved(~String, ~Lookup.string_same, to, k), tl, T.Counts{ti, te, tr, Word.inc(64n, th), tm}, tf}), Can.c_write(~String, ~Lookup.string_same, V, c_hit(V, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, T.Counts{ti, te, tr, th, tm}, tf})), k, v, deadline), CS.write_transform(V, tc, tb, to, tl, T.Counts{ti, te, tr, Word.inc(64n, th), tm}, tf, k, v, deadline)))), {==}, {==}, {==})

# Capacity eviction of a bound entry before an Add.
def evicted_cong(-V: Data, s: S.Model<String, V>, t: S.Model<String, V>, +k: String, +entry: T.Entry<String, V>, +related: E.states(~String, ~Lookup.string_same, V, s, t)) -> E.states(~String, ~Lookup.string_same, V, O.evicted_state(~String, ~Lookup.string_same, V, s, k), O.evicted_state(~String, ~Lookup.string_same, V, t, k)):
  S.Abstract{+sc, +sb, +so, +sl, T.Counts{+si, +se, +sr, +sh, +sm}, +sf} = s
  S.Abstract{+tc, +tb, +to, +tl, T.Counts{+ti, +te, +tr, +th, +tm}, +tf} = t
  Equal.trans(E.Canonical<String, V>, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, S.erase(~String, ~Lookup.string_same, V, sb, k), S.unlist(~String, ~Lookup.string_same, so, k), sl, T.Counts{si, Word.inc(64n, se), sr, sh, sm}, sf}), Can.c_drop(~String, ~Lookup.string_same, V, c_evict(V, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, T.Counts{si, se, sr, sh, sm}, sf})), k), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, S.erase(~String, ~Lookup.string_same, V, tb, k), S.unlist(~String, ~Lookup.string_same, to, k), tl, T.Counts{ti, Word.inc(64n, te), tr, th, tm}, tf}), CS.drop_transform(V, sc, sb, so, sl, T.Counts{si, Word.inc(64n, se), sr, sh, sm}, sf, k), Equal.trans(E.Canonical<String, V>, Can.c_drop(~String, ~Lookup.string_same, V, c_evict(V, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, T.Counts{si, se, sr, sh, sm}, sf})), k), Can.c_drop(~String, ~Lookup.string_same, V, c_evict(V, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, T.Counts{ti, te, tr, th, tm}, tf})), k), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, S.erase(~String, ~Lookup.string_same, V, tb, k), S.unlist(~String, ~Lookup.string_same, to, k), tl, T.Counts{ti, Word.inc(64n, te), tr, th, tm}, tf}), Equal.cong(E.Canonical<String, V>, E.Canonical<String, V>, c => Can.c_drop(~String, ~Lookup.string_same, V, c_evict(V, c), k), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, T.Counts{si, se, sr, sh, sm}, sf}), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, T.Counts{ti, te, tr, th, tm}, tf}), related), Equal.sym(E.Canonical<String, V>, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, S.erase(~String, ~Lookup.string_same, V, tb, k), S.unlist(~String, ~Lookup.string_same, to, k), tl, T.Counts{ti, Word.inc(64n, te), tr, th, tm}, tf}), Can.c_drop(~String, ~Lookup.string_same, V, c_evict(V, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, T.Counts{ti, te, tr, th, tm}, tf})), k), CS.drop_transform(V, tc, tb, to, tl, T.Counts{ti, Word.inc(64n, te), tr, th, tm}, tf, k))))

def miss_cong(-V: Data, s: S.Model<String, V>, t: S.Model<String, V>, +related: E.states(~String, ~Lookup.string_same, V, s, t)) -> E.observations(~String, ~Lookup.string_same, V, S.missing_get(String, V, s), S.missing_get(String, V, t)):
  S.Abstract{+sc, +sb, +so, +sl, T.Counts{+si, +se, +sr, +sh, +sm}, +sf} = s
  S.Abstract{+tc, +tb, +to, +tl, T.Counts{+ti, +te, +tr, +th, +tm}, +tf} = t
  (Equal.cong(E.Canonical<String, V>, E.Canonical<String, V>, c => c_miss(V, c), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, T.Counts{si, se, sr, sh, sm}, sf}), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, T.Counts{ti, te, tr, th, tm}, tf}), related), {==}, {==}, {==})

def purged_cong(-V: Data, s: S.Model<String, V>, t: S.Model<String, V>, +related: E.states(~String, ~Lookup.string_same, V, s, t)) -> E.states(~String, ~Lookup.string_same, V, S.purged(String, V, s), S.purged(String, V, t)):
  S.Abstract{+sc, +sb, +so, +sl, +sm, +sf} = s
  S.Abstract{+tc, +tb, +to, +tl, +tm, +tf} = t
  Equal.cong(E.Canonical<String, V>, E.Canonical<String, V>, c => c_purged(V, c), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}), related)

# ---------------------------------------------------------------------------
# Get/Peek/Contains (and the captured GetOldest read).
def decide_cong(-V: Data, +s: S.Model<String, V>, +t: S.Model<String, V>, +k: String, +entry: T.Entry<String, V>, +tracked: Bool, +related: E.states(~String, ~Lookup.string_same, V, s, t), expired: Bool) -> E.observations(~String, ~Lookup.string_same, V, O.read_decide(~String, ~Lookup.string_same, V, s, k, entry, tracked, expired), O.read_decide(~String, ~Lookup.string_same, V, t, k, entry, tracked, expired)):
  match expired:
    case False{}: (hit_cong(V, s, t, k, tracked, related), {==}, {==}, {==})
    case True{}: Ext.expired_result(~String, ~Lookup.string_same, V, S.remove(~String, ~Lookup.string_same, V, s, k), S.remove(~String, ~Lookup.string_same, V, t, k), tracked, remove_obs(V, s, t, k, related))

def read_life_cong(-V: Data, +s: S.Model<String, V>, +t: S.Model<String, V>, +k: String, +o: String, +v: V, +bits: Word(64n), +tracked: Bool, +related: E.states(~String, ~Lookup.string_same, V, s, t), immortal: Bool, events: List<&2, Clock.Event>) -> eres(V, Eff.read_lifetime(~String, ~Lookup.string_same, V, s, k, T.Item{o, v, T.I64{bits}}, tracked, events, immortal), Eff.read_lifetime(~String, ~Lookup.string_same, V, t, k, T.Item{o, v, T.I64{bits}}, tracked, events, immortal)):
  match immortal:
    case True{}: (decide_cong(V, s, t, k, T.Item{o, v, T.I64{bits}}, tracked, related, False{}), {==}, {==})
    case False{}:
      match events:
        case Nil{}: (related, {==}, {==}, {==})
        case Con{Clock.InvalidSample{reason}, tail}: (related, {==}, {==}, {==})
        case Con{Clock.ProviderException{reason}, tail}: (related, {==}, {==}, {==})
        case Con{Clock.Sample{+now}, tail}: (decide_cong(V, s, t, k, T.Item{o, v, T.I64{bits}}, tracked, related, N.expired(T.I64{bits}, now)), {==}, {==})

def read_found_cong(-V: Data, +s: S.Model<String, V>, +t: S.Model<String, V>, +k: String, +tracked: Bool, +events: List<&2, Clock.Event>, +related: E.states(~String, ~Lookup.string_same, V, s, t), found: Maybe<&2, T.Entry<String, V>>) -> eres(V, Eff.read_found(~String, ~Lookup.string_same, V, s, k, tracked, events, found), Eff.read_found(~String, ~Lookup.string_same, V, t, k, tracked, events, found)):
  match found:
    case None{}: ((Ext.count_miss(~String, ~Lookup.string_same, V, s, t, tracked, related), {==}, {==}, {==}), {==}, {==})
    case Some{T.Item{+o, +v, T.I64{+bits}}}: read_life_cong(V, s, t, k, o, v, bits, tracked, related, N.zero(bits), events)

def read_cong(-V: Data, s: S.Model<String, V>, t: S.Model<String, V>, +k: String, +tracked: Bool, +events: List<&2, Clock.Event>, +related: E.states(~String, ~Lookup.string_same, V, s, t)) -> eres(V, Eff.read(~String, ~Lookup.string_same, V, s, k, tracked, events), Eff.read(~String, ~Lookup.string_same, V, t, k, tracked, events)):
  S.Abstract{+sc, +sb, +so, +sl, +sm, +sf} = s
  S.Abstract{+tc, +tb, +to, +tl, +tm, +tf} = t
  %find_cong(V, S.Abstract{sc, sb, so, sl, sm, sf}, S.Abstract{tc, tb, to, tl, tm, tf}, related, k) : eres(V, Eff.read_found(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}, k, tracked, events, S.find(~String, ~Lookup.string_same, V, sb, k)), Eff.read_found(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}, k, tracked, events, _))
  read_found_cong(V, S.Abstract{sc, sb, so, sl, sm, sf}, S.Abstract{tc, tb, to, tl, tm, tf}, k, tracked, events, related, S.find(~String, ~Lookup.string_same, V, sb, k))

# GetAndRefresh.
def refresh_life_cong(-V: Data, +s: S.Model<String, V>, +t: S.Model<String, V>, +key: String, +value: V, +deadline: T.Int64, +bits: Word(64n), +related: E.states(~String, ~Lookup.string_same, V, s, t), immortal: Bool, events: List<&2, Clock.Event>) -> eres(V, Eff.refresh_lifetime(~String, ~Lookup.string_same, V, O.hit_state(~String, ~Lookup.string_same, V, s, key, True{}), T.Item{key, value, deadline}, T.I64{bits}, events, immortal), Eff.refresh_lifetime(~String, ~Lookup.string_same, V, O.hit_state(~String, ~Lookup.string_same, V, t, key, True{}), T.Item{key, value, deadline}, T.I64{bits}, events, immortal)):
  match immortal:
    case True{}: (refreshed_cong(V, s, t, key, value, deadline, T.I64{Word.zero(64n)}, related), {==}, {==})
    case False{}:
      match events:
        case Nil{}: (hit_cong(V, s, t, key, True{}, related), {==}, {==}, {==})
        case Con{Clock.InvalidSample{reason}, tail}: (hit_cong(V, s, t, key, True{}, related), {==}, {==}, {==})
        case Con{Clock.ProviderException{reason}, tail}: (hit_cong(V, s, t, key, True{}, related), {==}, {==}, {==})
        case Con{Clock.Sample{+now}, tail}: (refreshed_cong(V, s, t, key, value, deadline, N.deadline(now, T.I64{bits}), related), {==}, {==})

def refresh_found_cong(-V: Data, +s: S.Model<String, V>, +t: S.Model<String, V>, +ns: T.Int64, +events: List<&2, Clock.Event>, +related: E.states(~String, ~Lookup.string_same, V, s, t), found: Maybe<&2, T.Entry<String, V>>) -> eres(V, Eff.refresh_found(~String, ~Lookup.string_same, V, s, ns, events, found), Eff.refresh_found(~String, ~Lookup.string_same, V, t, ns, events, found)):
  T.I64{+bits} = ns
  match found:
    case None{}: (miss_cong(V, s, t, related), {==}, {==})
    case Some{T.Item{+key, +value, +deadline}}:
      refresh_life_cong(V, s, t, key, value, deadline, bits, related, N.zero(bits), events)

def refresh_cong(-V: Data, s: S.Model<String, V>, t: S.Model<String, V>, +k: String, +ns: T.Int64, +events: List<&2, Clock.Event>, +related: E.states(~String, ~Lookup.string_same, V, s, t)) -> eres(V, Eff.refresh(~String, ~Lookup.string_same, V, s, k, ns, events), Eff.refresh(~String, ~Lookup.string_same, V, t, k, ns, events)):
  S.Abstract{+sc, +sb, +so, +sl, +sm, +sf} = s
  S.Abstract{+tc, +tb, +to, +tl, +tm, +tf} = t
  %find_cong(V, S.Abstract{sc, sb, so, sl, sm, sf}, S.Abstract{tc, tb, to, tl, tm, tf}, related, k) : eres(V, Eff.refresh_found(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}, ns, events, S.find(~String, ~Lookup.string_same, V, sb, k)), Eff.refresh_found(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}, ns, events, _))
  refresh_found_cong(V, S.Abstract{sc, sb, so, sl, sm, sf}, S.Abstract{tc, tb, to, tl, tm, tf}, ns, events, related, S.find(~String, ~Lookup.string_same, V, sb, k))

# Keys/Values/PurgeExpired: the same oldest-prefix decision list applies to
# related models; its removals keep them related.
def remove_entries_cong(-V: Data, removed: List<&2, T.Entry<String, V>>, +s: S.Model<String, V>, +t: S.Model<String, V>, +related: E.states(~String, ~Lookup.string_same, V, s, t)) -> E.states(~String, ~Lookup.string_same, V, O.remove_entries(~String, ~Lookup.string_same, V, removed, s), O.remove_entries(~String, ~Lookup.string_same, V, removed, t)):
  match removed:
    case Nil{}: related
    case Con{T.Item{+k, v, d}, +rest}: remove_entries_cong(V, rest, O.observed_state(String, V, S.remove(~String, ~Lookup.string_same, V, s, k)), O.observed_state(String, V, S.remove(~String, ~Lookup.string_same, V, t, k)), CR.remove_congruence(V, s, t, k, related))

def apply_prefix_cong(-V: Data, +s: S.Model<String, V>, +t: S.Model<String, V>, +related: E.states(~String, ~Lookup.string_same, V, s, t), result: A.Prefix<String, V>) -> eres(V, A.apply_prefix(~String, ~Lookup.string_same, V, s, result), A.apply_prefix(~String, ~Lookup.string_same, V, t, result)):
  match result:
    case A.Finished{+removed, retained, events, requests}: ((remove_entries_cong(V, removed, s, t, related), {==}, {==}, {==}), {==}, {==})
    case A.Failed{error, +removed, retained, events, requests}: (remove_entries_cong(V, removed, s, t, related), {==}, {==}, {==})

def aggregate_cong(-V: Data, +s: S.Model<String, V>, +t: S.Model<String, V>, +events: List<&2, Clock.Event>, +related: E.states(~String, ~Lookup.string_same, V, s, t)) -> eres(V, A.purge_expired(~String, ~Lookup.string_same, V, s, events), A.purge_expired(~String, ~Lookup.string_same, V, t, events)):
  %CS.entries_agreement(V, s, t, related) : eres(V, A.apply_prefix(~String, ~Lookup.string_same, V, s, A.prefix(String, V, O.all_entries(~String, ~Lookup.string_same, V, s), events)), A.apply_prefix(~String, ~Lookup.string_same, V, t, A.prefix(String, V, _, events)))
  apply_prefix_cong(V, s, t, related, A.prefix(String, V, O.all_entries(~String, ~Lookup.string_same, V, s), events))

# ---------------------------------------------------------------------------
# Add/AddWithLifetime: related preparation, then related writes.
def prel(-V: Data, a: Eff.PreparedAdd<String, V>, b: Eff.PreparedAdd<String, V>) -> Type:
  match a b:
    case Eff.Prepared{sa, ka, ea} Eff.Prepared{sb, kb, eb}: E.states(~String, ~Lookup.string_same, V, sa, sb) & {ka == kb : String} & {ea == eb : Bool}

def evict_found_cong(-V: Data, s: S.Model<String, V>, t: S.Model<String, V>, +k: String, +related: E.states(~String, ~Lookup.string_same, V, s, t), found: Maybe<&2, T.Entry<String, V>>) -> prel(V, Eff.evict_found(~String, ~Lookup.string_same, V, s, k, found), Eff.evict_found(~String, ~Lookup.string_same, V, t, k, found)):
  S.Abstract{+sc, +sb, +so, +sl, T.Counts{+si, +se, +sr, +sh, +sm}, +sf} = s
  S.Abstract{+tc, +tb, +to, +tl, T.Counts{+ti, +te, +tr, +th, +tm}, +tf} = t
  match found:
    case None{}: (related, {==}, {==})
    case Some{T.Item{+ok, +ov, +od}}: (evicted_cong(V, S.Abstract{sc, sb, so, sl, T.Counts{si, se, sr, sh, sm}, sf}, S.Abstract{tc, tb, to, tl, T.Counts{ti, te, tr, th, tm}, tf}, ok, T.Item{ok, ov, od}, related), {==}, {==})

def evict_first_cong(-V: Data, +sc: Nat, +sb: List<&2, T.Entry<String, V>>, +so: List<&2, String>, +sl: T.Int64, +sm: T.Metrics, +sf: Bool, +tc: Nat, +tb: List<&2, T.Entry<String, V>>, +to: List<&2, String>, +tl: T.Int64, +tm: T.Metrics, +tf: Bool, +k: String, +related: E.states(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}, S.Abstract{tc, tb, to, tl, tm, tf}), order: List<&2, String>) -> prel(V, Eff.evict_first(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}, k, sb, order), Eff.evict_first(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}, k, tb, order)):
  match order:
    case Nil{}: (related, {==}, {==})
    case Con{+old, tail}:
      %find_cong(V, S.Abstract{sc, sb, so, sl, sm, sf}, S.Abstract{tc, tb, to, tl, tm, tf}, related, old) : prel(V, Eff.evict_found(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}, k, S.find(~String, ~Lookup.string_same, V, sb, old)), Eff.evict_found(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}, k, _))
      evict_found_cong(V, S.Abstract{sc, sb, so, sl, sm, sf}, S.Abstract{tc, tb, to, tl, tm, tf}, k, related, S.find(~String, ~Lookup.string_same, V, sb, old))

def room_cong(-V: Data, +sc: Nat, +sb: List<&2, T.Entry<String, V>>, +so: List<&2, String>, +sl: T.Int64, +sm: T.Metrics, +sf: Bool, +tc: Nat, +tb: List<&2, T.Entry<String, V>>, +to: List<&2, String>, +tl: T.Int64, +tm: T.Metrics, +tf: Bool, +k: String, +related: E.states(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}, S.Abstract{tc, tb, to, tl, tm, tf}), full: Bool) -> prel(V, Eff.room(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}, k, sb, so, full), Eff.room(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}, k, tb, so, full)):
  match full:
    case False{}: (related, {==}, {==})
    case True{}: evict_first_cong(V, sc, sb, so, sl, sm, sf, tc, tb, to, tl, tm, tf, k, related, so)

def prepare_found_cong(-V: Data, +sc: Nat, +sb: List<&2, T.Entry<String, V>>, +so: List<&2, String>, +sl: T.Int64, +sm: T.Metrics, +sf: Bool, +tc: Nat, +tb: List<&2, T.Entry<String, V>>, +to: List<&2, String>, +tl: T.Int64, +tm: T.Metrics, +tf: Bool, +k: String, +related: E.states(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}, S.Abstract{tc, tb, to, tl, tm, tf}), found: Maybe<&2, T.Entry<String, V>>) -> prel(V, Eff.prepare_found(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}, k, found), Eff.prepare_found(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}, k, found)):
  match found:
    case Some{T.Item{o, ov, od}}: (related, {==}, {==})
    case None{}:
      +orders = Equal.cong(E.Canonical<String, V>, List<&2, String>, c => order_of(V, c), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}), related)
      +caps = Equal.cong(E.Canonical<String, V>, Nat, c => cap_of(V, c), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}), related)
      %orders : prel(V, Eff.room(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}, k, sb, so, Nat.is_ge(List.length(&2, String, so), sc)), Eff.room(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}, k, tb, _, Nat.is_ge(List.length(&2, String, _), tc)))
      %caps : prel(V, Eff.room(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}, k, sb, so, Nat.is_ge(List.length(&2, String, so), sc)), Eff.room(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}, k, tb, so, Nat.is_ge(List.length(&2, String, so), _)))
      room_cong(V, sc, sb, so, sl, sm, sf, tc, tb, to, tl, tm, tf, k, related, Nat.is_ge(List.length(&2, String, so), sc))

def prepare_cong(-V: Data, s: S.Model<String, V>, t: S.Model<String, V>, +k: String, +related: E.states(~String, ~Lookup.string_same, V, s, t)) -> prel(V, Eff.prepare_add(~String, ~Lookup.string_same, V, s, k), Eff.prepare_add(~String, ~Lookup.string_same, V, t, k)):
  S.Abstract{+sc, +sb, +so, +sl, +sm, +sf} = s
  S.Abstract{+tc, +tb, +to, +tl, +tm, +tf} = t
  %find_cong(V, S.Abstract{sc, sb, so, sl, sm, sf}, S.Abstract{tc, tb, to, tl, tm, tf}, related, k) : prel(V, Eff.prepare_found(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}, k, S.find(~String, ~Lookup.string_same, V, sb, k)), Eff.prepare_found(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}, k, _))
  prepare_found_cong(V, sc, sb, so, sl, sm, sf, tc, tb, to, tl, tm, tf, k, related, S.find(~String, ~Lookup.string_same, V, sb, k))

def add_life_known(-V: Data, +sa: S.Model<String, V>, +sb: S.Model<String, V>, +ka: String, +ea: Bool, +value: V, +ns: T.Int64, +st: E.states(~String, ~Lookup.string_same, V, sa, sb), immortal: Bool, events: List<&2, Clock.Event>) -> eres(V, Eff.add_lifetime(~String, ~Lookup.string_same, V, Eff.Prepared{sa, ka, ea}, value, ns, events, immortal), Eff.add_lifetime(~String, ~Lookup.string_same, V, Eff.Prepared{sb, ka, ea}, value, ns, events, immortal)):
  match immortal:
    case True{}: (Write.observation(V, sa, sb, ka, value, T.I64{Word.zero(64n)}, ea, Nil{}, st), {==}, {==})
    case False{}:
      match events:
        case Nil{}: (st, {==}, {==}, {==})
        case Con{Clock.InvalidSample{reason}, tail}: (st, {==}, {==}, {==})
        case Con{Clock.ProviderException{reason}, tail}: (st, {==}, {==}, {==})
        case Con{Clock.Sample{+now}, tail}: (Write.observation(V, sa, sb, ka, value, N.deadline(now, ns), ea, Nil{}, st), {==}, {==})

def add_life_cong(-V: Data, a: Eff.PreparedAdd<String, V>, b: Eff.PreparedAdd<String, V>, +value: V, +ns: T.Int64, related: prel(V, a, b), +immortal: Bool, +events: List<&2, Clock.Event>) -> eres(V, Eff.add_lifetime(~String, ~Lookup.string_same, V, a, value, ns, events, immortal), Eff.add_lifetime(~String, ~Lookup.string_same, V, b, value, ns, events, immortal)):
  Eff.Prepared{+sa, +ka, +ea} = a
  Eff.Prepared{+sb, +kb, +eb} = b
  (+st, +keys, flags) = related
  %keys : eres(V, Eff.add_lifetime(~String, ~Lookup.string_same, V, Eff.Prepared{sa, ka, ea}, value, ns, events, immortal), Eff.add_lifetime(~String, ~Lookup.string_same, V, Eff.Prepared{sb, _, eb}, value, ns, events, immortal))
  %flags : eres(V, Eff.add_lifetime(~String, ~Lookup.string_same, V, Eff.Prepared{sa, ka, ea}, value, ns, events, immortal), Eff.add_lifetime(~String, ~Lookup.string_same, V, Eff.Prepared{sb, ka, _}, value, ns, events, immortal))
  add_life_known(V, sa, sb, ka, ea, value, ns, st, immortal, events)

def add_cong(-V: Data, +s: S.Model<String, V>, +t: S.Model<String, V>, +k: String, +value: V, ns: T.Int64, events: List<&2, Clock.Event>, +related: E.states(~String, ~Lookup.string_same, V, s, t)) -> eres(V, Eff.add_with_lifetime(~String, ~Lookup.string_same, V, s, k, value, ns, events), Eff.add_with_lifetime(~String, ~Lookup.string_same, V, t, k, value, ns, events)):
  T.I64{+bits} = ns
  add_life_cong(V, Eff.prepare_add(~String, ~Lookup.string_same, V, s, k), Eff.prepare_add(~String, ~Lookup.string_same, V, t, k), value, T.I64{bits}, prepare_cong(V, s, t, k, related), N.zero(bits), events)

# ---------------------------------------------------------------------------
# GetOldest and RemoveOldest act on the (equal) recency head.
def oldest_binding_cong(-V: Data, +s: S.Model<String, V>, +t: S.Model<String, V>, +zero_key: String, +zero_value: V, +events: List<&2, Clock.Event>, +related: E.states(~String, ~Lookup.string_same, V, s, t), found: Maybe<&2, T.Entry<String, V>>) -> sres(V, PC.oldest_binding(~String, ~Lookup.string_same, V, s, zero_key, zero_value, events, found), PC.oldest_binding(~String, ~Lookup.string_same, V, t, zero_key, zero_value, events, found)):
  match found:
    case None{}: (related, {==}, {==}, {==})
    case Some{T.Item{+original, v, d}}: effect_cong(V, zero_key, zero_value, PC.CapturedOldest{original}, Eff.read(~String, ~Lookup.string_same, V, s, original, False{}, events), Eff.read(~String, ~Lookup.string_same, V, t, original, False{}, events), read_cong(V, s, t, original, False{}, events, related))

def oldest_order_cong(-V: Data, +sc: Nat, +sb: List<&2, T.Entry<String, V>>, +so: List<&2, String>, +sl: T.Int64, +sm: T.Metrics, +sf: Bool, +tc: Nat, +tb: List<&2, T.Entry<String, V>>, +to: List<&2, String>, +tl: T.Int64, +tm: T.Metrics, +tf: Bool, +zero_key: String, +zero_value: V, +events: List<&2, Clock.Event>, +related: E.states(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}, S.Abstract{tc, tb, to, tl, tm, tf}), order: List<&2, String>) -> sres(V, PC.oldest_order(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}, sb, order, zero_key, zero_value, events), PC.oldest_order(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}, tb, order, zero_key, zero_value, events)):
  match order:
    case Nil{}: (related, {==}, {==}, {==})
    case Con{+first, tail}:
      %find_cong(V, S.Abstract{sc, sb, so, sl, sm, sf}, S.Abstract{tc, tb, to, tl, tm, tf}, related, first) : sres(V, PC.oldest_binding(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}, zero_key, zero_value, events, S.find(~String, ~Lookup.string_same, V, sb, first)), PC.oldest_binding(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}, zero_key, zero_value, events, _))
      oldest_binding_cong(V, S.Abstract{sc, sb, so, sl, sm, sf}, S.Abstract{tc, tb, to, tl, tm, tf}, zero_key, zero_value, events, related, S.find(~String, ~Lookup.string_same, V, sb, first))

def oldest_cong(-V: Data, s: S.Model<String, V>, t: S.Model<String, V>, +zero_key: String, +zero_value: V, +events: List<&2, Clock.Event>, +related: E.states(~String, ~Lookup.string_same, V, s, t)) -> sres(V, PC.oldest(~String, ~Lookup.string_same, V, s, zero_key, zero_value, events), PC.oldest(~String, ~Lookup.string_same, V, t, zero_key, zero_value, events)):
  S.Abstract{+sc, +sb, +so, +sl, +sm, +sf} = s
  S.Abstract{+tc, +tb, +to, +tl, +tm, +tf} = t
  %Equal.cong(E.Canonical<String, V>, List<&2, String>, c => order_of(V, c), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}), related) : sres(V, PC.oldest_order(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}, sb, so, zero_key, zero_value, events), PC.oldest_order(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}, tb, _, zero_key, zero_value, events))
  oldest_order_cong(V, sc, sb, so, sl, sm, sf, tc, tb, to, tl, tm, tf, zero_key, zero_value, events, related, so)

def oldest_remove_cong(-V: Data, +s: S.Model<String, V>, +t: S.Model<String, V>, +related: E.states(~String, ~Lookup.string_same, V, s, t), order: List<&2, String>) -> E.observations(~String, ~Lookup.string_same, V, O.oldest_remove(~String, ~Lookup.string_same, V, s, order), O.oldest_remove(~String, ~Lookup.string_same, V, t, order)):
  match order:
    case Nil{}: (related, {==}, {==}, {==})
    case Con{+k, tail}: remove_obs(V, s, t, k, related)

def remove_oldest_obs(-V: Data, s: S.Model<String, V>, t: S.Model<String, V>, +related: E.states(~String, ~Lookup.string_same, V, s, t)) -> E.observations(~String, ~Lookup.string_same, V, O.remove_oldest(~String, ~Lookup.string_same, V, s), O.remove_oldest(~String, ~Lookup.string_same, V, t)):
  S.Abstract{+sc, +sb, +so, +sl, +sm, +sf} = s
  S.Abstract{+tc, +tb, +to, +tl, +tm, +tf} = t
  %Equal.cong(E.Canonical<String, V>, List<&2, String>, c => order_of(V, c), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}), related) : E.observations(~String, ~Lookup.string_same, V, O.oldest_remove(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}, so), O.oldest_remove(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}, _))
  oldest_remove_cong(V, S.Abstract{sc, sb, so, sl, sm, sf}, S.Abstract{tc, tb, to, tl, tm, tf}, related, so)

# ---------------------------------------------------------------------------
# Configuration, counters and diagnostics.
def metrics_cong(-V: Data, s: S.Model<String, V>, t: S.Model<String, V>, +events: List<&2, Clock.Event>, +related: E.states(~String, ~Lookup.string_same, V, s, t)) -> sres(V, PC.metrics(String, V, s, events), PC.metrics(String, V, t, events)):
  S.Abstract{+sc, +sb, +so, +sl, +sm, +sf} = s
  S.Abstract{+tc, +tb, +to, +tl, +tm, +tf} = t
  (related, Equal.cong(T.Metrics, PC.Reply<String, V>, m => PC.Counters{m}, sm, tm, Equal.cong(E.Canonical<String, V>, T.Metrics, c => Ext.counts_of(String, V, c), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}), related)), {==}, {==})

def reset_cong(-V: Data, s: S.Model<String, V>, t: S.Model<String, V>, +events: List<&2, Clock.Event>, +related: E.states(~String, ~Lookup.string_same, V, s, t)) -> sres(V, PC.reset(String, V, s, events), PC.reset(String, V, t, events)):
  S.Abstract{+sc, +sb, +so, +sl, +sm, +sf} = s
  S.Abstract{+tc, +tb, +to, +tl, +tm, +tf} = t
  (Equal.cong(E.Canonical<String, V>, E.Canonical<String, V>, c => Ext.with_counts(String, V, c, T.zero_metrics()), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}), related), Equal.cong(T.Metrics, PC.Reply<String, V>, m => PC.Counters{m}, sm, tm, Equal.cong(E.Canonical<String, V>, T.Metrics, c => Ext.counts_of(String, V, c), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}), related)), {==}, {==})

def diagnostics_cong(-V: Data, s: S.Model<String, V>, t: S.Model<String, V>, +events: List<&2, Clock.Event>, +related: E.states(~String, ~Lookup.string_same, V, s, t)) -> sres(V, PC.diagnostics(~String, ~Lookup.string_same, V, s, events), PC.diagnostics(~String, ~Lookup.string_same, V, t, events)):
  S.Abstract{+sc, +sb, +so, +sl, +sm, +sf} = s
  S.Abstract{+tc, +tb, +to, +tl, +tm, +tf} = t
  +entries = CS.entries_agreement(V, S.Abstract{sc, sb, so, sl, sm, sf}, S.Abstract{tc, tb, to, tl, tm, tf}, related)
  +orders = Equal.cong(E.Canonical<String, V>, List<&2, String>, c => order_of(V, c), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}), related)
  +caps = Equal.cong(E.Canonical<String, V>, Nat, c => cap_of(V, c), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}), related)
  +counts = Equal.cong(E.Canonical<String, V>, T.Metrics, c => Ext.counts_of(String, V, c), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}), related)
  %entries : sres(V, PC.Returned{S.Abstract{sc, sb, so, sl, sm, sf}, PC.Storage{List.length(&2, T.Entry<String, V>, O.all_entries(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf})), List.length(&2, String, so), sc, sm}, events, 0n}, PC.Returned{S.Abstract{tc, tb, to, tl, tm, tf}, PC.Storage{List.length(&2, T.Entry<String, V>, _), List.length(&2, String, to), tc, tm}, events, 0n})
  %orders : sres(V, PC.Returned{S.Abstract{sc, sb, so, sl, sm, sf}, PC.Storage{List.length(&2, T.Entry<String, V>, O.all_entries(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf})), List.length(&2, String, so), sc, sm}, events, 0n}, PC.Returned{S.Abstract{tc, tb, to, tl, tm, tf}, PC.Storage{List.length(&2, T.Entry<String, V>, O.all_entries(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf})), List.length(&2, String, _), tc, tm}, events, 0n})
  %caps : sres(V, PC.Returned{S.Abstract{sc, sb, so, sl, sm, sf}, PC.Storage{List.length(&2, T.Entry<String, V>, O.all_entries(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf})), List.length(&2, String, so), sc, sm}, events, 0n}, PC.Returned{S.Abstract{tc, tb, to, tl, tm, tf}, PC.Storage{List.length(&2, T.Entry<String, V>, O.all_entries(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf})), List.length(&2, String, so), _, tm}, events, 0n})
  %counts : sres(V, PC.Returned{S.Abstract{sc, sb, so, sl, sm, sf}, PC.Storage{List.length(&2, T.Entry<String, V>, O.all_entries(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf})), List.length(&2, String, so), sc, sm}, events, 0n}, PC.Returned{S.Abstract{tc, tb, to, tl, tm, tf}, PC.Storage{List.length(&2, T.Entry<String, V>, O.all_entries(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf})), List.length(&2, String, so), sc, _}, events, 0n})
  (related, {==}, {==}, {==})

def add_plain_cong(-V: Data, s: S.Model<String, V>, t: S.Model<String, V>, +k: String, +value: V, +events: List<&2, Clock.Event>, +related: E.states(~String, ~Lookup.string_same, V, s, t)) -> eres(V, Eff.add(~String, ~Lookup.string_same, V, s, k, value, events), Eff.add(~String, ~Lookup.string_same, V, t, k, value, events)):
  S.Abstract{+sc, +sb, +so, +sl, +sm, +sf} = s
  S.Abstract{+tc, +tb, +to, +tl, +tm, +tf} = t
  %Equal.cong(E.Canonical<String, V>, T.Int64, c => life_of(V, c), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}), related) : eres(V, Eff.add_with_lifetime(~String, ~Lookup.string_same, V, S.Abstract{sc, sb, so, sl, sm, sf}, k, value, sl, events), Eff.add_with_lifetime(~String, ~Lookup.string_same, V, S.Abstract{tc, tb, to, tl, tm, tf}, k, value, _, events))
  add_cong(V, S.Abstract{sc, sb, so, sl, sm, sf}, S.Abstract{tc, tb, to, tl, tm, tf}, k, value, sl, events, related)

# The whole independent public semantics respects the canonical relation.
def execute_cong(-V: Data, +zero_key: String, +zero_value: V, +s: S.Model<String, V>, +t: S.Model<String, V>, +events: List<&2, Clock.Event>, +related: E.states(~String, ~Lookup.string_same, V, s, t), command: S.Command<String, V>) -> sres(V, PC.execute(~String, ~Lookup.string_same, V, s, zero_key, zero_value, events, command), PC.execute(~String, ~Lookup.string_same, V, t, zero_key, zero_value, events, command)):
  match command:
    case S.Add{+k, +v}: effect_cong(V, zero_key, zero_value, PC.Flag{}, Eff.add(~String, ~Lookup.string_same, V, s, k, v, events), Eff.add(~String, ~Lookup.string_same, V, t, k, v, events), add_plain_cong(V, s, t, k, v, events, related))
    case S.AddWithLifetime{+k, +v, +ns}: effect_cong(V, zero_key, zero_value, PC.Flag{}, Eff.add_with_lifetime(~String, ~Lookup.string_same, V, s, k, v, ns, events), Eff.add_with_lifetime(~String, ~Lookup.string_same, V, t, k, v, ns, events), add_cong(V, s, t, k, v, ns, events, related))
    case S.Get{+k}: effect_cong(V, zero_key, zero_value, PC.ValueOnly{}, Eff.read(~String, ~Lookup.string_same, V, s, k, True{}, events), Eff.read(~String, ~Lookup.string_same, V, t, k, True{}, events), read_cong(V, s, t, k, True{}, events, related))
    case S.GetAndRefresh{+k, +ns}: effect_cong(V, zero_key, zero_value, PC.ValueOnly{}, Eff.refresh(~String, ~Lookup.string_same, V, s, k, ns, events), Eff.refresh(~String, ~Lookup.string_same, V, t, k, ns, events), refresh_cong(V, s, t, k, ns, events, related))
    case S.Peek{+k}: effect_cong(V, zero_key, zero_value, PC.ValueOnly{}, Eff.read(~String, ~Lookup.string_same, V, s, k, False{}, events), Eff.read(~String, ~Lookup.string_same, V, t, k, False{}, events), read_cong(V, s, t, k, False{}, events, related))
    case S.Contains{+k}: effect_cong(V, zero_key, zero_value, PC.Flag{}, Eff.read(~String, ~Lookup.string_same, V, s, k, False{}, events), Eff.read(~String, ~Lookup.string_same, V, t, k, False{}, events), read_cong(V, s, t, k, False{}, events, related))
    case S.Remove{+k}: observation_cong(V, zero_key, zero_value, PC.Flag{}, S.remove(~String, ~Lookup.string_same, V, s, k), S.remove(~String, ~Lookup.string_same, V, t, k), events, 0n, remove_obs(V, s, t, k, related))
    case S.RemoveOldest{}: observation_cong(V, zero_key, zero_value, PC.RemovedOldest{}, O.remove_oldest(~String, ~Lookup.string_same, V, s), O.remove_oldest(~String, ~Lookup.string_same, V, t), events, 0n, remove_oldest_obs(V, s, t, related))
    case S.GetOldest{}: oldest_cong(V, s, t, zero_key, zero_value, events, related)
    case S.Keys{}: effect_cong(V, zero_key, zero_value, PC.Keys{}, A.purge_expired(~String, ~Lookup.string_same, V, s, events), A.purge_expired(~String, ~Lookup.string_same, V, t, events), aggregate_cong(V, s, t, events, related))
    case S.Values{}: effect_cong(V, zero_key, zero_value, PC.Values{}, A.purge_expired(~String, ~Lookup.string_same, V, s, events), A.purge_expired(~String, ~Lookup.string_same, V, t, events), aggregate_cong(V, s, t, events, related))
    case S.Purge{}: (purged_cong(V, s, t, related), {==}, {==}, {==})
    case S.PurgeExpired{}: effect_cong(V, zero_key, zero_value, PC.Nothing{}, A.purge_expired(~String, ~Lookup.string_same, V, s, events), A.purge_expired(~String, ~Lookup.string_same, V, t, events), aggregate_cong(V, s, t, events, related))
    case S.Len{}: (related, Equal.cong(Nat, PC.Reply<String, V>, n => PC.Length{n}, S.length(String, V, s), S.length(String, V, t), Ext.length(~String, ~Lookup.string_same, V, s, t, related)), {==}, {==})
    case S.SetLifetime{+ns}: (Ext.set_lifetime(~String, ~Lookup.string_same, V, s, t, ns, related), {==}, {==}, {==})
    case S.Metrics{}: metrics_cong(V, s, t, events, related)
    case S.ResetMetrics{}: reset_cong(V, s, t, events, related)
    case S.Diagnostics{}: diagnostics_cong(V, s, t, events, related)

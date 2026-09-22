import Base
import ../lib/array.bend as AR
import ../../spec/lru_fast.bend as S
import ../../spec/lru_numeric.bend as NS
import ../../src/lru/fast.bend as F
import ../../src/lru/wide.bend as W
import ../../types/lru_model.bend as T
import support/links_state.bend as DST
import ./num/numeric.bend as NUM
import ./state.bend as ST
import ./counts.bend as CT
import ./rs.bend as RS

# Facts shared by the reads: the Stamp encoding round-trips, a zero deadline
# never expires, and the hit / miss counters.

def stamp_parts(parts: W.Parts<32n, 32n>) -> {F.stamp_int(F.of_pair(W.limbs(parts))) == T.I64{NUM.rejoin(32n, 32n, parts)} : T.Int64}:
  W.Split{lo, hi} = parts
  {==}

def stamp_iso(t: T.Int64) -> {F.stamp_int(F.int_stamp(t)) == t : T.Int64}:
  match t:
    case T.I64{+w}:
      Equal.trans(T.Int64, F.stamp_int(F.of_pair(W.limbs(W.split(32n, 32n, w)))), T.I64{NUM.rejoin(32n, 32n, W.split(32n, 32n, w))}, T.I64{w},
        stamp_parts(W.split(32n, 32n, w)),
        Equal.cong(Word(64n), T.Int64, x => T.I64{x}, NUM.rejoin(32n, 32n, W.split(32n, 32n, w)), w, NUM.join_split(32n, 32n, w)))

def zero_live(+now: T.Int64) -> {NS.expired(S.zero_time(), now) == False{} : Bool}:
  match now:
    case T.I64{+b}:
      {==}

# ---- hit / miss counting ----

def hc(+tc: AR.Tree<U32>, tracked: Bool, hit: Bool) -> AR.Tree<U32>:
  match tracked hit:
    case False{} h:
      tc
    case True{} True{}:
      CT.bt(tc, 6n)
    case True{} False{}:
      CT.bt(tc, 8n)

def hc_ok(+tc: AR.Tree<U32>, tracked: Bool, hit: Bool, +pf: {AR.perfect(U32, 4n, tc) == True{} : Bool}) -> {F.hit_counts(AR.thaw(U32, tc), tracked, hit) == AR.thaw(U32, hc(tc, tracked, hit)) : Array<U32>}:
  match tracked hit:
    case False{} h:
      {==}
    case True{} True{}:
      CT.bump_ok(tc, 3, 6n, {==}, {==}, pf, {==})
    case True{} False{}:
      CT.bump_ok(tc, 4, 8n, {==}, {==}, pf, {==})

def hc_pf(+tc: AR.Tree<U32>, tracked: Bool, hit: Bool, +pf: {AR.perfect(U32, 4n, tc) == True{} : Bool}) -> {AR.perfect(U32, 4n, hc(tc, tracked, hit)) == True{} : Bool}:
  match tracked hit:
    case False{} h:
      pf
    case True{} True{}:
      RS.bt_pf(tc, 6n, pf)
    case True{} False{}:
      RS.bt_pf(tc, 8n, pf)

def hm_hit(tracked: Bool, +m: T.Metrics) -> T.Metrics:
  match tracked:
    case False{}:
      m
    case True{}:
      T.bump(3n, m)

def hc_mets_hit(+tc: AR.Tree<U32>, tracked: Bool, +pf: {AR.perfect(U32, 4n, tc) == True{} : Bool}) -> {ST.mets(AR.slots(U32, hc(tc, tracked, True{}))) == hm_hit(tracked, ST.mets(AR.slots(U32, tc))) : T.Metrics}:
  match tracked:
    case False{}:
      {==}
    case True{}:
      +cs = AR.slots(U32, tc)
      Equal.trans(T.Metrics, ST.mets(AR.slots(U32, CT.bt(tc, 6n))), ST.mets(CT.sbt(cs, 6n, U32.is_eq(U32.inc(DST.lat(cs, 6n)), 0), DST.lat(cs, 7n), U32.inc(DST.lat(cs, 6n)))), T.bump(3n, ST.mets(cs)),
        Equal.cong(List<&2, U32>, T.Metrics, z => ST.mets(z), AR.slots(U32, CT.bt(tc, 6n)), CT.sbt(cs, 6n, U32.is_eq(U32.inc(DST.lat(cs, 6n)), 0), DST.lat(cs, 7n), U32.inc(DST.lat(cs, 6n))), CT.slots_bt(tc, 6n, pf, {==})),
        CT.mets_bump_3(cs, RS.len16(tc, 7n, {==}, pf)))

def hc_mets_miss(+tc: AR.Tree<U32>, tracked: Bool, +pf: {AR.perfect(U32, 4n, tc) == True{} : Bool}) -> {ST.mets(AR.slots(U32, hc(tc, tracked, False{}))) == S.count_if(tracked, 4n, ST.mets(AR.slots(U32, tc))) : T.Metrics}:
  match tracked:
    case False{}:
      {==}
    case True{}:
      +cs = AR.slots(U32, tc)
      Equal.trans(T.Metrics, ST.mets(AR.slots(U32, CT.bt(tc, 8n))), ST.mets(CT.sbt(cs, 8n, U32.is_eq(U32.inc(DST.lat(cs, 8n)), 0), DST.lat(cs, 9n), U32.inc(DST.lat(cs, 8n)))), T.bump(4n, ST.mets(cs)),
        Equal.cong(List<&2, U32>, T.Metrics, z => ST.mets(z), AR.slots(U32, CT.bt(tc, 8n)), CT.sbt(cs, 8n, U32.is_eq(U32.inc(DST.lat(cs, 8n)), 0), DST.lat(cs, 9n), U32.inc(DST.lat(cs, 8n))), CT.slots_bt(tc, 8n, pf, {==})),
        CT.mets_bump_4(cs, RS.len16(tc, 9n, {==}, pf)))

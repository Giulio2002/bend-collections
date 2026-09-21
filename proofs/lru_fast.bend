import Base
import ./lib/logic.bend as L
import ../spec/common.bend as SC
import ../spec/lru_fast.bend as S
import ../src/lru/fast.bend as F
import ../types/lru_model.bend as T
import ../types/lru_fast.bend as E
import ./lru_fast/state.bend as ST
import ./lru_fast/steps.bend as SP
import ./lru_fast/trace.bend as TR

# Indexed LRU (src/lru/fast.bend): public proof entry point, values of an
# erased type V.
#
# Representation: a key table (native crit-bit Map from key to slot) over slot
# arenas (keys, entries, prev/next recency links as Base.Arrays), a free list
# threaded through the next links, and five 64-bit counters kept as ten U32
# limbs. As for the other array-backed structures the laws are about the cache
# BUILT from a Data mirror (ST.real of a shadow: perfect trees plus the ghost
# recency order and free list):
#   abstraction  ST.model (capacity, lifetime, the entries in recency order
#                with their deadlines, the counters) -- spec/lru_fast.bend
#   invariant    ST.good  (arrays perfect, depth <= 31, ghost order and free
#                list partition the slots below fresh <= 2^depth, links agree
#                with the order, the free chain with the free list, every slot
#                of the order occupied and mapped to by the table, the table's
#                keys exactly those of the order, crit-bit shape, length <= cap)
# Every public operation (len, capacity, set_lifetime, metrics, add, get,
# peek, contains, remove, purge, resize, keys) is proven in TR.step_ok, with
# expiry against the retained numeric semantics; arbitrary finite traces run
# from the real constructor (TR.trace_new). The only premise is the capacity
# condition: every capacity the cache takes (initial and Resize) is within
# 2^q, q <= 31, which bounds the arena size (arrays grow only while the cache
# holds fewer than cap entries).
#
# The definitions are generic in V; END_TO_END.bend instantiates them at
# V = U32 and V = String.

def new_real(~V: Data, +cap: U32) -> {F.init(~V, cap) == ST.real(~V, ST.initial(~V, cap)) : F.Fast<V>}:
  ST.new_real(~V, cap)

def new_abs(~V: Data, +cap: U32) -> {ST.model(~V, ST.initial(~V, cap)) == S.LM{cap, S.zero_time(), Nil{}, T.zero_metrics()} : S.Model<V>}:
  ST.new_model(~V, cap)

def new_inv(~V: Data, +cap: U32, +hc: {U32.is_eq(cap, 0) == False{} : Bool}) -> {ST.good(~V, ST.initial(~V, cap)) == True{} : Bool}:
  ST.new_good(~V, cap, hc)

# the checked constructors accept exactly the same capacities
def new_accepts(~V: Data, +cap: U32, +h0: {U32.is_eq(cap, 0) == False{} : Bool}, +h1: {U32.is_eq(cap, 4294967295) == False{} : Bool}) -> {F.new(~V, cap) == F.Made{F.init(~V, cap)} : F.Made<V>}:
  L.subst(Bool, z => {F.new_checked(~V, cap, z, U32.is_eq(cap, 4294967295)) == F.Made{F.init(~V, cap)} : F.Made<V>}, False{}, U32.is_eq(cap, 0), Equal.sym(Bool, U32.is_eq(cap, 0), False{}, h0),
    L.subst(Bool, z => {F.new_checked(~V, cap, False{}, z) == F.Made{F.init(~V, cap)} : F.Made<V>}, False{}, U32.is_eq(cap, 4294967295), Equal.sym(Bool, U32.is_eq(cap, 4294967295), False{}, h1), {==}))

def spec_new_accepts(-V: Data, +cap: U32, +h0: {U32.is_eq(cap, 0) == False{} : Bool}, +h1: {U32.is_eq(cap, 4294967295) == False{} : Bool}) -> {S.new(V, cap) == Done{S.LM{cap, S.zero_time(), Nil{}, T.zero_metrics()}} : Result<&2, &2, String, S.Model<V>>}:
  L.subst(Bool, z => {S.new_checked(V, cap, z, U32.is_eq(cap, 4294967295)) == Done{S.LM{cap, S.zero_time(), Nil{}, T.zero_metrics()}} : Result<&2, &2, String, S.Model<V>>}, False{}, U32.is_eq(cap, 0), Equal.sym(Bool, U32.is_eq(cap, 0), False{}, h0),
    L.subst(Bool, z => {S.new_checked(V, cap, False{}, z) == Done{S.LM{cap, S.zero_time(), Nil{}, T.zero_metrics()}} : Result<&2, &2, String, S.Model<V>>}, False{}, U32.is_eq(cap, 4294967295), Equal.sym(Bool, U32.is_eq(cap, 4294967295), False{}, h1), {==}))

def new_zero(~V: Data) -> {F.new(~V, 0) == F.Rejected{"capacity must be positive"} : F.Made<V>}:
  {==}

def spec_new_zero(-V: Data) -> {S.new(V, 0) == Fail{"capacity must be positive"} : Result<&2, &2, String, S.Model<V>>}:
  {==}

def new_reserved(~V: Data) -> {F.new(~V, 4294967295) == F.Rejected{"size must not be 0XFFFFFFFF"} : F.Made<V>}:
  {==}

def spec_new_reserved(-V: Data) -> {S.new(V, 4294967295) == Fail{"size must not be 0XFFFFFFFF"} : Result<&2, &2, String, S.Model<V>>}:
  {==}

def step_ok(~V: Data, +sh: ST.Shadow<V>, +op: E.Op<V>, +h: {ST.good(~V, sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hc: {TR.cb(V, q, sh) == True{} : Bool}) -> SP.StepOK(~V, sh, op):
  TR.step_ok(~V, sh, op, h, q, hq, hc)

def trace_new(~V: Data, +cap: U32, +ops: List<&2, E.Op<V>>, +hc0: {U32.is_eq(cap, 0) == False{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hc: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}, +hops: {TR.all_ok(V, q, ops) == True{} : Bool}) -> TR.TraceNew(~V, cap, ops):
  TR.trace_new(~V, cap, ops, hc0, q, hq, hc, hops)

def trace_from(~V: Data, +ops: List<&2, E.Op<V>>, +sh: ST.Shadow<V>, +h: {ST.good(~V, sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hc: {TR.cb(V, q, sh) == True{} : Bool}, +hops: {TR.all_ok(V, q, ops) == True{} : Bool}) -> TR.TraceOK(~V, ops, sh):
  TR.trace_from(~V, ops, sh, h, q, hq, hc, hops)

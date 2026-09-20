import Base
import ../src/cache.bend as C
import ../src/host.bend as H
import ../spec/host.bend as S
import ../spec/clock.bend as Clock
import ../spec/numeric.bend as N
import ../types/model.bend as T
import ./host_numeric.bend as HN
import ./numeric.bend as Numeric
import ./host_render.bend as Render
import ./division_quotient.bend as Quotient

# The remaining boundary entry points of src/host.bend, stated against the
# independent host specification.
def scalar_same(s: String) -> {H.scalar(s) == S.scalar(s) : Bool}:
  match s:
    case SNil{}: {==}
    case SCon{Chr{+x}, t}: Equal.cong(Bool, Bool, b => Bool.and(Bool.not(S.surrogate(x)), b), H.scalar(t), S.scalar(t), scalar_same(t))

def accept(s: String, ok: Bool) -> Result<&2, &2, String, String>:
  match ok:
    case True{}: Done{s}
    case False{}: Fail{"unpaired surrogate"}

# String keys: exactly the Unicode scalar strings are accepted, unchanged.
def accept_same(s: String, b: Bool) -> {H.string_if(s, b) == accept(s, b) : Result<&2, &2, String, String>}:
  match b:
    case True{}: {==}
    case False{}: {==}

def string_key(+s: String) -> {H.string_key(s) == accept(s, S.scalar(s)) : Result<&2, &2, String, String>}:
  Equal.trans(Result<&2, &2, String, String>, H.string_if(s, H.scalar(s)), H.string_if(s, S.scalar(s)), accept(s, S.scalar(s)), Equal.cong(Bool, Result<&2, &2, String, String>, b => H.string_if(s, b), H.scalar(s), S.scalar(s), scalar_same(s)), accept_same(s, S.scalar(s)))

def time_spec(m: Maybe<&2, Word(64n)>) -> Result<&2, &2, String, T.Int64>:
  match m:
    case None{}: Fail{"int64 value"}
    case Some{w}: Done{T.I64{w}}

def time_lift(m: Maybe<&2, Word(64n)>) -> {H.time_of(HN.lift(64n, "int64 value", m)) == time_spec(m) : Result<&2, &2, String, T.Int64>}:
  match m:
    case None{}: {==}
    case Some{w}: {==}

# Durations: signed int64 decimal text, rejected otherwise.
def time(+s: String) -> {H.time(s) == time_spec(S.int64_text(s)) : Result<&2, &2, String, T.Int64>}:
  %Equal.sym(Result<&2, &2, String, Word(64n)>, H.signed_word(63n, "int64 value", s), HN.lift(64n, "int64 value", S.int64_text(s)), HN.signed_word(63n, "int64 value", s)) : {H.time_of(_) == time_spec(S.int64_text(s)) : Result<&2, &2, String, T.Int64>}
  time_lift(S.int64_text(s))

def sample_spec(m: Maybe<&2, Word(64n)>) -> Clock.Event:
  match m:
    case None{}: Clock.InvalidSample{"int64 value"}
    case Some{w}: Clock.Sample{T.I64{w}}

def sample_lift(m: Maybe<&2, Word(64n)>) -> {H.sample_of(time_spec(m)) == sample_spec(m) : Clock.Event}:
  match m:
    case None{}: {==}
    case Some{w}: {==}

# Clock samples: an in-range int64 is a Sample; anything else is an invalid
# sample (execution failure), never a successful reading.
def sample(+s: String) -> {H.sample(s) == sample_spec(S.int64_text(s)) : Clock.Event}:
  %Equal.sym(Result<&2, &2, String, T.Int64>, H.time(s), time_spec(S.int64_text(s)), time(s)) : {H.sample_of(_) == sample_spec(S.int64_text(s)) : Clock.Event}
  sample_lift(S.int64_text(s))

def create_spec(-K: Data, -V: Data, capacity: Maybe<&2, Word(32n)>, size: Maybe<&2, Word(32n)>) -> Result<&2, &2, String, C.Cache<K, V>>:
  match capacity size:
    case None{} s: Fail{"uint32 capacity/size"}
    case Some{c} None{}: Fail{"uint32 capacity/size"}
    case Some{+c} Some{+s}: C.new_with_size(K, V, U32{c}, U32{s})

def create_lift(-K: Data, -V: Data, capacity: Maybe<&2, Word(32n)>, size: Maybe<&2, Word(32n)>) -> {H.create_of(K, V, H.u32_of(HN.lift(32n, "uint32 capacity/size", capacity)), H.u32_of(HN.lift(32n, "uint32 capacity/size", size))) == create_spec(K, V, capacity, size) : Result<&2, &2, String, C.Cache<K, V>>}:
  match capacity size:
    case None{} s: {==}
    case Some{c} None{}: {==}
    case Some{c} Some{s}: {==}

# Construction from host text: out-of-range capacity/size text is rejected
# before, and otherwise exactly, the actual C.new_with_size validation.
def create(-K: Data, -V: Data, +capacity: String, +size: String) -> {H.create(K, V, capacity, size) == create_spec(K, V, S.unsigned_text(32n, capacity), S.unsigned_text(32n, size)) : Result<&2, &2, String, C.Cache<K, V>>}:
  %Equal.sym(Result<&2, &2, String, Word(32n)>, H.unsigned_word(32n, "uint32 capacity/size", capacity), HN.lift(32n, "uint32 capacity/size", S.unsigned_text(32n, capacity)), HN.unsigned_word(32n, "uint32 capacity/size", capacity)) : {H.create_of(K, V, H.u32_of(_), H.uint32("uint32 capacity/size", size)) == create_spec(K, V, S.unsigned_text(32n, capacity), S.unsigned_text(32n, size)) : Result<&2, &2, String, C.Cache<K, V>>}
  %Equal.sym(Result<&2, &2, String, Word(32n)>, H.unsigned_word(32n, "uint32 capacity/size", size), HN.lift(32n, "uint32 capacity/size", S.unsigned_text(32n, size)), HN.unsigned_word(32n, "uint32 capacity/size", size)) : {H.create_of(K, V, H.u32_of(HN.lift(32n, "uint32 capacity/size", S.unsigned_text(32n, capacity))), H.u32_of(_)) == create_spec(K, V, S.unsigned_text(32n, capacity), S.unsigned_text(32n, size)) : Result<&2, &2, String, C.Cache<K, V>>}
  create_lift(K, V, S.unsigned_text(32n, capacity), S.unsigned_text(32n, size))

# Key identity across the boundary: the text returned for a key reads back as
# the same key word.
def uint64_roundtrip(+w: Word(64n)) -> {H.uint64_key(H.uint64_text(w)) == Done{w} : Result<&2, &2, String, Word(64n)>}:
  %Equal.sym(Result<&2, &2, String, Word(64n)>, H.unsigned_word(64n, "uint64 key", H.uint64_text(w)), HN.lift(64n, "uint64 key", S.unsigned_text(64n, H.uint64_text(w))), HN.unsigned_word(64n, "uint64 key", H.uint64_text(w))) : {_ == Done{w} : Result<&2, &2, String, Word(64n)>}
  %Equal.sym(Maybe<&2, Nat>, S.natural(H.unsigned_text(64n, w)), Some{N.unsigned(64n, w)}, Render.unsigned_text(64n, w)) : {HN.lift(64n, "uint64 key", S.bounded(64n, _)) == Done{w} : Result<&2, &2, String, Word(64n)>}
  %Equal.sym(Bool, S.fits(64n, N.unsigned(64n, w)), True{}, HN.fits_self(64n, w)) : {HN.lift(64n, "uint64 key", S.fits_if(64n, N.unsigned(64n, w), _)) == Done{w} : Result<&2, &2, String, Word(64n)>}
  Equal.cong(Word(64n), Result<&2, &2, String, Word(64n)>, x => Done{x}, N.from_nat(64n, N.unsigned(64n, w)), w, Quotient.reconstruct(64n, w))

def int64_roundtrip(+w: Word(64n)) -> {H.int64_key(H.int64_text(w)) == Done{w} : Result<&2, &2, String, Word(64n)>}:
  %Equal.sym(Result<&2, &2, String, Word(64n)>, H.signed_word(63n, "int64 key", H.int64_text(w)), HN.lift(64n, "int64 key", S.int64_text(H.int64_text(w))), HN.signed_word(63n, "int64 key", H.int64_text(w))) : {_ == Done{w} : Result<&2, &2, String, Word(64n)>}
  %Equal.sym(Maybe<&2, Word(64n)>, S.signed_text(63n, H.signed_text(63n, w, H.sign_bit(63n, w))), Some{w}, Render.signed_text(63n, w)) : {HN.lift(64n, "int64 key", _) == Done{w} : Result<&2, &2, String, Word(64n)>}
  {==}

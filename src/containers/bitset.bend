import Base
import ../math/pow2.bend as P2
import ./types/bitset.bend as E

# Packed fixed-size bitset over native Base.Array.
#
# A bitset of logical size `len` stores its bits LSB-first in a Base.Array of
# 2^depth 32-bit words: bit i lives in word i/32 at bit position i%32. The
# array holds at least ceil(len/32) words; every bit at a position >= len
# (the unused tail of the last used word, and any whole padding word) is
# zero. Both facts are the invariant proven in proofs/bitset.bend;
# union/intersection/difference/xor rely on it (e.g. difference is a AND NOT
# b, which stays masked because a's tail is zero).
#
# Representation note: `Base.Array` is a *linear* fixed-capacity array with
# O(1) indexed read and write, so every operation takes the bitset and gives
# it back, exactly like src/dynamic_array.bend. The earlier list-of-words
# representation made get/set O(words), which is not the algorithm the C
# reference runs; this one makes them a single indexed word access and matches
# the flat uint32_t array of benchmarks/native/bitset.c word for word.
#
# Capacity: `depth_for` stops at depth 31, i.e. 2^31 words = 2^36 bits, so
# every word index is a representable U32 and Base's index masking over the
# word array is the identity. The specification laws about `new(n)` therefore
# carry the explicit premise that n fits that capacity (proofs/bitset.bend
# `capacity`); every other law holds at every state satisfying the invariant,
# and the invariant implies the premise. This is the same kind of explicit,
# documented capacity bound that src/dynamic_array.bend carries, and the same
# one benchmarks/native/bitset.c has. It is a real narrowing compared with the
# earlier list-of-words representation, which had no capacity: see
# PROOF_STATUS.md and docs/archive/.
#
# Errors never change the state: get/set/clear with index >= len fail with
# IndexOutOfRange; binary operations on operands of different logical size
# fail with LengthMismatch and give both operands back unchanged. Because the
# array is linear, a binary operation returns BOTH operands (a linear API has
# to give back what it borrowed) and a bitset that is no longer needed is
# released with `dispose`; `clone` makes two independent copies.
#
# Cost (w = 2^depth words): new O(w); length O(1); get/set/clear one indexed
# word read (and, for set/clear, one indexed word write) plus a constant
# amount of word arithmetic; count/to_list O(32 * w) (32 shifts per word, the
# same loop the C reference runs); binary operations O(w); clone O(w);
# dispose O(w).
#
# "One indexed word access" is a claim about Bend's native C backend, not
# folklore: `Base.Array` is a flat array there, and the measured cost of
# `Array.get`/`Array.set` is constant across sizes 64 .. 262144 and at parity
# with the same access in C (see the cost model at the top of BENCHMARKS.md
# and the `bitset.get` / `bitset.set` rows). None of the proofs depend on it.

type Wd is Data:
  W{value: U32}

type Bitset is Type:
  BS{len: Nat, depth: Nat, words: Array<Wd>}

def wval(x: Wd) -> U32:
  match x:
    case W{v}:
      v

# Word-level operations (native U32 arithmetic).

type WordOp is Data:
  KOr{}
  KAnd{}
  KDiff{}
  KXor{}

def low(w: U32) -> Bool:
  Bool.not(U32.is_even(w))

def word_get(w: U32, k: Nat) -> Bool:
  low(U32.shrn(w, k))

def word_put(v: Bool, w: U32, k: Nat) -> U32:
  match v:
    case True{}:
      U32.or(w, U32.shln(1, k))
    case False{}:
      U32.and(w, U32.not(U32.shln(1, k)))

def word_op(k: WordOp, a: U32, b: U32) -> U32:
  match k:
    case KOr{}:
      U32.or(a, b)
    case KAnd{}:
      U32.and(a, b)
    case KDiff{}:
      U32.and(a, U32.not(b))
    case KXor{}:
      U32.xor(a, b)

def bit_value(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# Number of set bits among the low m bits of w.
def word_count(m: Nat, +w: U32) -> Nat:
  match m:
    case 0n:
      0n
    case 1n+p:
      Nat.add(bit_value(low(w)), word_count(p, U32.shr(w)))

def member_pick(b: Bool, +off: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      Con{off, rest}
    case False{}:
      rest

# Indices (from off) of set bits among the low m bits of w, then rest.
def word_members(m: Nat, +w: U32, +off: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match m:
    case 0n:
      rest
    case 1n+p:
      member_pick(low(w), off, word_members(p, U32.shr(w), 1n+off, rest))

# ---- index arithmetic ----

# The word index of bit i and the bit position inside that word. Base's
# Nat.div / Nat.mod are structural definitions the proofs can peel 32 steps
# at a time (proofs/bitset/index.bend) and the native backend evaluates in
# constant time.
def wordix(i: Nat) -> Nat:
  Nat.div(i, 32n)

def bitix(i: Nat) -> Nat:
  Nat.mod(i, 32n)

# 2^d.
def pow2(d: Nat) -> Nat:
  match d:
    case 0n:
      1n
    case 1n+p:
      Nat.double(pow2(p))

# 2^31 words = 2^36 bits: the capacity of the packed representation (the
# constant is never materialised as a value; `depth_for` simply stops at this
# depth). Every word index is then a representable U32 and Base's index
# masking over the word array is the identity.
def max_depth() -> Nat:
  31n

# The smallest depth whose 2^depth words hold n bits, capped at max_depth.
# `fuel` bounds the search structurally, `cap` is 2^d and `done` is the exit
# test `n <= 32 * cap`, so a depth that comes out of the loop below the cap
# always satisfies it (proofs/bitset/depth.bend).
def depth_go(fuel: Nat, +n: Nat, d: Nat, +cap: Nat, done: Bool) -> Nat:
  match fuel done:
    case 0n _:
      d
    case 1n+f True{}:
      d
    case 1n+f False{}:
      depth_go(f, n, 1n+d, Nat.double(cap), Nat.is_le(n, Nat.mul(Nat.double(cap), 32n)))

def depth_for(+n: Nat) -> Nat:
  depth_go(max_depth(), n, 0n, 1n, Nat.is_le(n, Nat.mul(1n, 32n)))

# ---- array access ----

def read_fin(p: Array<Wd> & Wd) -> Array<Wd> & U32:
  (a, x) = p
  (a, wval(x))

# Word q of the array (q < 2^depth).
def read(a: Array<Wd>, +d: Nat, +q: Nat) -> Array<Wd> & U32:
  read_fin(Array.get(Wd, a, U32.from_nat(q)))

# Replace word q.
def write(a: Array<Wd>, +d: Nat, +q: Nat, +v: U32) -> Array<Wd>:
  Array.set(Wd, a, U32.from_nat(q), W{v})

# ---- public API ----

# All-zero bitset of logical size n (see the capacity note).
def new_at(+n: Nat, +d: Nat) -> Bitset:
  BS{n, d, Array.new(Wd, d, W{0})}

def new(+n: Nat) -> Bitset:
  new_at(n, depth_for(n))

def length(s: Bitset) -> Bitset & Nat:
  match s:
    case BS{+n, d, a}:
      (BS{n, d, a}, n)

# ---- get ----

def get_read(p: Array<Wd> & U32, +n: Nat, +d: Nat, +b: Nat) -> Bitset & Result<&2, &2, E.Error, Bool>:
  (a, w) = p
  (BS{n, d, a}, Done{word_get(w, b)})

def get_if(ok: Bool, +n: Nat, +d: Nat, a: Array<Wd>, +i: Nat) -> Bitset & Result<&2, &2, E.Error, Bool>:
  match ok:
    case True{}:
      get_read(read(a, d, wordix(i)), n, d, bitix(i))
    case False{}:
      (BS{n, d, a}, Fail{E.IndexOutOfRange{}})

def get(s: Bitset, +i: Nat) -> Bitset & Result<&2, &2, E.Error, Bool>:
  match s:
    case BS{+n, +d, a}:
      get_if(Nat.is_lt(i, n), n, d, a, i)

# ---- set / clear ----

def assign_read(p: Array<Wd> & U32, +n: Nat, +d: Nat, +q: Nat, +b: Nat, +v: Bool) -> Bitset & Result<&2, &2, E.Error, Unit>:
  (a, w) = p
  (BS{n, d, write(a, d, q, word_put(v, w, b))}, Done{Unit{}})

def assign_if(ok: Bool, +n: Nat, +d: Nat, a: Array<Wd>, +i: Nat, +v: Bool) -> Bitset & Result<&2, &2, E.Error, Unit>:
  match ok:
    case True{}:
      assign_read(read(a, d, wordix(i)), n, d, wordix(i), bitix(i), v)
    case False{}:
      (BS{n, d, a}, Fail{E.IndexOutOfRange{}})

def assign(s: Bitset, +i: Nat, +v: Bool) -> Bitset & Result<&2, &2, E.Error, Unit>:
  match s:
    case BS{+n, +d, a}:
      assign_if(Nat.is_lt(i, n), n, d, a, i, v)

# Set bit i to 1.
def set(s: Bitset, +i: Nat) -> Bitset & Result<&2, &2, E.Error, Unit>:
  assign(s, i, True{})

# Set bit i to 0.
def clear(s: Bitset, +i: Nat) -> Bitset & Result<&2, &2, E.Error, Unit>:
  assign(s, i, False{})

# ---- whole-array walks ----

# Sum of the populations of words q, q+1, ... (m of them).
# Eight bits per iteration: word_count_t unrolled (the same shifts and adds).
def bv8(+w: U32) -> Nat:
  Nat.add(bit_value(low(w)), Nat.add(bit_value(low(U32.shr(w))), Nat.add(bit_value(low(U32.shr(U32.shr(w)))), Nat.add(bit_value(low(U32.shr(U32.shr(U32.shr(w))))), Nat.add(bit_value(low(U32.shr(U32.shr(U32.shr(U32.shr(w)))))), Nat.add(bit_value(low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))), Nat.add(bit_value(low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))), bit_value(low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))))))))))

def word_count_8(k: Nat, +w: U32, +acc: Nat) -> Nat:
  match k:
    case 0n:
      acc
    case 1n+p:
      word_count_8(p, U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))), Nat.add(acc, bv8(w)))

# A zero word contributes nothing and is skipped.
def count_word(+w: U32, +acc: Nat, zero: Bool) -> Nat:
  match zero:
    case True{}:
      acc
    case False{}:
      word_count_8(4n, w, acc)

def count_add(p: Array<Wd> & U32, +acc: Nat) -> Array<Wd> & Nat:
  (a, +w) = p
  (a, count_word(w, acc, U32.is_eq(w, 0)))

def count_go(m: Nat, p: Array<Wd> & Nat, +d: Nat, +q: Nat) -> Array<Wd> & Nat:
  match m:
    case 0n:
      p
    case 1n+r:
      (a, acc) = p
      count_go(r, count_add(read(a, d, q), acc), d, 1n+q)

def count_fin(p: Array<Wd> & Nat, +n: Nat, +d: Nat) -> Bitset & Nat:
  (a, c) = p
  (BS{n, d, a}, c)

def count(s: Bitset) -> Bitset & Nat:
  match s:
    case BS{+n, +d, a}:
      count_fin(count_go(P2.pow2t(d), (a, 0n), d, 0n), n, d)

# Indices of set bits, ascending. Walks the words from the last to the first
# so the list is built in ascending order without an append.
# The members of one word, by two TAIL loops: the set offsets are pushed in
# DESCENDING order onto a scratch list (low bit first), which is then
# reversed onto rest -- the same list word_members builds, without its
# non-tail recursion.
def word_desc(m: Nat, +w: U32, +off: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match m:
    case 0n:
      acc
    case 1n+p:
      word_desc(p, U32.shr(w), 1n+off, member_pick(low(w), off, acc))

# A zero word has no members and is skipped.
def members_word(+w: U32, +off: Nat, rest: List<&2, Nat>, zero: Bool) -> List<&2, Nat>:
  match zero:
    case True{}:
      rest
    case False{}:
      List.reverse.go(&2, Nat, word_desc(32n, w, off, Nil{}), rest)

def members_cons(p: Array<Wd> & U32, +off: Nat, rest: List<&2, Nat>) -> Array<Wd> & List<&2, Nat>:
  (a, +w) = p
  (a, members_word(w, off, rest, U32.is_eq(w, 0)))

def members_go(m: Nat, p: Array<Wd> & List<&2, Nat>, +d: Nat) -> Array<Wd> & List<&2, Nat>:
  match m:
    case 0n:
      p
    case 1n+ +r:
      (a, acc) = p
      members_go(r, members_cons(read(a, d, r), Nat.mul(r, 32n), acc), d)

def members_fin(p: Array<Wd> & List<&2, Nat>, +n: Nat, +d: Nat) -> Bitset & List<&2, Nat>:
  (a, xs) = p
  (BS{n, d, a}, xs)

def to_list(s: Bitset) -> Bitset & List<&2, Nat>:
  match s:
    case BS{+n, +d, a}:
      members_fin(members_go(P2.pow2t(d), (a, Nil{}), d), n, d)

# ---- binary operations ----

def zip_write(pa: Array<Wd> & U32, pb: Array<Wd> & U32, +k: WordOp, +d: Nat, +q: Nat) -> Array<Wd> & Array<Wd>:
  (a, x) = pa
  (b, y) = pb
  (write(a, d, q, word_op(k, x, y)), b)

def zip_step(p: Array<Wd> & Array<Wd>, +k: WordOp, +d: Nat, +q: Nat) -> Array<Wd> & Array<Wd>:
  (a, b) = p
  zip_write(read(a, d, q), read(b, d, q), k, d, q)

def zip_go(m: Nat, p: Array<Wd> & Array<Wd>, +k: WordOp, +d: Nat, +q: Nat) -> Array<Wd> & Array<Wd>:
  match m:
    case 0n:
      p
    case 1n+r:
      zip_go(r, zip_step(p, k, d, q), k, d, 1n+q)

# Discard a linear array (`dispose` below is the public form).
def burn_list(xs: List<Wd>) -> Unit:
  match xs:
    case Nil{}:
      Unit{}
    case Con{x, t}:
      burn_list(t)

# Releasing the word array is dropping it: `Base.Array` is linear, so the
# runtime frees the block when the last reference is erased.
def burn(a: Array<Wd>) -> Unit:
  Unit{}

# Release a bitset. `Base.Array` is linear, so a caller that stops using a
# bitset has to say so; every operation above gives the bitset back instead.
def dispose(s: Bitset) -> Unit:
  match s:
    case BS{n, d, a}:
      burn(a)

# Two independent bitsets with the same contents (the linear form of sharing).
def clone_fin(p: Array<Wd> & Array<Wd>, +n: Nat, +d: Nat) -> Bitset & Bitset:
  (a, b) = p
  (BS{n, d, a}, BS{n, d, b})

def clone(s: Bitset) -> Bitset & Bitset:
  match s:
    case BS{+n, +d, a}:
      clone_fin(Array.clone(Wd, a), n, d)

# Release two bitsets.
def dispose2_go(u: Unit, v: Unit) -> Unit:
  match u v:
    case Unit{} Unit{}:
      Unit{}

def dispose2(s: Bitset, t: Bitset) -> Unit:
  dispose2_go(dispose(s), dispose(t))

def zip_fin(p: Array<Wd> & Array<Wd>, +n: Nat, +d: Nat, +m: Nat, +e: Nat) -> Bitset & Bitset & Result<&2, &2, E.Error, Unit>:
  (a, b) = p
  (BS{n, d, a}, BS{m, e, b}, Done{Unit{}})

def combine_if(ok: Bool, +k: WordOp, +n: Nat, +d: Nat, a: Array<Wd>, +m: Nat, +e: Nat, b: Array<Wd>) -> Bitset & Bitset & Result<&2, &2, E.Error, Unit>:
  match ok:
    case True{}:
      zip_fin(zip_go(P2.pow2t(d), (a, b), k, d, 0n), n, d, m, e)
    case False{}:
      (BS{n, d, a}, BS{m, e, b}, Fail{E.LengthMismatch{}})

def combine_b(+k: WordOp, +n: Nat, +d: Nat, a: Array<Wd>, t: Bitset) -> Bitset & Bitset & Result<&2, &2, E.Error, Unit>:
  match t:
    case BS{+m, +e, b}:
      combine_if(Bool.and(Nat.is_eq(n, m), Nat.is_eq(d, e)), k, n, d, a, m, e, b)

# The operands are given back unchanged apart from the result written into the
# left one: a linear API has to return what it borrowed.
def combine(+k: WordOp, s: Bitset, t: Bitset) -> Bitset & Bitset & Result<&2, &2, E.Error, Unit>:
  match s:
    case BS{+n, +d, a}:
      combine_b(k, n, d, a, t)

def union(s: Bitset, t: Bitset) -> Bitset & Bitset & Result<&2, &2, E.Error, Unit>:
  combine(KOr{}, s, t)

def intersection(s: Bitset, t: Bitset) -> Bitset & Bitset & Result<&2, &2, E.Error, Unit>:
  combine(KAnd{}, s, t)

def difference(s: Bitset, t: Bitset) -> Bitset & Bitset & Result<&2, &2, E.Error, Unit>:
  combine(KDiff{}, s, t)

def xor(s: Bitset, t: Bitset) -> Bitset & Bitset & Result<&2, &2, E.Error, Unit>:
  combine(KXor{}, s, t)

# ---- building from a bit sequence ----

def fill_drop(s: Bitset, x: Result<&2, &2, E.Error, Unit>) -> Bitset:
  match x:
    case Fail{e}:
      s
    case Done{u}:
      s

def fill_set(p: Bitset & Result<&2, &2, E.Error, Unit>) -> Bitset:
  (s, x) = p
  fill_drop(s, x)

def fill_pick(b: Bool, s: Bitset, +i: Nat) -> Bitset:
  match b:
    case True{}:
      fill_set(set(s, i))
    case False{}:
      s

def fill(bs: List<&2, Bool>, +i: Nat, s: Bitset) -> Bitset:
  match bs:
    case Nil{}:
      s
    case Con{b, t}:
      fill(t, 1n+i, fill_pick(b, s, i))

def bool_count(bs: List<&2, Bool>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case Con{b, t}:
      1n+bool_count(t)

# Bitset whose logical bits are exactly bs (bit 0 first).
def from_bools(+bs: List<&2, Bool>) -> Bitset:
  fill(bs, 0n, new(bool_count(bs)))

# ---- combining with a bit sequence ----
#
# The trace runner's binary operations take the operand as a bit sequence.
# The logical sizes are compared *before* the operand bitset is built, so an
# operand of a different size costs nothing and can never be materialised at
# a size the representation cannot hold.

def drop_right_go(s: Bitset, u: Unit, x: Result<&2, &2, E.Error, Unit>) -> Bitset & Result<&2, &2, E.Error, Unit>:
  match u:
    case Unit{}:
      (s, x)

def drop_right(p: Bitset & Bitset & Result<&2, &2, E.Error, Unit>) -> Bitset & Result<&2, &2, E.Error, Unit>:
  (s, t, x) = p
  drop_right_go(s, dispose(t), x)

def comb_go(ok: Bool, +k: WordOp, +n: Nat, +d: Nat, a: Array<Wd>, +ys: List<&2, Bool>) -> Bitset & Result<&2, &2, E.Error, Unit>:
  match ok:
    case True{}:
      drop_right(combine(k, BS{n, d, a}, from_bools(ys)))
    case False{}:
      (BS{n, d, a}, Fail{E.LengthMismatch{}})

def comb_bits(+k: WordOp, s: Bitset, +ys: List<&2, Bool>) -> Bitset & Result<&2, &2, E.Error, Unit>:
  match s:
    case BS{+n, +d, a}:
      comb_go(Nat.is_eq(n, bool_count(ys)), k, n, d, a, ys)

# ---- trace runner ----

def obs_unit(r: Bitset & Result<&2, &2, E.Error, Unit>) -> Bitset & E.Obs:
  (s, x) = r
  (s, E.OUnit{x})

def obs_pair_done(s: Bitset, u: Unit, x: Result<&2, &2, E.Error, Unit>) -> Bitset & E.Obs:
  match u:
    case Unit{}:
      (s, E.OUnit{x})

# The trace runner owns the operand it built from the operation, so it
# releases it once the combination has been applied.
def obs_pair(r: Bitset & Bitset & Result<&2, &2, E.Error, Unit>) -> Bitset & E.Obs:
  (s, t, x) = r
  obs_pair_done(s, dispose(t), x)

def obs_bit(r: Bitset & Result<&2, &2, E.Error, Bool>) -> Bitset & E.Obs:
  (s, x) = r
  (s, E.OBit{x})

def obs_nat(r: Bitset & Nat) -> Bitset & E.Obs:
  (s, x) = r
  (s, E.ONat{x})

def obs_list(r: Bitset & List<&2, Nat>) -> Bitset & E.Obs:
  (s, xs) = r
  (s, E.OList{xs})

def step(s: Bitset, op: E.Op) -> Bitset & E.Obs:
  match op:
    case E.Length{}:
      obs_nat(length(s))
    case E.Get{i}:
      obs_bit(get(s, i))
    case E.Set{i}:
      obs_unit(set(s, i))
    case E.Clear{i}:
      obs_unit(clear(s, i))
    case E.Count{}:
      obs_nat(count(s))
    case E.Union{ys}:
      obs_unit(comb_bits(KOr{}, s, ys))
    case E.Intersection{ys}:
      obs_unit(comb_bits(KAnd{}, s, ys))
    case E.Difference{ys}:
      obs_unit(comb_bits(KDiff{}, s, ys))
    case E.Xor{ys}:
      obs_unit(comb_bits(KXor{}, s, ys))

    case E.ToList{}:
      obs_list(to_list(s))

def record(acc: List<&2, E.Obs>, r: Bitset & E.Obs) -> Bitset & List<&2, E.Obs>:
  (s, o) = r
  (s, Con{o, acc})

def step_acc(op: E.Op, st: Bitset & List<&2, E.Obs>) -> Bitset & List<&2, E.Obs>:
  (s, acc) = st
  record(acc, step(s, op))

def run_acc(ops: List<&2, E.Op>, st: Bitset & List<&2, E.Obs>) -> Bitset & List<&2, E.Obs>:
  match ops:
    case Nil{}:
      st
    case Con{op, rest}:
      run_acc(rest, step_acc(op, st))

def finish(st: Bitset & List<&2, E.Obs>) -> Bitset & List<&2, E.Obs>:
  (s, acc) = st
  (s, List.reverse(&2, E.Obs, acc))

def run(ops: List<&2, E.Op>, s: Bitset) -> Bitset & List<&2, E.Obs>:
  finish(run_acc(ops, (s, Nil{})))

import Base
import ./bitset.bend as B
import ./dynamic_array.bend as D
import ./types/dynamic_array.bend as DE
import ./types/bitlist.bend as E

# Packed growable bit list (SSZ-style Bitlist[N]).
#
# A bitlist is an ordered sequence of `len` bits with a maximum length
# `limit` (N). Bits are stored LSB-first in a dynamic array of 32-bit words:
# bit i lives in word i/32 at bit position i%32. The array holds at least
# ceil(len/32) words and every stored bit at a position >= len is zero (the
# masked tail). pop never shrinks the word array, so a later push reuses the
# zeroed word; push appends a word only when every stored bit is in use.
#
# Errors never change the state: get/assign with index >= len fail with
# IndexOutOfRange, push at len == limit fails with Full, pop of an empty
# list fails with Empty.
#
# Capacity: the word array is a dynamic array of depth limit 31 (2^31
# words), so a bitlist holds at most 2^36 bits; a push past that fails with
# Full exactly like a push past the limit. new() has no limit (None);
# with_limit(n) is Bitlist[n].
#
# Cost: length/limit O(1); get one word read; assign one word read and one
# write; push amortized O(1) (a word read and write, or one append; pushing
# a zero bit into allocated space only bumps the length); pop one word read
# and at most one write; count O(words); to_list O(len); clear O(capacity).
#
# Correctness: proofs/containers/bitlist refines every operation against an
# independent list-of-Bool specification.

type Bitlist is Type:
  BL{limit: Maybe<&2, Nat>, len: Nat, words: D.DynArray<&2, U32>}

def new() -> Bitlist:
  BL{None{}, 0n, D.new(U32)}

def with_limit(+n: Nat) -> Bitlist:
  BL{Some{n}, 0n, D.new(U32)}

# Room for one more bit under the limit.
def below(lim: Maybe<&2, Nat>, +n: Nat) -> Bool:
  match lim:
    case None{}:
      True{}
    case Some{k}:
      Nat.is_lt(n, k)

def length(s: Bitlist) -> Bitlist & Nat:
  BL{lim, +n, w} = s
  (BL{lim, n, w}, n)

def limit(s: Bitlist) -> Bitlist & Maybe<&2, Nat>:
  BL{+lim, n, w} = s
  (BL{lim, n, w}, lim)

# ---- get ----

def get_word(+i: Nat, +lim: Maybe<&2, Nat>, +n: Nat, r: D.DynArray<&2, U32> & Result<&2, &2, DE.Error, U32>) -> Bitlist & Result<&2, &2, E.Error, Bool>:
  match r:
    case Tuple{w, Done{x}}:
      (BL{lim, n, w}, Done{B.word_get(x, B.bitix(i))})
    case Tuple{w, Fail{e}}:
      (BL{lim, n, w}, Fail{E.IndexOutOfRange{}})

def get_if(ok: Bool, +lim: Maybe<&2, Nat>, +n: Nat, w: D.DynArray<&2, U32>, +i: Nat) -> Bitlist & Result<&2, &2, E.Error, Bool>:
  match ok:
    case True{}:
      get_word(i, lim, n, D.get(U32, w, B.wordix(i)))
    case False{}:
      (BL{lim, n, w}, Fail{E.IndexOutOfRange{}})

def get(s: Bitlist, +i: Nat) -> Bitlist & Result<&2, &2, E.Error, Bool>:
  BL{+lim, +n, w} = s
  get_if(Nat.is_lt(i, n), lim, n, w, i)

# ---- assign ----

def assign_set(+lim: Maybe<&2, Nat>, +n: Nat, r: D.DynArray<&2, U32> & Result<&2, &2, DE.Error, Unit>) -> Bitlist & Result<&2, &2, E.Error, Unit>:
  match r:
    case Tuple{w, Done{u}}:
      (BL{lim, n, w}, Done{Unit{}})
    case Tuple{w, Fail{e}}:
      (BL{lim, n, w}, Fail{E.IndexOutOfRange{}})

# Rewrite bit i of its word (the word read is r); the list gets length n.
def assign_word(+i: Nat, +v: Bool, +lim: Maybe<&2, Nat>, +n: Nat, r: D.DynArray<&2, U32> & Result<&2, &2, DE.Error, U32>) -> Bitlist & Result<&2, &2, E.Error, Unit>:
  match r:
    case Tuple{w, Done{+x}}:
      assign_set(lim, n, D.set(U32, w, B.wordix(i), B.word_put(v, x, B.bitix(i))))
    case Tuple{w, Fail{e}}:
      (BL{lim, n, w}, Fail{E.IndexOutOfRange{}})

def assign_if(ok: Bool, +lim: Maybe<&2, Nat>, +n: Nat, w: D.DynArray<&2, U32>, +i: Nat, +v: Bool) -> Bitlist & Result<&2, &2, E.Error, Unit>:
  match ok:
    case True{}:
      assign_word(i, v, lim, n, D.get(U32, w, B.wordix(i)))
    case False{}:
      (BL{lim, n, w}, Fail{E.IndexOutOfRange{}})

def assign(s: Bitlist, +i: Nat, +v: Bool) -> Bitlist & Result<&2, &2, E.Error, Unit>:
  BL{+lim, +n, w} = s
  assign_if(Nat.is_lt(i, n), lim, n, w, i, v)

def set(s: Bitlist, +i: Nat) -> Bitlist & Result<&2, &2, E.Error, Unit>:
  assign(s, i, True{})

def unset(s: Bitlist, +i: Nat) -> Bitlist & Result<&2, &2, E.Error, Unit>:
  assign(s, i, False{})

# ---- push ----

def push_new(+lim: Maybe<&2, Nat>, +n: Nat, r: D.DynArray<&2, U32> & Result<&2, &2, DE.Error, Unit>) -> Bitlist & Result<&2, &2, E.Error, Unit>:
  match r:
    case Tuple{w, Done{u}}:
      (BL{lim, 1n+n, w}, Done{Unit{}})
    case Tuple{w, Fail{e}}:
      (BL{lim, n, w}, Fail{E.Full{}})

# Bit n already lies in a stored word, where it is zero (masked tail).
def push_in(+lim: Maybe<&2, Nat>, +n: Nat, w: D.DynArray<&2, U32>, +v: Bool) -> Bitlist & Result<&2, &2, E.Error, Unit>:
  match v:
    case False{}:
      (BL{lim, 1n+n, w}, Done{Unit{}})
    case True{}:
      assign_word(n, True{}, lim, 1n+n, D.get(U32, w, B.wordix(n)))

def push_where(inside: Bool, +lim: Maybe<&2, Nat>, +n: Nat, w: D.DynArray<&2, U32>, +v: Bool) -> Bitlist & Result<&2, &2, E.Error, Unit>:
  match inside:
    case True{}:
      push_in(lim, n, w, v)
    case False{}:
      push_new(lim, n, D.push(U32, w, B.word_put(v, 0, 0n)))

def push_room(+lim: Maybe<&2, Nat>, +n: Nat, +v: Bool, r: D.DynArray<&2, U32> & Nat) -> Bitlist & Result<&2, &2, E.Error, Unit>:
  (w, +k) = r
  push_where(Nat.is_lt(n, Nat.mul(k, 32n)), lim, n, w, v)

def push_if(ok: Bool, +lim: Maybe<&2, Nat>, +n: Nat, w: D.DynArray<&2, U32>, +v: Bool) -> Bitlist & Result<&2, &2, E.Error, Unit>:
  match ok:
    case True{}:
      push_room(lim, n, v, D.length(U32, w))
    case False{}:
      (BL{lim, n, w}, Fail{E.Full{}})

def push(s: Bitlist, +v: Bool) -> Bitlist & Result<&2, &2, E.Error, Unit>:
  BL{+lim, +n, w} = s
  push_if(below(lim, n), lim, n, w, v)

# ---- pop ----

def pop_set(+lim: Maybe<&2, Nat>, +m: Nat, r: D.DynArray<&2, U32> & Result<&2, &2, DE.Error, Unit>) -> Bitlist & Result<&2, &2, E.Error, Bool>:
  match r:
    case Tuple{w, Done{u}}:
      (BL{lim, m, w}, Done{True{}})
    case Tuple{w, Fail{e}}:
      (BL{lim, m, w}, Done{True{}})

# The last bit b of word x: a set bit is cleared so the tail stays zero.
def pop_bit(+lim: Maybe<&2, Nat>, +m: Nat, w: D.DynArray<&2, U32>, +x: U32, +b: Bool) -> Bitlist & Result<&2, &2, E.Error, Bool>:
  match b:
    case False{}:
      (BL{lim, m, w}, Done{False{}})
    case True{}:
      pop_set(lim, m, D.set(U32, w, B.wordix(m), B.word_put(False{}, x, B.bitix(m))))

def pop_word(+lim: Maybe<&2, Nat>, +m: Nat, r: D.DynArray<&2, U32> & Result<&2, &2, DE.Error, U32>) -> Bitlist & Result<&2, &2, E.Error, Bool>:
  match r:
    case Tuple{w, Done{+x}}:
      pop_bit(lim, m, w, x, B.word_get(x, B.bitix(m)))
    case Tuple{w, Fail{e}}:
      (BL{lim, m, w}, Fail{E.Empty{}})

def pop_at(+lim: Maybe<&2, Nat>, +n: Nat, w: D.DynArray<&2, U32>) -> Bitlist & Result<&2, &2, E.Error, Bool>:
  match n:
    case 0n:
      (BL{lim, 0n, w}, Fail{E.Empty{}})
    case 1n+ +m:
      pop_word(lim, m, D.get(U32, w, B.wordix(m)))

def pop(s: Bitlist) -> Bitlist & Result<&2, &2, E.Error, Bool>:
  BL{+lim, +n, w} = s
  pop_at(lim, n, w)

# ---- clear ----

def clear(s: Bitlist) -> Bitlist:
  BL{lim, n, w} = s
  BL{lim, 0n, D.clear(U32, w)}

# ---- count ----

def count_add(g: D.DynArray<&2, U32> & Result<&2, &2, DE.Error, U32>, +acc: Nat) -> D.DynArray<&2, U32> & Nat:
  match g:
    case Tuple{w, Done{+x}}:
      (w, B.count_word(x, acc, U32.is_eq(x, 0)))
    case Tuple{w, Fail{e}}:
      (w, acc)

def count_go(k: Nat, p: D.DynArray<&2, U32> & Nat, +q: Nat) -> D.DynArray<&2, U32> & Nat:
  match k:
    case 0n:
      p
    case 1n+r:
      (w, +acc) = p
      count_go(r, count_add(D.get(U32, w, q), acc), 1n+q)

def count_fin(+lim: Maybe<&2, Nat>, +n: Nat, p: D.DynArray<&2, U32> & Nat) -> Bitlist & Nat:
  (w, c) = p
  (BL{lim, n, w}, c)

def count_len(+lim: Maybe<&2, Nat>, +n: Nat, r: D.DynArray<&2, U32> & Nat) -> Bitlist & Nat:
  (w, +k) = r
  count_fin(lim, n, count_go(k, (w, 0n), 0n))

def count(s: Bitlist) -> Bitlist & Nat:
  BL{+lim, +n, w} = s
  count_len(lim, n, D.length(U32, w))

# ---- to_list ----

# The low m bits of x, bit 0 first, in front of rest.
def word_bits(m: Nat, +x: U32, rest: List<&2, Bool>) -> List<&2, Bool>:
  match m:
    case 0n:
      rest
    case 1n+p:
      Con{B.low(x), word_bits(p, U32.shr(x), rest)}

# Word q holds bits 32q .. 32q+31; of the first n bits it contributes
# min(32, n - 32q) (none once 32q >= n).
def bits_add(+m: Nat, acc: List<&2, Bool>, g: D.DynArray<&2, U32> & Result<&2, &2, DE.Error, U32>) -> D.DynArray<&2, U32> & List<&2, Bool>:
  match g:
    case Tuple{w, Done{+x}}:
      (w, word_bits(m, x, acc))
    case Tuple{w, Fail{e}}:
      (w, acc)

# The first n bits, emitted from the last stored word down to word 0.
def bits_go(k: Nat, st: D.DynArray<&2, U32> & List<&2, Bool>, +n: Nat) -> D.DynArray<&2, U32> & List<&2, Bool>:
  match k:
    case 0n:
      st
    case 1n+ +q:
      (w, acc) = st
      bits_go(q, bits_add(Nat.min(32n, Nat.sub(n, Nat.mul(q, 32n))), acc, D.get(U32, w, q)), n)

def to_list_fin(+lim: Maybe<&2, Nat>, +n: Nat, p: D.DynArray<&2, U32> & List<&2, Bool>) -> Bitlist & List<&2, Bool>:
  (w, xs) = p
  (BL{lim, n, w}, xs)

def to_list_len(+lim: Maybe<&2, Nat>, +n: Nat, r: D.DynArray<&2, U32> & Nat) -> Bitlist & List<&2, Bool>:
  (w, +k) = r
  to_list_fin(lim, n, bits_go(k, (w, Nil{}), n))

def to_list(s: Bitlist) -> Bitlist & List<&2, Bool>:
  BL{+lim, +n, w} = s
  to_list_len(lim, n, D.length(U32, w))

# ---- from_bools ----

def from_push(p: Bitlist & Result<&2, &2, E.Error, Unit>) -> Bitlist:
  (s, r) = p
  s

def from_go(bs: List<&2, Bool>, s: Bitlist) -> Bitlist:
  match bs:
    case Nil{}:
      s
    case Con{+b, t}:
      from_go(t, from_push(push(s, b)))

# The bits of bs, in order, in an unbounded bitlist.
def from_bools(bs: List<&2, Bool>) -> Bitlist:
  from_go(bs, new())

# ---- one operation, for traces ----

def obs_nat(r: Bitlist & Nat) -> Bitlist & E.Obs:
  (s, x) = r
  (s, E.ONat{x})

def obs_bit(r: Bitlist & Result<&2, &2, E.Error, Bool>) -> Bitlist & E.Obs:
  (s, x) = r
  (s, E.OBit{x})

def obs_unit(r: Bitlist & Result<&2, &2, E.Error, Unit>) -> Bitlist & E.Obs:
  (s, x) = r
  (s, E.OUnit{x})

def obs_limit(r: Bitlist & Maybe<&2, Nat>) -> Bitlist & E.Obs:
  (s, x) = r
  (s, E.OLimit{x})

def obs_bits(r: Bitlist & List<&2, Bool>) -> Bitlist & E.Obs:
  (s, x) = r
  (s, E.OBits{x})

def step(s: Bitlist, op: E.Op) -> Bitlist & E.Obs:
  match op:
    case E.Length{}:
      obs_nat(length(s))
    case E.Limit{}:
      obs_limit(limit(s))
    case E.Get{+i}:
      obs_bit(get(s, i))
    case E.Assign{+i, +v}:
      obs_unit(assign(s, i, v))
    case E.Push{+v}:
      obs_unit(push(s, v))
    case E.Pop{}:
      obs_bit(pop(s))
    case E.Clear{}:
      (clear(s), E.OUnit{Done{Unit{}}})
    case E.Count{}:
      obs_nat(count(s))
    case E.ToList{}:
      obs_bits(to_list(s))

def record(acc: List<&2, E.Obs>, r: Bitlist & E.Obs) -> Bitlist & List<&2, E.Obs>:
  (s, o) = r
  (s, Con{o, acc})

def run_acc(ops: List<&2, E.Op>, st: Bitlist & List<&2, E.Obs>) -> Bitlist & List<&2, E.Obs>:
  match ops:
    case Nil{}:
      st
    case Con{op, rest}:
      (s, acc) = st
      run_acc(rest, record(acc, step(s, op)))

def finish(st: Bitlist & List<&2, E.Obs>) -> Bitlist & List<&2, E.Obs>:
  (s, os) = st
  (s, List.reverse(&2, E.Obs, os))

def run(ops: List<&2, E.Op>, s: Bitlist) -> Bitlist & List<&2, E.Obs>:
  finish(run_acc(ops, (s, Nil{})))

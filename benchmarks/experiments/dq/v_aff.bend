import Base
import ../../../types/deque.bend as E

# Double-ended queue: a RING BUFFER over a native Base.Array.
#
# Representation: DQ{depth, cap, lo, len, slots} with cap = 2^depth kept in
# the record. `slots` is a Base.Array of cap unboxed elements; the elements,
# front first, are the ring positions lo, lo + 1, ..., lo + len - 1 taken
# modulo cap, so element j lives in slot wrap(lo + j) where
# wrap(x) = x < cap ? x : x - cap (always applied to x < 2 cap, so it is the
# remainder mod cap). 0 <= lo < cap and len <= cap. Slots outside the ring
# hold stale values that are never read. A deque that has never held an
# element is DE{} and owns no block (Base.Array needs a filler value to
# allocate, and the first pushed element is it).
#
#   push_back   writes slot wrap(lo + len)                   (O(1))
#   push_front  moves lo one slot left (mod cap), writes it (O(1))
#   pop_front   reads slot lo, moves lo one slot right       (O(1))
#   pop_back    reads slot wrap(lo + len - 1)                (O(1))
#   peek_front  reads slot lo                                (O(1))
#   peek_back   reads slot wrap(lo + len - 1)                (O(1))
#   to_list     reads the len ring positions, back to front  (O(len))
#
# A push onto a FULL ring (len == cap) first grows it: a new block of 2 cap
# slots (filled with the pushed element) receives the len elements in order
# at slots 0 .. len - 1 and lo becomes 0 -- one O(len) copy after len pushes,
# so a push costs O(1) amortized. Pops never grow anything, so the block size
# follows the PEAK number of elements, not the number of pushes: steady
# push/pop traffic at a fixed size never reallocates.
#
# Capacity: the block has 2^depth slots with depth <= 31 (a Base.Array
# indexes correctly up to 2^31 slots, every slot index is a representable
# U32). A push that must grow a full ring of 2^31 elements would need 2^32
# slots; the push laws therefore carry the condition that the deque holds
# fewer than 2^31 elements when it is pushed onto (proofs/deque.bend).
#
# Every function is a template in the element type (`~T`), so every
# Base.Array call is compiled at a closed element type; the proofs are about
# these very definitions, instantiated at the checked element types.
#
# Errors: pop/peek on an empty deque return Fail{EmptyDeque} and the deque
# unchanged.

type Deque<-T: Data> is Type:
  DE{}
  DQ{depth: Nat, cap: Nat, lo: Nat, len: Nat, slots: Array<T>}

def max_depth() -> Nat:
  31n

# n - 1 on a nonzero n (the capacity 2^d is never zero).
def dec1(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# The slot of ring position x < 2 cap.
def wrap_go(+x: Nat, +cap: Nat, lt: Bool) -> Nat:
  match lt:
    case True{}:
      x
    case False{}:
      Nat.sub(x, cap)

def wrap(+x: Nat, +cap: Nat) -> Nat:
  wrap_go(x, cap, Nat.is_lt(x, cap))

def new(~T: Data) -> Deque<T>:
  DE{}

def length(~T: Data, d: Deque<T>) -> Deque<T> & Nat:
  match d:
    case DE{}:
      (DE{}, 0n)
    case DQ{dep, cp, lo, +len, a}:
      (DQ{dep, cp, lo, len, a}, len)

# ---- growth ----

# Copy ring positions j .. j + k - 1 of the full ring into slots
# j .. j + k - 1 of `dst`; `r` is the old block with ring position j already
# read (the read after the last copy is of a slot of the old block that is
# then dropped).
def copy_go(~T: Data, k: Nat, +j: Nat, +lo: Nat, +cap: Nat, dst: Array<T>, r: Array<T> & T) -> Array<T>:
  match k r:
    case 0n Tuple{src, x}:
      dst
    case 1n+ +p Tuple{src, x}:
      copy_go(~T, p, 1n+j, lo, cap, Array.set(T, dst, U32.from_nat(j), x), Array.get(T, src, U32.from_nat(wrap(Nat.add(lo, 1n+j), cap))))

# The block of a grown ring: 2 cap slots, the len elements at 0 .. len - 1.
def grow(~T: Data, +dep: Nat, +cap: Nat, +lo: Nat, +len: Nat, a: Array<T>, +v: T) -> Array<T>:
  copy_go(~T, len, 0n, lo, cap, Array.new(T, 1n+dep, v), Array.get(T, a, U32.from_nat(wrap(Nat.add(lo, 0n), cap))))

def first(~T: Data, +v: T) -> Deque<T>:
  DQ{0n, 1n, 0n, 1n, Array.new(T, 0n, v)}

# ---- push_back ----

def pb_room(~T: Data, +dep: Nat, +cap: Nat, +lo: Nat, +len: Nat, a: Array<T>, +v: T, room: Bool) -> Deque<T>:
  match room:
    case True{}:
      DQ{dep, cap, lo, 1n+len, Array.set(T, a, U32.from_nat(wrap(Nat.add(lo, len), cap)), v)}
    case False{}:
      DQ{1n+dep, Nat.double(cap), 0n, 1n+len, Array.set(T, grow(~T, dep, cap, lo, len, a, v), U32.from_nat(len), v)}

def push_back(~T: Data, d: Deque<T>, +v: T) -> Deque<T>:
  match d:
    case DE{}:
      first(~T, v)
    case DQ{+dep, +cap, +lo, +len, a}:
      pb_room(~T, dep, cap, lo, len, a, v, Nat.is_lt(len, cap))

# ---- push_front ----

def pf_lo(~T: Data, +dep: Nat, +cap: Nat, lo: Nat, +len: Nat, a: Array<T>, +v: T) -> Deque<T>:
  match lo:
    case 0n:
      DQ{dep, cap, dec1(cap), 1n+len, Array.set(T, a, U32.from_nat(dec1(cap)), v)}
    case 1n+ +k:
      DQ{dep, cap, k, 1n+len, Array.set(T, a, U32.from_nat(k), v)}

def pf_room(~T: Data, +dep: Nat, +cap: Nat, +lo: Nat, +len: Nat, a: Array<T>, +v: T, room: Bool) -> Deque<T>:
  match room:
    case True{}:
      pf_lo(~T, dep, cap, lo, len, a, v)
    case False{}:
      DQ{1n+dep, Nat.double(cap), dec1(Nat.double(cap)), 1n+len, Array.set(T, grow(~T, dep, cap, lo, len, a, v), U32.from_nat(dec1(Nat.double(cap))), v)}

def push_front(~T: Data, d: Deque<T>, +v: T) -> Deque<T>:
  match d:
    case DE{}:
      first(~T, v)
    case DQ{+dep, +cap, +lo, +len, a}:
      pf_room(~T, dep, cap, lo, len, a, v, Nat.is_lt(len, cap))

# ---- pop_front / pop_back ----

def popf_fin(~T: Data, +dep: Nat, +cap: Nat, +lo: Nat, +m: Nat, r: Array<T> & T) -> Deque<T> & Result<&2, &2, E.Error, T>:
  (a, x) = r
  (DQ{dep, cap, wrap(1n+lo, cap), m, a}, Done{x})

def popf_len(~T: Data, +dep: Nat, +cap: Nat, +lo: Nat, len: Nat, a: Array<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  match len:
    case 0n:
      (DQ{dep, cap, lo, 0n, a}, Fail{E.EmptyDeque{}})
    case 1n+ +m:
      popf_fin(~T, dep, cap, lo, m, Array.get(T, a, U32.from_nat(lo)))

def pop_front(~T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  match d:
    case DE{}:
      (DE{}, Fail{E.EmptyDeque{}})
    case DQ{+dep, +cap, +lo, len, a}:
      popf_len(~T, dep, cap, lo, len, a)

def popb_fin(~T: Data, +dep: Nat, +cap: Nat, +lo: Nat, +m: Nat, r: Array<T> & T) -> Deque<T> & Result<&2, &2, E.Error, T>:
  (a, x) = r
  (DQ{dep, cap, lo, m, a}, Done{x})

def popb_len(~T: Data, +dep: Nat, +cap: Nat, +lo: Nat, len: Nat, a: Array<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  match len:
    case 0n:
      (DQ{dep, cap, lo, 0n, a}, Fail{E.EmptyDeque{}})
    case 1n+ +m:
      popb_fin(~T, dep, cap, lo, m, Array.get(T, a, U32.from_nat(wrap(Nat.add(lo, m), cap))))

def pop_back(~T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  match d:
    case DE{}:
      (DE{}, Fail{E.EmptyDeque{}})
    case DQ{+dep, +cap, +lo, len, a}:
      popb_len(~T, dep, cap, lo, len, a)

# ---- peek_front / peek_back ----

def peek_fin(~T: Data, +dep: Nat, +cap: Nat, +lo: Nat, +len: Nat, r: Array<T> & T) -> Deque<T> & Result<&2, &2, E.Error, T>:
  (a, x) = r
  (DQ{dep, cap, lo, len, a}, Done{x})

def peekf_len(~T: Data, +dep: Nat, +cap: Nat, +lo: Nat, len: Nat, a: Array<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  match len:
    case 0n:
      (DQ{dep, cap, lo, 0n, a}, Fail{E.EmptyDeque{}})
    case 1n+ +m:
      peek_fin(~T, dep, cap, lo, 1n+m, Array.get(T, a, U32.from_nat(lo)))

def peek_front(~T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  match d:
    case DE{}:
      (DE{}, Fail{E.EmptyDeque{}})
    case DQ{+dep, +cap, +lo, len, a}:
      peekf_len(~T, dep, cap, lo, len, a)

def peekb_len(~T: Data, +dep: Nat, +cap: Nat, +lo: Nat, len: Nat, a: Array<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  match len:
    case 0n:
      (DQ{dep, cap, lo, 0n, a}, Fail{E.EmptyDeque{}})
    case 1n+ +m:
      peek_fin(~T, dep, cap, lo, 1n+m, Array.get(T, a, U32.from_nat(wrap(Nat.add(lo, m), cap))))

def peek_back(~T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>:
  match d:
    case DE{}:
      (DE{}, Fail{E.EmptyDeque{}})
    case DQ{+dep, +cap, +lo, len, a}:
      peekb_len(~T, dep, cap, lo, len, a)

# ---- to_list ----

# `r` is ring position k, already read; positions 0 .. k - 1 are still to
# be read (back to front, so the list is built front first).
def tl_go(~T: Data, k: Nat, +lo: Nat, +cap: Nat, acc: List<&1, T>, r: Array<T> & T) -> Array<T> & List<&1, T>:
  match k r:
    case 0n Tuple{a, x}:
      (a, Con{x, acc})
    case 1n+ +p Tuple{a, x}:
      tl_go(~T, p, lo, cap, Con{x, acc}, Array.get(T, a, U32.from_nat(wrap(Nat.add(lo, p), cap))))

def tl_fin(~T: Data, +dep: Nat, +cap: Nat, +lo: Nat, +len: Nat, r: Array<T> & List<&1, T>) -> Deque<T> & List<&1, T>:
  (a, xs) = r
  (DQ{dep, cap, lo, len, a}, xs)

def tl_len(~T: Data, +dep: Nat, +cap: Nat, +lo: Nat, len: Nat, a: Array<T>) -> Deque<T> & List<&1, T>:
  match len:
    case 0n:
      (DQ{dep, cap, lo, 0n, a}, Nil{})
    case 1n+ +m:
      tl_fin(~T, dep, cap, lo, 1n+m, tl_go(~T, m, lo, cap, Nil{}, Array.get(T, a, U32.from_nat(wrap(Nat.add(lo, m), cap)))))

def to_list(~T: Data, d: Deque<T>) -> Deque<T> & List<&1, T>:
  match d:
    case DE{}:
      (DE{}, Nil{})
    case DQ{+dep, +cap, +lo, len, a}:
      tl_len(~T, dep, cap, lo, len, a)

